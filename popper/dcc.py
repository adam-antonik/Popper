#!/usr/bin/env python3

import logging
import sys
import time
from datetime import datetime
from . util import Settings, Stats, timeout, parse_settings, format_program
from . asp import ClingoGrounder, ClingoSolver
from . tester import Tester
from . constrain import Constrain
from . generate import generate_program
from . core import Grounding, Clause, Literal, separable
from collections import defaultdict

WITH_OPTIMISTIC = False
WITH_CHUNKING = True
WITH_LAZINESS = True
WITH_MIN_LITERALS = False
WITH_MIN_LITERALS = True
WITH_MIN_RULE_SIZE = False
WITH_MIN_RULE_SIZE = True
WITH_MAX_RULE_BOUND = False
WITH_MAX_RULE_BOUND = True
WITH_CRAP_CHECK = False
WITH_CRAP_CHECK = True
WITH_BOOTSTRAPPING = True
WITH_SUBSUMPTION = False
WITH_SUBSUMPTION = True
WITH_COVERAGE_CHECK = False
# WITH_COVERAGE_CHECK = True
MAX_RULES = 6

class Bounds:
    def __init__(self, max_literals):
        self.min_literals = 1
        self.max_literals = max_literals
        self.min_rules = 1
        self.max_rules = MAX_RULES
        self.min_rule_size = 1

class Constraints:

    def __init__(self, tracker, generalisation, specialisation, redundancy, subsumption, elimination):
        self.tracker = tracker
        self.handles = set()

        def filter_rules(xs):
            for rule in xs:
                h, _b = rule
                if h:
                    self.handles.add(rule)
                else:
                    yield rule

        self.generalisation = set(filter_rules(generalisation))
        self.specialisation = set(filter_rules(specialisation))
        self.redundancy = set(filter_rules(redundancy))
        self.subsumption = set(filter_rules(subsumption))
        self.elimination = set(filter_rules(elimination))

    def all(self):
        return self.handles | self.generalisation | self.specialisation | self.redundancy | self.subsumption | self.elimination


class Tracker:
    def __init__(self, settings):
        self.settings = settings
        self.min_total_literals = 1
        self.max_total_literals = None
        self.min_total_rules = 1
        self.max_total_rules = MAX_RULES
        self.best_prog = None
        self.best_prog_size = None
        self.best_prog_errors = None
        self.best_progs = {}
        self.seen_consistent = set()
        self.seen_inconsistent = set()
        self.seen_crap = set()
        self.pos_coverage = {}
        # TMP!!
        self.pos_coverage2 = {}

        self.settings.WITH_OPTIMISTIC = WITH_OPTIMISTIC
        self.settings.WITH_CHUNKING = WITH_CHUNKING
        self.settings.WITH_LAZINESS = WITH_LAZINESS
        self.settings.WITH_MIN_RULE_SIZE = WITH_MIN_RULE_SIZE
        self.tester = Tester(settings)
        self.max_total_literals = settings.max_literals
        self.stats = Stats(log_best_programs=settings.info)
        self.pos = frozenset(self.tester.pos)
        self.neg = frozenset(self.tester.neg)
        self.best_progs = {ex:None for ex in self.pos}
        self.stats.crap_count = 0

        # VERY HACKY
        with open(settings.bias_file) as f:
            f_txt = f.read()
            self.settings.recursion = 'enable_recursion' in f_txt
            self.settings.predicate_invention = 'enable_pi' in f_txt

def bind_vars_in_cons(stats, grounder, clauses):
    ground_cons = set()

    for clause in clauses:
        head, body = clause

        with stats.duration('grounder.find_bindings'):
        # find bindings for variables in the constraint
            assignments = grounder.find_bindings(clause)

        # keep only standard literals
        body = tuple(literal for literal in body if not literal.meta)

        with stats.duration('Grounding.ground_clause'):
            # ground the clause for each variable assignment
            for assignment in assignments:
                ground_cons.add(Grounding.ground_clause((head, body), assignment))

    return ground_cons

def get_rule_ids(body):
    ids = set()
    for lit in body:
        if not isinstance(lit, Literal):
            continue
        if lit.predicate != 'included_clause':
            continue
        sym = lit.arguments[0]
        # sym = sym[1:-1]
        xs = sym.split(':-')
        b = xs[1]
        ids.add(frozenset(x.strip().replace('.',',') for x in b.split(',')))
    return frozenset(ids)

def get_handles(body):
    ids = set()
    for lit in body:
        if not isinstance(lit, Literal):
            continue
        if lit.predicate != 'included_clause':
            continue
        sym = lit.arguments[0]
        # sym = sym[1:-1]
        # xs = sym.split(':-')
        # b = xs[1]
        ids.add(sym)
    return ids

def get_something(body):
    ids = set()
    for lit in body:
        if lit.predicate == 'included_clause':
            return lit.arguments[0]

def tmp_subsumes(t1, t2):
    return all(any(r1.issubset(r2) for r1 in t1) for r2 in t2)

def build_constraints(tracker, stats, constrainer, tester, program, pos):
    cons = set()

    with stats.duration('build_a'):
        if tester.is_complete(program, pos):
            cons.update(constrainer.generalisation_constraint(program))
        else:
            cons.update(constrainer.specialisation_constraint(program))

            if tester.is_totally_incomplete(program, pos):
                cons.update(constrainer.redundancy_constraint(program))

    with stats.duration('build_b'):
        if tester.is_inconsistent(program):
            cons.update(constrainer.generalisation_constraint(program))
        else:
            if not tracker.settings.functional_test or tester.is_functional(program, pos):
                cons.update(constrainer.specialisation_constraint(program))

    # eliminate rules subsumed by this one
    if WITH_SUBSUMPTION:
        for rule in program:
            cons.update(constrainer.subsumption_constraint(rule))

    # apply functional test only when the program is complete and consistent
    if tracker.settings.functional_test and tester.is_complete(program, pos) and tester.is_non_functional(program, pos) and not tester.is_inconsistent(program):
        cons.update(constrainer.generalisation_constraint(program))

    # eliminate generalisations of rules with redundant literals
    for rule in program:
        if tester.rule_has_redundant_literal(rule):
            cons.update(constrainer.generalisation_constraint([rule]))

    if WITH_CRAP_CHECK:
        if program in tracker.seen_crap:
            cons.update(constrainer.elimination_constraint(program))

    with stats.duration('build_c'):
        if len(program) > 1:

            with stats.duration('build_c1'):
                # detect subsumption redundant rules
                for r1, r2 in tester.find_redundant_clauses(tuple(program)):
                    cons.update(constrainer.subsumption_constraint_pairs(r1, r2))

            with stats.duration('build_c2'):
                for rule in program:
                    sub_prog = frozenset([rule])

                    if tester.is_complete(sub_prog, pos):
                        cons.update(constrainer.generalisation_constraint(sub_prog))
                    else:
                        cons.update(constrainer.specialisation_constraint(sub_prog))

                    if tester.is_inconsistent(sub_prog):
                        cons.update(constrainer.generalisation_constraint(sub_prog))
                    else:
                        cons.update(constrainer.specialisation_constraint(sub_prog))

                    if WITH_CRAP_CHECK:
                        if sub_prog in tracker.seen_crap:
                              cons.update(constrainer.elimination_constraint([rule]))

            with stats.duration('build_c3'):
                if not tester.is_complete(program, pos) and separable(program):
                    for rule in program:
                        if tester.is_totally_incomplete(frozenset([rule]), pos):
                            cons.update(constrainer.redundancy_constraint([rule]))

    return cons

def cache_rules(tracker, program):
    if tracker.tester.is_inconsistent(program):
        tracker.seen_inconsistent.add(program)
    else:
        tracker.seen_consistent.add(program)

    if len(program) > 1:
        for rule in program:
            cache_rules(tracker, frozenset([rule]))

# def print_stats(cons, stats, grounder):
#     print(f'ALL:\t{len(cons.all())}')
#     print(f'INCS:\t{len(cons.handles)}')
#     print(f'GENS:\t{len(cons.generalisation)}')
#     print(f'SPEC:\t{len(cons.specialisation)}')
#     print(f'SUBS:\t{len(cons.subsumption)}')
#     print(f'REDU:\t{len(cons.redundancy)}')
#     ground_cons = bind_vars_in_cons(stats, grounder, cons.all())
#     print(f'GROUND:\t{len(ground_cons)}')
#     print(f'GROUND_INCS:\t{len(bind_vars_in_cons(stats, grounder, cons.handles))}')
#     print(f'GROUND_GENS:\t{len(bind_vars_in_cons(stats, grounder, cons.generalisation))}')
#     print(f'GROUND_SPEC:\t{len(bind_vars_in_cons(stats, grounder, cons.specialisation))}')
#     print(f'GROUND_SUBS:\t{len(bind_vars_in_cons(stats, grounder, cons.subsumption))}')
#     print(f'GROUND_REDU:\t{len(bind_vars_in_cons(stats, grounder, cons.redundancy))}')

# def save_cons(cons, name):
#     with open(f'{name}.pl', 'w') as f:
#         f.write('%chandles\n')
#         for rule in cons.handles:
#             f.write(Constrain.format_rule_clingo(rule) + '\n')
#         f.write('%generalisations\n')
#         for rule in cons.generalisation:
#             f.write(Constrain.format_rule_clingo(rule) + '\n')
#         f.write('%specialisation\n')
#         for rule in cons.specialisation:
#             f.write(Constrain.format_rule_clingo(rule) + '\n')
#         f.write('%redundancy\n')
#         for rule in cons.redundancy:
#             f.write(Constrain.format_rule_clingo(rule) + '\n')
#         f.write('%subs\n')
#         for rule in cons.subsumption:
#             f.write(Constrain.format_rule_clingo(rule) + '\n')
#         f.write('%elimination\n')
#         for rule in cons.elimination:
#             f.write(Constrain.format_rule_clingo(rule) + '\n')

    # with open(f'{name}.pl', 'w') as f:
    #     for rule in cons.generalisation | cons.specialisation | cons.elimination:
    #         f.write(Constrain.format_rule_clingo(rule) + '\n')

    # for rule in cons.covers:
        # f.write(rule + '.\n')

def popper(tracker, pos, neg, bootstap_cons, chunk_bounds):
    settings = tracker.settings
    stats = tracker.stats
    tester = tracker.tester
    constrainer = Constrain()
    solver = ClingoSolver(settings, chunk_bounds.max_rules, chunk_bounds.min_rule_size)
    grounder = ClingoGrounder(chunk_bounds.max_rules, solver.max_vars)

    dbg('POS:', chunk_bounds.max_literals, chunk_bounds.max_rules)

    all_fo_cons = bootstap_cons.all()

    # GROUND OLD CONSTRAINTS AND ADD TO SOLVER
    with stats.duration('bootstrap_ground'):
        ground_cons = bind_vars_in_cons(stats, grounder, all_fo_cons)
    with stats.duration('bootstrap_add'):
        solver.add_ground_clauses(ground_cons)

    min_size = chunk_bounds.min_literals if WITH_MIN_LITERALS else 1

    for size in range(min_size, chunk_bounds.max_literals + 1):
        dbg(f'num_literals:{size}')
        solver.update_number_of_literals(size)

        while True:

            # GENERATE HYPOTHESIS
            with stats.duration('generate'):
                model = solver.get_model()
                if not model:
                    break
                program = generate_program(model)

            # assert(len(program) == num_rules)
            # if size < chunk_bounds.min_literals:
            #     print('PROGRAM TOO SMALL')
            #     pprint(program)

            # if min(len(b) for h, b in program) < chunk_bounds.min_rule_size:
            #     print('PROGRAM TOO SMALL')
            #     pprint(program)

            tracker.stats.total_programs += 1

            if tracker.settings.debug:
                print('')
                pprint(program)
            #     # print('separable', separable(program))
            #     if separable(program):
            #         for rule in program:
            #             tmp = frozenset([rule])
            #             # print(tracker.tester.test(tmp, pos, neg), tracker.tester.test_all(tmp), tmp in tracker.seen_consistent)
            #     else:
            #         pass
            #         # print(tracker.tester.test(program, pos, neg), tracker.tester.test_all(program), program in tracker.seen_consistent)

            # assert(program not in tracker.seen_inconsistent)
            # assert(all(frozenset([rule]) not in tracker.seen_inconsistent for rule in program))

            # TEST HYPOTHESIS AND UPDATE BEST PROGRAM
            solution_found = False
            # tx = time.time()
            with stats.duration('test'):
                if tester.is_complete(program, pos) and not tester.is_inconsistent(program):
                    if not tracker.settings.functional_test or tester.is_functional(program, pos):
                        solution_found = True
            # ty = time.time()
            # print(f'test: {ty-tx}')

            # # if WITH_CRAP_CHECK:
            # has_crap = False
            # if program in tracker.seen_crap2:
            #     print('CRAP1')
            #     pprint(program)
            #     has_crap = True
            # for rule in program:
            #     if frozenset([rule]) in tracker.seen_crap2:
            #         print('CRAP2')
            #         pprint([rule])
            #         has_crap = True
            # if has_crap:
            #     stats.crap_count +=1

            with stats.duration('crap and cache'):
                check_crap(tracker, program)
                check_crap2(tracker, program)
                if len(program) > 1:
                    for rule in program:
                        check_crap(tracker, frozenset([rule]))
                        check_crap2(tracker, frozenset([rule]))

            with stats.duration('cache_rules'):
                cache_rules(tracker, program)

            if solution_found:
                return program

            # BUILD CONSTRAINTS
            # tx = time.time()
            with stats.duration('build'):
                fo_cons = build_constraints(tracker, stats, constrainer, tester, program, pos) - all_fo_cons
                all_fo_cons.update(fo_cons)
            # ty = time.time()
            # print(f'build: {ty-tx}')

            # GROUND CONSTRAINTS
            with stats.duration('ground'):
                ground_cons = bind_vars_in_cons(stats, grounder, fo_cons)

            # ADD CONSTRAINTS TO SOLVER
            with stats.duration('add'):
                solver.add_ground_clauses(ground_cons)
    return None

def tmp():
    now = datetime.now()
    current_time = now.strftime("%H:%M:%S")
    return current_time

def dbg(*args):
    print(tmp(), *args)

def pprint(prog):
    for rule in prog:
        dbg(Clause.to_code(rule) + '.')

def num_literals(prog):
    return sum(1 + len(body) for head_, body in prog)

def calc_score(tester, prog):
    fn = sum(1 for x in tester.pos if not tester.is_complete(prog, [x]))
    # tp, fn, tn, fp = tester.test_all(prog)
    return fn

def calc_score_subset(tester, prog, pos):
    fn = sum(1 for x in pos if not tester.is_complete(prog, [x]))
    # fn = len(pos) - tp
    # tp, fn, tn, fp = tester.test(prog, pos, tester.neg)
    return fn

def best_prog_improvement(tracker, prog):
    if tracker.best_prog is None:
        return True
    errors = calc_score(tracker.tester, prog)
    if errors < tracker.best_prog_errors:
        return True
    if errors == tracker.best_prog_errors and num_literals(prog) < tracker.best_prog_size:
        return True
    return False

def chunks(xs, size):
    for i in range(0, len(xs), size):
        yield xs[i:i+size]

def flatten(xs):
    return [item for sublist in xs for item in sublist]

def update_best_prog(tracker, prog):
    tracker.best_prog = prog
    tracker.best_prog_size = num_literals(prog)
    tracker.best_prog_errors = calc_score(tracker.tester, prog)

    dbg(f'BEST_PROG size:{tracker.best_prog_size} errors:{tracker.best_prog_errors}')
    pprint(prog)

    if tracker.best_prog_errors > 0:
        return

    if tracker.best_prog == None:
        return

    old_max_literals = tracker.max_total_literals
    tracker.max_total_literals = min(tracker.best_prog_size -1, tracker.max_total_literals)
    dbg(f'NEW MAX_LITERALS - OLD:{old_max_literals} NEW:{tracker.max_total_literals}')

def calc_max_rules(tracker, best_prog, chunk_exs):
    k = tracker.max_total_rules
    if best_prog != None:
        k = min(k, len(best_prog))

    if tracker.settings.recursion or tracker.settings.predicate_invention:
        return k

    if WITH_MAX_RULE_BOUND:
        if best_prog != None and len(best_prog) > 1:
            k = min(k, len(best_prog)-1)

    k = min(k, len(chunk_exs))
    return k

def calc_max_literals(tracker, best_prog):
    k = tracker.max_total_literals
    if best_prog != None:
        best_prog_size = num_literals(best_prog)
        # minus -1 because we want to learn a smaller program than the best one so far
        k = min(k, best_prog_size-1)
    return k

def calc_min_rule_size(tracker, best_prog):
    if best_prog != None:
        return 1 + min(len(body) for head, body in best_prog)
    return 1

def calc_chunk_bounds(tracker, best_prog, chunk_exs):
    bounds = Bounds(tracker.max_total_literals)

    if tracker.best_prog == None or tracker.best_prog_errors > 0:
        return bounds

    bounds.min_literals = 1 #
    if all(tracker.best_progs[ex] != None for ex in chunk_exs):
        bounds.min_literals = max(num_literals(tracker.best_progs[ex]) for ex in chunk_exs)
    bounds.max_rules = calc_max_rules(tracker, best_prog, chunk_exs)
    bounds.max_literals = calc_max_literals(tracker, best_prog)
    bounds.min_rule_size = calc_min_rule_size(tracker, best_prog)
    return bounds

def check_crap(tracker, prog):
    if tracker.settings.recursion or tracker.settings.predicate_invention:
        return

    if tracker.tester.is_inconsistent(prog):
        return

    # if tracker.is_totally_incomplete(prog, pos):
        # return

    xs = tracker.tester.all_pos_covered(prog)
    if xs not in tracker.pos_coverage:
        tracker.pos_coverage[xs] = prog
        return

    other_prog = tracker.pos_coverage[xs]

    if prog == other_prog:
        pass

    # if this program is smaller than another with the same success set
    elif num_literals(prog) < num_literals(other_prog):
        # then the other program is crap
        tracker.seen_crap.add(other_prog)
        tracker.pos_coverage[xs] = prog
    else:
        tracker.seen_crap.add(prog)

def check_crap2(tracker, prog):
    if tracker.settings.recursion or tracker.settings.predicate_invention:
        return

    if prog in tracker.pos_coverage2:
        return

    if tracker.tester.is_inconsistent(prog):
        return

    xs = tracker.tester.all_pos_covered(prog)

    to_remove = set()
    for prog2, xs2 in tracker.pos_coverage2.items():
        # if the other program is smaller and has a larger coverage
        if num_literals(prog2) < num_literals(prog) and xs.issubset(xs2):
            # then this program is crap
            tracker.seen_crap.add(prog)
            return
        # if this program is smaller and has a larger coverage
        if num_literals(prog) < num_literals(prog2) and xs2.issubset(xs):
            # other program is crap
            tracker.seen_crap.add(prog2)
            to_remove.add(prog2)
            # might be able to break here

    for k in to_remove:
        del tracker.pos_coverage2[k]

    tracker.pos_coverage2[prog] = xs

def check_old_programs(tracker, chunk_exs, chunk_bounds):
    # check all programs seen so far, the outputs are:
    # 1. the smallest complete and consistent hypothesis seen so far
    # 2. a set of constraints for the other programs

    tester = tracker.tester
    constrainer = Constrain()

    generalisation = set()
    specialisation = set()
    redundancy = set()
    subsumption = set()
    elimination = set()

    chunk_prog = None

    # CHECK CONSISTENT PROGRAMS
    dbg('CHECK CONSISTENT PROGRAMS')
    with tracker.stats.duration('CHECK CONSISTENT PROGRAMS'):
        for prog in tracker.seen_consistent:

            # if the program is too big, ignore it
            if num_literals(prog) > chunk_bounds.max_literals:
                continue

            if tester.is_complete(prog, chunk_exs):
                # if the program is not functional then we can prune generalisations of it
                if tracker.settings.functional_test and not tester.is_functional(prog, chunk_exs):
                    generalisation.update(constrainer.generalisation_constraint(prog))
                    continue

                # if prog is complete, then no need to make it more general
                # no need to add any constraints as we will never consider programs bigger than it (since it is complete and consistent)
                chunk_prog = prog
                chunk_bounds = calc_chunk_bounds(tracker, chunk_prog, chunk_exs)
                continue

            if not tracker.settings.functional_test or tester.is_functional(prog, chunk_exs):
                # if prog is consistent, then no need to make it more specific
                specialisation.update(constrainer.specialisation_constraint(prog))

            # TODO: CHECK WHETHER SEPARABLE CHECK IS NECESSARY
            if separable(prog):
                if tester.is_totally_incomplete(prog, chunk_exs):
                    redundancy.update(constrainer.redundancy_constraint(prog))
            else:
                if tester.is_totally_incomplete(prog, chunk_exs):
                    pass
                    # TODO: FIX - CAN ONLY APPLY WHEN THE PROGRAM HAS A BASECASE
                    # None included_clause(f(A):- f(C),tail(B.C),tail(A.B),C0),AllDifferent(C0),num_recursive(f,1)
                    # None included_clause(f(A):- f(B),tail(A.B),tail(B.A),C0),included_clause(f(A):- empty(A),C1),AllDifferent(C0,C1),num_recursive(f,1)

            if WITH_SUBSUMPTION:
                for rule in prog:
                    subsumption.update(constrainer.subsumption_constraint(rule))

            for rule in prog:
                if tester.rule_has_redundant_literal(rule):
                    generalisation.update(constrainer.generalisation_constraint([rule]))

            if len(prog) > 1:
                for r1, r2 in tester.find_redundant_clauses(tuple(prog)):
                    subsumption.update(constrainer.subsumption_constraint_pairs(r1, r2))

            # if WITH_COVERAGE_CHECK:
            #     for rule in prog:
            #         _, body = rule
            #         handle = constrainer.make_clause_handle(rule)
            #         covers.add(f'seen({handle},{len(body)})')
            #         for ex in chunk_exs:
            #             if tester.is_complete([rule], [ex]):
            #                 covers.add(f'covers({handle},{ex})')

        # if WITH_COVERAGE_CHECK:
        #     for e in chunk_exs:
        #         covers.add(f'example({e})')

    dbg('CHECK INCONSISTENT PROGRAMS')
    # CHECK INCONSISTENT PROGRAMS
    with tracker.stats.duration('CHECK INCONSISTENT PROGRAMS'):
        for prog in tracker.seen_inconsistent:
            prog_size = num_literals(prog)

            if prog_size > chunk_bounds.max_literals:
                continue

            generalisation.update(constrainer.generalisation_constraint(prog))

            # TODO: CHECK THE RECURSION ISSUE
            if not tester.is_complete(prog, chunk_exs):
                specialisation.update(constrainer.specialisation_constraint(prog))

                if tester.is_totally_incomplete(prog, chunk_exs):
                    redundancy.update(constrainer.redundancy_constraint(prog))



            if WITH_SUBSUMPTION:
                for rule in prog:
                    subsumption.update(constrainer.subsumption_constraint(rule))

            # t1 = time.time()
            for rule in prog:
                if tester.rule_has_redundant_literal(rule):
                    generalisation.update(constrainer.generalisation_constraint([rule]))
            t2 = time.time()
            # print('c', t2-t1)

            t1 = time.time()
            if len(prog) > 1:
                for r1, r2 in tester.find_redundant_clauses(tuple(prog)):
                    subsumption.update(constrainer.subsumption_constraint_pairs(r1, r2))
            t2 = time.time()
            # print('d', t2-t1)

    if WITH_CRAP_CHECK:
        # a program is crap if it is consistent and there is a smaller program with the same success set
        for prog in tracker.seen_crap:
            elimination.update(constrainer.elimination_constraint(prog))

    cons = Constraints(tracker, generalisation, specialisation, redundancy, subsumption, elimination)

    return chunk_prog, cons

def form_union(progs):
    union = set()
    for prog in progs:
        union.update(prog)
    return frozenset(union)

def remove_redundancy(tester, old_prog, pos):
    dbg('REMOVE_REDUNDANCY')
    assert(tester.is_complete(old_prog, pos))
    dbg('OLD_PROG')
    pprint(old_prog)
    old_success_set = tester.pos_covered_all(old_prog)
    new_prog = tester.reduce_subset(old_prog, pos)
    assert(tester.is_complete(new_prog, pos))
    dbg('NEW_PROG')
    pprint(new_prog)
    new_success_set = tester.pos_covered_all(new_prog)
    assert(old_success_set == new_success_set)
    if len(new_prog) < len(old_prog):
        dbg(f'reduced program from {len(old_prog)} to {len(new_prog)}')
    return new_prog

def get_union_of_example_progs(tracker, chunk_exs):
    # print('GET_UNION_OF_EXAMPLE_PROGS')
    if any(tracker.best_progs[ex] == None for ex in chunk_exs):
        return None
    union = form_union([tracker.best_progs[ex] for ex in chunk_exs])
    assert(tracker.tester.is_complete(union, chunk_exs))
    assert(not tracker.tester.is_inconsistent(union))
    chunk_prog = remove_redundancy(tracker.tester, union, chunk_exs)
    dbg(f'BEST_SO_FAR size:{num_literals(chunk_prog)} errors:{calc_score(tracker.tester, chunk_prog)}')
    pprint(chunk_prog)
    assert(tracker.tester.is_complete(chunk_prog, chunk_exs))
    assert(not tracker.tester.is_inconsistent(chunk_prog))
    assert(len(chunk_prog) == len(tracker.tester.reduce_subset(chunk_prog, chunk_exs)))
    return chunk_prog

def reuse_seen(tracker, chunk_exs, iteration_progs, chunk_bounds):
    # first filter programs that are small enough
    seen = (seen_prog for seen_prog in iteration_progs if num_literals(seen_prog) <= chunk_bounds.max_literals)
    # now sort by program size
    seen = sorted(seen, key = lambda x: num_literals(x))
    # take the first program we find that is complete
    for seen_prog in seen:
        if tracker.tester.is_complete(seen_prog, chunk_exs):
            return seen_prog
    return None

def process_chunk(tracker, chunk_exs, iteration_progs):
    chunk_prog = get_union_of_example_progs(tracker, chunk_exs)

    chunk_bounds = calc_chunk_bounds(tracker, chunk_prog, chunk_exs)

    # if we cannot learn something smaller, then this chunk program is the union of all the solutions for the smaller chunks
    if chunk_bounds.min_literals >= chunk_bounds.max_literals:
        return chunk_prog

    if WITH_LAZINESS:
        # try to reuse an already found hypothesis
        complete_seen_prog = reuse_seen(tracker, chunk_exs, iteration_progs, chunk_bounds)
        if complete_seen_prog:
            return complete_seen_prog

    bootstap_cons = set()

    if WITH_BOOTSTRAPPING:
        # find the best program already seen and build constraints for the other programs
        with tracker.stats.duration('check_old_programs'):
            complete_seen_prog, bootstap_cons = check_old_programs(tracker, chunk_exs, chunk_bounds)

        # this program might not be in the hypothesis, so we might need to search for a smaller one
        if complete_seen_prog:
            chunk_prog = complete_seen_prog
            chunk_bounds = calc_chunk_bounds(tracker, chunk_prog, chunk_exs)

            # also update when an improvement is possible
            if chunk_bounds.min_literals >= chunk_bounds.max_literals:
                return chunk_prog

    dbg(f'min_literals:{chunk_bounds.min_literals} max_literals:{chunk_bounds.max_literals} max_rules:{chunk_bounds.max_rules}')

    # call popper with the chunk examples and constraints
    t1 = time.time()
    new_solution = popper(tracker, chunk_exs, tracker.neg, bootstap_cons, chunk_bounds)
    t2 = time.time()
    # print('popper time', t2-t1)

    if new_solution == None:
        return chunk_prog

    chunk_prog = frozenset(new_solution)

    assert(tracker.tester.is_complete(chunk_prog, chunk_exs))
    assert(not tracker.tester.is_inconsistent(chunk_prog))
    assert(not tracker.tester.check_redundant_clause(chunk_prog))

    # dbg(f'NEW PROGRAM size:{num_literals(chunk_prog)} chunk_errors:{calc_score_subset(tracker.tester, chunk_prog, chunk_exs)} all_errors:{calc_score(tracker.tester, chunk_prog)}')
    dbg(f'NEW PROGRAM size:{num_literals(chunk_prog)}')
    pprint(chunk_prog)
    return chunk_prog

def learn_iteration_prog(tracker, all_chunks, chunk_size):
    # partition the positive examples in chunks of size chunk_size
    these_chunks = list(chunks(all_chunks, chunk_size))

    all_exs = []
    for chunk in all_chunks:
        all_exs.extend(chunk)

    iteration_progs = set()

    for chunk_num, chunk_exs in enumerate(these_chunks):
        chunk_exs = flatten(chunk_exs)

        dbg(f'chunk:{chunk_num+1}/{len(these_chunks)} num_examples:{len(chunk_exs)}')

        chunk_prog = process_chunk(tracker, chunk_exs, iteration_progs)

        if not chunk_prog:
            # return None, 'SHIT'
            continue

        # chunk_prog is guaranteed to be complete, consistent, and smaller than the previous best
        assert(tracker.tester.is_complete(chunk_prog, chunk_exs))
        assert(not tracker.tester.is_inconsistent(chunk_prog))

        # if we find a program that is complete and consistent for all examples then we can stop
        if tracker.tester.is_complete(chunk_prog, all_exs) and not tracker.tester.is_inconsistent(chunk_prog):
            return chunk_prog, True

        for ex in chunk_exs:
            tracker.best_progs[ex] = chunk_prog

        iteration_progs.add(chunk_prog)

    # dbg('ITERATION_PROGS')
    iteration_prog = form_union(iteration_progs)
    # dbg('ITERATION_PROG')
    # pprint(iteration_prog)
    # print('TYPE(ITERATION_PROG)',type(iteration_prog), type(these_chunks), type(these_chunks[0]))
    # print(type(iteration_prog), iteration_prog, type(all_exs), all_exs)
    # tracker.stats.show()
    assert(tracker.tester.is_complete(iteration_prog, all_exs))
    # print('ASDA!!!')
    # print('len(chunk_exs)', len(all_exs))
    iteration_prog = remove_redundancy(tracker.tester, iteration_prog, all_exs)

    # print('TYPE(ITERATION_PROG)',type(iteration_prog))
    # pprint(iteration_prog)
    assert(tracker.tester.is_complete(iteration_prog, chunk_exs))
    if not tracker.settings.recursion:
        assert(not tracker.tester.is_inconsistent(iteration_prog))
    return iteration_prog, False

def perform_chunking(tracker):
    tmp_chunks = {}
    for ex in tracker.pos:
        prog = tracker.best_progs[ex]
        # IF NO SOLUTION THEN IGNORE
        if prog == None:
            dbg(f'NO SOLUTION FOR EX: {ex} SO SKIPPING')
        elif prog not in tmp_chunks:
            tmp_chunks[prog] = set([ex])
        else:
            tmp_chunks[prog].add(ex)
    return list(tmp_chunks.values())

def dcc(settings):
    # maintain stuff during the search
    tracker = Tracker(settings)

    # size of the chunks/partitions of the examples
    chunk_size = 1

    # initially partitions each example into its own partition
    all_chunks = [[x] for x in tracker.pos]

    while True:
        dbg('CHUNK_SIZE', chunk_size)

        # program for this chunk size is the union of the chunk progs
        iteration_prog, proven_optimal = learn_iteration_prog(tracker, all_chunks, chunk_size)
        if proven_optimal == 'SHIT':
            tracker.stats.show()
            return tracker.best_prog, tracker.stats

        # TODO: add early stopping here
        if proven_optimal:
            if best_prog_improvement(tracker, iteration_prog):
                update_best_prog(tracker, iteration_prog)
            break

        dbg(f'CHUNK:{chunk_size} size:{num_literals(iteration_prog)} errors:{calc_score(tracker.tester, iteration_prog)}')

        pprint(iteration_prog)

        if best_prog_improvement(tracker, iteration_prog):
            # update the best program for each example
            # we logically reduce the iteration_prog with respect to each positive example
            for ex in flatten(all_chunks):
                tracker.best_progs[ex] = tracker.tester.reduce_subset(iteration_prog, [ex])

            update_best_prog(tracker, iteration_prog)

            if WITH_OPTIMISTIC and tracker.best_prog_errors == 0:
                break

        if WITH_CHUNKING:
            all_chunks = perform_chunking(tracker)

        if len(all_chunks) == 1 or chunk_size > len(tracker.pos):
            break

        # double the chunk size (loop at most log(len(pos)) iterations)
        chunk_size += chunk_size
        # chunk_size += 1

    print('SOLUTION:')
    for rule in tracker.best_prog:
        print(Clause.to_code(rule) + '.')
    return tracker.best_prog, tracker.stats