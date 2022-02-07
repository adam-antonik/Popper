#!/usr/bin/env python3

import logging
import sys
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
# WITH_MIN_LITERALS = True
WITH_MIN_RULE_SIZE = False
# WITH_MIN_RULE_SIZE = True
WITH_MAX_RULE_BOUND = False
WITH_MAX_RULE_BOUND = True
WITH_CRAP_CHECK = False
WITH_CRAP_CHECK = True
WITH_BOOTSTRAPPING = True
WITH_SUBSUMPTION = False
WITH_SUBSUMPTION = True
WITH_COVERAGE_CHECK = False
# WITH_COVERAGE_CHECK = True
MAX_RULES = 4

class Bounds:
    def __init__(self, max_literals):
        self.min_literals = 1
        self.max_literals = max_literals
        self.min_rules = 1
        self.max_rules = MAX_RULES
        self.min_rule_size = 1

class Constraints:

    def __init__(self, tracker, generalisation, specialisation, redundancy, subsumption):
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
        self.elimination = set()

    def all(self):
        return self.handles | self.generalisation | self.specialisation | self.redundancy | self.subsumption | self.elimination

    def reduce(self):
        self.reduce_generalisation()
        self.reduce_specialisation()
        self.reduce_redundancy()
        self.reduce_handles()


    def reduce_handles(self):
        needed = set()
        for _head, body in self.generalisation | self.specialisation | self.redundancy | self.subsumption:
            needed.update(get_rule_ids(body))

        asda = set()
        for rule in self.handles:
            head, _body = rule
            sym = head.arguments[0]
            xs = sym.split(':-')
            b = xs[1]
            k = frozenset(x.strip().replace('.',',') for x in b.split(','))
            if k in needed:
                asda.add(rule)
        self.handles = asda

    def reduce_generalisation(self):
        # SUPPOSE WE HAVE TWO GENERALISATION CONSTRAINTS FOR THE RULES
        # H1 = H :- A
        # H2 = {H :- A.; H - B}
        # WE NEED ONLY THE CONSTRAINT FOR H1

        subset = set()
        for rule in self.generalisation:
            head, body = rule
            t2 = get_rule_ids(body)
            should_add = True

            for t1 in subset:
                if t1.issubset(t2):
                    should_add = False
                    break
                elif t2.issubset(t1):
                    subset.remove(t1)
                    break
            if should_add:
                subset.add(t2)

        asda = set()
        for rule in self.generalisation:
            head, body = rule
            t2 = get_rule_ids(body)
            if t2 in subset:
                asda.add(rule)
        self.generalisation = asda

    def reduce_specialisation(self):
        # SUPPOSE WE HAVE TWO SPECIALISATION CONSTRAINTS FOR THE RULES
        # R1 = H :- A
        # R2 = H :- A, B
        # WE NEED ONLY THE CONSTRAINT FOR R1
        subset = set()
        for rule in self.specialisation:
            _head, body = rule
            t2 = get_rule_ids(body)

            should_add = True

            for t1 in subset:
                # if tracker.tester.subsumes2(t2, t1):
                if tmp_subsumes(t2, t1):
                    subset.remove(t1)
                    break
                elif tmp_subsumes(t1, t2):
                # elif tracker.tester.subsumes2(t1, t2):
                    should_add = False
                    break

            if should_add:
                subset.add(t2)

        asda = set()
        for rule in self.specialisation:
            _head, body = rule
            t2 = get_rule_ids(body)
            if t2 in subset:
                asda.add(rule)
        self.specialisation = asda

    def reduce_redundancy(self):
        gens = set()
        for rule in self.generalisation:
            _head, body = rule
            gens.add(get_rule_ids(body))

        asda = set()
        for rule in self.redundancy:
            _head, body = rule
            if get_rule_ids(body) not in gens:
                asda.add(rule)
        self.redundancy = asda

    def reduce_with_elims(self, constrainer):
        gens = set()
        for rule in self.generalisation:
            _head, body = rule
            gens.add(get_rule_ids(body))

        specs = set()
        for rule in self.specialisation:
            _head, body = rule
            specs.add(get_rule_ids(body))

        elim_ids = set()
        elims = set()

        for rule in self.redundancy:
            head, body = rule
            elim_ids.add(get_rule_ids(body))
            elims.update(constrainer.tmp_elimination_constraint(get_handles(body)))

        gen_and_spec = gens.intersection(specs)
        new_gen = set()
        new_spec = set()

        for rule in self.generalisation | self.specialisation:
            head, body = rule
            ids = get_rule_ids(body)
            if ids in gen_and_spec:
                elim_ids.add(ids)
                elims.update(constrainer.tmp_elimination_constraint(get_handles(body)))

        for rule in self.generalisation:
            head, body = rule
            ids = get_rule_ids(body)
            if ids not in elim_ids:
                new_gen.add(rule)

        for rule in self.specialisation:
            head, body = rule
            ids = get_rule_ids(body)
            if ids not in elim_ids:
                new_spec.add(rule)

        new_sub = set()
        for rule in self.subsumption:
            head, body = rule
            ids = get_rule_ids(body)
            if ids not in elim_ids:
                new_sub.add(rule)

        # k = len(self.generalisation) + len(self.specialisation) + len(self.redundancy)
        # print(f'gens old:{len(self.generalisation)} new:{len(new_gen)}')
        # print(f'spec old:{len(self.specialisation)} new:{len(new_spec)}')
        # print(f'sub old:{len(self.subsumption)} new:{len(new_sub)}')
        # print(f'red old:{len(self.redundancy)}')
        # print(f'total old:{k} new:{len(elims)}')

        # TODO: REDUCE FURTHER!!!!

        # :- included_clause("f(A):- has_car(A.C),has_car(A.B),roof_flat(B),short(C)",C0).
        # :- included_clause("f(A):- has_car(A.C),has_car(A.B),roof_flat(B),short(C),two_wheels(B)",C0),body_size(C0,5).
        # :- included_clause("f(A):- has_car(A.B),has_car(A.C),long(B),long(C)",C0).
        # :- included_clause("f(A):- has_car(A.B),has_car(A.C),long(B),long(C),roof_flat(C)",C0).
        # :- included_clause("f(A):- has_car(A.B),has_car(A.C),long(B),long(C),roof_open(B)",C0).
        # :- included_clause("f(A):- has_car(A.B),has_car(A.C),long(B),long(C),three_wheels(B)",C0),body_size(C0,5).

        self.generalisation = new_gen
        self.specialisation = new_spec
        self.redundancy = set()
        self.subsumption = new_sub
        self.elimination = elims

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

        self.settings.WITH_OPTIMISTIC = WITH_OPTIMISTIC
        self.settings.WITH_CHUNKING = WITH_CHUNKING
        self.settings.WITH_LAZINESS = WITH_LAZINESS
        self.settings.WITH_MIN_RULE_SIZE = WITH_MIN_RULE_SIZE
        self.tester = Tester(settings)
        self.max_total_literals = settings.max_literals
        self.stats = Stats(log_best_programs=settings.info)
        self.pos = frozenset(self.tester.pos)
        self.neg = frozenset(self.tester.neg)
        self.unsolvable = set()
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

        # find bindings for variables in the constraint
        assignments = grounder.find_bindings(clause)

        # keep only standard literals
        body = tuple(literal for literal in body if not literal.meta)

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

def build_constraints(settings, stats, constrainer, tester, program, pos):
    cons = set()

    if tester.is_complete(program, pos):
        cons.update(constrainer.generalisation_constraint(program))
    else:
        cons.update(constrainer.specialisation_constraint(program))

    if tester.is_inconsistent(program):
        cons.update(constrainer.generalisation_constraint(program))
    else:
        cons.update(constrainer.specialisation_constraint(program))

    if tester.is_totally_incomplete(program, pos):
        cons.update(constrainer.redundancy_constraint(program))

    # eliminate rules subsumed by this one
    if WITH_SUBSUMPTION:
        for rule in program:
            cons.update(constrainer.subsumption_constraint(rule))

    if settings.functional_test and tester.is_non_functional(program):
        cons.update(constrainer.generalisation_constraint(program))

    # eliminate generalisations of rules with redundant literals
    for rule in program:
        if tester.rule_has_redundant_literal(rule):
            cons.update(constrainer.redundant_literal_constraint(rule))

    if len(program) > 1:

        # detect subsumption redundant rules
        for r1, r2 in tester.find_redundant_clauses(tuple(program)):
            cons.update(constrainer.subsumption_constraint_pairs(r1, r2))

        for rule in program:
            sub_prog = [rule]

            if tester.is_complete(sub_prog, pos):
                cons.update(constrainer.generalisation_constraint(sub_prog))
            else:
                cons.update(constrainer.specialisation_constraint(sub_prog))

            if tester.is_inconsistent(sub_prog):
                cons.update(constrainer.generalisation_constraint(sub_prog))
            else:
                cons.update(constrainer.specialisation_constraint(sub_prog))

        # eliminate totally incomplete rules
        if separable(program):
            for rule in program:
                if tester.is_totally_incomplete([rule], pos):
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

def print_stats(cons, stats, grounder):
    print(f'ALL:\t{len(cons.all())}')
    print(f'INCS:\t{len(cons.handles)}')
    print(f'GENS:\t{len(cons.generalisation)}')
    print(f'SPEC:\t{len(cons.specialisation)}')
    print(f'SUBS:\t{len(cons.subsumption)}')
    print(f'REDU:\t{len(cons.redundancy)}')
    ground_cons = bind_vars_in_cons(stats, grounder, cons.all())
    print(f'GROUND:\t{len(ground_cons)}')
    print(f'GROUND_INCS:\t{len(bind_vars_in_cons(stats, grounder, cons.handles))}')
    print(f'GROUND_GENS:\t{len(bind_vars_in_cons(stats, grounder, cons.generalisation))}')
    print(f'GROUND_SPEC:\t{len(bind_vars_in_cons(stats, grounder, cons.specialisation))}')
    print(f'GROUND_SUBS:\t{len(bind_vars_in_cons(stats, grounder, cons.subsumption))}')
    print(f'GROUND_REDU:\t{len(bind_vars_in_cons(stats, grounder, cons.redundancy))}')

def save_cons(cons, name):
    with open(f'{name}.pl', 'w') as f:
        f.write('%generalisations\n')
        for rule in cons.generalisation:
            f.write(Constrain.format_rule_clingo(rule) + '\n')
        f.write('%specialisation\n')
        for rule in cons.specialisation:
            f.write(Constrain.format_rule_clingo(rule) + '\n')
        f.write('%redundancy\n')
        for rule in cons.redundancy:
            f.write(Constrain.format_rule_clingo(rule) + '\n')
        f.write('%subs\n')
        for rule in cons.subsumption:
            f.write(Constrain.format_rule_clingo(rule) + '\n')
        f.write('%elimination\n')
        for rule in cons.elimination:
            f.write(Constrain.format_rule_clingo(rule) + '\n')

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

    best_score = None

    dbg('POS:', chunk_bounds.max_literals, chunk_bounds.max_rules)

    # FILTER OLD CONSTRAINTS
    with tracker.stats.duration('filtering'):
        save_cons(bootstap_cons, 'cons0')
        bootstap_cons.reduce()
        # TMP!!!
        save_cons(bootstap_cons, 'cons1')
        if not settings.recursion:
            bootstap_cons.reduce_with_elims(constrainer)
            save_cons(bootstap_cons, 'cons2')


    all_fo_cons = bootstap_cons.all()

    # GROUND OLD CONSTRAINTS AND ADD TO SOLVER
    with stats.duration('bootstrap'):
        ground_cons = bind_vars_in_cons(stats, grounder, all_fo_cons)
        solver.add_ground_clauses(ground_cons)

    min_size = chunk_bounds.min_literals if WITH_MIN_LITERALS else 1

    def size_bounds():
        for num_rules in range(1, chunk_bounds.max_rules+1):
            for num_literals in range(min_size, chunk_bounds.max_literals + 1):
                yield num_literals, num_rules

    for size in range(min_size, chunk_bounds.max_literals + 1):
    # for size, num_rules in size_bounds():
        # dbg(f'num_rules:{num_rules} num_literals:{size}')
        dbg(f'num_literals:{size}')
        solver.update_number_of_literals(size)
        # solver.update_number_of_rules(num_rules)
        # dbg(f'new size: {size}')

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
                # print('separable', separable(program))
                if separable(program):
                    for rule in program:
                        tmp = frozenset([rule])
                        print(tracker.tester.test(tmp, pos, neg), tracker.tester.test_all(tmp), tmp in tracker.seen_consistent)
                else:
                    print(tracker.tester.test(program, pos, neg), tracker.tester.test_all(program), program in tracker.seen_consistent)

            assert(program not in tracker.seen_inconsistent)
            assert(all(frozenset([rule]) not in tracker.seen_inconsistent for rule in program))

            # # TMP!!!
            # if tester.is_incomplete(program, pos) and tester.is_inconsistent(program):
            #     print('----')
            #     pprint(program)
            #     dbg('INCOMPLETE AND INCONSISTENT!!')

            # TEST HYPOTHESIS AND UPDATE BEST PROGRAM
            solution_found = False
            with stats.duration('test'):
                if tester.is_complete(program, pos) and tester.is_consistent_all(program):
                    solution_found = True

            # # if WITH_CRAP_CHECK:
            # has_crap = False
            # if program in tracker.seen_crap:
            #     print('CRAP1')
            #     pprint(program)
            #     has_crap = True
            # for rule in program:
            #     if frozenset([rule]) in tracker.seen_crap:
            #         print('CRAP2')
            #         pprint([rule])
            #         has_crap = True
            # if has_crap:
            #     stats.crap_count +=1

            if not tracker.settings.recursion:
                check_crap(tracker, program)

            cache_rules(tracker, program)

            if solution_found:
                return program

            # BUILD CONSTRAINTS
            with stats.duration('build'):
                fo_cons = build_constraints(settings, stats, constrainer, tester, program, pos) - all_fo_cons
                all_fo_cons.update(fo_cons)

                # print('FIRST-ORDER')
                # for h, b in fo_cons:
                #     if h:
                #         print('inc', h)
                #     else:
                #         print('con', ','.join(str(x) for x in b))

            # GROUND CONSTRAINTS
            with stats.duration('ground'):
                ground_cons = bind_vars_in_cons(stats, grounder, fo_cons)
                # print('PROPOSITIONAL')
                # for h, b in ground_cons:
                #     if h:
                #         print('inc', h)
                #     else:
                #         print('con', ','.join(str(x) for x in b))

            # ADD CONSTRAINTS TO SOLVER
            with stats.duration('add'):
                solver.add_ground_clauses(ground_cons)

            # if stats.total_programs > 10:
                # exit()

    return None

def tmp():
    now = datetime.now()
    current_time = now.strftime("%H:%M:%S")
    return current_time

def dbg(*args):
    print(tmp(), *args)

def pprint(prog):
    for rule in prog:
        dbg(Clause.to_code(rule))

def num_literals(prog):
    return sum(1 + len(body) for head_, body in prog)

def calc_score(tester, prog):
    tp, fn, tn, fp = tester.test_all(prog)
    return fn + fp

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
    bounds.max_rules = calc_max_rules(tracker, best_prog, chunk_exs)
    bounds.min_literals = 1 #
    if all(tracker.best_progs[ex] != None for ex in chunk_exs):
        bounds.min_literals = max(num_literals(tracker.best_progs[ex]) for ex in chunk_exs)
    bounds.max_literals = calc_max_literals(tracker, best_prog)
    bounds.min_rule_size = calc_min_rule_size(tracker, best_prog)
    return bounds

def check_crap(tracker, prog):
    if tracker.tester.is_inconsistent(prog):
        return

    prog_size = num_literals(prog)
    xs = tracker.tester.pos_covered(prog)
    if xs in tracker.pos_coverage:
        if tracker.pos_coverage[xs] == prog:
            pass
        elif prog_size < num_literals(tracker.pos_coverage[xs]):
            tracker.seen_crap.add(tracker.pos_coverage[xs])
            tracker.pos_coverage[xs] = prog
        else:
            tracker.seen_crap.add(prog)
    else:
        tracker.pos_coverage[xs] = prog

def check_old_programs(tracker, chunk_exs, chunk_bounds):
    tester = tracker.tester
    constrainer = Constrain()

    generalisation = set()
    specialisation = set()
    redundancy = set()
    subsumption = set()
    covers = set()

    chunk_prog = None

    # CHECK CONSISTENT PROGRAMS
    for prog in tracker.seen_consistent:
        prog_size = num_literals(prog)

        if prog_size > chunk_bounds.max_literals:
            continue

        if tester.is_complete(prog, chunk_exs):
            chunk_prog = prog
            chunk_bounds = calc_chunk_bounds(tracker, chunk_prog, chunk_exs)
            continue

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

        if tester.is_incomplete(prog, chunk_exs):
            specialisation.update(constrainer.specialisation_constraint(prog))

        if WITH_SUBSUMPTION:
            for rule in prog:
                subsumption.update(constrainer.subsumption_constraint(rule))

        for rule in prog:
            if tester.rule_has_redundant_literal(rule):
                generalisation.update(constrainer.redundant_literal_constraint(rule))

        if len(prog) > 1:
            for r1, r2 in tester.find_redundant_clauses(tuple(prog)):
                subsumption.update(constrainer.subsumption_constraint_pairs(r1, r2))

        if WITH_COVERAGE_CHECK:
            for rule in prog:
                _, body = rule
                handle = constrainer.make_clause_handle(rule)
                covers.add(f'seen({handle},{len(body)})')
                for ex in chunk_exs:
                    if tester.is_complete([rule], [ex]):
                        covers.add(f'covers({handle},{ex})')

    if WITH_COVERAGE_CHECK:
        for e in chunk_exs:
            covers.add(f'example({e})')

    # CHECK INCONSISTENT PROGRAMS
    for prog in tracker.seen_inconsistent:
        prog_size = num_literals(prog)

        if prog_size > chunk_bounds.max_literals:
            continue

        generalisation.update(constrainer.generalisation_constraint(prog))

        # TODO: CHECK THE RECURSION ISSUE
        if tester.is_totally_incomplete(prog, chunk_exs):
            redundancy.update(constrainer.redundancy_constraint(prog))

        if tester.is_incomplete(prog, chunk_exs):
            specialisation.update(constrainer.specialisation_constraint(prog))

        if WITH_SUBSUMPTION:
            for rule in prog:
                subsumption.update(constrainer.subsumption_constraint(rule))

        for rule in prog:
            if tester.rule_has_redundant_literal(rule):
                generalisation.update(constrainer.redundant_literal_constraint(rule))

        if len(prog) > 1:
            for r1, r2 in tester.find_redundant_clauses(tuple(prog)):
                subsumption.update(constrainer.subsumption_constraint_pairs(r1, r2))

    # if WITH_CRAP_CHECK:
        # for prog in tracker.seen_crap:
            # generalisation.update(constrainer.elimination_constraint(prog))

    cons = Constraints(tracker, generalisation, specialisation, redundancy, subsumption)
    cons.covers = covers

    return chunk_prog, cons

def form_union(progs):
    union = set()
    for prog in progs:
        union.update(prog)
    return union

def remove_redundancy(tester, old_prog):
    old_size = num_literals(old_prog)
    old_success_set = tester.success_set(old_prog)
    new_prog = tester.reduce_success_set_all(old_prog)
    new_success_set = tester.success_set(new_prog)
    assert(old_success_set == new_success_set)
    if len(new_prog) < len(old_prog):
        dbg(f'reduced program from {len(old_prog)} to {len(new_prog)}')
        # dbg('old program:')
        # pprint(old_prog)
        # print(tester.test_all(old_prog))
        # dbg('new program:')
        # pprint(new_prog)
        # print(tester.test_all(new_prog))
    return new_prog

def get_union_of_example_progs(tracker, chunk_exs):
    if any(tracker.best_progs[ex] == None for ex in chunk_exs):
        return None
    union = form_union([tracker.best_progs[ex] for ex in chunk_exs])
    chunk_prog = remove_redundancy(tracker.tester, union)
    dbg('BEST_SO_FAR')
    pprint(chunk_prog)
    assert(tracker.tester.is_complete(chunk_prog, chunk_exs))
    assert(len(chunk_prog) == len(tracker.tester.reduce_subset(chunk_prog, chunk_exs)))
    return chunk_prog

def reuse_seen(tracker, chunk_exs, iteration_progs, chunk_bounds):
    seen = (seen_prog for seen_prog in iteration_progs if num_literals(seen_prog) <= chunk_bounds.max_literals)
    seen = sorted(seen, key = lambda x: num_literals(x))
    for seen_prog in seen:
        if tracker.tester.is_complete(seen_prog, chunk_exs):
            return seen_prog
    return None

def process_chunk(tracker, chunk_exs, iteration_progs):
    chunk_prog = get_union_of_example_progs(tracker, chunk_exs)

    chunk_bounds = calc_chunk_bounds(tracker, chunk_prog, chunk_exs)

    # if we cannot learn something smaller, then this chunk program is the union of all the solutions for the smaller chunks
    if chunk_bounds.min_literals >= chunk_bounds.max_literals:
        # dbg(f'skipping as min_literals ({chunk_bounds.min_literals}) >= max_literals ({chunk_bounds.max_literals})')
        return chunk_prog

    bootstap_cons = set()

    if WITH_LAZINESS:
        # try to reuse an already found hypothesis
        complete_seen_prog = reuse_seen(tracker, chunk_exs, iteration_progs, chunk_bounds)
        if complete_seen_prog:
            return complete_seen_prog

    if WITH_BOOTSTRAPPING:
        # find the best program already seen
        seen_prog, bootstap_cons = check_old_programs(tracker, chunk_exs, chunk_bounds)

        if seen_prog:
            chunk_prog = seen_prog
            chunk_bounds = calc_chunk_bounds(tracker, chunk_prog, chunk_exs)

            # also update when an improvement is possible
            if chunk_bounds.min_literals >= chunk_bounds.max_literals:
                return chunk_prog

    dbg(f'min_literals:{chunk_bounds.min_literals} max_literals:{chunk_bounds.max_literals} max_rules:{chunk_bounds.max_rules}')

    # call popper with the chunk examples and chunk constraints
    new_solution = popper(tracker, chunk_exs, tracker.neg, bootstap_cons, chunk_bounds)

    if new_solution == None:
        return chunk_prog

    chunk_prog = frozenset(new_solution)

    assert(tracker.tester.is_complete(chunk_prog, chunk_exs))
    assert(tracker.tester.is_consistent_all(chunk_prog))
    assert(not tracker.tester.check_redundant_clause(chunk_prog))

    dbg('NEW PROGRAM:')
    pprint(chunk_prog)

    return chunk_prog

def learn_iteration_prog(tracker, all_chunks, chunk_size):
    # partition the positive examples in chunks of size chunk_size
    these_chunks = list(chunks(all_chunks, chunk_size))

    iteration_progs = set()

    for chunk_num, chunk_exs in enumerate(these_chunks):
        chunk_exs = flatten(chunk_exs)

        dbg(f'chunk:{chunk_num+1}/{len(these_chunks)} num_examples:{len(chunk_exs)}')

        chunk_prog = process_chunk(tracker, chunk_exs, iteration_progs)

        if not chunk_prog:
            dbg(f'!!!!! NO CHUNK PROG FOR {chunk_exs} !!!!!')
            tracker.unsolvable.update(chunk_exs)
            continue

        # chunk_prog is guaranteed to be complete, consistent, and smaller than the previous best

        assert(tracker.tester.is_complete(chunk_prog, chunk_exs))
        assert(tracker.tester.is_consistent_all(chunk_prog))

        # if we find a program that is complete and consistent for all examples then we can stop
        if tracker.tester.is_complete_all(chunk_prog) and tracker.tester.is_consistent_all(chunk_prog):
            # dbg('SOLUTION FOUND!!! CAN STOP EARLY!!!')
            return chunk_prog, True

        for ex in chunk_exs:
            tracker.best_progs[ex] = chunk_prog

        iteration_progs.add(chunk_prog)

    iteration_prog = remove_redundancy(tracker.tester, form_union(iteration_progs))
    assert(tracker.tester.is_complete(iteration_prog, chunk_exs))
    assert(tracker.tester.is_complete_all(iteration_prog))
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
    # maintains stuff during the search
    tracker = Tracker(settings)

    # size of the chunks/partitions of the examples
    chunk_size = 1

    # initially partitions each example into its own partition
    all_chunks = [[x] for x in tracker.pos]

    while True:
        dbg('CHUNK_SIZE', chunk_size)

        # program for this chunk size is the union of the chunk progs
        iteration_prog, proven_optimal = learn_iteration_prog(tracker, all_chunks, chunk_size)

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
    pprint(tracker.best_prog)
    print(tracker.stats.crap_count)
    return tracker.best_prog, tracker.stats