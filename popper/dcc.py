#!/usr/bin/env python3

import time
from datetime import datetime
from itertools import chain, combinations
from . util import Settings, Stats, timeout, parse_settings, format_program
from . asp import ClingoGrounder, ClingoSolver
from . tester import Tester
from . constrain import Constrain
from . generate import generate_program
from . core import Grounding, Clause, Literal, separable, rule_is_recursive, rule_is_invented, rule_calls_invented, rule_to_code
from collections import defaultdict
import clingo.script
clingo.script.enable_python()
import pkg_resources

OPTIMAL = 'OPTIMAL'
INCONSISTENT = 'INCONSISTENT'
SOLUTION = 'SOLUTION'

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
WITH_BOOTSTRAPPING = False
WITH_BOOTSTRAPPING = True
WITH_SUBSUMPTION = False
WITH_SUBSUMPTION = True
WITH_COVERAGE_CHECK = False
# WITH_COVERAGE_CHECK = True
# MAX_RULES = 3
MAX_RULES = 6
# MAX_RULES = 10
MAX_LITERALS = 20

NON_REC_BOUNDS_FILE = pkg_resources.resource_string(__name__, "lp/bounds.pl").decode()
REC_BOUNDS_FILE = pkg_resources.resource_string(__name__, "lp/bounds-rec.pl").decode()

# class Bounds:
#     def __init__(self, max_literals):
#         self.min_literals = 1
#         self.max_literals = max_literals
#         self.min_rules = 1
#         self.max_rules = MAX_RULES
#         self.min_rule_size = 1

class Constraints:

    def __init__(self, tracker, generalisation = set(), specialisation = set(), redundancy = set(), subsumption = set(), elimination = set()):
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
        self.min_size = {}
        self.no_single_rule_solutions = []
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

        self.num_ground_cons = 0

        self.cached_min_rule = {}
        self.cached_before = {}


        # VERY HACKY
        with open(settings.bias_file) as f:
            f_txt = f.read()
            self.settings.recursion = 'enable_recursion' in f_txt
            self.settings.predicate_invention = 'enable_pi' in f_txt

        self.settings.WITH_OPTIMISTIC = WITH_OPTIMISTIC
        self.settings.WITH_CHUNKING = WITH_CHUNKING
        self.settings.WITH_LAZINESS = WITH_LAZINESS
        self.settings.WITH_MIN_RULE_SIZE = WITH_MIN_RULE_SIZE and not (self.settings.recursion or self.settings.predicate_invention)
        self.tester = Tester(settings)
        self.max_total_literals = settings.max_literals
        self.stats = Stats(log_best_programs=settings.info)
        self.pos = frozenset(self.tester.pos)
        self.neg = frozenset(self.tester.neg)
        self.best_progs = {ex:None for ex in self.pos}
        self.stats.crap_count = 0


cached_grounding = {}

def bind_vars_in_cons(stats, grounder, clauses):
    ground_cons = set()

    for clause in clauses:
        head, body = clause

        # find bindings for variables in the constraint
        assignments = grounder.find_bindings(clause)

        # keep only standard literals
        body = tuple(literal for literal in body if not literal.meta)

        k = hash((head, body))

        # ground the clause for each variable assignment
        for assignment in assignments:

            k = hash((k, tuple(sorted(assignment.items()))))
            if k in cached_grounding:
                cons = cached_grounding[k]
            else:
                cons = Grounding.ground_clause((head, body), assignment)
                cached_grounding[k] = cons

            ground_cons.add(cons)

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
    # print('BUILDING')
    cons = set()

    if tester.is_complete(program, pos):
        cons.update(constrainer.generalisation_constraint(program))
    else:
        cons.update(constrainer.specialisation_constraint(program))

        if tester.is_totally_incomplete(program, pos):
            cons.update(constrainer.redundancy_constraint(program))

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

    if len(program) > 1:

        # detect subsumption redundant rules
        for r1, r2 in tester.find_redundant_clauses(tuple(program)):
            cons.update(constrainer.subsumption_constraint_pairs(r1, r2))

        for rule in program:
            sub_prog = frozenset([rule])

            if not separable(sub_prog) or rule_calls_invented(rule):
                continue

            if tester.is_complete(sub_prog, pos):
                cons.update(constrainer.generalisation_constraint(sub_prog))
            else:
                cons.update(constrainer.specialisation_constraint(sub_prog))

                if tester.is_totally_incomplete(sub_prog, pos):
                    cons.update(constrainer.redundancy_constraint(sub_prog))

            if tester.is_inconsistent(sub_prog):
                cons.update(constrainer.generalisation_constraint(sub_prog))
            else:
                cons.update(constrainer.specialisation_constraint(sub_prog))

            if WITH_CRAP_CHECK:
                if sub_prog in tracker.seen_crap:
                      cons.update(constrainer.elimination_constraint([rule]))
    return cons

def cache_rules(tracker, program):
    if tracker.tester.is_inconsistent(program):
        tracker.seen_inconsistent.add(program)
    else:
        tracker.seen_consistent.add(program)

    if len(program) > 1:
        for rule in program:
            cache_rules(tracker, frozenset([rule]))

def popper(tracker, pos, neg, bootstap_cons, bounds):
    settings = tracker.settings
    stats = tracker.stats
    tester = tracker.tester
    constrainer = Constrain(tracker)
    solver = ClingoSolver(settings, bounds)
    grounder = ClingoGrounder(bounds.max_rules, settings.max_vars)

    all_fo_cons = bootstap_cons.all()

    # ground old constraints and add to solver
    with stats.duration('bootstrap'):
        ground_cons = bind_vars_in_cons(stats, grounder, all_fo_cons)
        solver.add_ground_clauses(ground_cons)

    min_size = bounds.min_literals if WITH_MIN_LITERALS else 1

    dbg(f'Running Popper min_rules:{bounds.min_rules} max_rules:{bounds.max_rules} min_literals:{bounds.min_literals} max_literals:{bounds.max_literals}')

    for size in range(min_size, bounds.max_literals + 1):
        dbg(f'num_literals:{size}')
        solver.update_number_of_literals(size)

        while True:

            # generate hypothesis
            with stats.duration('generate'):
                model = solver.get_model()
                if not model:
                    break
                prog = generate_program(model)
                constrainer.cache_bounds(prog)

            tracker.stats.total_programs += 1

            if tracker.settings.debug:
                print('--')
                for rule in prog:
                    print(rule_to_code(rule))
            # pprint(program)
            if tracker.best_prog:
                if prog.issubset(tracker.best_prog):
                    # print('')
                    print('SUBSET'*10)
                    # for rule in prog:
                        # print(rule_to_code(rule))

            # test hypothesis
            solution_found = False
            with stats.duration('test'):
                if tester.is_complete(prog, pos) and not tester.is_inconsistent(prog):
                    if not tracker.settings.functional_test or tester.is_functional(prog, pos):
                        solution_found = True

            with stats.duration('crap and cache'):
                check_crap(tracker, prog)
                check_crap2(tracker, prog)
                if len(prog) > 1:
                    for rule in prog:
                        check_crap(tracker, frozenset([rule]))
                        check_crap2(tracker, frozenset([rule]))
                cache_rules(tracker, prog)

            if solution_found:
                return prog

            # build constraints
            with stats.duration('build'):
                fo_cons = build_constraints(tracker, stats, constrainer, tester, prog, pos) - all_fo_cons
                all_fo_cons.update(fo_cons)

            # ground constraints
            with stats.duration('ground'):
                ground_cons = bind_vars_in_cons(stats, grounder, fo_cons)

            # add constraints to solver
            with stats.duration('add'):
                solver.add_ground_clauses(ground_cons)

    return None

def dbg(*args):
    now = datetime.now()
    current_time = now.strftime("%H:%M:%S")
    print(current_time, *args)

def pprint(prog):
    for rule in prog:
        dbg(rule_to_code(rule) + '.')

def num_literals(prog):
    return sum(1 + len(body) for head_, body in prog)

def calc_score(tester, prog):
    fn = sum(1 for x in tester.pos if not tester.is_complete(prog, [x]))
    return fn

def calc_fp(tester, rules):
    return tester.fp(rules)

def best_prog_improvement(tracker, prog):
    # print('best_prog_improvement')
    # pprint(prog)
    # TODO: DOUBLE CHECK!!
    # if tracker.best_prog is None:
        # return True

    # if prog == None:
        # print('WTF!!!?')

    errors = calc_score(tracker.tester, prog)
    if errors > 0:
        return False

    if tracker.best_prog == None:
        return True

    if num_literals(prog) < tracker.best_prog_size:
        return True

    return False

def chunk_list(xs, size):
    for i in range(0, len(xs), size):
        yield xs[i:i+size]

def flatten(xs):
    return [item for sublist in xs for item in sublist]

def update_best_prog(tracker, prog):
    tracker.best_prog = prog
    tracker.best_prog_size = num_literals(prog)
    tracker.best_prog_errors = calc_score(tracker.tester, prog)

    dbg(f'new best prog size:{tracker.best_prog_size} tp:{len(tracker.tester.pos)} fp:{calc_fp(tracker.tester, prog)}')
    pprint(prog)

    if tracker.best_prog_errors > 0:
        return

    if tracker.best_prog == None:
        return

    # TODO: NEEDED?
    old_max_literals = tracker.max_total_literals
    tracker.max_total_literals = min(tracker.best_prog_size -1, tracker.max_total_literals)

# def calc_max_rules(tracker, best_prog, chunk_exs):
#     k = tracker.max_total_rules

#     if not WITH_MAX_RULE_BOUND:
#         return k

#     if not(tracker.settings.recursion or tracker.settings.predicate_invention):
#         k = min(k, len(chunk_exs))

#     if tracker.best_prog != None and tracker.best_prog_errors == 0:
#         k = min(k, len(best_prog))

#     return k

# def calc_max_literals(tracker, best_prog):
#     k = tracker.max_total_literals
#     if best_prog != None:
#         best_prog_size = num_literals(best_prog)
#         # minus -1 because we want to learn a smaller program than the best one so far
#         k = min(k, best_prog_size-1)
#     return k

# def calc_min_rule_size(tracker, best_prog):
#     if best_prog != None:
#         return 1 + min(len(body) for head, body in best_prog)
#     return 1

# def calc_chunk_bounds(tracker, best_prog, chunk_exs):
#     bounds = Bounds(tracker.max_total_literals)

#     bounds.min_literals = 1 #
#     if all(tracker.best_progs[ex] != None for ex in chunk_exs):
#         bounds.min_literals = max(num_literals(tracker.best_progs[ex]) for ex in chunk_exs)
#     bounds.max_rules = calc_max_rules(tracker, best_prog, chunk_exs)
#     bounds.max_literals = calc_max_literals(tracker, best_prog)
#     bounds.min_rule_size = calc_min_rule_size(tracker, best_prog)
#     return bounds

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

def check_old_programs(tracker, pos, min_literals, max_literals):
    # check all programs seen so far, the outputs are:
    # 1. the smallest complete and consistent hypothesis seen so far
    # 2. a set of constraints for the other programs

    tester = tracker.tester
    constrainer = Constrain(tracker)

    generalisation = set()
    specialisation = set()
    redundancy = set()
    subsumption = set()
    elimination = set()

    chunk_prog = None

    # with tracker.stats.duration('CHECK CONSISTENT PROGRAMS'):
    # check consistent programs
    for prog in tracker.seen_consistent:

        # if the program is too big, ignore it
        # TODO: ARE WE MISSING SOME STUFF HERE?
        if num_literals(prog) > max_literals:
            continue

        if tester.is_complete(prog, pos):
            # if the program is not functional then we can prune generalisations of it
            if tracker.settings.functional_test and not tester.is_functional(prog, pos):
                generalisation.update(constrainer.generalisation_constraint(prog))
                continue

            # if prog is complete, then no need to make it more general
            # no need to add any constraints as we will never consider programs bigger than it (since it is complete and consistent)
            chunk_prog = prog
            max_literals = num_literals(prog) - 1
            generalisation.update(constrainer.generalisation_constraint(prog))
            specialisation.update(constrainer.specialisation_constraint(prog))
            continue

        if not tracker.settings.functional_test or tester.is_functional(prog, pos):
            # if prog is consistent, then no need to make it more specific
            specialisation.update(constrainer.specialisation_constraint(prog))

        # TODO: CHECK WHETHER SEPARABLE CHECK IS NECESSARY
        if separable(prog):
            if tester.is_totally_incomplete(prog, pos):
                redundancy.update(constrainer.redundancy_constraint(prog))
        else:
            if tester.is_totally_incomplete(prog, pos):
                # ensure a base case
                if any(not rule_is_recursive(rule) for rule in prog):
                    redundancy.update(constrainer.redundancy_constraint(prog))

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

    # dbg('CHECK INCONSISTENT PROGRAMS')
    # with tracker.stats.duration('CHECK INCONSISTENT PROGRAMS'):
    for prog in tracker.seen_inconsistent:
        prog_size = num_literals(prog)

        if prog_size > max_literals:
            continue

        generalisation.update(constrainer.generalisation_constraint(prog))

        # TODO: CHECK THE RECURSION ISSUE
        if not tester.is_complete(prog, pos):
            specialisation.update(constrainer.specialisation_constraint(prog))

            # Q. IS THIS EVEN NECESSARY?
            if tester.is_totally_incomplete(prog, pos):
                redundancy.update(constrainer.redundancy_constraint(prog))

        if WITH_SUBSUMPTION:
            for rule in prog:
                subsumption.update(constrainer.subsumption_constraint(rule))

        for rule in prog:
            if tester.rule_has_redundant_literal(rule):
                generalisation.update(constrainer.generalisation_constraint([rule]))

        if len(prog) > 1:
            for r1, r2 in tester.find_redundant_clauses(tuple(prog)):
                subsumption.update(constrainer.subsumption_constraint_pairs(r1, r2))

    if WITH_CRAP_CHECK:
        # a program is crap if it is consistent and there is a smaller program with the same success set
        for prog in tracker.seen_crap:
            if num_literals(prog) > max_literals:
                continue
            elimination.update(constrainer.elimination_constraint(prog))

    # if tracker.best_prog:
    #     assert(tracker.tester.is_complete(tracker.best_prog, pos))
    #     assert(not tracker.tester.is_inconsistent(tracker.best_prog))
    #     for sub_prog in powerset(tracker.best_prog):
    #         if num_literals(sub_prog) > max_literals:
    #             continue
    #         if num_literals(sub_prog) < min_literals:
    #             continue
    #         specialisation.update(constrainer.specialisation_constraint(sub_prog))

    cons = Constraints(tracker, generalisation, specialisation, redundancy, subsumption, elimination)

    return chunk_prog, cons

def form_union(progs):
    union = set()
    for prog in progs:
        union.update(prog)
    return frozenset(union)

def remove_redundancy(tester, old_prog, pos):
    new_prog = tester.reduce_subset(old_prog, pos)
    assert(tester.is_complete(old_prog, pos))
    assert(tester.is_complete(new_prog, pos))
    old_success_set = tester.pos_covered_all(old_prog)
    new_success_set = tester.pos_covered_all(new_prog)
    assert(old_success_set == new_success_set)
    return new_prog

def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

def get_union_of_example_progs(tracker, pos):
    if any(tracker.best_progs[x] == None for x in pos):
        return None

    prog = form_union([tracker.best_progs[x] for x in pos])
    assert(tracker.tester.is_complete(prog, pos))
    if not tracker.settings.recursion:
        assert(not tracker.tester.is_inconsistent(prog))

    prog = remove_redundancy(tracker.tester, prog, pos)
    assert(tracker.tester.is_complete(prog, pos))
    if not tracker.settings.recursion:
        assert(not tracker.tester.is_inconsistent(prog))
    assert(len(prog) == len(tracker.tester.reduce_subset(prog, pos)))

    if tracker.tester.is_inconsistent(prog):
        print('SHIT!!!!!!!!!!!'*4)
        return None

    dbg(f'BEST_SO_FAR size:{num_literals(prog)}')
    pprint(prog)

    return prog

def reuse_seen(tracker, pos, iteration_progs, max_literals):
    # print('TRY SEEN!!!', MAX_LITERALS)
    # filter programs that are small enough
    seen = (prog for prog in iteration_progs if num_literals(prog) <= max_literals)
    # sort by program size
    seen = sorted(seen, key = lambda x: num_literals(x))
    # take the first complete program
    for prog in seen:
        if tracker.tester.is_complete(prog, pos):
            return prog
    return None

def run_clingo_opt(prog, opt_statement):
    solver = clingo.Control()
    solver.add('base', [], prog + '\n' + opt_statement)
    solver.ground([("base", [])])
    sat = False
    opt_value = None
    with solver.solve(yield_=True) as handle:
        for m in handle:
            opt_value = abs(m.cost[0])
            sat = True
    return sat, opt_value

def non_recursive_bounds(tracker, pos, max_rule_size, min_rules, max_rules, min_literals, max_literals):
    prog = [NON_REC_BOUNDS_FILE]
    prog.append(f'max_rule_size({max_rule_size}).')
    prog.append(f'max_rules({min(max_rules, len(pos))}).')
    prog.append(f'min_literals({min_literals}).')
    prog.append(f'max_literals({max_literals}).')

    for x in pos:
        v = tracker.min_size[x]
        prog.append(f'min_rule_size({x},{v}).')

    for size, exs in tracker.no_single_rule_solutions:
        prog.append(f':- rule(R,K), K <= {size},' + ','.join(f'covers(R,{x})' for x in exs) + '.')

    prog = '\n'.join(prog)
    # print(prog)

    sat, max_rules_ = run_clingo_opt(prog, "#maximize{X : num_rules(X)}.")
    if sat:
        max_rules = max_rules_
        _, min_rules = run_clingo_opt(prog, "#minimize{X : num_rules(X)}.")
        _, max_literals = run_clingo_opt(prog, "#maximize{X : num_literals(X)}.")
    print(f'\tSAT:{sat}, MIN_RULES:{min_rules} MAX_RULES:{max_rules} MIN_LITERALS:{min_literals} MAX_LITERALS:{max_literals}')

    # TODO: MIN RULE SIZE??
    return BoundsStruct(sat, min_rules, max_rules, min_literals, max_literals)

def recursive_bounds(tracker, max_rule_size, min_rules, max_rules, min_literals, max_literals):
    prog = []
    prog.append(f'max_rules({max_rules}).')
    prog.append(f'max_rule_size({max_rule_size}).')
    prog.append(f'min_literals({min_literals}).')
    prog.append(f'max_literals({max_literals}).')
    # print('\n'.join(prog))
    prog.append(REC_BOUNDS_FILE)
    prog = '\n'.join(prog)

    sat, max_rules_ = run_clingo_opt(prog, "#maximize{X : num_rules(X)}.")
    if sat:
        max_rules = max_rules_
        _, min_rules = run_clingo_opt(prog, "#minimize{X : num_rules(X)}.")
        _, max_literals = run_clingo_opt(prog, "#maximize{X : num_literals(X)}.")

    print(f'\tSAT-REC:{sat}, MIN_RULES:{min_rules} MAX_RULES:{max_rules} MIN_LITERALS:{min_literals} MAX_LITERALS:{max_literals}')
    return BoundsStruct(sat, min_rules, max_rules, min_literals, max_literals)

class BoundsStruct:
    def __init__(self, sat, min_rules, max_rules, min_literals, max_literals):
        self.sat = sat
        self.min_rules = min_rules
        self.max_rules = max_rules
        self.min_literals = min_literals
        self.max_literals = max_literals
        self.min_rule_size = 1

class Bounds2:
    def __init__(self, tracker, prog, pos):
        self.max_rule_size_ = tracker.settings.max_body_atoms+1
        self.min_rules = 1
        self.max_rules = MAX_RULES
        self.min_literals = 1
        self.max_literals = MAX_LITERALS
        self.rec = None
        self.non_rec = None
        self.sat = True

        if not (tracker.settings.recursion or tracker.settings.predicate_invention):
            self.max_rules = min(self.max_rules, len(pos))

        # defaults
        self.non_rec = BoundsStruct(True, self.min_rules, min(self.max_rules, len(pos)), self.min_literals, self.max_literals)
        self.rec = BoundsStruct(True, self.min_rules, self.max_rules, self.min_literals, self.max_literals)

        if any(x not in tracker.min_size for x in pos):
            return

        if all(tracker.best_progs[x] != None for x in pos):
            self.min_literals = max(num_literals(tracker.best_progs[x]) for x in pos)

        if prog:
            # TODO: CHECK WITH RECURSION
            self.max_rules = min(self.max_rules, len(prog))
            self.max_literals = min(self.max_literals, num_literals(prog))
            self.max_literals -= 1

        self.non_rec = non_recursive_bounds(tracker, pos, self.max_rule_size_, self.min_rules, self.max_rules, self.min_literals, self.max_literals)
        self.sat = self.non_rec.sat

        if self.sat:
            self.max_rules = self.non_rec.max_rules
            self.max_literals = self.non_rec.max_literals

        if tracker.settings.recursion or tracker.settings.predicate_invention:
            self.rec = recursive_bounds(tracker, self.max_rule_size_, self.min_rules, self.max_rules, self.min_literals, self.max_literals)
            if self.rec.sat:
                self.sat = True
                self.max_rules = self.non_rec.max_rules
                self.max_literals = self.non_rec.max_literals

# def recursive_bounds(tracker, max_rule_size, min_rules, max_rules, min_literals, max_literals):

def process_chunk(tracker, pos, iteration_progs):
    prog = get_union_of_example_progs(tracker, pos)

    # union can be inconsistent when there is recursion
    if prog and tracker.tester.is_inconsistent(prog):
        prog = None

    # if we cannot learn something smaller, then this chunk program is the union of all the solutions for the smaller chunks
    bounds = Bounds2(tracker, prog, pos)
    if not bounds.sat:
        return prog

    if WITH_LAZINESS:
        # try to reuse an already found hypothesis
        better_seen = reuse_seen(tracker, pos, iteration_progs, bounds.max_literals)
        if better_seen:
            prog = better_seen
            assert(tracker.tester.is_complete(prog, pos))
            assert(not tracker.tester.is_inconsistent(prog))
            for e in pos:
                if e not in tracker.min_size:
                    tracker.min_size[e] = num_literals(prog)
            return prog

    bootstap_cons = Constraints(tracker)

    if WITH_BOOTSTRAPPING:
        # find the best program already seen and build constraints for the other programs
        with tracker.stats.duration('check_seen'):
            better_seen, bootstap_cons = check_old_programs(tracker, pos, bounds.min_literals, bounds.max_literals)

        # this program might not be in the hypothesis, so we might need to search for a smaller one
        if better_seen:
            prog = better_seen
            assert(tracker.tester.is_complete(prog, pos))
            assert(not tracker.tester.is_inconsistent(prog))

            for e in pos:
                if e not in tracker.min_size:
                    tracker.min_size[e] = num_literals(prog)

            bounds = Bounds2(tracker, prog, pos)
            if not bounds.sat:
                return prog

    new_solution = popper(tracker, pos, tracker.neg, bootstap_cons, bounds)

    if new_solution == None:
        # TODO: ADD MORE HERE ABOUT FAILURES!!
        tracker.no_single_rule_solutions.append((bounds.max_literals, pos))

        # TMP!!!!!!
        if prog:
            for x in pos:
                tracker.best_progs[x] = prog
                # print('UPDATING BEST PROG DURING FAILURE', x, num_literals(prog))
        return prog

    prog = new_solution

    for x in pos:
        if x not in tracker.min_size:
            tracker.min_size[x] = num_literals(prog)

    prog = frozenset(prog)
    assert(tracker.tester.is_complete(prog, pos))
    assert(not tracker.tester.is_inconsistent(prog))
    assert(not tracker.tester.check_redundant_clause(prog))

    dbg(f'NEW PROGRAM size:{num_literals(prog)}')
    pprint(prog)
    return prog

def learn_iteration_prog(tracker, chunks):
    all_exs = [x for chunk in chunks for x in flatten(chunk)]

    iteration_progs = set()

    # print('CHUNKS',chunks)

    for chunk_num, pos in enumerate(chunks):
        pos = flatten(pos)
        dbg(f'chunk:{chunk_num+1}/{len(chunks)} num_examples:{len(pos)}')

        prog = process_chunk(tracker, pos, iteration_progs)
        if not prog:
            print('NO PROG')
            continue

        # chunk_prog is guaranteed to be complete, consistent, and smaller than the previous best
        assert(tracker.tester.is_complete(prog, pos))
        assert(not tracker.tester.is_inconsistent(prog))

        # if we find a program that is complete and consistent for all examples then we can stop
        if tracker.tester.is_complete(prog, all_exs) and not tracker.tester.is_inconsistent(prog):
            return prog, OPTIMAL

        for x in pos:
            # print('ASDA PRICE')
            tracker.best_progs[x] = prog

        iteration_progs.add(prog)
        # TODO: CHECK WHETHER UNION OF ITERATION_PROG IS A SOLUTION FOR EARLIER PRUNING

    iteration_prog = form_union(iteration_progs)
    assert(tracker.tester.is_complete(iteration_prog, all_exs))
    if not tracker.settings.recursion:
        assert(not tracker.tester.is_inconsistent(iteration_prog))

    iteration_prog = remove_redundancy(tracker.tester, iteration_prog, all_exs)
    assert(tracker.tester.is_complete(iteration_prog, all_exs))
    if not tracker.settings.recursion:
        assert(not tracker.tester.is_inconsistent(iteration_prog))

    if tracker.tester.is_inconsistent(iteration_prog):
        return iteration_prog, INCONSISTENT
    return iteration_prog, SOLUTION

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

def load_bias_setting(settings):
    ALAN_FILE = pkg_resources.resource_string(__name__, "lp/alan.pl").decode()
    solver = clingo.Control()
    solver.add('base', [], ALAN_FILE)
    with open(settings.bias_file) as f:
        solver.add('base', [], f.read())
    solver.add('base', [], '\n' + f'max_clauses({MAX_RULES}).')
    solver.ground([('base', [])])

    max_body_atoms = solver.symbolic_atoms.by_signature('max_body', arity=1)
    settings.max_body_atoms = next(max_body_atoms).symbol.arguments[0].number

    max_vars_atoms = solver.symbolic_atoms.by_signature('max_vars', arity=1)
    settings.max_vars = next(max_vars_atoms).symbol.arguments[0].number

    # max_clauses_atoms = self.solver.symbolic_atoms.by_signature('max_clauses', arity=1)
    # settings.max_clauses = next(max_clauses_atoms).symbol.arguments[0].number

def dcc(settings):
    # maintain stuff during the search
    tracker = Tracker(settings)
    load_bias_setting(settings)

    # size of the chunks/partitions of the examples
    chunk_size = 1

    # initially partitions each example into its own partition
    all_chunks = [[x] for x in tracker.pos]

    while True:
        dbg('CHUNK_SIZE', chunk_size)

        # program for this chunk size is the union of the chunk progs
        # partition positive examples in chunks of size chunk_size
        chunks = list(chunk_list(all_chunks, chunk_size))
        iteration_prog, status = learn_iteration_prog(tracker, chunks)

        if status == OPTIMAL:
            if best_prog_improvement(tracker, iteration_prog):
                update_best_prog(tracker, iteration_prog)
            break

        dbg(f'CHUNK:{chunk_size} size:{num_literals(iteration_prog)} stats:{status}')
        # pprint(iteration_prog)
        # for rule in iteration_prog:
            # print(rule_to_code(rule))

        if status == SOLUTION:
            if best_prog_improvement(tracker, iteration_prog):
                # update the best program for each example
                # we logically reduce the iteration_prog with respect to each positive example
                for ex in flatten(all_chunks):
                    # print('UPDATING BEST PROGS')
                    tracker.best_progs[ex] = tracker.tester.reduce_subset(iteration_prog, [ex])

                update_best_prog(tracker, iteration_prog)

                if WITH_OPTIMISTIC and tracker.best_prog_errors == 0:
                    break

        if status == INCONSISTENT:
            pass

        if WITH_CHUNKING:
            all_chunks = perform_chunking(tracker)

        if len(all_chunks) == 1 or chunk_size > len(tracker.pos):
            break

        # double the chunk size (loop at most log(len(pos)) iterations)
        # chunk_size += chunk_size
        chunk_size += 1

    print('SOLUTION:')
    for rule in tracker.best_prog:
        print(rule_to_code(rule) + '.')
    return tracker.best_prog, tracker.stats