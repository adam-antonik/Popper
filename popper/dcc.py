#!/usr/bin/env python3

import logging
import sys
from datetime import datetime
from . util import Settings, Stats, timeout, parse_settings, format_program
from . asp import ClingoGrounder, ClingoSolver
from . tester import Tester
from . constrain import Constrain
from . generate import generate_program
from . core import Grounding, Clause
from collections import defaultdict

WITH_OPTIMISTIC = False
WITH_CHUNKING = True
WITH_LAZINESS = True
MAX_RULES = 10
MAX_RULE_SIZE = 6

class Bounds:
    def __init__(self, max_literals):
        self.min_literals = 1
        self.max_literals = max_literals
        self.min_rules = 1
        self.max_rules = MAX_RULES

class Tracker:
    def __init__(self):
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

def build_constraints(settings, stats, constrainer, tester, program, pos):
    cons = set()

    if tester.is_inconsistent(program):
        cons.update(constrainer.generalisation_constraint(program))

    if tester.is_totally_incomplete(program, pos):
        cons.update(constrainer.redundancy_constraint(program))

    if tester.is_incomplete(program, pos):
        cons.update(constrainer.specialisation_constraint(program))

    # eliminate rules subsumed by this one
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

        # eliminate inconsistent rules
        for rule in program:
            if tester.is_inconsistent([rule]):
                cons.update(constrainer.generalisation_constraint([rule]))

        # eliminate totally incomplete rules
        if all(Clause.is_separable(rule) for rule in program):
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

def popper(tracker, pos, neg, bootstap_cons, chunk_bounds):
    settings = tracker.settings
    stats = tracker.stats
    solver = ClingoSolver(settings, chunk_bounds.max_rules)
    tester = tracker.tester
    grounder = ClingoGrounder(chunk_bounds.max_rules, solver.max_vars)
    constrainer = Constrain()
    best_score = None

    dbg('POS:', chunk_bounds.max_literals, chunk_bounds.max_rules)

    all_ground_cons = set()
    all_fo_cons = set()

    # BOOTSTRAPPING
    with tracker.stats.duration('bootstrapping'):

        # GROUND CONSTRAINTS
        with stats.duration('ground_bootstrap'):
            ground_cons = bind_vars_in_cons(stats, grounder, bootstap_cons)

        all_fo_cons.update(bootstap_cons)
        all_ground_cons.update(bootstap_cons)

        # ADD CONSTRAINTS TO SOLVER
        with stats.duration('add_bootstrap'):
            solver.add_ground_clauses(ground_cons)

    for size in range(1, chunk_bounds.max_literals + 1):
        solver.update_number_of_literals(size)
        dbg(f'new size: {size}')

        while True:

            # GENERATE HYPOTHESIS
            with stats.duration('generate'):
                model = solver.get_model()
                if not model:
                    break
                program = generate_program(model)

            tracker.stats.total_programs += 1

            assert(all(frozenset([rule]) not in tracker.seen_inconsistent for rule in program))

            # CACHE RULES
            with stats.duration('cache_rules'):
                cache_rules(tracker, program)

            # TEST HYPOTHESIS AND UPDATE BEST PROGRAM
            with stats.duration('test'):
                if tester.is_complete(program, pos) and tester.is_consistent_all(program):
                    return program

            # BUILD CONSTRAINTS
            with stats.duration('build'):
                fo_cons = build_constraints(settings, stats, constrainer, tester, program, pos) - all_fo_cons
                all_fo_cons.update(fo_cons)

            # GROUND CONSTRAINTS
            with stats.duration('ground'):
                ground_cons = bind_vars_in_cons(stats, grounder, fo_cons) - all_ground_cons
                all_ground_cons.update(ground_cons)

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
    # SOMETHING ABOUT RECURSION + PI
    k = min(k, len(chunk_exs))
    return k

def calc_literal_bounds(tracker, best_prog):
    k = tracker.max_total_literals
    if best_prog != None:
        best_prog_size = num_literals(best_prog)
        # minus -1 because we want to learn a smaller program than the best one so far
        k = min(k, best_prog_size-1)
    return k

def calc_chunk_bounds(tracker, best_prog, chunk_exs):
    bounds = Bounds(tracker.max_total_literals)
    bounds.max_rules = calc_max_rules(tracker, best_prog, chunk_exs)
    bounds.min_literals = 1 # min_literals = max(num_literals(best_prog[ex]) for ex in exs)
    bounds.max_literals = calc_literal_bounds(tracker, best_prog)
    return bounds

def check_old_programs(tracker, chunk_exs, chunk_bounds):
    tester = tracker.tester
    constrainer = Constrain()

    all_generalisation = set()
    all_specialisation = set()
    all_redundancy = set()
    all_subsumption = set()

    # TODO: ELIMINATE THE PREVIOUS H FROM THE SEARCH SPACE???
    chunk_prog = None

    # # first check consistent programs
    with tracker.stats.duration('check_old_consistent'):

        # TODO: ORDER BY SIZE OR GENERALITY TO REDUCE THE NUMBER OF CHECKS
        for prog in tracker.seen_consistent:
            prog_size = num_literals(prog)

            # TODO: WOULD HELP IF WE ORDERED THE PROGRAMS BY SIZE
            # if prog_size >= chunk_bounds.max_literals:
                # continue

            if tester.is_complete(prog, chunk_exs):
                chunk_prog = prog
                chunk_bounds = calc_chunk_bounds(tracker, chunk_prog, chunk_exs)
                continue

            all_specialisation.update(constrainer.specialisation_constraint(prog))

            if tester.is_totally_incomplete(prog, chunk_exs):
                all_redundancy.update(constrainer.redundancy_constraint(prog))

            if tester.is_incomplete(prog, chunk_exs):
                all_specialisation.update(constrainer.specialisation_constraint(prog))

            for rule in prog:
                all_subsumption.update(constrainer.subsumption_constraint(rule))

            for rule in prog:
                if tester.rule_has_redundant_literal(rule):
                    all_generalisation.update(constrainer.redundant_literal_constraint(rule))

            if len(prog) > 1:
                for r1, r2 in tester.find_redundant_clauses(tuple(prog)):
                    all_subsumption.update(constrainer.subsumption_constraint_pairs(r1, r2))


    # # THEN CHECK INCONSISTENT PROGRAMS
    with tracker.stats.duration('check_old_inconsistent'):
        for prog in tracker.seen_inconsistent:
            prog_size = num_literals(prog)

            # TODO: WOULD HELP IF WE ORDERED THE PROGRAMS BY SIZE
            # if prog_size >= chunk_bounds.max_literals:
                # continue

            all_generalisation.update(constrainer.generalisation_constraint(prog))

            if tester.is_totally_incomplete(prog, chunk_exs):
                all_redundancy.update(constrainer.redundancy_constraint(prog))

            if tester.is_incomplete(prog, chunk_exs):
                all_specialisation.update(constrainer.specialisation_constraint(prog))

            for rule in prog:
                all_subsumption.update(constrainer.subsumption_constraint(rule))

            for rule in prog:
                if tester.rule_has_redundant_literal(rule):
                    all_generalisation.update(constrainer.redundant_literal_constraint(rule))

            if len(prog) > 1:
                for r1, r2 in tester.find_redundant_clauses(tuple(prog)):
                    all_subsumption.update(constrainer.subsumption_constraint_pairs(r1, r2))

    new_cons = set()
    new_cons.update(all_generalisation)
    new_cons.update(all_specialisation)
    new_cons.update(all_redundancy)
    new_cons.update(all_subsumption)
    return chunk_prog, new_cons

def remove_redundancy(tester, progs):
    union = set()
    for prog in progs:
        union.update(prog)
    old_size = num_literals(union)
    old_prog = union
    union = tester.reduce_ss(union)
    if len(union) < len(old_prog):
        dbg(f'reduced program from {len(old_prog)} to {len(union)}')
        dbg('original program:')
        pprint(old_prog)
        dbg('old program:')
        pprint(union)
    return union

def get_union_of_example_progs(tracker, chunk_exs):
    if any(tracker.best_progs[ex] == None for ex in chunk_exs):
        return None
    progs = [tracker.best_progs[ex] for ex in chunk_exs]
    chunk_prog = remove_redundancy(tracker.tester, progs)
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
            # dbg('reusing seen prog')
            return seen_prog
    return None

def process_chunk(tracker, chunk_exs, iteration_progs):
    chunk_prog = get_union_of_example_progs(tracker, chunk_exs)

    # TODO: DO WE NEED TO UPDATE BEST_PROGS?
    chunk_bounds = calc_chunk_bounds(tracker, chunk_prog, chunk_exs)

    # if we cannot learn something smaller, then this chunk program is the union of all the solutions for the smaller chunks
    if chunk_bounds.min_literals >= chunk_bounds.max_literals:
        dbg(f'\t skipping as min_literals ({chunk_bounds.min_literals}) >= max_literals ({chunk_bounds,max_literals})')
        return chunk_prog

    # try to reuse an already found hypothesis
    complete_seen_prog = reuse_seen(tracker, chunk_exs, iteration_progs, chunk_bounds)

    if complete_seen_prog:
        return complete_seen_prog

    bootstap_cons = set()

    if WITH_LAZINESS:
        # find the best program already seen
        seen_prog, bootstap_cons = check_old_programs(tracker, chunk_exs, chunk_bounds)

        if seen_prog:
            chunk_prog = seen_prog
            chunk_bounds = calc_chunk_bounds(tracker, chunk_prog, chunk_exs)

            # also update when an improvement is possible
            if chunk_bounds.min_literals >= chunk_bounds.max_literals:
                print('EARLY SKIPPING')
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

        for ex in chunk_exs:
            tracker.best_progs[ex] = chunk_prog

        assert(tracker.tester.is_complete(chunk_prog, chunk_exs))
        assert(len(tracker.tester.reduce_subset(chunk_prog, chunk_exs)) == len(chunk_prog))

        # chunk_prog is guaranteed to be complete, consistent, and smaller than the previous best
        iteration_progs.add(chunk_prog)

    return remove_redundancy(tracker.tester, iteration_progs)

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
    tracker = Tracker()
    tracker.settings = settings
    tracker.tester = Tester(settings)
    tracker.max_total_literals = settings.max_literals
    tracker.stats = Stats(log_best_programs=settings.info)
    tracker.pos = frozenset(tracker.tester.pos)
    tracker.neg = frozenset(tracker.tester.neg)
    tracker.unsolvable = set()
    tracker.best_progs = {ex:None for ex in tracker.pos}

    # size of the chunks/partitions of the examples
    chunk_size = 1

    # initially partitions each example into its own partition
    all_chunks = [[x] for x in tracker.pos]

    while True:
        dbg('CHUNK_SIZE', chunk_size)

        # program for this chunk size is the union of the chunk progs
        iteration_prog = learn_iteration_prog(tracker, all_chunks, chunk_size)

        dbg(f'CHUNK:{chunk_size} size:{num_literals(iteration_prog)} errors:{calc_score(tracker.tester, iteration_prog)}')
        pprint(iteration_prog)

        if best_prog_improvement(tracker, iteration_prog):
            # update the best program for each example: we try to logically reduce the iteration_prog with respect to each positive example
            for ex in flatten(all_chunks):
                tracker.best_progs[ex] = tracker.tester.reduce_subset(iteration_prog, [ex])
            update_best_prog(tracker, iteration_prog)

            if WITH_OPTIMISTIC and tracker.best_prog_errors == 0:
                break

        if WITH_CHUNKING:
            all_chunks = perform_chunking(tracker)

        if len(all_chunks) == 1:
            break

        # double the chunk size (so the loop runs for at most log(len(pos)) iterations)
        if chunk_size > len(tracker.pos):
            break
        chunk_size += chunk_size

    return tracker.best_prog, tracker.stats