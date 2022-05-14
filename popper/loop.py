import logging
import sys
from datetime import datetime
from . util import Settings2, Stats, timeout, format_rule, chunk_list, flatten
# from . tester import Tester
from . pltester import Tester
# from . asptester import Tester
from . generate import Generator
from . select import Selector
from . constrain import Constrainer, specialisation_constraint, elimination_constraint
import time

def dbg(*args):
    now = datetime.now()
    current_time = now.strftime("%H:%M:%S")
    print(current_time, *args)

ss = {}

def find_rules(settings, cons, rule_size, rule_coverage, chunk_pos):
    bootstrap_cons = deduce_cons(cons, chunk_pos)
    # bootstrap_cons = set()
    generator = Generator(settings, bootstrap_cons)
    tester = Tester(settings)

    for size in range(1, settings.max_size+1):
        generator.update_num_literals(size)

        while True:

            # print('')
            with settings.stats.duration('gen'):
                rule = generator.gen_prog()

            if rule == None:
                break

            settings.stats.total_programs += 1


            with settings.stats.duration('test'):
                inconsistent, pos_covered = tester.test_rule(rule)

            chunk_pos_covered = set([x for x in chunk_pos if x in pos_covered])
            incomplete = len(chunk_pos_covered) != len(chunk_pos)

            # dbg(format_rule(rule), f'incomplete:{incomplete}', f'inconsistent:{inconsistent}', len(pos_covered))
            # print('%', format_rule(rule))
            # print('')
            # print(format_rule(rule))
            # print(f'inconsistent:{inconsistent}')
            # print(f'incomplete:{incomplete}')
            # print(f'totally incomplete:{len(pos_covered) == 0}')
            # print('pos_covered',pos_covered)
            # print('chunk_pos_covered',chunk_pos_covered

            add_spec = False

            if not inconsistent and len(pos_covered) > 0:
                xs = frozenset(pos_covered)
                if xs in ss:
                    add_spec = True
                    # con = specialisation_constraint(rule)
                    # cons.add(con)
                    # print('')
                    # print('---')
                    # print('SKIP')
                    # print('OLD', format_rule(ss[xs]))
                    # print('NEW', format_rule(rule))
                    for e in settings.pos:
                        cons.add_specialisation(rule, e)
                    # for e in pos:
                        # spec_cons[e].add(con)
                    # continue
                    # skip = True
                else:
                    ss[xs] = rule

            # add_gen = False
            cons.add_elimination(rule)

            # if inconsistent, then rule all generalisations
            if inconsistent:
                pass
                # cons.add_generalisation(rule)
                # add_gen = True
            else:
                # if consistent, no need to specialise
                add_spec = True
                for e in settings.pos:
                    cons.add_specialisation(rule, e)

            # for any examples uncovered, save a specialisation constraint
            for e in settings.pos:
                if e not in pos_covered:
                    cons.add_specialisation(rule, e)

            # if consistent and covers at least one pos example, yield rule
            if len(pos_covered) > 0 and not inconsistent:
                print('yield')
                rule_size[rule] = size + 1 # need to add 1 for the head literal
                rule_coverage[rule] = pos_covered
                yield rule

            # if it does not cover any chunk example, then prune specialisations
            if len(chunk_pos_covered) == 0:
                add_spec = True

            # if it covers all examples, add candidate rule and prune specialisations
            if len(chunk_pos_covered) == len(chunk_pos) and not inconsistent:
                dbg(f'complete_rule {format_rule(rule)} {settings.stats.total_programs}')
                return

            with settings.stats.duration('constrain'):
                # elim_con = elimination_constraint(rule)
                # generator.add_constraint(elim_con)
                if add_spec:
                    spec_con = specialisation_constraint(rule)
                    generator.add_constraint(spec_con)
                else:
                    elim_con = elimination_constraint(rule)
                    generator.add_constraint(elim_con)
    # assert(False)

def deduce_cons(cons, chunk_pos):
    return set.intersection(*[cons.spec_cons[x] for x in chunk_pos]) | cons.elim_cons

def popper(ignore, stats):
    settings = Settings2()
    settings.stats=stats
    cons = Constrainer(settings)
    selector = Selector(settings)

    all_chunks = [[x] for x in settings.pos]

    chunk_size = 1
    # chunk_size = len(settings.pos)

    all_rules = set()

    while chunk_size <= len(settings.pos):
        print('CHUNK_SIZE', chunk_size)
        chunks = list(chunk_list(all_chunks, chunk_size))

        # examples already covered by rules already
        covered = set()

        for chunk_pos in chunks:
            chunk_pos = set(flatten(chunk_pos))

            # chunk_pos = {'f(t33)'}
            # 10:47:53 complete_rule f(A):- has_car(A,B),has_car(A,C),roof_closed(C),roof_open(B),two_wheels(B). 19

            # print(chunk_pos)

            if chunk_pos.issubset(covered):
                # print('skip')
                continue

            # if all examples are covered, stop
            if len(covered) == len(chunks):
                break

            # find new candidate rules
            new_rules = list(find_rules(settings, cons, selector.rule_size, selector.rule_coverage, chunk_pos))
            # print(len(new_rules))
            # assert(len(new_rules) > 0)
            for rule in new_rules:
                covered.update(selector.rule_coverage[rule])
                all_rules.add(rule)

            if len(new_rules) > 0:
                with settings.stats.duration('select'):
                    selector.update_best_solution(all_rules)

        # return

        # chunk_size += chunk_size
        if chunk_size == 1:
            chunk_size = len(settings.pos)
        elif chunk_size == len(settings.pos):
            chunk_size += 1

    # with settings.stats.duration('select'):
        # selector.update_best_solution(all_rules)
    return


def learn_solution(settings):
    stats = Stats(log_best_programs=settings.info)
    stats.solution_found = False
    log_level = logging.DEBUG if settings.debug else logging.INFO
    logging.basicConfig(level=log_level, stream=sys.stderr, format='%(message)s')
    timeout(popper, (settings, stats), timeout_duration=int(settings.timeout))

    return stats.solution_found, stats
