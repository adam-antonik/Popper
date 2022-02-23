from pyswip import Prolog

import os
import sys
import time
import pkg_resources
from contextlib import contextmanager
from . core import Clause, Literal, separable
from datetime import datetime

class Tester():
    def __init__(self, settings):
        self.settings = settings
        self.prolog = Prolog()
        self.eval_timeout = settings.eval_timeout
        self.cached_redundant_literals = {}

        bk_pl_path = self.settings.bk_file
        exs_pl_path = self.settings.ex_file
        test_pl_path = pkg_resources.resource_filename(__name__, "lp/test.pl")

        for x in [exs_pl_path, bk_pl_path, test_pl_path]:
            if os.name == 'nt': # if on Windows, SWI requires escaped directory separators
                x = x.replace('\\', '\\\\')
            self.prolog.consult(x)

        # load examples
        list(self.prolog.query('load_examples'))

        self.pos = [x['I'] for x in self.prolog.query('current_predicate(pos_index/2),pos_index(I,_)')]
        self.neg = [x['I'] for x in self.prolog.query('current_predicate(neg_index/2),neg_index(I,_)')]

        self.prolog.assertz(f'timeout({self.eval_timeout})')

        self.cached_is_inconsistent = {}
        self.cached_all_pos_covered = {}
        self.cached_pos_covered = {}

    def first_result(self, q):
        return list(self.prolog.query(q))[0]

    @contextmanager
    def using(self, rules):
        recursive = not separable(rules)
        current_clauses = set()
        try:
            if recursive:
                self.prolog.assertz('recursive')

            # print('')
            for rule in rules:
                head, body = rule
                x = Clause.to_code(Clause.to_ordered(rule))
                self.prolog.assertz(x)
                current_clauses.add((head.predicate, head.arity))
            yield
        finally:
            if recursive:
                self.prolog.retractall('recursive')
            for predicate, arity in current_clauses:
                args = ','.join(['_'] * arity)
                self.prolog.retractall(f'{predicate}({args})')

    def rule_has_redundant_literal(self, rule):
        k = hash(rule)
        if k in self.cached_redundant_literals:
            return self.cached_redundant_literals[k]

        head, body = rule
        C = f"[{','.join(('not_'+ Literal.to_code(head),) + tuple(Literal.to_code(lit) for lit in body))}]"
        has_redundant_literal = len(list(self.prolog.query(f'redundant_literal({C})'))) > 0
        self.cached_redundant_literals[k] = has_redundant_literal
        return has_redundant_literal

    def check_redundant_clause(self, program):
        # AC: if the overhead of this call becomes too high, such as when learning programs with lots of clauses, we can improve it by not comparing already compared clauses
        prog = []
        for (head, body) in program:
            C = f"[{','.join(('not_'+ Literal.to_code(head),) + tuple(Literal.to_code(lit) for lit in body))}]"
            prog.append(C)
        prog = f"[{','.join(prog)}]"
        return list(self.prolog.query(f'redundant_clause({prog})'))

    def is_functional(self, program, pos):
        with self.using(program):
            return list(self.prolog.query(f'non_functional.')) == []

    def find_redundant_clauses(self, rules):
        prog = []
        for i, (head, body) in enumerate(rules):
            C = f"[{','.join(('not_'+ Literal.to_code(head),) + tuple(Literal.to_code(lit) for lit in body))}]"
            C = f'{i}-{C}'
            prog.append(C)
        prog = f"[{','.join(prog)}]"
        res = self.prolog.query(f'find_redundant_clauses({prog},R0,R1)')

        for dic in res:
            r0 = dic['R0']
            r1 = dic['R1']
            yield rules[r0], rules[r1]

    def pos_covered(self, rules, x):
        if all(not Clause.is_separable(rule) for rule in rules):
            return False

        if rules in self.cached_pos_covered:
            if x in self.cached_pos_covered[rules]:
                return self.cached_pos_covered[rules][x]
        else:
            self.cached_pos_covered[rules] = {}

        # if a single rule or non-separable
        if len(rules) == 1 or any(not Clause.is_separable(rule) for rule in rules):
            with self.using(rules):
                res = len(list(self.prolog.query(f'pos_covered({x})'))) > 0
                self.cached_pos_covered[rules][x] = res
                return res

        res = any(self.pos_covered(frozenset([rule]), x) for rule in rules)
        self.cached_pos_covered[rules][x] = res
        return res

    def pos_covered_batch(self, rules, xs):
        if all(not Clause.is_separable(rule) for rule in rules):
            return False

        if rules not in self.cached_pos_covered:
            self.cached_pos_covered[rules] = {}

        with self.using(rules):
            ys = set(list(self.prolog.query(f'pos_covered_batch({xs},S)'))[0]['S'])
            for x in xs:
                self.cached_pos_covered[rules][x] = x in ys

    def pos_covered_all(self, rules):
        if all(not Clause.is_separable(rule) for rule in rules):
            return set()

        return frozenset((self.pos_covered(rules, x) for x in self.pos))

    def is_complete(self, rules, pos):
        if all(not Clause.is_separable(rule) for rule in rules):
            return False

        to_check = []
        if rules in self.cached_pos_covered:
            for x in pos:
                if x not in self.cached_pos_covered[rules]:
                    to_check.append(x)
        if len(to_check) > 1:
            self.pos_covered_batch(rules, to_check)
        return all(self.pos_covered(rules, x) for x in pos)

    def is_inconsistent(self, rules):
        if all(not Clause.is_separable(rule) for rule in rules):
            return False

        if rules in self.cached_is_inconsistent:
            return self.cached_is_inconsistent[rules]

        with self.using(rules):
            res = len(list(self.prolog.query(f'inconsistent'))) > 0
        self.cached_is_inconsistent[rules] = res
        return res

    def is_totally_incomplete(self, rules, pos):
        if all(not Clause.is_separable(rule) for rule in rules):
            return False

        to_check = []
        if rules in self.cached_pos_covered:
            for x in pos:
                if x not in self.cached_pos_covered[rules]:
                    to_check.append(x)
        if len(to_check) > 1:
            self.pos_covered_batch(rules, to_check)
        return all(not self.pos_covered(rules, x) for x in pos)

    def all_pos_covered(self, rules):
        if all(not Clause.is_separable(rule) for rule in rules):
            return set()

        if rules in self.cached_all_pos_covered:
            return self.cached_all_pos_covered[rules]

        # if a single rule or non-separable
        if len(rules) == 1 or any(not Clause.is_separable(rule) for rule in rules):
            # print('all_pos_covered')
            with self.using(rules):
                res = frozenset(next(self.prolog.query('all_pos_covered(Xs)'))['Xs'])
            self.cached_all_pos_covered[rules] = res
            # hacky but should help
            if rules not in self.cached_pos_covered:
                self.cached_pos_covered[rules] = {}
            for x in self.pos:
                self.cached_pos_covered[rules][x] = x in res
            return res

        xs = set()
        for rule in rules:
            sub = frozenset([rule])
            xs.update(self.all_pos_covered(sub))
        xs = frozenset(xs)
        if rules not in self.cached_pos_covered:
            self.cached_pos_covered[rules] = {}
        for x in self.pos:
            self.cached_pos_covered[rules][x] = x in xs
        self.cached_all_pos_covered[rules] = xs
        return xs

    # def is_incomplete(self, rules, pos):
        # return self.is_complete(self, rules, pos)


    # # OLD!!!
    # def is_complete(self, rules, pos):
    #     return all(x in self.success_set(rules) for x in pos)

    # def is_inconsistent(self, rules):
    #     return any(x in self.success_set(rules) for x in self.neg)

    # def is_totally_incomplete(self, rules, pos):
    #     return all(x not in self.success_set(rules) for x in pos)

    # def all_pos_covered(self, rules):
    #     covered = self.success_set(rules)
    #     return frozenset(x for x in self.pos if x in covered)


    # def is_complete_all(self, rules):
        # return self.is_complete(rules, self.pos)

    # def is_consistent_all(self, rules):
        # return all(x not in self.success_set(rules) for x in self.neg)

    # def is_incomplete_all(self, rules):
        # return self.is_incomplete(rules, self.pos)

    # def is_totally_incomplete_all(self, rules):
        # return self.is_totally_incomplete(rules, self.pos)

    # # TMP!!!!!
    # def reduce_success_set_all(self, rules):
    #     assert(not self.is_inconsistent(rules))
    #     rules_ss = self.pos_covered_all(rules)
    #     rules = list(rules)
    #     for i in range(len(rules)):
    #         subrules = frozenset(rules[:i] + rules[i+1:])
    #         subrules_ss = self.pos_covered_all(subrules)
    #         if rules_ss == subrules_ss and not self.is_inconsistent(subrules):
    #             return self.reduce_success_set_all(subrules)
    #     return frozenset(rules)

    def reduce_subset(self, rules, pos):
        # print('<REDUCE_SUBSET>')
        # for rule in rules:
        #     x = Clause.to_code(Clause.to_ordered(rule))
        #     print(x)
        # print('</REDUCE_SUBSET>')
        rules = list(rules)
        for i in range(len(rules)):
            subrules = frozenset(rules[:i] + rules[i+1:])
            if self.is_complete(subrules, pos) and not self.is_inconsistent(subrules):
                return self.reduce_subset(subrules, pos)
        return frozenset(rules)

    def subsumes(self, r1, r2):
        r1 = list(r1)
        r1 = f"[{','.join(x for x in r1)}]"
        r2 = list(r2)
        r2 = f"[{','.join(x for x in r2)}]"
        res = list(self.prolog.query(f'subsumes2({r1},{r2})'))
        return len(res) > 0

    def subsumes2(self, t1, t2):
        def fmt(r):
            r = list(r)
            return '[' + ','.join(x for x in r) + ']'

        t1 = '['+ ','.join(fmt(r) for r in t1) + ']'
        t2 = '['+ ','.join(fmt(r) for r in t2) + ']'
        res = list(self.prolog.query(f'subsumes3({t1},{t2})'))
        return len(res) > 0