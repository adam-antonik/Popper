import operator
from collections import defaultdict
from . core import ConstVar, Literal, Clause

def alldiff(args):
    return Literal('AllDifferent', args, meta=True)

def lt(a, b):
    return Literal('<', (a,b), meta=True)

def eq(a, b):
    return Literal('==', (a,b), meta=True)

def gteq(a, b):
    return Literal('>=', (a,b), meta=True)

def vo_clause(variable):
    return ConstVar(f'C{variable}', 'Clause')

def vo_variable(variable):
    return ConstVar(f'{variable}', 'Variable')

# restrict a clause id to have a specific body size
def body_size_literal(clause_var, body_size):
    return Literal('body_size', (clause_var, body_size))

class Constrain:
    def __init__(self):
        self.seen_clause_handle = {}
        self.added_clauses = set()

    # def make_literal_handle(self, literal):
        # return f'{literal.predicate}{"".join(literal.arguments)}'

    def make_literal_handle(self, literal):
        return f'{literal.predicate}({".".join(literal.arguments)})'

    def make_clause_handle(self, clause):
        if clause in self.seen_clause_handle:
            return self.seen_clause_handle[clause]
        head, body = clause
        body_literals = sorted(body, key = operator.attrgetter('predicate'))
        head = self.make_literal_handle(head)
        body = ','.join(self.make_literal_handle(literal) for literal in body_literals)
        # clause_handle = ''.join(self.make_literal_handle(literal) for literal in [head] + body_literals)
        clause_handle = f'"{head}:- {body}"'
        self.seen_clause_handle[clause] = clause_handle
        return clause_handle

    # def make_clause_inclusion_rule(self, clause, min_num=None, clause_handle):
    def make_clause_inclusion_rule(self, clause, clause_handle):
        if clause_handle in self.added_clauses:
            return
            yield

        (head, body) = clause

        self.added_clauses.add(clause_handle)
        clause_number = vo_clause('l')

        literals = []
        literals.append(Literal('head_literal', (clause_number, head.predicate, head.arity, tuple(vo_variable(v) for v in head.arguments))))

        for body_literal in body:
            literals.append(Literal('body_literal', (clause_number, body_literal.predicate, body_literal.arity, tuple(vo_variable(v) for v in body_literal.arguments))))

        # literals.append(gteq(clause_number, min_num))

        # ensure that each var_var is ground to a unique value
        # literals.append(alldiff(tuple(vo_variable(v) for v in Clause.all_vars(clause))))

        for idx, var in enumerate(head.arguments):
            literals.append(eq(vo_variable(var), idx))

        yield (Literal('included_clause', (clause_handle, clause_number)), tuple(literals))

    # def banish_constraint(self, program, before = {}, min_clause = defaultdict(lambda: 0)):
    # def banish_constraint(self, program):
    #     literals = []
    #     for clause_number, clause in enumerate(program):
    #         (head, body) = clause
    #         clause_handle = self.make_clause_handle(clause)
    #         yield from self.make_clause_inclusion_rule(clause, min_clause[clause_number], clause_handle)

    #         literals.append(Literal('included_clause', (clause_handle, vo_clause(clause_number))))
    #         literals.append(body_size_literal(vo_clause(clause_number), len(body)))

    #     # for clause_id1, clause_numbers in before.items():
    #     #     for clause_id2 in clause_numbers:
    #     #         literals.append(lt(vo_clause(clause_id1), vo_clause(clause_id2)))

    #     # for clause_number, clause in enumerate(program):
    #     #     literals.append(gteq(vo_clause(clause_number), min_clause[clause]))

    #     num_clauses = len(program)
    #     # ensure that each clause_var is ground to a unique value
    #     literals.append(alldiff(tuple(vo_clause(c) for c in range(num_clauses))))
    #     literals.append(Literal('clause', (num_clauses, ), positive = False))

    #     yield (None, tuple(literals))

    def elimination_constraint(self, program):
        literals = []
        for clause_number, clause in enumerate(program):
            head, body = clause
            clause_handle = self.make_clause_handle(clause)
            yield from self.make_clause_inclusion_rule(clause, clause_handle)
            literals.append(Literal('included_clause', (clause_handle, vo_clause(clause_number))))
            # literals.append(body_size_literal(vo_clause(clause_number), len(body)))

        # for clause_id1, clause_numbers in before.items():
        #     for clause_id2 in clause_numbers:
        #         literals.append(lt(vo_clause(clause_id1), vo_clause(clause_id2)))

        # for clause_number, clause in enumerate(program):
        #     literals.append(gteq(vo_clause(clause_number), min_clause[clause]))

        # num_clauses =
        # ensure that each clause_var is ground to a unique value
        # literals.append(alldiff(tuple(vo_clause(c) for c in range(len(program)))))
        # literals.append(Literal('clause', (num_clauses, ), positive = False))

        # for x in literals:
        # print(':- ' + ','.join(str(x) for x in literals))

        yield (None, tuple(literals))

    def tmp_elimination_constraint(self, handles):
        literals = []
        for clause_number, handle in enumerate(handles):
            literals.append(Literal('included_clause', (handle, vo_clause(clause_number))))
            # literals.append(body_size_literal(vo_clause(clause_number), len(body)))

        # for clause_id1, clause_numbers in before.items():
        #     for clause_id2 in clause_numbers:
        #         literals.append(lt(vo_clause(clause_id1), vo_clause(clause_id2)))

        # for clause_number, clause in enumerate(program):
        #     literals.append(gteq(vo_clause(clause_number), min_clause[clause]))

        # num_clauses =
        # ensure that each clause_var is ground to a unique value
        # literals.append(alldiff(tuple(vo_clause(c) for c in range(len(program)))))
        # literals.append(Literal('clause', (num_clauses, ), positive = False))

        # for x in literals:
        # print(':- ' + ','.join(str(x) for x in literals))

        yield (None, tuple(literals))

    # def generalisation_constraint(self, program, before = {}, min_clause = defaultdict(lambda: 0)):
    def generalisation_constraint(self, program):

        # if a program is too general (entails a negative example) then rule out any generalisations
        # :- included_clause("next_value(A.B):- c1(B),c2(C),true_value(A.C)",C0),body_size(C0,3).
        # :- included_clause("next_value(A.B):- c1(B),c1(C),my_succ(D.C),true_value(A.D)",C0),body_size(C0,4).

        literals = []
        for clause_number, clause in enumerate(program):
            (_head, body) = clause
            clause_handle = self.make_clause_handle(clause)
            # yield from self.make_clause_inclusion_rule(clause, min_clause[clause], clause_handle)
            yield from self.make_clause_inclusion_rule(clause, clause_handle)

            literals.append(Literal('included_clause', (clause_handle, vo_clause(clause_number))))
            literals.append(body_size_literal(vo_clause(clause_number), len(body)))

        # for clause_id1, clause_numbers in before.items():
        #     for clause_id2 in clause_numbers:
        #         literals.append(lt(vo_clause(clause_id1), vo_clause(clause_id2)))

        # for clause_number, clause in enumerate(program):
        #     literals.append(gteq(vo_clause(clause_number), min_clause[clause]))

        # ensure that each clause_var is ground to a unique value
        if len(program) > 1:
            literals.append(alldiff(tuple(vo_clause(c) for c in range(len(program)))))

        yield (None, tuple(literals))

    # def specialisation_constraint(self, program, before = {}, min_clause = defaultdict(lambda: 0)):
    def specialisation_constraint(self, program):
        # IF TOO SPECIFIC (DOES NOT ENTAIL ALL POSITIVE) THEN RULE OUT SPECIALISATIONS
        #  :- included_clause("next_value(A.B):- c1(B),c1(C),my_succ(D.C),true_value(A.D)",C0),not clause(1).
        #  :- included_clause("next_value(A.B):- c1(B),c1(C),true_value(A.C)",C0),not clause(1).
        #  :- included_clause("next_value(A.B):- c1(B),c2(C),my_succ(D.C),true_value(A.D)",C0),not clause(1).
        #  :- included_clause("next_value(A.B):- c1(B),c2(C),true_value(A.C)",C0),not clause(1).

        literals = []

        for clause_number, clause in enumerate(program):
            clause_handle = self.make_clause_handle(clause)
            # yield from self.make_clause_inclusion_rule(clause, min_clause[clause], clause_handle)
            yield from self.make_clause_inclusion_rule(clause, clause_handle)
            clause_variable = vo_clause(clause_number)
            literals.append(Literal('included_clause', (clause_handle, clause_variable)))

        # for clause_id1, clause_numbers in before.items():
        #     for clause_id2 in clause_numbers:
        #         literals.append(lt(vo_clause(clause_id1), vo_clause(clause_id2)))

        num_clauses = len(program)
        # ensure that each clause_var is ground to a unique value
        if num_clauses > 1:
            literals.append(alldiff(tuple(vo_clause(c) for c in range(num_clauses))))
        literals.append(Literal('clause', (num_clauses, ), positive = False))

        yield (None, tuple(literals))

    def subsumption_constraint(self, rule1):
        # prune all rules that rule1 subsumes, where k is the number of literals in the body of rule1
        # :- seen(rule1,C0), seen(rule1,C1), C0 != C1, body_size(C0,k)
        _head1, body1 = rule1
        rule1_handle = self.make_clause_handle(rule1)
        # yield from self.make_clause_inclusion_rule(rule1, min_clause[rule1], rule1_handle)
        yield from self.make_clause_inclusion_rule(rule1, rule1_handle)
        v1 = vo_clause(0)
        v2 = vo_clause(1)
        literals = []
        literals.append(body_size_literal(v1, len(body1)))
        literals.append(Literal('included_clause', (rule1_handle, v1)))
        literals.append(Literal('included_clause', (rule1_handle, v2)))
        literals.append(alldiff((v1, v2)))
        yield None, tuple(literals)

    def subsumption_constraint_pairs(self, rule1, rule2):
        # if rule1 subsumes rule2 then build the following constraint where k is the body size of rule1
        # :- seen(rule1,C0), seen(rule2,C1), C0 != C1, body_size(C0,k)
        _head1, body1 = rule1
        literals = []
        rule1_handle = self.make_clause_handle(rule1)
        rule2_handle = self.make_clause_handle(rule2)
        # yield from self.make_clause_inclusion_rule(rule1, min_clause[rule1], rule1_handle)
        # yield from self.make_clause_inclusion_rule(rule2, min_clause[rule2], rule2_handle)
        yield from self.make_clause_inclusion_rule(rule1, rule1_handle)
        yield from self.make_clause_inclusion_rule(rule2, rule2_handle)
        v1 = vo_clause(0)
        v2 = vo_clause(1)
        literals = []
        literals.append(body_size_literal(v1, len(body1)))
        literals.append(Literal('included_clause', (rule1_handle, v1)))
        literals.append(Literal('included_clause', (rule2_handle, v2)))
        literals.append(alldiff((v1, v2)))
        yield None, tuple(literals)

    # AC: THIS CONSTRAINT DUPLICATES THE GENERALISATION CONSTRAINT AND NEEDS REFACTORING
    # def redundant_literal_constraint(self, clause, before = {}, min_clause = None):
    def redundant_literal_constraint(self, clause):
        # if min_clause == None:
        #     min_clause = defaultdict(0)
        _head, body = clause
        clause_handle = self.make_clause_handle(clause)
        # yield from self.make_clause_inclusion_rule(clause, min_clause[clause], clause_handle)
        yield from self.make_clause_inclusion_rule(clause, clause_handle)
        literals = []
        clause_variable = vo_clause(0)
        literals.append(Literal('included_clause', (clause_handle, clause_variable)))
        literals.append(body_size_literal(clause_variable, len(body)))
        yield (None, tuple(literals))

    # Jk: AC, I cleaned this up a bit, but this reorg is for you. Godspeed!
    # AC: @JK, I made another pass through it. It was tough. I will try again once we have the whole codebase tidied.
    # def redundancy_constraint(self, program, before = {}, min_clause = defaultdict(lambda: 0)):
    def redundancy_constraint(self, program):
        #  :- included_clause("next_value(A.B):- c1(B),c2(C),my_succ(D.C),true_value(A.D)",C0),num_recursive(next_value,0).
        #  :- included_clause("next_value(A.B):- c1(B),c1(C),true_value(A.C)",C0),num_recursive(next_value,0).

        lits_num_clauses = defaultdict(int)
        lits_num_recursive_clauses = defaultdict(int)
        for clause in program:
            (head, _) = clause
            lits_num_clauses[head.predicate] += 1
            if Clause.is_recursive(clause):
                lits_num_recursive_clauses[head.predicate] += 1

        recursively_called = set()
        while True:
            something_added = False
            for clause in program:
                (head, body) = clause
                is_rec = Clause.is_recursive(clause)
                for body_literal in body:
                    if body_literal.predicate not in lits_num_clauses:
                        continue
                    if (body_literal.predicate != head.predicate and is_rec) or (head.predicate in recursively_called):
                        something_added |= not body_literal.predicate in recursively_called
                        recursively_called.add(body_literal.predicate)
            if not something_added:
                break

        for lit in lits_num_clauses.keys() - recursively_called:
            literals = []

            for clause_number, clause in enumerate(program):
                clause_handle = self.make_clause_handle(clause)
                # yield from self.make_clause_inclusion_rule(clause, min_clause[clause], clause_handle)
                yield from self.make_clause_inclusion_rule(clause, clause_handle)
                clause_variable = vo_clause(clause_number)
                literals.append(Literal('included_clause', (clause_handle, clause_variable)))

            # for clause_id1, clause_numbers in before.items():
            #     for clause_id2 in clause_numbers:
            #         literals.append(lt(vo_clause(clause_id1), vo_clause(clause_id2)))

            # ensure that each clause_var is ground to a unique value
            if len(program) > 1:
                literals.append(alldiff(tuple(vo_clause(c) for c in range(len(program)))))

            for other_lit, num_clauses in lits_num_clauses.items():
                if other_lit == lit:
                    continue
                literals.append(Literal('num_clauses', (other_lit, num_clauses)))
            num_recursive = lits_num_recursive_clauses[lit]

            literals.append(Literal('num_recursive', (lit, num_recursive)))

            yield (None, tuple(literals))

    @staticmethod
    def format_constraint(con):
        (head, body) = con
        constraint_literals = []
        for constobj in body:
            if not constobj.meta:
                constraint_literals.append(str(constobj))
                continue
            if constobj.predicate == 'AllDifferent':
                # AC: TODO!!!
                continue
            arga, argb = constobj.arguments
            if isinstance(arga, ConstVar):
                arga = arga.name
            else:
                arga = str(arga)
            if isinstance(argb, ConstVar):
                argb = argb.name
            else:
                argb = str(argb)
            constraint_literals.append(f'{arga}{constobj.predicate}{argb}')

        x = f':- {", ".join(constraint_literals)}.'
        if head:
            x = f'{head} {x}'
        return x



    @staticmethod
    def format_rule_clingo(rule):
        head, body = rule
        constraint_literals = []
        # body = ','.join(str(x) for x in body)
        new_body = []
        if head == None:
            head = ''
        # print(str(head) + ':- ' + body)
        for literal in body:
            if not literal.meta:
                new_body.append(str(literal))
                continue
            arga, argb = literal.arguments
            if literal.predicate == 'AllDifferent':
                new_body.append(f'{arga.name} != {argb.name}')
                continue
            if isinstance(arga, ConstVar):
                arga = arga.name
            else:
                arga = str(arga)
            if isinstance(argb, ConstVar):
                argb = argb.name
            else:
                argb = str(argb)
            new_body.append(f'{arga}{literal.predicate}{argb}')
        # if head:
        return str(head) + ' :- ' + ','.join(new_body) + '.'