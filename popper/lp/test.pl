%%%%%%%%%% EXAMPLE LOADING %%%%%%%%%%
:- dynamic recursive/0.


load_examples:-
    load_pos,
    load_neg.

load_pos:-
    current_predicate(pos/1),!,
    findall(X, pos(X), Pos),
    assert_pos_aux(Pos,1).
load_pos.

load_neg:-
    current_predicate(neg/1),!,
    findall(X, neg(X), Neg),
    assert_neg_aux(Neg,-1).
load_neg.

assert_pos_aux([],_).
assert_pos_aux([H|T],I1):-
    assertz(pos_index(I1, H)),
    I2 is I1+1,
    assert_pos_aux(T,I2).

assert_neg_aux([],_).
assert_neg_aux([H|T],I1):-
    assertz(neg_index(I1, H)),
    I2 is I1-1,
    assert_neg_aux(T,I2).

%%%%%%%%%% EXAMPLE TESTING %%%%%%%%%%

%% ex_index(ID,Atom):-
%%     current_predicate(pos_index/2),
%%     pos_index(ID,Atom).
%% ex_index(ID,Atom):-
%%     current_predicate(neg_index/2),
%%     neg_index(ID,Atom).

test_ex(Atom):-
    recursive,!,
    timeout(T),
    catch(call_with_time_limit(T, call(Atom)), time_limit_exceeded,false),!.

test_ex(Atom):-
    call(Atom).

%% success_set(Xs):-
    %% findall(ID, (ex_index(ID,Atom),test_ex(Atom)), Xs).

%% pos_covered(X):-
%%     pos_index(X,Atom),
%%     call(Atom).

all_pos_covered(Xs):-
    findall(ID, (pos_index(ID,Atom), test_ex(Atom)), Xs).

pos_covered(X):-
    pos_index(X,Atom),
    test_ex(Atom),!.

pos_covered_batch(Xs,Ys):-
    findall(X, (member(X,Xs), pos_index(X,Atom), test_ex(Atom)), Ys).

%% covered(X):-
%%     ex_index(X,Atom),
%%     call(Atom),!.

inconsistent:-
    \+ current_predicate(neg_index/2),!,
    false.

inconsistent:-
    %% timeout(T),
    neg_index(_,Atom),
    test_ex(Atom),!.
    %% functor(Atom,P,A),
    %% current_predicate(P/A),
    %% timeout(T),
    %% call(Atom),!.
    %% test_ex(Atom),!.

%% ========== FUNCTIONAL CHECKS ==========

non_functional_aux(Atom):-
    timeout(T),
    catch(call_with_time_limit(T, non_functional(Atom)),time_limit_exceeded,false),!.

non_functional:-
    pos_index(_,Atom),
    non_functional_aux(Atom),!.


%% ========== REDUNDANCY CHECKS ==========

subsumes(C,D) :- \+ \+ (copy_term(D,D2), numbervars(D2,0,_), subset(C,D2)).

subset([], _D).
subset([A|B], D):-
    member(A, D),
    subset(B,D).

redundant_literal(C1):-
    select(_,C1,C2),
    subsumes(C1,C2),!.

redundant_clause(P1):-
    select(C1,P1,P2),
    member(C2,P2),
    subsumes(C1,C2),!.

fp(0):-
    \+ current_predicate(neg_index/2),!.

fp(N):-
    findall(1, (neg_index(_,Atom), test_ex(Atom)), S),
    length(S,N).


%% TODO: ADD MEANINGFUL COMMENT
find_redundant_clauses(P1,K1,K2):-
    select(K1-C1,P1,P2),
    member(K2-C2,P2),
    subsumes(C1,C2).



%% subsumes2(C,D) :-
    %% \+ \+ (copy_term(D,D2), numbervars(D2,0,_), subset(C,D2)).


subsumes3(_, []).
subsumes3(T1, [R2|T2]):-
    member(R1, T1),
    subsumes(R1, R2),
    subsumes3(T1, T2).
