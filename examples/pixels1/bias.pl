max_vars(7).
max_body(6).
%% max_clauses(1).
%% enable_recursion.

head_pred(out,3).
body_pred(in,3).
body_pred(succ,2).

type(out,(ex, int, int)).
type(in,(ex, int, int)).
type(succ,(int, int)).

%% BECAUSE WE DO NOT LEARN FROM INTERPRETATIONS
:-
    clause(C),
    #count{V : clause_var(C,V),var_type(C,V,ex)} != 1.

%% functional(succ,2).
%% irreflexive(succ,2).

%% prop(antitransitive,succ).
%% prop(antitriangular,succ).
%% prop(unique_a_b,succ).
%% prop(unique_b_a,succ).


%% out(A,B,C):-
%%     succ(D,E),
%%     succ(B,F),
%%     in(A,C,G),
%%     in(A,G,C),
%%     succ(B,D),
%%     succ(F,E).


%% out(B,C):-
%%     succ(D,E),
%%     succ(B,F),
%%     in(C,G),
%%     in(G,C),
%%     succ(B,D),
%%     succ(F,E).