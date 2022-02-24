max_vars(4).
max_body(3).
enable_recursion.

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

%%
%% functional(succ,2).
%% irreflexive(succ,2).



%% in(2,3).


%% out(A,B,blue):- succ(A,A1), in(A1,B,black).
%% out(A,B,blue):- succ(B,B1), in(A,B1,black).
%% out(A,B,blue):- succ(B,B1), in(A,B1,black).
%% out(A,B,blue):- succ(B,B1), in(A,B1,black).



%% 11,21,31,41
%% 21,22,32,42