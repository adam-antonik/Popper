%% max_clauses(6).
max_vars(6).
max_body(5).

%% 3/6/5

head_pred(next_cell,3).
body_pred(does_jump,4).
body_pred(my_succ,2).
body_pred(my_true_cell,3).
body_pred(role,1).
body_pred(my_pos,1).
body_pred(different,2).
body_pred(c_zerocoins,1).
body_pred(c_onecoin,1).
body_pred(c_twocoins,1).

type(next_cell,(ex,pos,cell_value)).
type(does_jump,(ex,agent,pos,pos)).
type(my_succ,(pos,pos)).
type(my_true_cell,(ex,pos,cell_value)).
type(role,(agent,)).
type(my_pos,(pos,)).
type(different,(pos,pos)).
type(c_zerocoins,(cell_value,)).
type(c_onecoin,(cell_value,)).
type(c_twocoins,(cell_value,)).

%% functional(my_succ,2).
%% irreflexive(my_succ,2).
%% functional(my_true_step,2).

%% BECAUSE WE DO NOT LEARN FROM INTERPRETATIONS
:-
    clause(C),
    #count{V : clause_var(C,V),var_type(C,V,ex)} != 1.

%% next_cell(A,B,C):-different(D,B),different(B,F),my_true_cell(A,B,C),does_jump(A,E,D,F),role(E).
%% next_cell(A,B,C):-does_jump(A,F,D,B),c_twocoins(C),different(E,D),does_jump(A,F,D,E).
%% next_cell(A,B,C):-c_zerocoins(C),different(E,D),does_jump(A,F,B,E),does_jump(A,F,D,E).
%% %time,547.8122680187225
