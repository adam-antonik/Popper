max_vars(6).
max_body(6).

%% 10:17:46 next(A,B):-c_b(C),my_input(D,C),does(A,D,C),my_true(A,B),c_r(B)
%% 10:17:46 next(A,B):-c_b(C),my_input(D,C),c_p(E),does(A,D,C),c_q(B),my_true(A,E)
%% 10:17:46 next(A,B):-not_my_true(A,B),my_input(D,C),c_a(C),does(A,D,C),c_p(B)
%% 10:17:46 next(A,B):-my_succ(C,B),my_true(A,C)
%% 10:17:46 next(A,B):-c_q(B),does(A,E,D),c_c(D),c_r(C),role(E),my_true(A,C)
%% 10:17:46 next(A,B):-my_input(E,C),c_c(C),does(A,E,C),c_q(D),my_true(A,D),c_r(B)
%% 10:17:46 next(A,B):-my_input(C,D),c_p(B),c_c(D),my_true(A,B),does(A,C,D)
%% 10:17:46 next(A,B):-c_b(E),does(A,C,E),c_q(D),c_p(B),my_input(C,E),my_true(A,D)

head_pred(next,2).
body_pred(does,3).
body_pred(my_input,2).
body_pred(my_true,2).
body_pred(my_succ,2).
body_pred(role,1).
body_pred(c_p,1).
body_pred(c_q,1).
body_pred(c_r,1).
body_pred(c_a,1).
body_pred(c_b,1).
body_pred(c_c,1).
body_pred(not_my_true,2).

type(next,(ex,prop)).
type(does,(ex,agent,action)).
type(my_input,(agent,action)).
type(my_true,(ex,prop)).
type(my_succ,(prop,prop)).
type(role,(agent,)).
type(c_p,(prop,)).
type(c_q,(prop,)).
type(c_r,(prop,)).
type(c_a,(action,)).
type(c_b,(action,)).
type(c_c,(action,)).
type(not_my_true,(ex,prop)).

%% BECAUSE WE DO NOT LEARN FROM INTERPRETATIONS
:-
    clause(C),
    #count{V : clause_var(C,V),var_type(C,V,ex)} != 1.