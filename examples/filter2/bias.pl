%% WITH MUCH BIAS
%% python3 popper.py examples/filter --eval-timeout=0.01
%% f(A,B) :- empty(B),empty(A).
%% f(A,B) :- tail(A,D),head(A,C),odd(C),f(D,B).
%% f(A,B) :- tail(A,D),head(A,C),even(C),f(D,E),prepend(C,E,B).
%% 90.26s user 0.49s system 100% cpu 1:30.60 total

%% WITH LITTLE BIAS
%% python3 /Users/andrew/icloud/code/popper/popper.py examples/filter
%% f(A,B) :- empty(A),empty(B).
%% f(A,B) :- head(A,D),odd(D),tail(A,C),f(C,B).
%% f(A,B) :- tail(A,C),head(A,E),even(E),f(C,D),prepend(E,D,B).
%% 933.52s user 4.18s system 100% cpu 15:35.98 total

max_vars(5).
max_body(5).
max_clauses(3).
enable_recursion.

head_pred(f,2).
body_pred(empty,1).
body_pred(odd,1).
body_pred(even,1).
body_pred(head,2).
body_pred(tail,2).
body_pred(prepend,3).

%% body_pred(c_2,1).
%% body_pred(c_4,1).
%% body_pred(c_6,1).
%% body_pred(c_8,1).
%% body_pred(c_10,1).

type(f,(list,list)).
type(head,(list,element)).
type(tail,(list,list)).
type(empty,(list,)).
type(odd,(element,)).
type(even,(element,)).
type(prepend,(element,list,list)).

%% type(c_2,(element,)).
%% type(c_4,(element,)).
%% type(c_6,(element,)).
%% type(c_8,(element,)).
%% type(c_10,(element,)).

direction(f,(in,out)).
direction(empty,(out,)).
direction(head,(in,out)).
direction(tail,(in,out)).
direction(odd,(in,)).
direction(even,(in,)).
direction(prepend,(in,in,out)).

%% direction(c_2, (in, )).
%% direction(c_4, (in, )).
%% direction(c_6, (in, )).
%% direction(c_8, (in, )).
%% direction(c_10, (in, )).

%% EXTRA BIAS TO REDUCE LEARNING TIM
only_once(head).
only_once(tail).
only_once(prepend).
:-
    only_once(P),
    clause(C),
    #count{Vars : body_literal(C,P,A,Vars)} > 1.
:-
    body_literal(0,_,2,_).
:-
    body_literal(0,_,3,_).
x:-
    body_literal(1,empty,_,_).
x:-
    body_literal(2,empty,_,_).