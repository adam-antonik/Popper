%% f(A,B):-prepend(E,D,B),even(E),f(C,D),tail(A,C),head(A,E).
%% f(A,B):-f(C,B),tail(A,C),odd(D),head(A,D).
%% f(A,B):-empty(A),empty(B).
%% Total programs: 72703
%% Bootstrap:
%%     Called: 1 times      Total: 0.00     Mean: 0.000     Max: 0.000
%% Crap And Cache:
%%     Called: 72703 times      Total: 0.57     Mean: 0.000     Max: 0.000
%% Ground:
%%     Called: 72702 times      Total: 6.87     Mean: 0.000     Max: 0.163
%% Build:
%%     Called: 72702 times      Total: 33.23    Mean: 0.000     Max: 2.120
%% Test:
%%     Called: 72703 times      Total: 79.30    Mean: 0.001     Max: 1.116
%% Generate:
%%     Called: 72716 times      Total: 454.97   Mean: 0.006     Max: 1.718
%% Add:
%%     Called: 72702 times      Total: 500.97   Mean: 0.007     Max: 0.018
%% Total operation time: 1075.93s
%% Total execution time: 1314.91s

max_vars(5).
max_body(5).
%% max_clauses(3).
enable_recursion.

head_pred(f,2).
body_pred(empty,1).
body_pred(odd,1).
body_pred(even,1).
body_pred(head,2).
body_pred(tail,2).
body_pred(prepend,3).

type(f,(list,list)).
type(head,(list,element)).
type(tail,(list,list)).
type(empty,(list,)).
type(odd,(element,)).
type(even,(element,)).
type(prepend,(element,list,list)).

direction(f,(in,out)).
direction(empty,(out,)).
direction(head,(in,out)).
direction(tail,(in,out)).
direction(odd,(in,)).
direction(even,(in,)).
direction(prepend,(in,in,out)).


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

:-
    body_literal(2,empty,_,_).