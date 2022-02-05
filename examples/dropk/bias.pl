%% 14:19:31 BEST_PROG size:7 errors:0
%% 14:19:31 f(A,B,C):-decrement(B,E),tail(D,C),f(A,E,D)
%% 14:19:31 f(A,B,C):-one(B),tail(A,C)
%% 14:19:31 NEW MAX_LITERALS - OLD:100 NEW:6
%% 0
%% Total programs: 1296
%% Total execution time: 24.39s

max_vars(6).
max_body(6).
enable_recursion.

head_pred(f,3).
body_pred(head,2).
body_pred(tail,2).
body_pred(element,2).
body_pred(increment,2).
body_pred(decrement,2).
body_pred(geq,2).
body_pred(empty,1).
body_pred(even,1).
body_pred(odd,1).
body_pred(one,1).
body_pred(zero,1).

type(f,(list,element,list)).
type(head,(list,element)).
type(tail,(list,list)).
type(element,(list,element)).
type(increment,(element,element)).
type(decrement,(element,element)).
type(geq,(element,element)).
type(empty,(list,)).
type(even,(element,)).
type(odd,(element,)).
type(one,(element,)).
type(zero,(element,)).

direction(f,(in,in,out)).
direction(head,(in,out)).
direction(tail,(in,out)).
direction(element,(in,out)).
direction(increment,(in,out)).
direction(decrement,(in,out)).
direction(geq,(in,in)).
direction(empty,(in,)).
direction(even,(in,)).
direction(odd,(in,)).
direction(one,(in,)).
direction(zero,(out,)).