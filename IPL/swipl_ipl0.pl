:- module(swipl_ipl0, [f/0, t/0, and/2, or/2]).


f :- false.
t :- true.

and(X,Y) :- X, Y. 

or(X,Y) :- X ; Y.



/*
Instead of `f`, you can just use false:

?- false.
false





Instead of `t`, you can just use true:

?- true.
true





Instead of `and(X,Y)`, you can just use `X, Y`: 
?- true, true.
true.

?- true, false.
false.

?- false, true.
false.

?- false, false.
false.





Instead of or(X,Y), you can just query:
?- X ; Y.

?- true ; true.
true

?- true ; false.
true

?- false ; true.
true

?- false ; false.
false





What about `implies(X,Y)` ?


*/
