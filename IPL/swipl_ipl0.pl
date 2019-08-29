:- module(swipl_ipl0, [bottom/0, top/0, and/2, or/2]).

bottom :- false.
top.
and(X,Y) :- X, Y. 
or(X,Y) :- X ; Y.

/*
Instead of bottom, you can just use false:

?- false.
false
*/

/*
Instead of top, you can just use true:

?- true.
true
*/

/*
Instead of and(X,Y), you can just query: 
? X, Y.

?- true, true.
true.

?- true, false.
false.

?- false, true.
false.

?- false, false.
false.
*/

/*
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
*/


/*
What about ":-" ?
*/
