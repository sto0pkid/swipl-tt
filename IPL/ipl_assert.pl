:- dynamic a/2, f/0, t/0, and/2, or/2, implies/2.

f :- false.
t :- true.
and(X,Y) :- X, Y.
or(X,Y) :- X ; Y.
implies(X,Y) :- assertz(X),Y,retract(X).


a(X,mortal) :- a(X,man).
