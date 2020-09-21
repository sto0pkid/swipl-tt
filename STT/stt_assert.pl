:- dynamic ':'/2.

:- op(999, xfx, :).

% FALSE / EMPTY type
% no constructors / introduction rules

% TRUE / UNIT / TOP type
% introduction
null:unit.

% AND / CONJUNCTION / PRODUCT / PAIR type
% introduction
(X,Y) : and(A,B) :- X:A, Y:B.

% OR / DISJUNCTION / DISJOINT UNION / UNION type
% introduction
left(X) : or(A,B) :- X:A.
right(Y) : or(A,B) :- Y:B.

% IMPLICATION / FUNCTION type
% introduction
lambda(Fresh,Expr) : implies(X,Y) :- gensym(x,Fresh), assertz(Fresh:X),Y,retract(Fresh:X).


a(X,mortal) :- a(X,man).
