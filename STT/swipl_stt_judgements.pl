:- module(swipl_stt,[judgement/2]).

/*
*
* This fixes the termination issue we had in proof-checking IPL, though that's
* somewhat independent of the motivation for development of IPL into STT.
* 
* Termination can be demonstrated by noting that in proof-checking, the rules
* only do substructural recursion. 
*
* How about termination of proof-search? This should be logically equivalent
* to IPL so we should hypothetically be able to have complete proof search.
*/

% hypothesis rule
judgement(x(V):X, [x(V):X|_]).
judgement(x(V):X, [x(W):_|G]) :- V \= W, judgement(x(V):X,G).



% reification of `false`
judgement(type(empty),_).



% reification of `true`
judgement(type(unit),_).
judgement(null:unit,_).

% bool
judgement(type(bool),_).
judgement(true:bool,_).
judgement(false:bool,_).

judgement(if_then_else(B, X, Y):C, G) :-
	judgement(B:bool, G),
	judgement(X:C, G),
	judgement(Y:C, G).

/*
beta_reduction(if_then_else(true, X, Y), X).
beta_reduction(if_then_else(false, X, Y), Y).
*/

% reification of `,`
judgement(type(pair(A,B)), G) :- 
	judgement(type(A), G),
	judgement(type(B), G).


judgement((X,Y):pair(A,B), G) :- 
	judgement(type(pair(A,B)), G),
	judgement(X:A, G),
	judgement(Y:B, G).

% negative formulation of and_elim rules
judgement(first(P):A, G) :- 
	judgement(P:pair(A,_), G).

judgement(second(P):B, G) :- 
	judgement(P:pair(_,B), G).

/*
beta_reduction(first((X,Y)), X).
beta_reduction(second((X,Y)), Y).
*/

% reification of `;`
judgement(type(union(A, B)), G) :- 
	judgement(type(A), G),
	judgement(type(B), G).

judgement(left(X):union(A, B), G) :- 
	judgement(type(union(A, B)), G),
	judgement(X:A, G).

judgement(right(Y):union(A,B), G) :- 
	judgement(type(union(A,B)), G),
	judgement(Y:B, G).

/*
proof(or_elim1(P,variable(V),Left,Right),C,Assumptions) :- 
	proof(P,disjunction(X,Y),Assumptions),
	proof(Left,C,[assumption(variable(V),X)|Assumptions]),
	proof(Right,C,[assumption(variable(V),Y)|Assumptions]).
*/


% reification of `:-`
judgement(type(function(A, B)), G) :- 
	judgement(type(A), G),
	judgement(type(B), G).

judgement(lambda(x(V),Expr):function(A,B), G) :- 
	judgement(type(function(A,B)), G),
	judgement(Expr:B, [ x(V):A | G]).

judgement(apply(F,X):B,  G) :- 
	judgement(F:function(A,B), G),
	judgement(X:A, G).

/*
beta_reduction(apply(lambda(x(V),Expr),X), FX) :-
	substitute(X,x(V),Expr,FX).
*/
