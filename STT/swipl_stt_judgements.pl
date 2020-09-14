:- module(swipl_stt,[judgement/2, substitute/4, beta_reduction/2]).
:- use_module(library(gensym)).

:- discontiguous beta_reduction/2.
:- discontiguous judgement/2.
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
substitute(x(X), x(X), For,  For) :- !.
substitute(x(X), x(Y),   _, x(X)) :- !, X \= Y.

substitute([],_,_,[]) :- !.
substitute([X | Rest], x(V), For, [SubX | SubRest]) :-
	!,
	substitute(X, x(V), For, SubX),
	substitute(Rest, x(V), For, SubRest).

substitute(bind(x(X),Expr),x(Y), For, bind(x(Fresh),ExprSub)) :-
	!,
	gensym(x,Fresh),
	substitute(Expr, x(X), x(Fresh), ExprFresh),
	substitute(ExprFresh, x(Y), For, ExprSub).

substitute(Term, x(X), For, TermSub) :-
	Term =.. [F | Args],
	substitute(Args, x(X), For, ArgsSub),
	TermSub =.. [F | ArgsSub].




% hypothesis rule
judgement(x(V):X, [x(V):X|_]).
judgement(x(V):X, [x(W):_|G]) :- V \= W, judgement(x(V):X,G).



% reification of `false`
judgement(type(empty),_).

judgement(explosion(F):_, G) :-
	judgement(F:empty, G).





% reification of `true`
judgement(type(unit),_).

judgement(null:unit,_).

judgement(unit_elim(U, X):C, G) :-
	judgement(U:unit, G),
	judgement(X:C, G).

beta_reduction(unit_elim(null, X), X).





% bool
judgement(type(bool),_).

judgement(true:bool,_).
judgement(false:bool,_).

judgement(if_then_else(B, X, Y):C, G) :-
	judgement(B:bool, G),
	judgement(X:C, G),
	judgement(Y:C, G).


beta_reduction(if_then_else(true, X, _), X).
beta_reduction(if_then_else(false, _, Y), Y).





% reification of `,`
judgement(type(pair(A,B)), G) :- 
	judgement(type(A), G),
	judgement(type(B), G).


judgement((X,Y):pair(A,B), G) :- 
	judgement(type(pair(A,B)), G),
	judgement(X:A, G),
	judgement(Y:B, G).

judgement(first(P):A, G) :- 
	judgement(P:pair(A,_), G).

judgement(second(P):B, G) :- 
	judgement(P:pair(_,B), G).


beta_reduction(first((X,_)), X).
beta_reduction(second((_,Y)), Y).





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


judgement(case(P, bind(x(V),L), bind(x(W),R)):C, G) :- 
	proof(P, union(A,B), G),
	proof(L, C, [x(V):A | G]),
	proof(R, C, [x(W):B | G]).

beta_reduction(case(left(X), bind(x(V),L), _), LSub) :-
	substitute(L, x(V), X, LSub).
beta_reduction(case(right(Y), _, bind(x(V),R)), RSub) :-
	substitute(R, x(V), Y, RSub).




% reification of `:-`
judgement(type(function(A, B)), G) :- 
	judgement(type(A), G),
	judgement(type(B), G).

judgement(lambda(bind(x(V),Expr)):function(A,B), G) :- 
	judgement(type(function(A,B)), G),
	judgement(Expr:B, [ x(V):A | G]).

judgement(apply(F,X):B,  G) :- 
	judgement(F:function(A,B), G),
	judgement(X:A, G).


beta_reduction(apply(lambda(bind(x(V), Expr)), X), FX) :-
	!,
	substitute(Expr, x(V), X, FX).

beta_reduction(apply(apply(F, SubArg), Arg), FArg) :-
	beta_reduction(apply(F, SubArg), FSubArg),
	(
		FSubArg = lambda(_)
	->	beta_reduction(apply(FSubArg, Arg), FArg)
	;	FArg = apply(FSubArg, Arg)
	).

example(X) :-
	beta_reduction(
		apply(
			apply(
				lambda(bind(x(1), lambda(bind(x(2), x(1))))),
				"hi"
			),
			"bye"
		),
		X
	).

