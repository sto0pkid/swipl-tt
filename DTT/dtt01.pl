:- module(ptt,[judgement/2, substitute/4, beta_reduction/2]).
:- use_module(library(gensym)).

:- discontiguous beta_reduction/2.
:- discontiguous judgement/2.
/*
* TODO:
* * Should beta reduction be a judgement?
* * What's up with the congruence rule
* * Needs cuts on all the beta reduction rules because of the congruence rule; is this a proper formulation?
* * Termination proof with the congruence rule?
* * Synthesize these rules into a generalized type declaration system
* * Make bidirectional to do proof search?
*/

% substitute(In, Var, For, Out)
% substitute Var in In for For to get Out
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


% TYPE IN TYPE
judgement(type:type,_).


% EMPTY
judgement(empty:type,_).

judgement(explosion(F):C_F, G) :-
	judgement(F:empty, G),
	judgement(C:type, [x(V):empty|G]),
	substitute(C, x(V), F, C_F).





% UNIT
judgement(unit:type,_).

judgement(null:unit,_).

judgement(unit_elim(U, X):C_U, G) :-
	judgement(U:unit, G),
	judgement(C:type, [x(V):unit | G]),
	substitute(C, x(V), null, C_null),
	judgement(X:C_null, G),
	substitute(C_U, x(V), U, C_U).

beta_reduction(unit_elim(null, X), X) :- !.





% BOOL
judgement(bool:type,_).

judgement(true:bool,_).
judgement(false:bool,_).

judgement(if_then_else(B, X, Y):C_B, G) :-
	judgement(B:bool, G),
	judgement(C:type, [x(V):bool|G]),
	substitute(C, x(V), true, C_true),
	judgement(X:C_true, G),
	substitute(C, x(V), false, C_false),
	judgement(Y:C, G),
	substitute(C, x(V), B, C_B).


beta_reduction(if_then_else(true, X, _), X) :- !.
beta_reduction(if_then_else(false, _, Y), Y) :- !.




% PAIR TYPE
judgement(pair(A,B):type, G) :- 
	judgement(A:type, G),
	judgement(B:type, G).


judgement((X,Y):pair(A,B), G) :- 
	judgement(pair(A,B):type, G),
	judgement(X:A, G),
	judgement(Y:B, G).

judgement(first(P):A, G) :- 
	judgement(P:pair(A,_), G).

judgement(second(P):B, G) :- 
	judgement(P:pair(_,B), G).


beta_reduction(first((X,_)), X) :- !.
beta_reduction(second((_,Y)), Y) :- !.


% SIGMA TYPE
judgement(sigma(A,bind(x(V),B)):type, G) :- 
	judgement(A:type, G),
	judgement(B:type, [x(V):A | G]).


judgement((X,Y):sigma(A,bind(x(V),B)), G) :- 
	judgement(sigma(A,bind(x(V),B)):type, G),
	judgement(X:A, G),
	substitute(B, x(V), X, B_Sub),
	judgement(Y:B_Sub, G).

judgement(proj1(P):A, G) :- 
	judgement(P:sigma(A,_), G).

judgement(proj2(P):B_Sub, G) :-
	judgement(P:sigma(_,bind(x(V),B)), G),
	substitute(B,x(V),proj1(P),B_Sub).


beta_reduction(proj1((X,_)), X) :- !.
beta_reduction(proj2((_,Y)), Y) :- !.




% reification of `;`
judgement(union(A, B):type, G) :- 
	judgement(A:type, G),
	judgement(B:type, G).

judgement(left(X):union(A, B), G) :- 
	judgement(union(A, B):type, G),
	judgement(X:A, G).

judgement(right(Y):union(A,B), G) :- 
	judgement(union(A,B):type, G),
	judgement(Y:B, G).


judgement(case(P, bind(x(V),L), bind(x(W),R)):C, G) :- 
	proof(P, union(A,B), G),
	proof(L, C, [x(V):A | G]),
	proof(R, C, [x(W):B | G]).

beta_reduction(case(left(X), bind(x(V),L), _), LSub) :-
	!,
	substitute(L, x(V), X, LSub).
beta_reduction(case(right(Y), _, bind(x(V),R)), RSub) :-
	!,
	substitute(R, x(V), Y, RSub).




% reification of `:-`
judgement(function(A, bind(x(V),B)):type, G) :- 
	judgement(A:type, G),
	judgement(B:type, [x(V):A|G]).

judgement(lambda(bind(x(V),Expr)):function(A,bind(x(W),B)), G) :-
	judgement(function(A,B):type, G),
	substitute(B, x(W), x(V), B_Sub),
	judgement(Expr:B, [ x(V):A | G]).

judgement(apply(F,X):B_Sub, G) :- 
	judgement(F:function(A,bind(x(V),B)), G),
	judgement(X:A, G),
	substitute(B,x(V),X,B_Sub).


beta_reduction(apply(lambda(bind(x(V), Expr)), X), FX) :-
	!,
	substitute(Expr, x(V), X, FX).



% congruence rule:
beta_reduction(T, T_Out) :-
	T =.. [F | Args],
	maplist(beta_reduction, Args, Args_Reduced),
	T_Reduced =.. [F | Args_Reduced],
	(
		Args \= Args_Reduced
	->	beta_reduction(T_Reduced,T_Out)
	;	T_Out = T_Reduced
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

