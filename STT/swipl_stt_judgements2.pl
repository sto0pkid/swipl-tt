:- module(swipl_stt,[judgement/2, substitute/4, beta_reduction/2]).
:- use_module(library(gensym)).


% CAPTURE-AVOIDING SUBSTITUTION
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




% HYPOTHESIS RULE
judgement(x(V):X, [x(V):X|_]).
judgement(x(V):X, [x(W):_|G]) :- V \= W, judgement(x(V):X,G).






% EMPTY / FALSE type  ; nullary sum
% formation
judgement(type(empty),_).

% introduction
% -- no introduction rules!

% elimination
judgement(explosion(F):C, G) :-
	judgement(F:empty, G),
	judgement(type(C), G).

% beta?
% -- no beta rules because no introduction rules

% eta?
judgement(F = explosion(F), G) :-
	judgement(F:empty, G).


/*
* Notes:
* They use "abort_C" instead of "explosion" on ncatlab: https://ncatlab.org/nlab/show/empty+type
*  but, why should the label for the eliminator vary depending on the type that it's eliminating into?
*  We don't do this for any of the other types ex.. `unit_elim`, `if_then_else`, `case`, `apply`, ...
*
* It seems to be implying that we need a different abort_C for every type C to make sure that the object
* abort_C(F) / explosion_C(F) actually has type C, and since there are different types we can't have the
* same abort_C on the same object F for every C... but... if we have a proof of False then the system is
* inconsistent and all the types should reduce to each other anyway, i.e. explosion(F) has every type in
* any context where F:empty
*
* They also have a different eta rule, i.e. abort_C(F):C <--eta--> c:C for any c:C;
* this should be logically equivalent to my F <--eta--> explosion(F) though, by similar logic as above?
*
*
* Trying to do proof-search by running bidirectionally: it immediately loops on the eliminator here
* (funny enough that means its search strategy is to try to prove everything via proving the logic
*  inconsistent...)
*
*/







% UNIT / TRUE / TOP / 1-member type ; nullary product)
% formation
judgement(type(unit),_).

% introduction
judgement(null:unit,_).

% elimination
judgement(unit_elim(U, X):C, G) :-
	judgement(U:unit, G),
	judgement(type(C), G),
	judgement(X:C, G).

% beta
judgement(unit_elim(null, X) = X, _).

% eta
judgement(U = unit_elim(U,null), G) :-
	judgement(U:unit, G).







% BOOL / 2-member type
% formation
judgement(type(bool),_).

% introduction
judgement(true:bool,_).
judgement(false:bool,_).

% elimination
judgement(if_then_else(B, X, Y):C, G) :-
	judgement(B:bool, G),
	judgement(type(C), G),
	judgement(X:C, G),
	judgement(Y:C, G).

% beta
judgement(if_then_else(true, X, _) = X).
judgement(if_then_else(false, _, Y) = Y).

% eta
judgement(B = if_then_else(B, true, false), G) :-
	judgement(B:bool, G).

/*
* Notes:
* Can construct any finite enumeration type in similar fashion, but we can't construct
* the actual type *family* of finite enumerations, i.e. `Fin`, due to lack of dependent types.
*
*/






% PAIR / PRODUCT / CONJUNCTION / "AND" type
% formation
judgement(type(pair(A,B)), G) :- 
	judgement(type(A), G),
	judgement(type(B), G).


% introduction
judgement((X,Y):pair(A,B), G) :- 
	judgement(type(pair(A,B)), G),
	judgement(X:A, G),
	judgement(Y:B, G).

% elimination
judgement(first(P):A, G) :- 
	judgement(P:pair(A,_), G).

judgement(second(P):B, G) :- 
	judgement(P:pair(_,B), G).

% beta
judgement(first((X,_)) = X, _).
judgement(second((_,Y)) = Y, _).

% eta
judgement(P = (first(P), second(P)), G) :-
	judgement(P:pair(_,_), G).






% DISJOINT UNION / DISJUNCTION / "OR" TYPE

% formation
judgement(type(union(A, B)), G) :- 
	judgement(type(A), G),
	judgement(type(B), G).

% introduction
judgement(left(X):union(A, B), G) :- 
	judgement(type(union(A, B)), G),
	judgement(X:A, G).

judgement(right(Y):union(A,B), G) :- 
	judgement(type(union(A,B)), G),
	judgement(Y:B, G).

% elimination
judgement(case(P, bind(x(V),L), bind(x(W),R)):C, G) :- 
	judgement(P:union(A,B), G),
	judgement(type(C), G),
	judgement(L:C, [x(V):A | G]),
	judgement(R:C, [x(W):B | G]).

% beta
judgement(case(left(X), bind(x(V),L), _) = LSub, _) :-
	substitute(L, x(V), X, LSub).
judgement(case(right(Y), _, bind(x(V),R)) = RSub, _) :-
	substitute(R, x(V), Y, RSub).


% eta
judgement(C = case(C, bind(x(V),left(x(V))), bind(x(W),right(x(W)))), G) :-
	judgement(C:union(_,_), G).





% IMPLICATION / FUNCTION TYPE
% formation
judgement(type(function(A, B)), G) :- 
	judgement(type(A), G),
	judgement(type(B), G).

% introduction
judgement(lambda(bind(x(V),Expr)):function(A,B), G) :- 
	judgement(type(function(A,B)), G),
	judgement(Expr:B, [ x(V):A | G]).

% elimination
judgement(apply(F,X):B,  G) :- 
	judgement(F:function(A,B), G),
	judgement(X:A, G).


% beta
judgement(apply(lambda(bind(x(V), Expr)), X) = FX, _) :-
	substitute(Expr, x(V), X, FX).

% eta
judgement(F = lambda(bind(x(V),apply(F,x(V)))), G) :-
	judgement(F:function(_,_),G).







% NATURAL NUMBERS
% formation
judgement(type(nat), _).

% introduction
judgement(0:nat, _).
judgement(suc(N):nat, G) :-
	judgement(N:nat, G).

% elimination
judgement(nat_rec(N,Z,bind(x(V),S)):C, G) :-
	judgement(N:nat, G),
	judgement(type(C), G),
	judgement(Z:C, G),
	judgement(S:C, [x(V):nat|G]).

% beta
judgement(nat_rec(0, Z, S) = Z, _).
judgement(nat_rec(suc(N), Z, bind(x(V),S)) = S_Sub, _) :-
	substitute(S, x(V), N, S_Sub).

% eta
judgement(N = nat_rec(N, 0, bind(x(V),suc(x(V)))), G) :-
	judgement(N:nat, G).






% LIST TYPE
% formation
judgement(type(list(A)), G) :-
	judgement(type(A), G).

% introduction
judgement([]:list(A), G) :-
	judgement(type(list(A)), G).
judgement([X | Xs]:list(A), G) :-
	judgement(type(list(A)), G),
	judgement(X:A, G),
	judgement(Xs:list(A), G).

% elimination
judgement(list_rec(L, Last, bind(x(V),bind(x(W),F))):C, G) :-
	judgement(type(C), G),
	judgement(L:list(_), G),
	judgement(Last:C, G),
	judgement(F:C, [x(V):list(A)|G]).


% beta
judgement(list_rec([], Nil, _) = Nil, _).
judgement(list_rec([X|Xs], _, bind(x(V),bind(x(W),Cons))) = Cons_Sub, _) :-
	substitute(Cons, x(V), X, Cons_Sub1),
	substitute(Cons_Sub1, x(W), Xs, Cons_Sub).
% eta
judgement(L = list_rec(L, [], bind(x(V),bind(x(W),[x(V)|x(W)]))), G) :-
	judgement(L:list(_), G).


/*
* Notes:
* Can make a Vector type for any N, just can't construct the type *family* itself due to
* lack of dependent types.
*
*/





% CONGRUENCE RULE
judgement(T1 = T2, G) :-
	T =.. [F | Args],
	maplist([X,Y]>>judgement(X = Y, G), Args, Args_Reduced),
	T_Reduced =.. [F | Args_Reduced],
	(
		Args \= Args_Reduced
	->	judgement(T_Reduced = T_Out, G)
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

