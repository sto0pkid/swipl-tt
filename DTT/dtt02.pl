:- module(swipl_stt,[judgement/2, substitute/4, example/1, alpha_eq/2]).
:- use_module(library(gensym)).

:- discontiguous judgement/2.
:- op(999, xfx, user:'~>').	% one step normalization
:- op(999, xfx, user:'~>>').	% full normalization




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






% ALPHA EQUALITY
% terms are alpha-equal if they're identical up to variable renaming
% in De Bruijn index notation, alpha-equal terms are syntactically identical
alpha_eq(x(X), x(X)) :- !.
alpha_eq(bind(x(X),A), bind(x(Y),B)) :-
	!,
	substitute(B, x(Y), x(X), B_Sub),
	alpha_eq(A, B_Sub).
alpha_eq(T1, T2) :-
	T1 =.. [F1 | Args1],
	T2 =.. [F2 | Args2],
	F1 = F2,
	maplist(alpha_eq, Args1, Args2).






% HYPOTHESIS RULE
judgement(x(V):X, [x(V):X|_]).
judgement(x(V):X, [x(W):_|G]) :- V \= W, judgement(x(V):X,G).






% EMPTY / FALSE type  ; nullary sum
% formation
judgement(empty:type,_).

% introduction
% -- no introduction rules!

% elimination
judgement(explosion(F):C_Sub, G) :-
	judgement(F:empty, G),
	judgement(C:type, [x(V):empty, G]),
	substitute(C, x(V), F, C_Sub).

% beta?
% -- no beta rules because no introduction rules

% eta?
judgement(explosion(F) ~> F, G) :-
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
judgement(unit:type,_).

% introduction
judgement(null:unit,_).

% elimination
judgement(unit_elim(U, X):C_U, G) :-
	judgement(U:unit, G),
	judgement(C:type, [x(V):unit | G]),
	substitute(C, x(V), null, C_null),
	judgement(X:C_null, G),
	substitute(C, x(V), U, C_U).

% beta
judgement(unit_elim(null, X) ~> X, _).

% eta
judgement(unit_elim(U,null) ~> U, G) :-
	judgement(U:unit, G).








% BOOL / 2-member type
% formation
judgement(bool:type,_).

% introduction
judgement(true:bool,_).
judgement(false:bool,_).

% elimination
judgement(if_then_else(B, X, Y):C_B, G) :-
	judgement(B:bool, G),
	judgement(C:type, [x(V):bool | G]),
	substitute(C, x(V), true, C_true),
	judgement(X:C_true, G),
	substitute(C, x(V), false, C_false),
	judgement(Y:C_false, G),
	substitute(C, x(V), B, C_B).

% beta
judgement(if_then_else(true, X, _) ~> X, _).
judgement(if_then_else(false, _, Y) ~> Y, _).

% eta
judgement(if_then_else(B, true, false) ~> B, G) :-
	judgement(B:bool, G).

/*
* Notes:
* Can construct any finite enumeration type in similar fashion, but we can't construct
* the actual type *family* of finite enumerations, i.e. `Fin`, due to lack of dependent types.
*
*/






% PAIR / PRODUCT / CONJUNCTION / "AND" type
% formation
judgement(pair(A,B):type, G) :- 
	judgement(A:type, G),
	judgement(B:type, G).


% introduction
judgement((X,Y):pair(A,B), G) :- 
	judgement(pair(A,B):type, G),
	judgement(X:A, G),
	judgement(Y:B, G).

% elimination
judgement(split(P, bind(x(V),bind(x(W),Expr))):C_P, G) :-
	judgement(P:pair(A,B), G),
	judgement(C:type, [x(X):pair(A,B) | G]),
	substitute(C, x(X), (x(V), x(W)), C_AB),
	judgement(Expr:C_AB, [x(V):A, x(W):B | G]),
	substitute(C, x(X), P, C_P).

% beta
judgement(split((A,B), bind(x(V),bind(x(W),Expr))) ~> Expr_AB) :-
	substitute(Expr, x(V), A, Expr_A),
	substitute(Expr_A, x(W), B, Expr_AB).

% eta
judgement((funsplit(P,bind(x(V),bind(x(W),x(V)))), funsplit(P,bind(x(V),bind(x(W),x(W))))) ~> P, G) :-
	judgement(P:pair(_,_), G).






% DISJOINT UNION / DISJUNCTION / "OR" TYPE

% formation
judgement(union(A, B):type, G) :- 
	judgement(type(A), G),
	judgement(type(B), G).

% introduction
judgement(left(X):union(A, B), G) :- 
	judgement(union(A, B):type, G),
	judgement(X:A, G).

judgement(right(Y):union(A,B), G) :- 
	judgement(union(A,B):type, G),
	judgement(Y:B, G).

% elimination
judgement(case(P, bind(x(V),L), bind(x(W),R)):C_P, G) :- 
	judgement(P:union(A,B), G),
	judgement(C:type, [x(X):union(A,B) | G]),
	substitute(C, x(X), left(x(V)), C_left),
	judgement(L:C_left, [x(V):A | G]),
	substitute(C, x(X), right(x(V)), C_right),
	judgement(R:C_right, [x(W):B | G]),
	substitute(C, x(X), P, C_P).

% beta
judgement(case(left(X), bind(x(V),L), _) ~> LSub, _) :-
	substitute(L, x(V), X, LSub).
judgement(case(right(Y), _, bind(x(V),R)) ~> RSub, _) :-
	substitute(R, x(V), Y, RSub).


% eta
judgement(case(C, bind(x(V),left(x(V))), bind(x(W),right(x(W)))) ~> C, G) :-
	judgement(C:union(_,_), G).






% IMPLICATION / FUNCTION TYPE
% formation
judgement(function(A, B):type, G) :- 
	judgement(A:type, G),
	judgement(B:type, G).

% introduction
judgement(lambda(bind(x(V),Expr)):function(A,B), G) :- 
	judgement(function(A,B):type, G),
	judgement(Expr:B, [ x(V):A | G]).

% elimination
judgement(apply(F,X):B,  G) :- 
	judgement(F:function(A,B), G),
	judgement(X:A, G).


% beta
judgement(apply(lambda(bind(x(V), Expr)), X) ~> FX, _) :-
	substitute(Expr, x(V), X, FX).

% eta
judgement(lambda(bind(x(V),apply(F,x(V)))) ~> F, G) :-
	judgement(F:function(_,_),G).






% FORALL / PI / DEPENDENT PRODUCT / DEPENDENT FUNCTION type
% formation
judgement(forall(A, bind(x(V),B)):type, G) :-
	judgement(A:type, G),
	judgement(B:type, [x(V):A | G]).

% introduction
judgement(lambda(bind(x(V),Expr)):forall(A,bind(x(W),B)), G) :-
	judgement(forall(A,bind(x(W),B)):type, G),
	substitute(B, x(W), x(V), B_Sub),
	judgement(Expr:B_Sub, [x(V):A | G]).

% elimination
judgement(apply(F,X):B_X, G) :-
	judgement(F:forall(A,bind(x(W),B)), G),
	judgement(X:A, G),
	substitute(B, x(W), X, B_X).

% beta
judgement(apply(lambda(bind(x(V),Expr)), X) ~> FX, _) :-
	substitute(Expr, x(V), X, FX).

% eta
judgement(lambda(bind(x(V),apply(F,x(V)))) ~> F, G) :-
	judgement(F:forall(_,_),G).






% EXISTS / SIGMA / DEPENDENT SUM / DEPENDENT PAIR type
% formation
judgement(exists(A,bind(x(V),B)):type, G) :-
	judgement(A:type, G),
	judgement(B:type, [x(V):A | G]).

% introduction
judgement((X,Y):exists(A,bind(x(V),B)), G) :-
	judgement(exists(A,bind(x(V),B)):type, G),
	judgement(X:A, G),
	substitute(B, x(V), X, B_X),
	judgement(Y:B_X, G).

% elimination
judgement(proj1(P):A, G) :-
	judgement(P:exists(A,_), G).
judgement(proj2(P):B_Sub, G) :-
	judgement(P:exists(_,bind(x(V),B)), G),
	substitute(B, x(V), proj1(P), B_Sub).
% beta
judgement(proj1((X, _)) ~> X, _).
judgement(proj2((_, Y)) ~> Y, _).

% eta
judgement((proj1(P), proj2(P)) ~> P, G) :-
	judgement(P:exists(_,_), G).






% NATURAL NUMBERS
% formation
judgement(nat:type, _).

% introduction
judgement(0:nat, _).
judgement(suc(N):nat, G) :-
	judgement(N:nat, G).

% elimination
judgement(nat_rec(N,Z,bind(x(V),bind(x(Ind),S))):C, G) :-
	judgement(N:nat, G),
	judgement(C:type, [x(X):nat | G]),
	substitute(C, x(X), 0, C_zero),
	judgement(Z:C_zero, G),
	substitute(C, x(X), x(V), C_n),
	substitute(C, x(X), suc(x(V)), C_sn),
	judgement(S:C_sn, [x(V):nat, x(Ind):C_n|G]).

% beta
judgement(nat_rec(0, Z, _) ~> Z, _).
judgement(nat_rec(suc(N), Z, bind(x(V), bind(x(Ind), S))) ~> S_Sub, _) :-
	substitute(S, x(V), N, S_V),
	substitute(S_V, x(Ind), nat_rec(N, Z, bind(x(V), bind(x(Ind), S))), S_Sub).

% eta
judgement(nat_rec(N, 0, bind(x(V),bind(_,suc(x(V))))) ~> N, G) :-
	judgement(N:nat, G).






% LIST TYPE
% formation
judgement(list(A):type, G) :-
	judgement(A:type, G).


% introduction
judgement([]:list(A), G) :-
	judgement(list(A):type, G).

judgement([X | Xs]:list(A), G) :-
	judgement(list(A):type, G),
	judgement(X:A, G),
	judgement(Xs:list(A), G).


% elimination
judgement(list_rec(L, Nil, bind(x(V),bind(x(W),bind(x(Ind),Cons)))):C, G) :-
	judgement(L:list(A), G),
	judgement(C:type, [x(X):list(A) | G]),
	substitute(C, x(X), [], C_nil),
	judgement(Nil:C_nil, G),
	substitute(C, x(X), [x(V) | x(W)], C_cons),
	substitute(C, x(X), x(W), C_rest),
	judgement(Cons:C_cons, [x(V):A, x(W):list(A), x(Ind):C_rest | G]).


% beta
judgement(list_rec([], Nil, _) ~> Nil, _).
judgement(list_rec([X|Xs], Nil, bind(x(V),bind(x(W),bind(x(Ind),Cons)))) ~> Cons_Sub, _) :-
	substitute(Cons, x(V), X, Cons_Sub1),
	substitute(Cons_Sub1, x(W), Xs, Cons_Sub2),
	substitute(Cons_Sub2, x(Ind), list_rec(Xs, Nil, bind(x(V),bind(x(W),bind(x(Ind),Cons)))), Cons_Sub).
% eta
judgement(list_rec(L, [], bind(x(V),bind(x(W),bind(_,[x(V)|x(W)])))) ~> L, G) :-
	judgement(L:list(_), G).



/*
* Notes:
* Can make a Vector type for any N, just can't construct the type *family* itself due to
* lack of dependent types.
*
*/





% CONGRUENCE RULE
judgement(T1 ~> T2, G) :-
	T1 =.. [F | Args_1],
	cong(Args_1, Args_2, G),
	T2 =.. [F | Args_2].

cong([Arg_1 | Args], [Arg_2 | Args], G) :-
	judgement(Arg_1 ~> Arg_2, G).
cong([Arg | Args_1], [Arg | Args_2], G) :-
	\+judgement(Arg ~> _, G),
	cong(Args_1, Args_2, G).


% NORMALIZATION
judgement(T1 ~>> NF, G) :-
	judgement(T1 ~> T2, G),
	judgement(T2 ~>> NF, G).

judgement(NF ~>> NF, G) :-
	\+judgement(NF ~> _, G).



% EQUALITY
judgement(T1 = T2, G) :-
	judgement(T1 ~>> NF1, G),
	judgement(T2 ~>> NF2, G),
	alpha_eq(NF1, NF2).
/*
* Notes:
* The rules extend the one-step beta/eta rules to give an actual evaluation/reduction strategy.
* Different formulations of these rules will give variations on the evaluation strategy, ex.. we
* can get call-by-value, call-by-name, etc...
*
* I haven't thought deeply on this yet.
*
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

example(X) :-
	judgement(
		apply(
			apply(
				lambda(bind(x(1), lambda(bind(x(2), x(1))))),
				"hi"
			),
			"bye"
		) ~>> X,
		[]
	).
