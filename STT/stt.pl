:- module(swipl_stt,[substitute/4, '#'/2]).
:- use_module(library(gensym)).
:- op(999, xfx, user:'#').
:- op(998, xfx, user:'~>').	% one step normalization
:- op(998, xfx, user:'~>>').	% full normalization
:- op(998, xfx, user:'@=').




% CAPTURE-AVOIDING SUBSTITUTION
substitute(X, Y, For,  X_Sub) :-
	var(X),
	!,
	(
		X == Y
	->	X_Sub = For
	;	X_Sub = X
	).
	
substitute([], _, _, []) :- !.
substitute([Term | Rest], X, For, [Term_Sub | Rest_Sub]) :-
	!,
	substitute(Term, X, For, Term_Sub),
	substitute(Rest, X, For, Rest_Sub).
	
substitute(bind(X,Expr), Y, For, bind(Fresh,Expr_Sub)) :-
	!,
	substitute(Expr, X, Fresh, Expr_Fresh),
	substitute(Expr_Fresh, Y, For, Expr_Sub).

substitute(Term, X, For, Term_Sub) :-
	Term =.. [F | Args],
	substitute(Args, X, For, Args_Sub),
	Term_Sub =.. [F | Args_Sub].


% ALPHA EQUALITY
% terms are alpha-equal if they're identical up to variable renaming
% in De Bruijn index notation, alpha-equal terms are syntactically identical
x(X) @= x(X) :- !.
bind(x(X),A) @= bind(x(Y),B) :-
	!,
	substitute(B, x(Y), x(X), B_Sub),
	A @= B_Sub.

T1 @= T2 :-
	T1 =.. [F1 | Args1],
	T2 =.. [F2 | Args2],
	F1 = F2,
	maplist(@=, Args1, Args2).




% HYPOTHESIS RULE
[X:T|_] # X:T.
[X:_|G] # Y:T :- X \== Y, G # Y:T.



% EMPTY / FALSE type  ; nullary sum
% formation
_ # type(empty).

% introduction
% -- no introduction rules!

% elimination
G # explosion(F):C :- 
	G # F:empty,
	G # type(C).

% beta?
% -- no beta rules because no introduction rules

% eta?
G # explosion(F) ~> F :-
	G # F:empty.


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







% UNIT / TRUE / TOP / 1-member type ; nullary product
% formation
_ # type(unit).

% introduction
_ # null:unit.

% elimination
G # unit_elim(U, X):C :-
	G # U:unit,
	G # type(C),
	G # X:C.

% beta
_ # unit_elim(null, X) ~> X.

% eta
G # unit_elim(U,null) ~> U :-
	G # U:unit.







% BOOL / 2-member type
% formation
_ # type(bool).

% introduction
_ # true:bool.
_ # false:bool.

% elimination
G # if_then_else(B, X, Y):C :-
	G # B:bool,
	G # type(C),
	G # X:C,
	G # Y:C.

% beta
_ # if_then_else(true, X, _) ~> X.
_ # if_then_else(false, _, Y) ~> Y.

% eta
G # if_then_else(B, true, false) ~> B :-
	G # B:bool.

/*
* Notes:
* Can construct any finite enumeration type in similar fashion, but we can't construct
* the actual type *family* of finite enumerations, i.e. `Fin`, due to lack of dependent types.
*
*/





% PAIR / PRODUCT / CONJUNCTION / "AND" type
% formation
G # type(pair(A,B)) :- 
	G # type(A),
	G # type(B).


% introduction
G # (X,Y):pair(A,B) :- 
	G # type(pair(A,B)),
	G # X:A,
	G # Y:B.

% elimination
G # first(P):A :- 
	G # P:pair(A,_).

G # second(P):B :- 
	G # P:pair(_,B).

% beta
_ # first((X,_)) ~> X.
_ # second((_,Y)) ~> Y.

% eta
G # (first(P), second(P)) ~> P :-
	G # P:pair(_,_).







% DISJOINT UNION / DISJUNCTION / "OR" TYPE

% formation
G # type(union(A, B)) :- 
	G # type(A),
	G # type(B).

% introduction
G # left(X):union(A, B) :- 
	G # type(union(A, B)),
	G # X:A.

G # right(Y):union(A,B) :- 
	G # type(union(A,B)),
	G # Y:B.

% elimination
G # case(P, bind(x(V),L), bind(x(W),R)):C :- 
	G # P:union(A,B),
	G # type(C),
	[x(V):A | G] # L:C,
	[x(W):B | G] # R:C.

% beta
_ # case(left(X), bind(x(V),L), _) ~> LSub :-
	substitute(L, x(V), X, LSub).

_ # case(right(Y), _, bind(x(V),R)) ~> RSub :-
	substitute(R, x(V), Y, RSub).


% eta
G # case(C, bind(x(V),left(x(V))), bind(x(W),right(x(W)))) ~> C :-
	G # C:union(_,_).






% IMPLICATION / FUNCTION TYPE
% formation
G # type(function(A, B)) :- 
	G # type(A),
	G # type(B).

% introduction
G # lambda(bind(x(V),Expr)):function(A,B) :- 
	G # type(function(A,B)),
	[ x(V):A | G] # Expr:B.

% elimination
G # apply(F,X):B :- 
	G # F:function(A,B),
	G # X:A.


% beta
_ # apply(lambda(bind(x(V), Expr)), X) ~> FX :-
	substitute(Expr, x(V), X, FX).

% eta
G # lambda(bind(x(V),apply(F,x(V)))) ~> F :-
	G # F:function(_,_).







% NATURAL NUMBERS
% formation
_ # type(nat).

% introduction
_ # 0:nat.
G # suc(N):nat :-
	G # N:nat.

% elimination
G # nat_rec(N,Z,bind(x(V),S)):C :-
	G # N:nat,
	G # type(C),
	G # Z:C,
	[x(V):nat|G] # S:C.

% beta
_ # nat_rec(0, Z, _) ~> Z.
_ # nat_rec(suc(N), _, bind(x(V),S)) ~> S_Sub :-
	substitute(S, x(V), N, S_Sub).

% eta
G # nat_rec(N, 0, bind(x(V),suc(x(V)))) ~> N :-
	G # N:nat.




% LIST TYPE
% formation
G # type(list(A)) :-
	G # type(A).

% introduction
G # []:list(A) :-
	G # type(list(A)).

G # [X | Xs]:list(A) :-
	G # type(list(A)),
	G # X:A,
	G # Xs:list(A).

% elimination
G # list_rec(L, Last, bind(x(V),bind(x(W),F))):C :-
	G # type(C),
	G # L:list(_),
	G # Last:C,
	[x(V):A, x(W):list(A)|G] # F:C.


% beta
_ # list_rec([], Nil, _) ~> Nil.
_ # list_rec([X|Xs], _, bind(x(V),bind(x(W),Cons))) ~> Cons_Sub :-
	substitute(Cons, x(V), X, Cons_Sub1),
	substitute(Cons_Sub1, x(W), Xs, Cons_Sub).
% eta
G # list_rec(L, [], bind(x(V),bind(x(W),[x(V)|x(W)]))) ~> L :-
	G # L:list(_).


/*
* Notes:
* Can make a Vector type for any N, just can't construct the type *family* itself due to
* lack of dependent types.
*
*/

% CONGRUENCE RULE
G # T1 ~> T2 :-
	T1 =.. [F | Args_1],
	cong(Args_1, Args_2, G),
	T2 =.. [F | Args_2].


% NORMALIZATION
G # T1 ~>> NF :-
	G # T1 ~> T2,
	G # T2 ~>> NF.

G # NF ~>> NF :-
	\+(G # NF ~> _).



% EQUALITY
G # T1 = T2 :-
	G # T1 ~>> NF1,
	G # T2 ~>> NF2,
	NF1 @= NF2.


cong([Arg_1 | Args], [Arg_2 | Args], G) :-
	G # Arg_1 ~> Arg_2.
cong([Arg | Args_1], [Arg | Args_2], G) :-
	\+(G # Arg ~> _),
	cong(Args_1, Args_2, G).
