:- module(swipl_stt,[judgement/2, substitute/4, example/1, alpha_eq/2, get_rules/2]).
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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/*
% type declaration format:

data name(T1,...,Tk) :  Set where
	intro1 : ArgT11 -> ... -> ArgT1(N_1) -> name(T1, ..., Tk)
	...
	introM : ArgTM1 -> ... -> ArgT(N_M) -> name(T1, ..., Tk)

% examples:
data empty : Set where

data unit : Set where
	null : unit

data pair(A,B) : Set where
	conj : A -> B -> pair(A,B)

data union(A,B) : Set where
	left : A -> union(A,B)
	right : B -> union(A,B)

data nat : Set where
	0 : nat
	suc : nat -> nat

data list(A) : Set where
	[] : list(A)
	cons : A -> list(A) -> list(A)

% note: no function type here;
*/

/*


_{
	"name":Name,
	"params":[T1, ..., Tk],
	"intros":[
		Intro1_Name:[ArgT11, ..., ArgT1(N_1)],
		Intro2_Name:[ArgTM1, ..., ArgTM(N_M)]
	]
}

% examples:
_{
	"name":empty,
	"params":[],
	"intros":[]
}

_{
	"name":unit,
	"params":[],
	"intros":[
		null:[]
	]
}

_{
	"name":pair,
	"params":[A,B],
	"intros":[
		conj:[A,B]
	]
}

_{
	"name":union,
	"params":[A,B],
	"intros":[
		left:[A],
		right:[B]
	]
}

_{
	"name":nat,
	"params":[],
	"intros":[
		0:[],
		suc:[nat]
	]
}

_{
	"name":list,
	"params":[A],
	"intros":[
		[]:[],
		cons:[A,list(A)]
	]
}
*/

list_to_tuple([], true).
list_to_tuple([X | Xs], (X, Xs_Tuple)) :-
	list_to_tuple(Xs, Xs_Tuple).




% FORMATION RULES: definitional

% judgement(<name>(T1,...,Tk):type, G) :-
%	judgement(T1:type, G),
%	...
%	judgement(Tk:type, G).


get_formation_rules(Decl, Formation) :-
	Type =.. [Decl.name | Decl.params],
	maplist(
		{Context}/[
			
			Param,
			Body_Item
		]>>(
			Body_Item = judgement(Param:type, Context)
		),
		Decl.params,
		Body_List
	),
	list_to_tuple(Body_List, Body),
	Formation_Rule = (judgement(Type:type, Context) :- Body),
	Formation = [Formation_Rule].





% INTRODUCTION RULES: definitional
%
% judgement(<intro1>(arg11,...,arg1(N_1)):<name>(<params>), G) :-
% 	judgement(<name>(<params>):type, G),
%	judgement(arg11:ArgT11, G),
%	...
%	judgement(arg1(N_1):ArgT1(N_1), G).
% ...
% judgement(<introM>(argM1,...,argM(N_M)):<name>(<params>), G) :-
% 	judgement(<name>(<params>):type, G),
%	judgement(argM1:ArgTM1, G),
%	...
%	judgement(argM(N_M):ArgTM(N_M), G).


get_introduction_rules(Decl, Introduction) :-
	maplist(
		{Context}/[Intro,Rule]>>(
			get_introduction_rule(Decl,Intro,Rule,Context)
		),
		Decl.intros,
		Introduction
	).

get_introduction_rule(Decl, IntroName:Arg_Types, Rule, Context) :-
	maplist(
		{Context}/[Arg_Type, Arg_Var, Body_Item]>>(
			Body_Item = judgement(Arg_Var:Arg_Type, Context)
		),
		Arg_Types,
		Arg_Vars,
		Arg_Items
	),

	Type =.. [Decl.name | Decl.params],
	Body_Items = [judgement(Type:type, Context) | Arg_Items],
	list_to_tuple(Body_Items, Body),
	Term =.. [IntroName | Arg_Vars],
	Rule = (judgement(Term:Type, Context) :- Body).





% ELIMINATION RULES: derived from introduction rules according to description for "positive types"
%
% judgement(<name>_elim(Obj, bind([x(X11), ... x(X1(N_1))],Case1), ... bind([x(XM1), ..., x(XM(N_M)],CaseM)):C, G) :-
%	judgement(Obj:<name>(<params>), G),
%	judgement(C:type, G),
%	judgement(Case1:C, [x(X11):ArgT11, ..., x(X1(N_1)):ArgT1(N_1) | G]),
%	...
%	judgement(CaseM:C, [x(XM1):ArgTM1, ..., x(XM(N_M)):ArgTM(N_M) | G]),


get_elimination_rules(Decl, Elimination) :-
	Type =.. [Decl.name | Decl.params],

	maplist(
		{Context, C}/[_:Arg_Types, Case_Item, Case_Binding]>>(
			maplist(
				[Arg_Type,Arg_Var,Assumption]>>(
					Arg_Var = x(_),
					Assumption = Arg_Var:Arg_Type
				),
				Arg_Types, Arg_Vars, Assumptions
			),
			append(Assumptions, Context, Full_Context),
			Case_Item = judgement(Case_Var:C, Full_Context),
			Case_Binding = bind(Arg_Vars, Case_Var)
		),
		Decl.intros,
		Case_Items,
		Case_Bindings
	),
	Body_Items = [
		judgement(Obj:Type, Context),
		judgement(C:type, Context) 
		| Case_Items
	],
	list_to_tuple(Body_Items, Body),
	Elim =.. [elim, Decl.name, Obj | Case_Bindings],
	Rule = (judgement(Elim:C, Context) :- Body),
	Elimination = [Rule].







% BETA REDUCTION RULES: derived from "local soundness" part of "logical harmony conditions"
%
% judgement(
% 	<name>_elim(
%		intro1(Arg11, ..., Arg1(N_1)),
%		bind([x(X11), ..., x(X1(N_1))], Case1),
%		...,
%		bind([x(XM1), ..., x(XM(N_M))], CaseM)
%	) ~> Case1_Sub,
%	_
% ) :-
%	substitute(Case1, Vars1, Args1, Case1_Sub).
%
% ...
%
% judgement(
%	<name>_elim(
%		introM(ArgM1, ..., ArgM(N_M)),
%		bind([x(X11), ..., x(X1(N_1))], Case1),
%		...,
%		bind([x(XM1), ..., x(XM(N_M))], CaseM)
%	) ~> CaseM_Sub,
%	_
% ) :-
%	substitute(CaseM, VarsM, ArgsM, CaseM_Sub).


get_beta_rules(_Decl, Beta) :- 
	Beta = [].





% ETA REDUCTION RULES: derived from "local completeness" part of "logical harmony" conditions
%
% judgement(
%	<name>_elim(
%		Obj,
%		bind([x(X11), ..., x(X1(N_1))], intro1(x(X11), ..., x(X1(N_1)))),
%		...,
%		bind([x(XM1), ..., x(XM(N_M))], introM(x(XM1), ..., x(XM(N_M))))
%	) ~> Obj,
%	G
% ) :-
%	judgement(Obj:<name>, G).


get_eta_rules(_Decl, Eta) :- 
	Eta = [].





get_rules(Decl, Rules) :-
	get_formation_rules(Decl, Formation),
	get_introduction_rules(Decl, Introduction),
	get_elimination_rules(Decl, Elimination),
	get_beta_rules(Decl, Beta),
	get_eta_rules(Decl, Eta),
	Rules = _{
		formation:Formation,
		introduction:Introduction,
		elimination:Elimination,
		beta:Beta,
		eta:Eta
	}.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


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
judgement(type(unit),_).

% introduction
judgement(null:unit,_).

% elimination
judgement(unit_elim(U, X):C, G) :-
	judgement(U:unit, G),
	judgement(type(C), G),
	judgement(X:C, G).

% beta
judgement(unit_elim(null, X) ~> X, _).

% eta
judgement(unit_elim(U,null) ~> U, G) :-
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
judgement(type(pair(A,B)), G) :- 
	judgement(type(A), G),
	judgement(type(B), G).


% introduction
judgement((X,Y):pair(A,B), G) :- 
	judgement(type(pair(A,B)), G),
	judgement(X:A, G),
	judgement(Y:B, G).

% elimination
judgement(split(P, bind(x(V),bind(x(W),Expr))):C, G) :-
	judgement(P:pair(A,B), G),
	judgement(type(C), G),
	judgement(Expr:C, [x(V):A, x(W):B | G]).

% beta
judgement(split((A,B), bind(x(V),bind(x(W),Expr))) ~> Expr_AB) :-
	substitute(Expr, x(V), A, Expr_A),
	substitute(Expr_A, x(W), B, Expr_AB).

% eta
judgement((funsplit(P,bind(x(V),bind(x(W),x(V)))), funsplit(P,bind(x(V),bind(x(W),x(W))))) ~> P, G) :-
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
judgement(case(left(X), bind(x(V),L), _) ~> LSub, _) :-
	substitute(L, x(V), X, LSub).
judgement(case(right(Y), _, bind(x(V),R)) ~> RSub, _) :-
	substitute(R, x(V), Y, RSub).


% eta
judgement(case(C, bind(x(V),left(x(V))), bind(x(W),right(x(W)))) ~> C, G) :-
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
judgement(apply(lambda(bind(x(V), Expr)), X) ~> FX, _) :-
	substitute(Expr, x(V), X, FX).

% eta
judgement(lambda(bind(x(V),apply(F,x(V)))) ~> F, G) :-
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
judgement(nat_rec(0, Z, _) ~> Z, _).
judgement(nat_rec(suc(N), _, bind(x(V),S)) ~> S_Sub, _) :-
	substitute(S, x(V), N, S_Sub).

% eta
judgement(nat_rec(N, 0, bind(x(V),suc(x(V)))) ~> N, G) :-
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
	judgement(F:C, [x(V):A,x(W):list(A)|G]).


% beta
judgement(list_rec([], Nil, _) ~> Nil, _).
judgement(list_rec([X|Xs], _, bind(x(V),bind(x(W),Cons))) ~> Cons_Sub, _) :-
	substitute(Cons, x(V), X, Cons_Sub1),
	substitute(Cons_Sub1, x(W), Xs, Cons_Sub).
% eta
judgement(list_rec(L, [], bind(x(V),bind(x(W),[x(V)|x(W)]))) ~> L, G) :-
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
