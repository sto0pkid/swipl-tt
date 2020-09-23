:- module(swipl_stt,[judgement/2, substitute/4, example/1, alpha_eq/2, get_rules/2]).
:- use_module(library(gensym)).

:- discontiguous judgement/2.
:- op(999, xfx, user:'~>').	% one step normalization
:- op(999, xfx, user:'~>>').	% full normalization


list_to_tuple([], true).
list_to_tuple([X | Xs], (X, Xs_Tuple)) :-
	list_to_tuple(Xs, Xs_Tuple).




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

data name(T1,...,Tk):
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
%		bind(Vars1, Case1),
%		...,
%		bind(VarsM, CaseM)
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
%		bind(Vars1, Case1),
%		...,
%		bind(VarsM, CaseM)
%	) ~> CaseM_Sub,
%	_
% ) :-
%	substitute(CaseM, VarsM, ArgsM, CaseM_Sub).


get_beta_rules(Decl, Beta) :- 
	maplist(
		[Intro, Case_Arg]>>(
			Case_Arg = bind(_, _)
		),
		Decl.intros,
		Case_Args
	),

	maplist(
		[Intro, Case_Arg, Rule]>>(
			get_beta_rule(Decl, Intro, Case_Arg, Rule, Case_Args)
		),
		Decl.intros,
		Case_Args,
		Beta
	).

get_beta_rule(Decl, IntroName:IntroArgTypes, bind(Vars, Case), Rule, Case_Args) :-
	maplist({ArgVar}/[_, ArgVar]>>(ArgVar = _), IntroArgTypes, IntroArgs),
	Obj =.. [IntroName | IntroArgs],
	Elim =.. [elim, Decl.name, Obj | Case_Args],
	Rule = (judgement(Elim ~> Case_Sub) :- substitute(Case, Vars, IntroArgs, Case_Sub)).






% ETA REDUCTION RULES: derived from "local completeness" part of "logical harmony" conditions
%
% judgement(
%	<name>_elim(
%		Obj,
%		bind([x(X11), ..., x(X1(N_1))], intro1(x(X11), ..., x(X1(N_1)))),
%		...,
%		bind([x(XM1), ..., x(XM(N_M))], introM(x(XM1), ..., x(XM(N_M))))
%	) ~> Obj,
%	Context
% ) :-
%	judgement(Obj:<name>(_,...,_), Context).


get_eta_rules(Decl, Eta) :- 
	maplist(
		[Intro, Case]>>(
			Intro = IntroName:ArgTypes,
			maplist({ArgVarInner}/[_, ArgVar]>>(ArgVar = x(ArgVarInner)), ArgTypes, IntroArgs),
			IntroObj =.. [IntroName | IntroArgs],
			Case = bind(IntroArgs, IntroObj)
		),
		Decl.intros,
		Cases
	),
	Elim =.. [elim, Obj | Cases],
	Type =.. [Decl.name | Decl.params],
	Rule = (judgement(Elim ~> Obj, Context) :- judgement(Obj:Type, Context)),
	Eta = [Rule].




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




% CONGRUENCE RULE
judgement(T1 ~> T2, G) :-
	T1 =.. [F | Args_1],
	cong(Args_1, Args_2, G),
	T2 =.. [F | Args_2].

% stops when it finds any reducible expression
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
