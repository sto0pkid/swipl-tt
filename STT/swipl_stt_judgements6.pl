:- module(swipl_stt,[judgement/2, substitute/4, example/1, alpha_eq/2, gen_rules/2]).
:- use_module(library(gensym)).
:- use_module('./util.pl', [list_to_tuple/2]).

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
judgement(Term1:Type, [Term2:Type|_]) :- alpha_eq(Term1, Term2), !.
judgement(Term1:Type, [Term2:_|G]) :- \alpha_eq(Term1, Term2), judgement(Term1:Type,G).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/* TODO:
*  1) recursion
*  2) "bind([],Expr)" ~> Expr
*  3) variable names
*  4) eliminate axiomatic premises, ex.. 
*  	"judgement(bool:type,_14550)" in "judgement(true:bool,_14550):-judgement(bool:type,_14550),true"
*
*
*/

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


mk_binding([], Expr, Expr).
mk_binding([V|Vs], Expr, bind([V|Vs], Expr)).

mk_rule(Head, true, Head) :- !.
mk_rule(Head, Body, (Head :- Body)). 

mk_type(Decl, Type) :-
	Type =.. [Decl.name | Decl.params].









% FORMATION RULES: definitional

% judgement(<name>(T1,...,Tk):type, G) :-
%	judgement(T1:type, G),
%	...
%	judgement(Tk:type, G).


gen_formation_rules(Decl, Formation) :-
	% <name>(T1,...,Tk)
	mk_type(Decl, Type),

	% Param		Body_Item
	% ----------------------------
	% T1		judgement(T1:type, G)
	% ...		...
	% Tk		judgement(Tk:type, G)
	maplist(
		{Context}/[Param, Body_Item]>>(
			Body_Item = judgement(Param:type, Context)
		),
		Decl.params, Body_List
	),
	list_to_tuple(Body_List, Body),



	% Formation_Rule:
	% ---------------
	%
	% judgement(<name>(T1,...,Tk):type, G) :-
	%	judgement(T1:type, G),
	%	...
	%	judgement(Tk:type, G).
	%
	mk_rule(judgement(Type:type, Context), Body, Formation_Rule),

	Formation = [Formation_Rule].














% INTRODUCTION RULES: definitional
%
% judgement(<intro1>(arg11,...,arg1(N_1)):<name>(T1, ..., Tk), G) :-
% 	judgement(<name>(T1, ..., Tk):type, G),
%	judgement(arg11:ArgT11, G),
%	...
%	judgement(arg1(N_1):ArgT1(N_1), G).
% ...
% judgement(<introM>(argM1,...,argM(N_M)):<name>(T1, ..., Tk), G) :-
% 	judgement(<name>(T1, ..., Tk):type, G),
%	judgement(argM1:ArgTM1, G),
%	...
%	judgement(argM(N_M):ArgTM(N_M), G).


gen_introduction_rules(Decl, Introduction) :-
	maplist(
		{Context}/[Intro,Rule]>>(
			gen_introduction_rule(Decl,Intro,Rule,Context)
		),
		Decl.intros,
		Introduction
	).

gen_introduction_rule(Decl, IntroName:Arg_Types, Rule, Context) :-
	% <name>(T1, ..., Tk)
	mk_type(Decl, Type),




	% Arg_Types	Arg_Vars	Arg_Items
	% --------------------------------------------------------------
	% ArgT_i1, 	arg_i1,		judgement(arg_i1:ArgT_i1, G)
	% ...		...		...
	% ArgT_i(N_i),	arg_i(N_I)	judgement(arg_i(N_i):ArgT_i(N_i), G).
	maplist(
		{Context}/[Arg_Type, Arg_Var, Body_Item]>>(
			Body_Item = judgement(Arg_Var:Arg_Type, Context)
		),
	  	Arg_Types, Arg_Vars, Arg_Items
	),





	% <intro_i>(arg_i1, ..., arg_i(N_i))
	Term =.. [IntroName | Arg_Vars],





	% (
	% 	judgement(name(T1,...,Tk):type, G),		% if Decl.params \= []
	% 	judgement(arg_i1:ArgT_i1, G),
	%	...
	%	judgement(arg_i(N_i):ArgT_i(N_i), G)
	% )
	(
		Decl.params \= []
	->	Body_Items = [judgement(Type:type, Context) | Arg_Items]
	;	
		% Type:type is axiomatic when there are no params
		Body_Items = Arg_Items
	),
	list_to_tuple(Body_Items, Body),







	% judgement(<introM>(argM1,...,argM(N_M)):<name>(T1, ..., Tk), G) :-
	% 	judgement(<name>(T1, ..., Tk):type, G),		% if Decl.params \= []
	%	judgement(argM1:ArgTM1, G),
	%	...
	%	judgement(argM(N_M):ArgTM(N_M), G).
	mk_rule(judgement(Term:Type, Context),Body,Rule).














% ELIMINATION RULES: derived from introduction rules according to description for "positive types"
%
% judgement(<name>_elim(Obj, bind([x(X11), ... x(X1(N_1))],Case1), ... bind([x(XM1), ..., x(XM(N_M)],CaseM)):C, G) :-
%	judgement(Obj:<name>(T1, ..., Tk), G),
%	judgement(C:type, G),
%	judgement(Case1:C, [x(X11):ArgT11, ..., x(X1(N_1)):ArgT1(N_1) | G]),
%	...
%	judgement(CaseM:C, [x(XM1):ArgTM1, ..., x(XM(N_M)):ArgTM(N_M) | G]),


gen_elimination_rules(Decl, Elimination) :-
	% name(T1, ..., Tk)
	mk_type(Decl, Type),

	% Arg_Types 	:      [        ArgT_11, ...,             ArgT_1(N_1)]
	% Assumptions 	:      [x(X_11):ArgT_11, ..., x(X_1(N_1)):ArgT_1(N_1)]
	% Case_Binding 	: bind([x(X_11),         ..., x(X_1(N_1))            ], X1)
	% Out		: [
	% 		       [x(R_11),         ..., x(R_1(N_1))],
	%		       X1
	%		  ]
	maplist(
		{Context, C}/[_:Arg_Types, Case_Binding, Case_Item]>>(

			% Arg_Type	Arg_Var		Assumption		
			% -------------------------------------------------------
			% ArgT_11	x(X_11)		[x(X_11):ArgT_11 | * ]
			% ...		...		...			
			% ArgT_1(N_1)	x(X_1(N_1))	[x(X_1(N_1)):ArgT_1(N_1) | * ]
			maplist(
				[Arg_Type,Arg_Var, Arg_Assumptions, Rec]>>(
					Arg_Var = x(_),
					Assumption = Arg_Var:Arg_Type,
					(
						Arg_Type == Type
					->	Arg_Assumptions = Assumption
					;	Arg_Assumptions = [Assumption, x(_):C]
					)
				),
				Arg_Types, Arg_Vars, Assumptions
			),
			flatten(Assumptions, Assumptions_Flat),
			append(Assumptions_Flat, Context, Full_Context),

			Case_Item = judgement(Case_Var:C, Full_Context),	
			% bind([x(X_11), ...], Case_Var)
			mk_binding(Arg_Vars, Case_Var, Case_Binding)

		),
		Decl.intros, Case_Bindings, Case_Items

	),




	Body_Items = [
		judgement(Obj:Type, Context),
		judgement(C:type, Context) 
		| Case_Items
	],
	list_to_tuple(Body_Items, Body),
	Elim =.. [elim, Decl.name, Obj | Case_Bindings],
	mk_rule(judgement(Elim:C, Context),Body,Rule),
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


gen_beta_rules(Decl, Beta) :- 
	maplist(
		[Intro, Case_Arg]>>(
			Intro = _:IntroArgTypes,
			length(IntroArgTypes, L),
			length(IntroArgs, L),
			mk_binding(IntroArgs, _, Case_Arg)
		),
		Decl.intros,
		Case_Args
	),
	maplist(
		[Intro, Case_Arg, Rule]>>(
			gen_beta_rule(Decl, Intro, Case_Arg, Rule, Case_Args)
		),
		Decl.intros,
		Case_Args,
		Beta
	).

gen_beta_rule(Decl, IntroName:IntroArgTypes, Binding, Rule, Case_Args) :-
	length(IntroArgTypes, L),
	length(IntroArgs, L),
	Obj =.. [IntroName | IntroArgs],
	Elim =.. [elim, Decl.name, Obj | Case_Args],
	(
		Binding = bind(Vars, Case)
	->	Rule = (judgement(Elim ~> Case_Sub, _) :- substitute(Case, Vars, IntroArgs, Case_Sub))
	;	Rule = (judgement(Elim ~> Binding, _))
	).










% ETA REDUCTION RULES: derived from "local completeness" part of "logical harmony" conditions
%
% judgement(
%	elim(
%		<name>,
%		Obj,
%		bind([x(X11), ..., x(X1(N_1))], intro1(x(X11), ..., x(X1(N_1)))),
%		...,
%		bind([x(XM1), ..., x(XM(N_M))], introM(x(XM1), ..., x(XM(N_M))))
%	) ~> Obj,
%	Context
% ) :-
%	judgement(Obj:<name>(T1,...,Tk), Context).


gen_eta_rules(Decl, Eta) :- 
	% <name>(T1, ..., Tk)
	mk_type(Decl, Type),



	% Intro				Case
	% ---------------------------------------------------------------------------
	% intro_1:[ArgT_11, ...]	bind([x(X_11), ...], intro_1(x(X_11), ....))
	% ...
	% intro_M:[ArgT_M1, ...]	bind([x(X_M1), ...], intro_M(x(X_M1), ....))
	maplist(
		[Intro, Case]>>(
			Intro = IntroName:ArgTypes,


			% IntroArgs: [x(X_i1), ...]
			maplist(
				{ArgVarInner}/[_, ArgVar]>>(
					ArgVar = x(ArgVarInner)
				),
				ArgTypes, IntroArgs
			),

			% intro_i(x(X_i1), ...)
			IntroObj =.. [IntroName | IntroArgs],

			% bind([x(X_i1), ...], intro(x(X_i1, ...))
			mk_binding(IntroArgs, IntroObj, Case)
		),
		Decl.intros, Cases
	),


	% elim(
	% 	<name>,
	% 	Obj,
	% 	bind([x(X_11), ...], intro(x(X_11), ...)),
	%	...
	% 	bind([x(X_M1), ...], intro(x(X_M1), ...)),
	% ) 	
	Elim =.. [elim, Decl.name, Obj | Cases],





	% judgement(
	%	elim(
	%		<name>,
	%		Obj,
	%		bind([x(X11), ..., x(X1(N_1))], intro1(x(X11), ..., x(X1(N_1)))),
	%		...,
	%		bind([x(XM1), ..., x(XM(N_M))], introM(x(XM1), ..., x(XM(N_M))))
	%	) ~> Obj,
	%	Context
	% ) :-
	%	judgement(Obj:<name>(T1,...,Tk), Context).
	Rule = (judgement(Elim ~> Obj, Context) :- judgement(Obj:Type, Context)),
	Eta = [Rule].




gen_rules(Decl, Rules) :-
	gen_formation_rules(Decl, Formation),
	gen_introduction_rules(Decl, Introduction),
	gen_elimination_rules(Decl, Elimination),
	gen_beta_rules(Decl, Beta),
	gen_eta_rules(Decl, Eta),
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
