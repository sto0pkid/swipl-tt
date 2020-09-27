:- module(swipl_stt,[gen_rules/2]).
:- use_module('./util.pl', [list_to_tuple/2]).
:- use_module('./base.pl', []).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TODO:
%  3) variable names
%  	* singletons --> _
%  5) better intermediate representations
%  	* ex.. preparation stage
%  	* ex.. "no syntax sugar" stage
%  	* ex.. separate stage for eliminating bindings
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%





mk_binding([], Expr, Expr).
mk_binding([V|Vs], Expr, bind([V|Vs], Expr)).

mk_rule(Head, true, Head) :- !.
mk_rule(Head, Body, (Head :- Body)). 

mk_type(Decl, Type) :-
	Type =.. [Decl.name | Decl.params].









%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% FORMATION RULES: definitional
%
% judgement(<name>(T1,...,Tk):type, G) :-
%	judgement(T1:type, G),
%	...
%	judgement(Tk:type, G).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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














%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
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
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


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













%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% ELIMINATION RULES: derived from introduction rules according to description 
% for "positive types"
%
% judgement(
% 	elim(
% 		Obj,
% 		bind([x(X11), ... x(X1(N_1))],Case1),
% 		...,
% 		bind([x(XM1), ..., x(XM(N_M)],CaseM)
% 	):G, 
% 	Context
% ) :-
%	judgement(Obj:<name>(T1, ..., Tk), G),
%	judgement(C:type, G),
%	judgement(Case1:C, [x(X11):ArgT11, ..., x(X1(N_1)):ArgT1(N_1) | G]),
%	...
%	judgement(CaseM:C, [x(XM1):ArgTM1, ..., x(XM(N_M)):ArgTM(N_M) | G]).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


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
				{C}/[Arg_Type,Arg_Var, Assumption, Rec]>>(
					Arg_Var = x(_),
					Assumption = Arg_Var:Arg_Type,
					(
						Arg_Type == Type
					->	Rec = x(_):C
					;	false
					)
				),
				Arg_Types, Arg_Vars, Assumptions, Recs0
			),
			include([X]>>(X \= false), Recs0, Recs),
			maplist([Rec, Rec_Var]>>(Rec = Rec_Var:_), Recs, Rec_Vars),
			flatten([Assumptions, Recs], Assumptions_Flat),
			append(Assumptions_Flat, Context, Full_Context),
			append(Arg_Vars, Rec_Vars, Full_Vars),

			Case_Item = judgement(Case_Var:C, Full_Context),	
			% bind([x(X_11), ...], Case_Var)
			mk_binding(Full_Vars, Case_Var, Case_Binding)

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









%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% BETA REDUCTION RULES: derived from "local soundness" part of "logical harmony conditions"
%
% judgement(
% 	elim(
% 		<name>,
%		intro1(Arg11, ..., Arg1(N_1)),
%		bind([X_11, ..., R_11, ...], Case1),
%		...,
%		bind([X_M1, ..., R_M1, ...], CaseM)
%	) ~> Case1_Sub,
%	_
% ) :-
%	substitute(Case1, Vars1, Args1, Case1_Sub).
%
% ...
%
% judgement(
%	elim(
%		<name>,
%		introM(ArgM1, ..., ArgM(N_M)),
%		bind([X_11, ..., R_11, ...], Case1),
%		...,
%		bind([X_M1, ..., R_M1, ...], CaseM)
%	) ~> CaseM_Sub,
%	_
% ) :-
%	substitute(CaseM, VarsM, ArgsM, CaseM_Sub).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


gen_beta_rules(Decl, Beta) :-
	% <name>(T1, ..., Tk)
	mk_type(Decl, Type),


        % Intro				Case_Arg					RecA
	% -----------------------------------------------------------------------------------------
	% intro1:[ArgT_11,...]		bind([X_11, ..., R_11, ...], Case1)		[x(X_11):x(R_11), ...]
	% ...
	% introM:[ArgT_M1,...]		bind([X_M1, ..., R_M1, ...], CaseM)		[x(X_M1):x(R_M1), ...]
	maplist(
		[Intro, Case_Arg, RecA]>>(
			Intro = _:Intro_Arg_Types,
			maplist(
				[Arg_Type, Arg, Rec, RecA]>>(
					Arg = x(_),
					(
						Arg_Type == Type
					->	Rec = x(_), RecA = (Arg:Rec)
					;	Rec = false, RecA = false
					)
				),
				Intro_Arg_Types, Intro_Args, Rec0, RecA0
			),
			include([X]>>(X \= false), Rec0, Rec),	 % [x(R_11), ...]
			include([X]>>(X \= false), RecA0, RecA), % [x(X_11):x(R_11), ...]
			append(Intro_Args, Rec, Full_Args),
			Case_Arg = bind(Full_Args, _)
		),
		Decl.intros, Case_Args0, Case_RecAs
	),
	maplist([X,Y]>>(X = bind(Vars,Case), (Vars = [] -> Y = Case ; Y = X)), Case_Args0, Case_Args),

	maplist(
		{Case_Args}/[Intro, Case_Arg, Case_RecA, Rule]>>(
			gen_beta_rule(Decl, Intro, Case_Arg, Case_RecA, Rule, Case_Args)
		),
		Decl.intros, Case_Args, Case_RecAs, Beta
	).

gen_beta_rule(Decl, Intro_Name:Intro_Arg_Types, Binding, Case_RecA, Rule, Case_Args) :-
	length(Intro_Arg_Types, L),
	length(Intro_Args, L),
	Obj =.. [Intro_Name | Intro_Args],

	% elim(<name>, intro_i(X_i1,...), ...)
	Elim =.. [elim, Decl.name, Obj | Case_Args],


	% RecA			Rec_Elim
	%-------------------------------------------
	% x(X_11):x(R_11)	elim(<name>,x(X_11),...)
	% ...
	% x(X_M1):x(R_M1)	elim(<name>,x(X_M1),...)
	maplist(
		[RecA, Rec_Elim]>>(
			RecA = x(V):_,
			Rec_Elim =.. [elim, Decl.name, x(V) | Case_Args]
		),
		Case_RecA, Rec_Elims
	),


	append(Intro_Args, Rec_Elims, Full_Args),


	(
		nonvar(Binding)
	->	Binding = bind(Vars, Case),
		(
			Vars \= []
		->	Rule = (judgement(Elim ~> Case_Sub, _) :- substitute(Case, Vars, Full_Args, Case_Sub))
		;	Rule = (judgement(Elim ~> Case, _))
		)
	;	Rule = (judgement(Elim ~> Binding, _))
	).









%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
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
%	judgement(Obj:<name>(_,...,_), Context).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



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



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
