:- module(builtin, [substitute/4, alpha_eq/2, judgement/2]).


% CAPTURE-AVOIDING SUBSTITUTION
substitute(T, [], [], T).
substitute(T, [Var | Var_Rest], [For | For_Rest], T_Out) :-
	substitute(T, Var, For, T_1),
	substitute(T_1, Var_Rest, For_Rest, T_Out).
	
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


