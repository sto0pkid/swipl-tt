:- module('swipl_stt_tree_tactics', [prove/3]).

:- use_module('swipl_stt_tree',[proof/3]).
:- use_module('../Tree/tree',[subst/4]).

tactic_lookup(X,XProof,[assumption(XProof,X) | _]).
tactic_lookup(X,XProof,[assumption(_,Y) | Assumptions]) :- X \= Y, tactic_lookup(X,XProof,Assumptions).


prove(Proposition,Proof,Assumptions) :-
	reset_gensym,
	proof(Proposition,tree(proposition,[]),Assumptions),
	tactic_auto(Proposition,Proof,Assumptions),
	% TODO: replace vars starting from v1
	nonvar(Proof),
	proof(Proof,Proposition,Assumptions).


/*
	X, where X is not of the form "A -> B"
*/
tactic_auto(X,Expr,Assumptions) :- 
	(
		tactic_lookup(X,Expr,Assumptions)
	;
		tactic_case(X,Expr,Assumptions)
	).



/*
	Maybe don't need to curry, just collect all the assumptions including the conjunction itself?
	(p : A and B) -> Y
	curried into (a : A) -> (b : B) -> Y
	prove (y : Y) under assumptions [(a : A), (b : B)]
	replace occurrences in y of 'a' and 'b' with conjunction_elim1(p) and conjunction_elim2(p), respectively
*/
tactic_case(
	tree(implication,[tree(conjunction,[A,B]),Y]),
	tree(implication_intro1,[binding(variable(Fresh),ExprSub)]),
	Assumptions
) :- 
	!,
	/*
	% Breaks on (a ^ (b ^ c)) -> ((a ^ b) ^ c)

	gensym(w,W1),
	gensym(w,W2),
	gensym(v,Fresh),
	tactic_auto(
		Y,
		Expr,
		[
			assumption(variable(W1),A),
			assumption(variable(W2),B),
			assumption(variable(Fresh),tree(conjunction,[A,B])) 
			| Assumptions
		]
	),
	subst(Expr,variable(W1),tree(conjunction_elim1,[variable(V)]),ExprSubA),
	subst(ExprSubA,variable(W2),tree(conjunction_elim2,[variable(V)]),ExprSub).
	*/
	
	gensym(v,Fresh),
	tactic_auto(
		tree(implication,[A,tree(implication,[B,Y])]),
		tree(implication_intro1,[binding(variable(V),tree(implication_intro1,[binding(variable(W),Expr)]))]),
		[assumption(variable(Fresh),tree(conjunction,[A,B])) | Assumptions]
	),
	%gensym(v,Fresh),
	subst(Expr,variable(V),tree(conjunction_elim1,[variable(Fresh)]),ExprSubA),
	subst(ExprSubA,variable(W),tree(conjunction_elim2,[variable(Fresh)]),ExprSub).

/*
	X -> Y, where X is not of the form "A and B"
*/
tactic_case(
	tree(implication,[X,Y]),
	tree(implication_intro1,[binding(variable(Fresh),Expr)]),
	Assumptions
) :- 
	!, 
	gensym(v,Fresh),
	tactic_auto(Y,Expr,[assumption(variable(Fresh),X)|Assumptions]).



tactic_case(
	tree(conjunction,[X,Y]),
	tree(conjunction_intro1,[XProof,YProof]),
	Assumptions
) :-
	tactic_auto(X,XProof,Assumptions),
	tactic_auto(Y,YProof,Assumptions).

tactic_case(
	tree(disjunction,[X,_]),
	tree(disjunction_intro1,[XProof]),
	Assumptions
) :-
	tactic_auto(X,XProof,Assumptions).

tactic_case(
	tree(disjunction,[_,Y]),
	tree(disjunction_intro2,[YProof]),
	Assumptions
) :-
	tactic_auto(Y,YProof,Assumptions).

