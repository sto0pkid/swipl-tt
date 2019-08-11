:- use_module('swipl_stt_tree',[proof/3]).
:- use_module('../Tree/tree',[subst/4]).

tactic_lookup(X,XProof,[assumption(XProof,X) | _]).
tactic_lookup(X,XProof,[assumption(_,Y) | Assumptions]) :- X \= Y, tactic_lookup(X,XProof,Assumptions).



run_tactic(auto,Proposition,Proof,Assumptions) :-
	reset_gensym,
	proof(Proposition,tree(proposition,[]),Assumptions),
	tactic_auto(Proposition,Proof,Assumptions),
	nonvar(Proof),
	proof(Proof,Proposition,Assumptions).



tactic_auto(tree(implies,[tree(conjunction,[A,B]),Y]),tree(function,[binding(variable(Fresh),ExprSub)]), Assumptions) :- 
	!, 
	tactic_auto(tree(implies,[A,tree(implies,[B,Y])]),tree(function,[binding(variable(V),tree(function,[binding(variable(W),Expr)]))]),Assumptions),
	gensym(v,Fresh),
	subst(Expr,variable(V),tree(and_elim1,[variable(Fresh)]),ExprSubA),
	subst(ExprSubA,variable(W),tree(and_elim2,[variable(Fresh)]),ExprSub).


	
tactic_auto(tree(implies,[X,Y]),tree(function,[binding(variable(Fresh),Expr)]),Assumptions) :- 
	!, 
	gensym(v,Fresh),
	tactic_auto(Y,Expr,[assumption(variable(Fresh),X)|Assumptions]).

tactic_auto(X,Expr,Assumptions) :- 
	(
		tactic_lookup(X,Expr,Assumptions)
	;
		tactic_case(X,Expr,Assumptions)
	).



tactic_case(tree(conjunction,[X,Y]),tree(and_intro1,[XProof,YProof]),Assumptions) :-
	tactic_auto(X,XProof,Assumptions),
	tactic_auto(Y,YProof,Assumptions).



tactic_case(tree(disjunction,[X,_]),tree(or_intro1,[XProof]),Assumptions) :-
	tactic_auto(X,XProof,Assumptions).

tactic_case(tree(disjunction,[_,Y]),tree(or_intro2,[YProof]),Assumptions) :-
	tactic_auto(Y,YProof,Assumptions).
