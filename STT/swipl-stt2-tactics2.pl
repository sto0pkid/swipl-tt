tactic-lookup(X,XProof,[assumption(XProof,X) | _]).
tactic-lookup(X,XProof,[assumption(_,Y) | Assumptions]) :- X \= Y, tactic-lookup(X,XProof,Assumptions).


tactic-auto(implies(X,Y),function(variable(V),Expr),Assumptions) :- !, tactic-auto(Y,Expr,[assumption(variable(V),X)|Assumptions]).
tactic-auto(X,Expr,Assumptions) :- 
	% find the shortest chain of implications in the assumptions ending with X and see if it can be applied to assumptions to get X
	(
		tactic-lookup(X,Expr,Assumptions)
	;
		tactic-case(X,Expr,Assumptions)
	).

tactic-case(conjunction(X,Y),pair(XProof,YProof),Assumptions) :-
	tactic-auto(X,XProof,Assumptions),
	tactic-auto(Y,YProof,Assumptions).

tactic-case(disjunction(X,_),left(XProof),Assumptions) :-
	tactic-auto(X,XProof,Assumptions).
tactic-case(disjunction(_,Y),right(YProof),Assumptions) :-
	tactic-auto(Y,YProof,Assumptions).
