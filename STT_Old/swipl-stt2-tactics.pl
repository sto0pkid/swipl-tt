tactic-lookup(X,XProof,[assumption(XProof,X) | _]).
tactic-lookup(X,XProof,[assumption(_,Y) | Assumptions]) :- X \= Y, tactic-lookup(X,XProof,Assumptions).

tactic-find-in-assumption-helper(X,X).
tactic-find-in-assumption-helper(X,implies(_,B)) :- tactic-find-in-assumption-helper(X,B).

tactic-find-in-assumption(X,assumption(_,Type)) :- tactic-find-in-assumption-helper(X,Type).
tactic-find(X,[Assumption],Result) :- 
	(
		tactic-find-in-assumption(X,Assumption) 
	->	Result = [ Assumption]
	;
		Result = []
	).
tactic-find(X,[Assumption | [HeadRest | TailRest]],Result) :- 
	(
		tactic-find-in-assumption(X,Assumption) 
	->	Result = [Assumption | ResultRest]
	;
		Result = ResultRest
	),
	tactic-find(X,[HeadRest | TailRest],ResultRest).


tactic-auto(implies(X,Y),function(variable(V),Expr),Assumptions) :- !, tactic-auto(Y,Expr,[assumption(variable(V),X)|Assumptions]).
tactic-auto(X,Expr,Assumptions) :- 
	% find the shortest chain of implications in the assumptions ending with X and see if it can be applied to assumptions to get X
	tactic-find(X,Assumptions,Found),
	tactic-closure(X,Assumptions,Found,Expr).
	(
		tactic-lookup(X,Expr,Assumptions)
	;
		tactic-lookup(implies(Y,X),F,Assumptions),
		tactic-route(Y,YProof,Assumptions),
		Expr = apply(F,YProof)
	).
