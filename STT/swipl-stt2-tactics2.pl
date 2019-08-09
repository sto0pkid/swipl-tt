:- use_module('swipl_stt',[proof/3]).

tactic_lookup(X,XProof,[assumption(XProof,X) | _]).
tactic_lookup(X,XProof,[assumption(_,Y) | Assumptions]) :- X \= Y, tactic_lookup(X,XProof,Assumptions).

subst(variable(X),variable(X),For,For).
subst(variable(X),variable(Y),_,variable(X)) :- X \= Y.
subst(conjunction(X,Y),variable(V),For,conjunction(XSub,YSub)) :- subst(X,variable(V),For,XSub), subst(Y,variable(V),For,YSub).
subst(and_intro1(X,Y),variable(V),For,and_intro1(XSub,YSub)) :- subst(X,variable(V),For,XSub), subst(Y,variable(V),For,YSub).
subst(and_elim1(P),variable(V),For,and_elim1(PSub)) :- subst(P,variable(V),For,PSub).
subst(and_elim2(P),variable(V),For,and_elim2(PSub)) :- subst(P,variable(V),For,PSub).
subst(disjunction(X,Y),variable(V),For,disjunction(XSub,YSub)) :- subst(X,variable(V),For,XSub), subst(Y,variable(V),For,YSub).
subst(or_intro1(X),variable(V),For,or_intro1(XSub)) :- subst(X,variable(V),For,XSub).
subst(or_intro2(Y),variable(V),For,or_intro2(YSub)) :- subst(Y,variable(V),For,YSub).
subst(top,_,_,top).
subst(implies(X,Y),variable(V),For,implies(XSub,YSub)) :- subst(X,variable(V),For,XSub), subst(Y,variable(V),For,YSub).
subst(function(variable(V),Expr),variable(W),For,function(variable(Fresh),ExprSub)) :- 
	gensym(v,Fresh),
	subst(Expr,variable(V),variable(Fresh),ExprFresh),
	subst(ExprFresh,variable(W),For,ExprSub).

run_tactic(auto,Proposition,Proof,Assumptions) :-
	tactic_auto(Proposition,Proof,Assumptions),
	nonvar(Proof),
	proof(Proof,Proposition,Assumptions),
	reset_gensym.

tactic_auto(implies(conjunction(A,B),Y),function(variable(Fresh),ExprSub),Assumptions) :- 
	!, 
	tactic_auto(implies(A,implies(B,Y)),function(variable(V),function(variable(W),Expr)),Assumptions),
	gensym(v,Fresh),
	subst(Expr,variable(V),and_elim1(variable(Fresh)),ExprSubA),
	subst(ExprSubA,variable(W),and_elim2(variable(Fresh)),ExprSub).
	
tactic_auto(implies(X,Y),function(variable(Fresh),Expr),Assumptions) :- !, gensym(v,Fresh), tactic_auto(Y,Expr,[assumption(variable(Fresh),X)|Assumptions]).
tactic_auto(X,Expr,Assumptions) :- 
	(
		tactic_lookup(X,Expr,Assumptions)
	;
		tactic_case(X,Expr,Assumptions)
	).

tactic_case(conjunction(X,Y),and_intro1(XProof,YProof),Assumptions) :-
	tactic_auto(X,XProof,Assumptions),
	tactic_auto(Y,YProof,Assumptions).

tactic_case(disjunction(X,_),or_intro1(XProof),Assumptions) :-
	tactic_auto(X,XProof,Assumptions).
tactic_case(disjunction(_,Y),or_intro2(YProof),Assumptions) :-
	tactic_auto(Y,YProof,Assumptions).
