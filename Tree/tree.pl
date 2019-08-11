:- module(tree,[subst/4]).

subst(variable(X),variable(X),For,For).
subst(variable(X),variable(Y),_,variable(X)) :- X \= Y.
subst([],_,_,[]).
subst([X | Rest], variable(V),For,[XSub | RestSubs]) :- subst(X,variable(V),For,XSub), subst(Rest,variable(V),For,RestSubs).
subst(tree(Label,Children),variable(V),For,tree(Label,ChildrenSubs)) :- subst(Children,variable(V),For,ChildrenSubs).
subst(binding(variable(X),Expr),variable(V),For,binding(variable(Fresh),ExprSub)) :- 
	gensym(v,Fresh),
	subst(Expr,variable(X),variable(Fresh),ExprFresh),
	subst(ExprFresh,variable(V),For,ExprSub).

