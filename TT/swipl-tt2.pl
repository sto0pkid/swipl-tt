/* CONTEXT LOOKUP RULES */
lookup(variable(X),[assumption(variable(X),Proposition) |_],Proposition).
lookup(variable(X),[_|Rest],Proposition) :- lookup(variable(X),Rest,Proposition).

/* SUBSTITUTIONS */
substitute(const(X),_,_,const(X)).
substitute(variable(X),variable(X),For,For).
substitute(variable(X),variable(Y),_,variable(X)) :- X \= Y.
substitute([],_,_,[]).
substitute([X | Rest],variable(V),For,[SubX | SubRest]) :- substitute(X,variable(V),For,SubX),substitute(Rest,variable(V),For,SubRest).
substitute(bind(variable(X),Expr),variable(X),_,bind(variable(X),Expr)).
substitute(bind(variable(X),Expr),variable(Y),For,bind(variable(X),ExprSub)) :- X \= Y, For \= Y, substitute(Expr,variable(Y),For,ExprSub).
substitute(bind(variable(X),Expr),variable(Y),variable(X),bind(Fresh,ExprSub)) :- 
substitute(tree(Label,Children),variable(X),For,tree(Label,ChildrenSub)) :- substitute(Children,variable(X),For,ChildrenSub).


substitute(empty,_,_,empty).

substitute(top,_,_,top).
substitute(unit,_,_,unit).

substitute(bool,_,_,bool).
substitute(on,_,_,on).
substitute(off,_,_,off).

substitute(nat,_,_,nat).
substitute(zero,_,_,zero).
substitute(suc(X),Var,For,suc(SubX)) :- substitute(X,Var,For,SubX).

substitute(conjunction(X,Y),variable(V),For,conjunction(SubX, SubY)) :- substitute(X,variable(V),For, SubX), substitute(Y,variable(V),For,SubY).
substitute(pair(X,Y),variable(V),For,pair(SubX,SubY)) :- substitute(X,variable(V),For,SubX), substitute(Y,variable(V),For,SubY).


substitute(disjunction(X,Y),variable(V),For,disjunction(SubX, SubY)) :- substitute(X,variable(V),For, SubX), substitute(Y,variable(V),For,SubY).
substitute(left(X),variable(V),For,left(SubX)) :- substitute(X,variable(V),For,SubX).
substitute(right(Y),variable(V),For,right(SubY)) :- substitute(Y,variable(V),For,SubY).

substitute(list(T),Var,For,list(SubT)) :- substitute(T,Var,For,SubT).
substitute(emptyList,_,_,emptyList).
substitute(concat(X,Xs),Var,For,concat(SubX,SubXs)) :- substitute(X,Var,For,SubX), substitute(Xs,Var,For,SubXs).

% needs capture-avoiding substitution!
substitute(implies(X,Y),variable(V),For,implies(SubX, SubY)) :- substitute(X,variable(V),For, SubX), substitute(Y,variable(V),For,SubY).
substitute(function(variable(Arg),Expr),variable(V),For,function(variable(Arg),ExprSub)) :- substitute(Expr,variable(V),For,ExprSub).


substitute(identity(A,X,Y),variable(V),For,identity(SubA,SubX,SubY)) :- 
	substitute(A,variable(V),For,SubA),
	substitute(X,variable(V),For,SubX),
	substitute(Y,variable(V),For,SubY).
substitute(refl(X,Y),variable(V),For,refl(SubX,SubY)) :- substitute(X,variable(V),For,SubX), substitute(Y,variable(V),For,SubY).

%substitute(variable(X),variable(X),For,For).
%substitute(variable(X),variable(Y),_,variable(X)) :- X \= Y.


/* HYPOTHESIS RULE */
proof(variable(X),A,Assumptions) :- lookup(variable(X),Assumptions,A).

/* TYPES */

% empty
proof(empty,proposition,_).
proof(absurd(X),C,Assumptions) :- 
	proof(X,empty,Assumptions),
	proof(C,proposition,[assumption(_,empty) | Assumptions]).

% top
proof(top,proposition,_).
proof(top-intro1,top,_).
proof(top-elim1(P,bind(variable(V),Case-top-intro1)),C,Assumptions) :-
	proof(C,proposition,[assumption(variable(V),bool) | Assumptions]),
	substitute(C,variable(V),top-intro1,C1),
	proof(Case-top-intro1,C1,Assumptions).

% bool
proof(bool,proposition,_).
proof(bool-intro1, bool,_).
proof(bool-intro2, bool,_).
proof(bool_elim1(P,variable(V),Case-bool-intro1,Case-bool-intro2),C,Assumptions) :-
	%proof(P,bool,Assumptions),
	proof(C,proposition,[assumption(variable(V),bool) | Assumptions]),
	substitute(C,variable(V),on,CTrue),
	proof(TrueOption,CTrue,Assumptions),
	substitute(C,variable(V),off,CFalse),
	proof(FalseOption,CFalse,Assumptions).

proof(identity(A,X,Y),proposition,Assumptions) :- 
	proof(A,proposition,Assumptions),
	proof(X,A,Assumptions),
	proof(Y,A,Assumptions).
proof(refl(X,X),identity(A,X,X),Assumptions) :- proof(identity(A,X,X),proposition,Assumptions).



% nat
proof(nat,proposition,_).
proof(zero, nat, _).
proof(suc(X), nat, Assumptions) :- proof(X, nat, Assumptions).

% conjunction
proof(conjunction(X,Y),proposition,Assumptions) :- proof(X,proposition,Assumptions), proof(Y,proposition,Assumptions).
proof(pair(XProof,YProof),conjunction(X,Y),Assumptions) :- proof(XProof,X,Assumptions), proof(YProof, Y, Assumptions).
proof(proj_left(P),X,Assumptions) :- proof(P,conjunction(X,_),Assumptions).
proof(proj_right(P),Y,Assumptions) :- proof(P,conjunction(_,Y),Assumptions).

% disjunction
proof(disjunction(X,Y),proposition,Assumptions) :- proof(X,proposition,Assumptions), proof(Y,proposition,Assumptions).
proof(left(XProof),disjunction(X,_), Assumptions) :- proof(disjunction(X,_),proposition,Assumptions), proof(XProof, X, Assumptions).
proof(right(YProof),disjunction(_,Y), Assumptions) :- proof(disjunction(_,Y),proposition,Assumptions), proof(YProof, Y, Assumptions).
proof(or_elim(P,XOption,YOption),C,Assumptions) :- 
	proof(P,disjunction(X,Y),Assumptions),
	proof(XOption,C,[assumption(variable(_),X) | Assumptions]),
	proof(YOption,C,[assumption(variable(_),Y) | Assumptions]).

% list
proof(list(Type),proposition,Assumptions) :- proof(Type,proposition,Assumptions).
proof(emptyList, list(Type), Assumptions) :- proof(list(Type),proposition,Assumptions).
proof(concat(Head,Tail), list(Type), Assumptions) :- proof(list(Type),proposition,Assumptions), proof(Head,Type,Assumptions), proof(Tail,list(Type),Assumptions).

% implication
proof(implies(A,B),proposition,Assumptions) :- proof(A,proposition,Assumptions), proof(B,proposition,Assumptions).
proof(function(variable(X),Expr),implies(A,B),Assumptions) :- 
	proof(Expr, B, [assumption(variable(X),A) | Assumptions]).
proof(apply(F,X),B,Assumptions) :- proof(X,A,Assumptions), proof(F,implies(A,B),Assumptions).



/* COMPUTATION RULES */
compute(apply(function(variable(X),Expr),Argument), Substituted, Assumptions) :- proof(function(variable(X),Expr), implies(_,_), Assumptions), substitute(Expr,variable(X),Argument,Substituted).
compute(proj_left(pair(XProof,YProof)),XProof, Assumptions) :- proof(pair(XProof,YProof),conjunction(_,_), Assumptions).
compute(proj_right(pair(XProof,YProof)),YProof, Assumptions) :- proof(pair(XProof,YProof),conjunction(_,_), Assumptions).
