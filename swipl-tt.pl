/* CONTEXT LOOKUP RULES */
lookup(var(X),[proof(var(X),Proposition) |_],Proposition).
lookup(var(X),[_|Rest],Proposition) :- lookup(var(X),Rest,Proposition).

/* SUBSTITUTION RULES */
substitute(empty,_,_,empty).

substitute(top,_,_,top).
substitute(unit,_,_,unit).

substitute(bool,_,_,bool).
substitute(on,_,_,on).
substitute(off,_,_,off).

substitute(nat,_,_,nat).
substitute(zero,_,_,zero).
substitute(suc(X),Var,For,suc(SubX)) :- substitute(X,Var,For,SubX).

substitute(list(T),Var,For,list(SubT)) :- substitute(T,Var,For,SubT).
substitute(emptyList,_,_,emptyList).
substitute(concat(X,Xs),Var,For,concat(SubX,SubXs)) :- substitute(X,Var,For,SubX), substitute(Xs,Var,For,SubXs).

substitute(var(X),var(X),For,For).
substitute(var(X),var(Y),_,var(X)) :- X \= Y.


/* TYPE FORMATION RULES */
proposition(empty).
proposition(top).
proposition(bool).
proposition(nat).
proposition(conjunction(T1,T2)) :- proposition(T1), proposition(T2).
proposition(disjunction(T1,T2)) :- proposition(T1), proposition(T2).
proposition(list(T)) :- proposition(T).


/* INTRODUCTION RULES */

% top
proof(unit,top).

% bool
proof(on, bool).
proof(off, bool).

% nat
proof(zero, nat).
proof(suc(X), nat) :- proof(X, nat).

% conjunction
proof(pair(XProof,YProof),conjunction(X,Y)) :- proof(XProof,X), proof(YProof,Y).

% disjunction
proof(left(XProof),disjunction(X,_)) :- proof(XProof,X).
proof(right(YProof),disjunction(_,Y)) :- proof(YProof,Y).

% list
proof(emptyList, list(T)) :- proposition(list(T)).
proof(concat(X,XS), list(T)) :- proof(X,T), proof(XS,list(T)).


/* ELIMINATION RULES */
proof(absurd(X),_) :- proof(X,empty).

proof(proj_left(P),X) :- proof(P,conjunction(X,_)).
proof(proj_right(P),Y) :- proof(P,conjunction(_,Y)).


/* DEFINITIONAL EQUALITY */
proof(def_equality(XProof,Normalized)) :- compute(XProof,Normalized). 


/* COMPUTATION RULES */
compute(proj_left(pair(XProof,YProof)),XProof) :- proof(pair(XProof,YProof),conjunction(_,_)).
compute(proj_right(pair(XProof,YProof)),YProof) :- proof(pair(XProof,YProof),conjunction(_,_)).



% proof_under_assumptions(function(var(X),Expr),implies(A,B),Assumptions) :- 
%	substitute(Expr,X,var(y),Substituted),
%	proof_under_assumptions(Substituted, B, [assumption(var(y),A) | Assumptions]).
