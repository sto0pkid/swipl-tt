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
% empty
proof(absurd(X),_) :- proof(X,empty).

% conjunction
proof(proj_left(P),X) :- proof(P,conjunction(X,_)).
proof(proj_right(P),Y) :- proof(P,conjunction(_,Y)).


/* COMPUTATION / NORMALIZATION / DEFINITIONAL-EQUALITY RULES */
% conjunction
compute(proj_left(pair(XProof,YProof)),XProof) :- proof(pair(XProof,YProof),conjunction(_,_)).
compute(proj_right(pair(XProof,YProof)),YProof) :- proof(pair(XProof,YProof),conjunction(_,_)).
