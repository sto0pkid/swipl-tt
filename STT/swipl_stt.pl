:- module(swipl_stt,[proof/3]).


/*
*
* This fixes the termination issue we had in proof-checking IPL, though that's
* somewhat independent of the motivation for development of IPL into STT.
* 
* Termination can be demonstrated by noting that in proof-checking, the rules
* only do substructural recursion. 
*
* How about termination of proof-search? This should be logically equivalent
* to IPL so we should hypothetically be able to have complete proof search.
*/

% hypothesis rule
proof(x(V), X,[(x(V),X)|_]).
proof(x(V), X,[(x(W),_)|Assumptions]) :- V \= W, proof(x(V),X,Assumptions).



% reification of `false`
proof(empty,proposition,_).



% reification of `true`
proof(unit,proposition,_).
proof(unit_intro1,unit,_).
/*
proof(top_elim(T,CProof), C, Assumptions) :-
	proof(T,top),
	proof(CProof,C,[(x(V),top)|Assumptions]).
*/

% bool
proof(bool,proposition,_).
proof(bool_intro1,bool,_).
proof(bool_intro2,bool,_).

/*
proof(bool_elim(B, CProof1, CProof2), C, Assumptions) :-
	proof(B,bool,Assumptions),
	proof(CProof1,C,[(x(V),bool)|Assumptions]),
	proof(Cproof2,C,[(x(W),bool)|Assumptions]).
*/


% reification of `,`
proof(and(X,Y),proposition,Assumptions) :- 
	proof(X,proposition,Assumptions),
	proof(Y,proposition,Assumptions).


proof(and_intro1(XProof,YProof),and(X,Y),Assumptions) :- 
	proof(and(X,Y),proposition,Assumptions),
	proof(XProof,X,Assumptions),
	proof(YProof,Y,Assumptions).

% negative formulation of and_elim rules
proof(and_elim1(P),X,Assumptions) :- 
	proof(P,and(X,_),Assumptions).

proof(and_elim2(P),Y,Assumptions) :- 
	proof(P,and(_,Y),Assumptions).

/*
% positive formulation of and_elim
proof(and_elim3(P, CProof),C,Assumptions) :-
	proof(P, and(X,Y), Assumptions),
	proof(CProof, C, [assumption(XProof,X), assumption(YProof,Y) | C]).
*/


% reification of `;`
proof(or(X,Y),proposition,Assumptions) :- 
	proof(X,proposition,Assumptions),
	proof(Y, proposition, Assumptions).

proof(or_intro1(XProof),or(X,Y),Assumptions) :- 
	proof(or(X,Y),proposition,Assumptions),
	proof(XProof,X,Assumptions).

proof(or_intro2(YProof),or(X,Y),Assumptions) :- 
	proof(or(X,Y),proposition,Assumptions),
	proof(YProof,Y,Assumptions).

/*
proof(or_elim1(P,variable(V),Left,Right),C,Assumptions) :- 
	proof(P,disjunction(X,Y),Assumptions),
	proof(Left,C,[assumption(variable(V),X)|Assumptions]),
	proof(Right,C,[assumption(variable(V),Y)|Assumptions]).
*/


% reification of `:-`
proof(implies(X,Y),proposition,Assumptions) :- 
	proof(X,proposition,Assumptions),
	proof(Y,proposition,Assumptions).

proof(implies_intro(variable(V),Expr),implies(X,Y), Assumptions) :- 
	proof(implies(X,Y),proposition,Assumptions),
	proof(Expr,Y,[(x(V),X)|Assumptions]).

proof(implies_elim(F,X),B,Assumptions) :- 
	proof(X,A,Assumptions),
	proof(F,implies(A,B),Assumptions).
