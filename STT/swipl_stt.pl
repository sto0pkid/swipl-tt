:- module(swipl_stt,[proof/3]).


% hypothesis rule
proof(variable(V), X,[assumption(variable(V),X)|_]).
proof(variable(V), X,[assumption(variable(W),_)|Assumptions]) :- V \= W, proof(variable(V),X,Assumptions).



% reification of `false`
proof(empty,proposition,_).



% reification of `true`
proof(top,proposition,_).
proof(top_intro1,top,_).



% bool
proof(bool,proposition,_).
proof(bool_intro1,bool,_).
proof(bool_intro2,bool,_).



% reification of `,`
proof(conjunction(X,Y),proposition,Assumptions) :- 
	proof(X,proposition,Assumptions),
	proof(Y,proposition,Assumptions).

proof(and_intro1(XProof,YProof),conjunction(X,Y),Assumptions) :- 
	proof(conjunction(X,Y),proposition,Assumptions),
	proof(XProof,X,Assumptions),
	proof(YProof,Y,Assumptions).

proof(and_elim1(P),X,Assumptions) :- 
	proof(P,conjunction(X,_),Assumptions).

proof(and_elim2(P),Y,Assumptions) :- 
	proof(P,conjunction(_,Y),Assumptions).



% reification of `;`
proof(disjunction(X,Y),proposition,Assumptions) :- 
	proof(X,proposition,Assumptions),
	proof(Y, proposition, Assumptions).

proof(or_intro1(XProof),disjunction(X,Y),Assumptions) :- 
	proof(disjunction(X,Y),proposition,Assumptions),
	proof(XProof,X,Assumptions).

proof(or_intro2(YProof),disjunction(X,Y),Assumptions) :- 
	proof(disjunction(X,Y),proposition,Assumptions),
	proof(YProof,Y,Assumptions).

%proof(or_elim1(P,variable(V),Left,Right),C,Assumptions) :- 
%	proof(P,disjunction(X,Y),Assumptions),
%	proof(Left,C,[assumption(variable(V),X)|Assumptions]),
%	proof(Right,C,[assumption(variable(V),Y)|Assumptions]).



% reification of `:-`
proof(implies(X,Y),proposition,Assumptions) :- 
	proof(X,proposition,Assumptions),
	proof(Y,proposition,Assumptions).

proof(function(variable(V),Expr),implies(X,Y), Assumptions) :- 
	proof(implies(X,Y),proposition,Assumptions),
	proof(Expr,Y,[assumption(variable(V),X)|Assumptions]).

proof(apply(F,X),B,Assumptions) :- 
	proof(X,A,Assumptions),
	proof(F,implies(A,B),Assumptions).
