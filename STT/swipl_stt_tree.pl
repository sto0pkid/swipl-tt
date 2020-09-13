:- module(swipl_stt_tree,[proof/3]).

/*
*
* Introducing variable binding. This sucks! Get rid of the "tree" thing but
* keep the variable binding.
*
*/


% hypothesis
proof(variable(V), X,[assumption(variable(V),X)|_]).

proof(variable(V), X,[assumption(variable(W),_)|Assumptions]) :- V \= W, proof(variable(V),X,Assumptions).



% reification of `false`
proof(tree(empty,[]),tree(proposition,[]),_).



% reification of `true`
proof(tree(top,[]),tree(proposition,[]),_).

proof(tree(top_intro1,[]), tree(top,[]),_).



% bool
proof(tree(bool,[]),tree(proposition,[]),_).

proof(tree(bool_intro1,[]), tree(bool,[]),_).

proof(tree(bool_intro2,[]), tree(bool,[]),_).


% reification of `,`
proof(tree(conjunction,[X,Y]),tree(proposition,[]),Assumptions) :- 
	proof(X, tree(proposition,[]), Assumptions),
	proof(Y, tree(proposition,[]), Assumptions).

proof(tree(conjunction_intro1,[XProof,YProof]),tree(conjunction,[X,Y]),Assumptions) :- 
	proof(tree(conjunction,[X,Y]),tree(proposition,[]),Assumptions),
	proof(XProof,X,Assumptions),
	proof(YProof,Y,Assumptions).

proof(tree(conjunction_elim1,[P]),X,Assumptions) :- 
	proof(P,tree(conjunction, [X,_]),Assumptions).

proof(tree(conjunction_elim2,[P]),Y,Assumptions) :- 
	proof(P,tree(conjunction, [_,Y]),Assumptions).



% reification of `;`
proof(tree(disjunction,[X,Y]),tree(proposition,[]),Assumptions) :-
	proof(X, tree(proposition,[]), Assumptions),
	proof(Y, tree(proposition,[]), Assumptions).

proof(tree(disjunction_intro1,[XProof]),tree(disjunction,[X,Y]),Assumptions) :- 
	proof(tree(disjunction,[X,Y]),tree(proposition,[]),Assumptions),
	proof(XProof,X,Assumptions).

proof(tree(disjunction_intro2,[YProof]),tree(disjunction,[X,Y]),Assumptions) :- 
	proof(tree(disjunction,[X,Y]),tree(proposition,[]),Assumptions),
	proof(YProof,Y,Assumptions).

proof(tree(disjunction_elim1, [P,binding(variable(V),Left),binding(variable(W),Right)]),C,Assumptions) :-
	proof(P,tree(disjunction,[X,Y]),Assumptions),
	proof(Left,C,[assumption(variable(V),X)|Assumptions]),
	proof(Right,C,[assumption(variable(W),Y)|Assumptions]).



% reification of `:-`
proof(tree(implication,[X,Y]),tree(proposition,[]),Assumptions) :-
	proof(X, tree(proposition,[]), Assumptions),
	proof(Y, tree(proposition,[]), Assumptions).

proof(tree(implication_intro1,[binding(variable(V),Expr)]),tree(implication,[X,Y]), Assumptions) :- 
	proof(tree(implication,[X,Y]),tree(proposition,[]),Assumptions),
	proof(Expr,Y,[assumption(variable(V),X)|Assumptions]).

proof(tree(implication_elim1,[F,X]),B,Assumptions) :- 
	proof(X,A,Assumptions),
	proof(F,tree(implication,[A,B]),Assumptions).
