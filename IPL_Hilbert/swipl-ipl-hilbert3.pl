theorem(X,[X|_]).
theorem(X,[_|Rest]) :- theorem(X,Rest).
theorem(implies(A,B),Assumptions) :- theorem(B,[A|Assumptions]).

theorem(Y,G) :- theorem(X,G), theorem(implies(X,Y),G).
theorem(implies(A,implies(_,A)),_).
theorem(implies(implies(A,implies(B,C)),implies(implies(A,B),implies(A,C))),_).
theorem(implies(conjunction(A,_),A),_).
theorem(implies(conjunction(_,B),B),_).
theorem(implies(A,implies(B,conjunction(A,B))),_).
theorem(implies(A,disjunction(A,_)),_).
theorem(implies(B,disjunction(_,B)),_).
theorem(implies(implies(A,C),implies(implies(B,C),implies(disjunction(A,B),C))),_).
theorem(implies(empty,_),_).
