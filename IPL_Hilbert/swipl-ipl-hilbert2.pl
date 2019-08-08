%theorem(X,[X|Assumptions]).
%theorem(X,[_|Rest]) :- theorem(X,Rest).
%theorem(implies(A,B),Assumptions) :- theorem(B,[A|Assumptions]).

theorem(Y) :- theorem(X), theorem(implies(X,Y)).
theorem(implies(A,implies(_,A))).
theorem(implies(implies(A,implies(B,C)),implies(implies(A,B),implies(A,C)))).
theorem(implies(conjunction(A,_),A)).
theorem(implies(conjunction(_,B),B)).
theorem(implies(A,implies(B,conjunction(A,B)))).
theorem(implies(A,disjunction(A,_))).
theorem(implies(B,disjunction(_,B))).
theorem(implies(implies(A,C),implies(implies(B,C),implies(disjunction(A,B),C)))).
theorem(implies(empty,_)).
