/*

*/

theorem(X,[X|_]).
theorem(X,[Y|Assumptions]) :- X \= Y, theorem(X,Assumptions).

% reification of `false`; principle of explosion
theorem(_, Assumptions) :- theorem(bottom,Assumptions).

% reification of `true`
theorem(top,_).

% reification of `,`
theorem(conjunction(X,Y), Assumptions) :- theorem(X,Assumptions), theorem(Y,Assumptions).
theorem(X,Assumptions) :- theorem(conjunction(X,_),Assumptions).
theorem(Y,Assumptions) :- theorem(conjunction(_,Y),Assumptions).

% reification of `;`
theorem(disjunction(X,_), Assumptions) :- theorem(X,Assumptions).
theorem(disjunction(_,Y), Assumptions) :- theorem(Y,Assumptions).
theorem(C,Assumptions) :- theorem(disjunction(X,Y),Assumptions),theorem(C,[X|Assumptions]),theorem(C,[Y|Assumptions]).

% reification of `:-`
theorem(implies(X,Y), Assumptions) :- theorem(Y,[X|Assumptions]).
theorem(Y,Assumptions) :- theorem(X,Assumptions), theorem(implies(X,Y),Assumptions).
