/*

*/

theorem(X,[X|_]).
theorem(X,[Y|Assumptions]) :- X \= Y, theorem(X,Assumptions).

% reification of `false`; principle of explosion
theorem(_, Assumptions) :- theorem(bottom,Assumptions).

% reification of `true`
theorem(top,_).

% reification of `,`
theorem(and(X,Y), Assumptions) :- theorem(X,Assumptions), theorem(Y,Assumptions).
theorem(X,Assumptions) :- theorem(and(X,_),Assumptions).
theorem(Y,Assumptions) :- theorem(and(_,Y),Assumptions).

% reification of `;`
theorem(or(X,_), Assumptions) :- theorem(X,Assumptions).
theorem(or(_,Y), Assumptions) :- theorem(Y,Assumptions).
theorem(C,Assumptions) :- theorem(or(X,Y),Assumptions),theorem(C,[X|Assumptions]),theorem(C,[Y|Assumptions]).

% reification of `:-`
theorem(implies(X,Y), Assumptions) :- theorem(Y,[X|Assumptions]).
theorem(Y,Assumptions) :- theorem(X,Assumptions), theorem(implies(X,Y),Assumptions).


/*
* Issue: non-termination
*
*/
