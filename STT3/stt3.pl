:- op(999, xfx, user:'#').
:- op(998, xfx, user:'->').
:- op(998, xfx, user:'~>').

% CAPTURE-AVOIDING SUBSTITUTION
substitute(x(X), x(Y), For,  For) :- X == Y, !.
substitute(x(X), x(Y),   _, x(X)) :- X \== Y, !.


substitute([], _, _, []) :- !.
substitute([Term | Rest], X, For, [Term_Sub | Rest_Sub]) :-
	!,
	substitute(Term, X, For, Term_Sub),
	substitute(Rest, X, For, Rest_Sub).
	
substitute(bind(X,Expr), Y, For, bind(Fresh,Expr_Sub)) :-
	!,
	substitute(Expr, X, Fresh, Expr_Fresh),
	substitute(Expr_Fresh, Y, For, Expr_Sub).

substitute(Term, X, For, Term_Sub) :-
	Term =.. [F | Args],
	substitute(Args, X, For, Args_Sub),
	Term_Sub =.. [F | Args_Sub].


cong([Arg_1 | Args], [Arg_2 | Args], G) :-
	G # Arg_1 ~> Arg_2.
cong([Arg | Args_1], [Arg | Args_2], G) :-
	\+(G # Arg ~> _),
	cong(Args_1, Args_2, G).



% HYPOTHESIS RULE
[X|_] # Y :- X == Y, !.
[X|G] # Y :- X \== Y, G # Y.

% CONGRUENCE RULE
_ # x(_) ~> _ :-
	!,
	false.

G # bind(x(X),T1) ~> bind(x(X),T2) :-
	!,
	G # T1 ~> T2.

G # T1 ~> T2 :-
	T1 =.. [F | Args_1],
	cong(Args_1, Args_2, G),
	T2 =.. [F | Args_2].


% NORMALIZATION
G # T1 ~>> NF :-
	G # T1 ~> T2,
	G # T2 ~>> NF.

G # NF ~>> NF :-
	\+(G # NF ~> _).



% EQUALITY
G # T1 = T2 :-
	G # T1 ~>> NF1,
	G # T2 ~>> NF2,
	NF1 @= NF2.






% http://www.cs.nott.ac.uk/~psztxa/publ/jcats07.pdf
% The authors allow variable types requiring them to explicitly define a notion of
% constant types. This seems to be for the purpose of making the mu types work because
% the bodies would have to contain variables.
% Instead I make `type/1` a judgement like normal and have explicit hypothetical judgements
% with #, so the variables in the mu types get added to a context/environment and so further
% occurrences of that variable in the body expression are treated effectively as constant
% types when checking the subexpression.
% Then isolated variable types are removed from the grammar and in the resulting grammar
% all types are constant, so we don't need to add this as an extra condition.


% FORMATION RULES
_ # type(1).
_ # type(1).
G # type(S + T) :- G # type(S), G # type(T).
G # type(S * T) :- G # type(S), G # type(T).
G # type(S -> T) :- G # type(S), G # type(T).
G # type(mu(bind(x(X),T))) :- [type(x(X))|G] # type(T).



% INTRODUCTION RULES
_ # null:1.

G # left(X):S+T :-
	G # type(S+T),
	G # X:S.

G # right(X):S+T :-
	G # type(S+T),
	G # X:T.

G # (X,Y):S*T :-
	G # type(S*T),
	G # X:S,
	G # Y:T.

G # lambda(bind(x(X),E)):S->T :-
	G # type(S->T),
	[x(X):S|G] # E:T.

G # intro(E):mu(bind(x(X),T)) :- 
	substitute(T,x(X),mu(bind(x(X),T)),T_Sub),
	G # E:T_Sub.




% ELIMINATION RULES
G # abort(F):C :-
	G # F:0.

G # case(P, bind(x(X),L), bind(x(Y),R)):C :-
	G # P:S+T,
	[x(X):S|G] # L:C,
	[x(Y):T|G] # R:C.

G # fst(P):S :- G # P:S*_.
G # snd(P):T :- G # P:_*T.

G # apply(F,X):T :- G # X:S, G # F:S->T.

G # unfold(O):E :-
	G # O:mu(bind(x(X),T)),
	substitute(T,x(X),mu(bind(x(X),T)),E).



% BETA RULES
_ # case(left(A), bind(x(X),L), _) ~> L_Sub :-
	substitute(L,x(X),A,L_Sub).

_ # case(right(B), _, bind(x(Y),R)) ~> R_Sub :-
	substitute(R,x(Y),B,R_Sub).

_ # fst((X,_)) ~> X.

_ # snd((_,Y)) ~> Y.

_ # apply(lambda(bind(x(X),E)), X) ~> E_Sub :-
	substitute(E,x(X),X,E_Sub).

_ # unfold(fold(O)) ~> O.


% ETA RULES
G # abort(F) ~> F :-
	G # F:0.

G # case(P, bind(x(X),left(x(X))), bind(x(Y),right(x(Y)))) ~> P :-
	G # P:_+_.

G # (fst(P),snd(P)) ~> P :-
	G # P:_*_.

G # lambda(bind(x(X),apply(F,x(X)))) ~> F :-
	G # F:_->_.

G # fold(unfold(O)) ~> O :-
	G # O:mu(_).


/*
Empty		= 0

Unit		= 1
null		= null

Bool		= 1+1
true		= left(null)
false		= right(null)

Nat 		= mu(bind(x(X),1+x(X)))
		= 1 + Nat
		= 1 + (1 + Nat)
		= 1 + (1 + (1 + ....)))

0		= intro(left(null))
1		= intro(right(intro(left(null))))
2		= intro(right(intro(right(intro(left(null))))))


List A 		= mu(bind(x(X),1+A*x(X)))
		= 1 + A*(List A)
		= 1 + A + A*A*(List A)
		= 1 + A + A*A + A*A*A + ....

[]		= intro(left(null))
[x]		= intro(right(intro(left(x))))
[x,y]		= intro(right(intro(right(intro(left((x,y)))))))



BinTree A 	= mu(bind(x(X),1+A*A*x(X)))
		= 1 + A*A*(BinTree A)
		= 1 + A*A + A*A*A*A*(BinTree A)
		= 1 + A*A + A*A*A*A + ...

*/
