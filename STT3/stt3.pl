% _#_ : Context -> Judgement -> Prop
:- op(999, xfx, user:'#').

% _->_ : Type -> Type -> Judgement
:- op(997, xfx, user:'->').

% _~>_ : Term -> Term -> Judgement
:- op(998, xfx, user:'~>').

% _~>>_ : Term -> Term -> Judgement
:- op(998, xfx, user:'~>>').

% _=_ : Term -> Term -> Judgement

% _type : Term -> Judgement
:- op(998, xf, user:'type').

% _:_ : Term -> Term -> Judgement

% x(_) : Label -> Variable

% \ (_,_) : Variable * Term -> not quite a term

% _@=_ : Term -> Term -> Prop
:- op(998, xfx, user:'@=').

% left : Term -> Term
:- op(399, fx, user:'left').

:- op(399, fx, user:'right').

:- op(399, fx, user:'fold').

:- op(399, fx, user:'unfold').

:- op(399, fx, user:'abort').

:- op(399, fx, user:'fst').

:- op(399, fx, user:'snd').

:- op(399, fx, user:'mu').

:- op(399, fx, user:'\\').

:- op(398, xfx, user:'>>').



% CAPTURE-AVOIDING SUBSTITUTION
% substitute
% substitute Var for Replacement in Term to get New_Term
% trying to make it run bidirectionally; 
%  * elimination rule for mu types assumes that it does

substitute(x(X), For, x(X), For).
substitute(x(Y), _, x(X), x(X)) :- X \= Y, !.

substitute(x(Y), For, [x(X)]>>Expr, [x(Fresh)]>>Expr_Sub) :-
	nonvar(X), nonvar(Expr),
	!,
	gensym(x,Fresh),
	substitute(x(X), x(Fresh), Expr, Expr_Fresh),
	substitute(x(Y), For, Expr_Fresh, Expr_Sub).

substitute(x(Y), For, [x(X)]>>Expr, [x(Fresh)]>>Expr_Sub) :-
	var(X), var(Expr), nonvar(Fresh),nonvar(Expr_Sub),
	!,
	gensym(x,X),
	substitute(x(Fresh), x(X), Expr_Sub, Expr_Fresh),
	substitute(x(Y), For, Expr, Expr_Fresh).



substitute(x(X), For, Term, New_Term) :-
	nonvar(For), nonvar(Term), Term \= x(_),
	!,
	Term =.. [F | Subterms],
	maplist(
		substitute(x(X),For),
		Subterms, New_Subterms
	),
	New_Term =.. [F | New_Subterms].

substitute(x(X), For, Term, New_Term) :-
	nonvar(For), nonvar(New_Term), New_Term \= x(_),
	New_Term =.. [F | New_Subterms],
	maplist(
		substitute(x(X),For),
		Subterms, New_Subterms
	),
	Term =.. [F | Subterms].



cong([Arg_1 | Args], [Arg_2 | Args], G) :-
	G # Arg_1 ~> Arg_2.
cong([Arg | Args_1], [Arg | Args_2], G) :-
	\+(G # Arg ~> _),
	cong(Args_1, Args_2, G).


% ALPHA EQUALITY
% TERM @= TERM
%
% terms are alpha-equal if they're identical up to variable renaming
% note: in De Bruijn index notation, alpha-equal terms are syntactically identical
x(X) @= x(X) :- !.
[x(X)]>>A @= [x(Y)]>>B :-
	!,
	substitute(x(Y), x(X), B, B_Sub),
	A @= B_Sub.

T1 @= T2 :-
	T1 =.. [F1 | Args1],
	T2 =.. [F2 | Args2],
	F1 = F2,
	maplist(@=, Args1, Args2).




% HYPOTHESIS RULE
[X|_] # Y :- X == Y, !.
[X|G] # Y :- X \== Y, G # Y.

% CONGRUENCE RULE
_ # x(_) ~> _ :-
	!,
	false.

G # [x(X)]>>T1 ~> [x(X)]>>T2 :-
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
_ # 0 type.

_ # 1 type.

G # S + T type :- 
	G # S type,
	G # T type.

G # S * T type :- 
	G # S type,
	G # T type.

G # S -> T type :-
	G # S type,
	G # T type.

G # mu[x(X)]>>T type :- 
	[x(X) type | G] # T type.



% INTRODUCTION RULES
_ # null : 1.

G # left X : S + T :-
	G # S + T type,
	G # X:S.

G # right X : S + T :-
	G # S + T type,
	G # X:T.

G # (X,Y) : S * T :-
	G # S * T type,
	G # X:S,
	G # Y:T.

G # \[x(X)]>>E : S -> T :-
	G # S -> T type,
	[x(X):S|G] # E:T.

G # fold E : mu[x(X)]>>T :-
	G # mu[x(X)]>>T type,
	substitute(x(X), mu[x(X)]>>T, T, T_Sub),
	G # E:T_Sub.


% ELIMINATION RULES
G # abort E :_ :-
	G # E:0.

G # case(P, [x(X)]>>L, [x(Y)]>>R):C :-
	G # P:S + T,
	[ x(X):S | G] # L:C,
	[ x(Y):T | G] # R:C.

G # fst P : S :- G # P: S * _.
G # snd P : T :- G # P: _ * T.

G # apply(F,X):T :- G # X:S, G # F:S -> T.

G # unfold O : E :-
	substitute(x(X), mu [x(X)]>>T, T, E),
	G # O : mu [x(X)]>>T.



% BETA RULES
_ # case(left A, [x(X)]>>L, _) ~> L_Sub :-
	substitute(x(X), A, L, L_Sub).

_ # case(right B, _, [x(Y)]>>R) ~> R_Sub :-
	substitute(x(Y), B, R, R_Sub).

_ # fst (X,_) ~> X.

_ # snd (_,Y) ~> Y.

_ # apply(\[x(V)]>>E, X) ~> E_Sub :-
	substitute(x(V), X, E, E_Sub).

_ # unfold (fold O) ~> O.


% ETA RULES
G # abort E ~> E :-
	G # E:0.

G # case(P, [x(X)]>>(left x(X)), [x(Y)]>>(right x(Y))) ~> P :-
	G # P: _ + _.

G # (fst P, snd P) ~> P :-
	G # P: _ * _.

G # \[x(X)]>>apply(F, x(X)) ~> F :-
	G # F: _ -> _.

G # fold (unfold O) ~> O :-
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
