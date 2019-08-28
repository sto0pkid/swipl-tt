:- use_module(swipl_stt_tree_tactics, [prove/3]).

examples([
	example(
		tree(implication,[variable(a),variable(a)]),
		[assumption(variable(a),tree(proposition,[]))]
	),
	example(
		tree(implication, [variable(a), tree(implication, [variable(b), variable(a)])]),
		[
			assumption(variable(a), tree(proposition,[])),
			assumption(variable(b), tree(proposition,[]))
		]
	),
	example(
		tree(implication, [variable(a), tree(implication, [variable(b), variable(b)])]),
		[
			assumption(variable(a), tree(proposition,[])),
			assumption(variable(b), tree(proposition,[]))
		]
	),
	example(
		tree(implication, [tree(conjunction, [variable(a), variable(b)]), variable(a)]),
		[
			assumption(variable(a), tree(proposition,[])),
			assumption(variable(b), tree(proposition,[]))
		]
	),
	example(
		tree(implication, [tree(conjunction, [variable(a), variable(b)]), variable(b)]),
		[
			assumption(variable(a), tree(proposition,[])),
			assumption(variable(b), tree(proposition,[]))
		]
	),
	example(
		tree(implication, [tree(conjunction, [variable(a), variable(b)]), tree(conjunction, [variable(b),variable(a)])]),
		[
			assumption(variable(a), tree(proposition,[])),
			assumption(variable(b), tree(proposition,[]))
		]
	),
	example(
		tree(implication, [tree(conjunction, [variable(a), variable(b)]), tree(conjunction, [variable(a),variable(b)])]),
		[
			assumption(variable(a), tree(proposition,[])),
			assumption(variable(b), tree(proposition,[]))
		]
	),
	example(
		tree(implication, [variable(a), tree(implication, [variable(b), tree(conjunction,[variable(a),variable(b)])])]),
		[
			assumption(variable(a), tree(proposition,[])),
			assumption(variable(b), tree(proposition,[]))
		]
	),
	example(
		tree(implication, [tree(conjunction, [variable(a), tree(conjunction,[variable(b),variable(c)])]), tree(conjunction, [tree(conjunction,[variable(a),variable(b)]),variable(c)])]),
		[
			assumption(variable(a), tree(proposition,[])),
			assumption(variable(b), tree(proposition,[])),
			assumption(variable(c), tree(proposition,[]))
		]

	),
	example(
		tree(implication, [tree(conjunction, [variable(a), variable(b)]), tree(disjunction, [variable(a),variable(b)])]),
		[
			assumption(variable(a), tree(proposition,[])),
			assumption(variable(b), tree(proposition,[]))
		]
	),
	example(
		tree(implication, [tree(implication, [variable(a), variable(b)]), tree(implication, [variable(a),variable(b)])]),
		[
			assumption(variable(a), tree(proposition,[])),
			assumption(variable(b), tree(proposition,[]))
		]
	)
]).

run :-
	%gtrace,
	examples(Examples),
	findall(
		_,
		(
			member(example(Proposition, Assumptions), Examples),
			run_example(Proposition, Assumptions)
		),
		_
	).

run_example(Proposition, Assumptions) :-
	pretty(Proposition, Proposition_String),
	format('Proposition: ~w~n',[Proposition_String]),
	(
		prove(Proposition, Proof, Assumptions)
	->
		(
			pretty(Proof, Proof_String),
			format('Proof:       ~w~n~n',[Proof_String])
		)
	;
		format('Fail~n~n')
	).


pretty(tree(implication,[X,tree(implication,[Y,Z])]),String) :-
	!,
	pretty2(X, XString),
	pretty(tree(implication,[Y,Z]), YZString),
	format(atom(String), "~w -> ~w", [XString, YZString]).

pretty(tree(implication,[X,Y]), String) :-
	pretty2(X, XString),
	pretty2(Y, YString),
	format(atom(String), "~w -> ~w",[XString, YString]).

pretty(tree(conjunction,[X,Y]), String) :-
	pretty2(X, XString),
	pretty2(Y, YString),
	format(atom(String), "~w ∧ ~w",[XString, YString]).

pretty(tree(disjunction,[X,Y]), String) :-
	pretty2(X, XString),
	pretty2(Y, YString),
	format(atom(String), "~w ∨ ~w",[XString, YString]).

pretty(variable(X), String) :-
	atom_string(X,String).

pretty(tree(implication_intro1,[binding(Variable,tree(implication_intro1,[binding(Variable2,Expr)]))]), String) :-
	!,
	pretty2(Variable, Var_String),
	pretty(tree(implication_intro1,[binding(Variable2,Expr)]), Expr_String),
	format(atom(String),"λ~w.~w",[Var_String, Expr_String]).

pretty(tree(implication_intro1,[binding(Variable,Expr)]), String) :-
	pretty2(Variable, Var_String),
	pretty2(Expr, Expr_String),
	format(atom(String),"λ~w.~w",[Var_String, Expr_String]).

pretty(tree(implication_elim1,[Function, Argument]), String) :-
	pretty2(Function, Function_String),
	pretty2(Argument, Argument_String),
	format(atom(String),"~w ~w",[Function_String, Argument_String]).

pretty(tree(conjunction_intro1,[X,Y]), String) :-
	pretty2(X, XString),
	pretty2(Y, YString),
	format(atom(String), "~w, ~w",[XString, YString]).

pretty(tree(conjunction_elim1,[X]), String) :-
	pretty2(X, XString),
	format(atom(String), "first ~w", [XString]).

pretty(tree(conjunction_elim2,[X]), String) :-
	pretty2(X, XString),
	format(atom(String), "second ~w", [XString]).

pretty(tree(disjunction_intro1,[X]), String) :-
	pretty2(X, XString),
	format(atom(String), "left ~w", [XString]).

pretty(tree(disjunction_intro2,[X]), String) :-
	pretty2(X, XString),
	format(atom(String), "right ~w", [XString]).


pretty2(variable(X), String) :-
	!,
	atom_string(X, String).

pretty2(Term, String) :-
	pretty(Term, Term_String),
	format(atom(String), "(~w)", [Term_String]).
