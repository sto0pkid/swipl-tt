:- module(
	fol_grammar,
	[
		proposition/1,
		term/1,
		variable/1,
		predicate/1,
		pretty/2
	]
).


proposition(forall(Var, Prop)) :- variable(Var), proposition(Prop).
proposition(exists(Var, Prop)) :- variable(Var), proposition(Prop).
proposition(and(Prop1, Prop2)) :- proposition(Prop1), proposition(Prop2).
proposition(or(Prop1, Prop2)) :- proposition(Prop1), proposition(Prop2).
proposition(implies(Prop1, Prop2)) :- proposition(Prop1), proposition(Prop2).
proposition(not(Prop)) :- proposition(Prop).
proposition(Prop) :- predicate(Prop).

variable('?'(_)).

term(V) :- variable(V).

/*
Signature: 
constants: [c], 
functions: [f/1, +/2, * /2]
relations: [P/1, R/2, =/2]
*/

term('+'(Arg1,Arg2)) :- term(Arg1), term(Arg2).
term('*'(Arg1,Arg2)) :- term(Arg1), term(Arg2).
term('f'(Arg1)) :- term(Arg1).
term('c'()).


predicate(Arg1=Arg2) :- term(Arg1), term(Arg2).
predicate('P'(Arg1)) :- term(Arg1).
predicate('R'(Arg1, Arg2)) :- term(Arg1), term(Arg2).


pretty(forall(Var, Prop), String) :-
	pretty(Var, VarString),
	pretty(Prop, PropString),
	format(atom(String), "∀~w,~w", [VarString, PropString]).

pretty(exists(Var, Prop), String) :-
	pretty(Var, VarString),
	pretty(Prop, PropString),
	format(atom(String), "∃~w,~w", [VarString, PropString]).

pretty(and(Prop1,Prop2), String) :-
	pretty(Prop1, Prop1String),
	pretty(Prop2, Prop2String),
	format(atom(String), "~w ∧ ~w", [Prop1String, Prop2String]).

pretty(or(Prop1,Prop2), String) :-
	pretty(Prop1, Prop1String),
	pretty(Prop2, Prop2String),
	format(atom(String), "~w ∨ ~w", [Prop1String, Prop2String]).

pretty(implies(Prop1,Prop2), String) :-
	pretty(Prop1, Prop1String),
	pretty(Prop2, Prop2String),
	format(atom(String), "~w -> ~w", [Prop1String, Prop2String]).

pretty(not(Prop), String) :-
	pretty(Prop, PropString),
	format(atom(String), "¬~w", [PropString]).

pretty(Arg1=Arg2, String) :-
	pretty(Arg1, Arg1String),
	pretty(Arg2, Arg2String),
	format(atom(String), "~w=~w", [Arg1String, Arg2String]).

pretty('R'(Arg1,Arg2), String) :-
	pretty(Arg1, Arg1String),
	pretty(Arg2, Arg2String),
	format(atom(String), "R(~w,~w)", [Arg1String, Arg2String]).

pretty('P'(Arg), String) :-
	pretty(Arg, ArgString),
	format(atom(String), "P(~w)", [ArgString]).

pretty('+'(Arg1,Arg2), String) :-
	pretty(Arg1, Arg1String),
	pretty(Arg2, Arg2String),
	format(atom(String), "~w + ~w", [Arg1String, Arg2String]).

pretty('*'(Arg1,Arg2), String) :-
	pretty(Arg1, Arg1String),
	pretty(Arg2, Arg2String),
	format(atom(String), "~w * ~w", [Arg1String, Arg2String]).

pretty('f'(Arg), String) :-
	pretty(Arg, ArgString),
	format(atom(String), "f(~w)", [ArgString]).

pretty('c'(), "c").

pretty('?'(V), String) :-
	atom_string(V, String).
