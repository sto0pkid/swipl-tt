:- consult('stt3.pl').

examples([
	[] # 0 type,
	[] # 1 type,
	[] # null:1,
	[A type, B type] # A + B type,
	[] # left null : 1 + 1,
	[] # right null : 1 + 1,
	[] # (null,null) : 1 * 1,
	[] # \[x(1)]>>null : 1 -> 1,
	[] # \[x(1)]>>x(1) : 1 -> 1,
	[] # mu[x(1)]>>(1+x(1)) type,
	[] # fold (left null) : mu[x(1)]>>(1 + x(1)),
	[] # fold (right (fold (left null))) : mu [x(1)]>>(1 + x(1)),
	[] # unfold (fold (left null)) : 1 + mu[x(1)]>>(1 + x(1)),
	[] # unfold (fold (left null)) ~>> left null,
	[] # left null : 1 + mu[x(1)]>>(1 + x(1))
]).

run(Results) :-
	examples(Examples),
	findall(
		Result,
		(
			member(Example, Examples),
			format("Trying: ~w~n",[Example]),
			(call(Example)->Result=true;Result=false),
			format("Result: ~w~n~n", [Result])
		),
		Results
	),
	writeln(Results).
