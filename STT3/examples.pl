:- consult('stt3.pl').

examples([
	[] # type(0),
	[] # type(1),
	[] # null:1,
	[type(A),type(B)] # type(A + B),
	[] # left(null):1+1,
	[] # right(null):1+1,
	[] # (null,null):1*1,
	[] # lambda(bind(x(1),null)):1->1,
	[] # lambda(bind(x(1),x(1))):1->1,
	[] # type(mu(bind(x(1),1+x(1)))),
	[] # fold(left(null)):mu(bind(x(1),1+x(1))),
	[] # fold(right(fold(left(null)))):mu(bind(x(1),1+x(1))),
	[] # unfold(fold(left(null))):1+mu(bind(x(1),1+x(1))),
	[] # unfold(fold(left(null)))~>>left(null),
	[] # left(null):1+mu(bind(x(1),1+x(1)))
]).

run(Results) :-
	examples(Examples),
	findall(
		Result,
		(
			member(Example, Examples),
			(call(Example)->Result=true;Result=false)
		),
		Results
	),
	writeln(Results).
