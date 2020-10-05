:- use_module('stt.pl').

examples([
	[] # if_then_else(true,0,suc(0)):nat,
	[] # if_then_else(true,0,suc(0)) ~> 0,
	[] # if_then_else(true,0,suc(0)) ~>> 0,
	[] # if_then_else(false,0,suc(0)) ~>> suc(0),
	[] # nat_rec(0,0,bind(x(N),bind(x(R),suc(suc(x(R)))))):nat,
	[] # nat_rec(0,0,bind(x(N),bind(x(R),suc(suc(x(R)))))) ~> 0,
	[] # nat_rec(0,0,bind(x(N),bind(x(R),suc(suc(x(R)))))) ~>> 0,
	(
		[] # nat_rec(0,0,bind(x(N),bind(x(R),suc(suc(x(R)))))) ~> What,
		What == 0
	),
	[] # nat_rec(suc(0),0,bind(x(N),bind(x(R),suc(suc(x(R)))))) ~>> suc(suc(0)),
	[] # nat_rec(suc(suc(0)),0,bind(x(N),bind(x(R),suc(suc(x(R)))))) ~>> suc(suc(suc(suc(0)))),
	\+([] # nat_rec(suc(suc(0)),0,bind(x(N),bind(x(R),suc(suc(x(R)))))) ~>> suc(suc(suc(0)))),
	[] # elim(list(bool),[true,false],0,bind(_,bind(_,bind(x(R),suc(x(R)))))):nat,
	[] # elim(list(bool),[true,false],0,bind(_,bind(_,bind(x(R),suc(x(R))))))~>>suc(suc(0)),
	[] # suc(suc(0)) = elim(list(bool),[true,false],0,bind(_,bind(_,bind(x(R),suc(x(R))))))
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
