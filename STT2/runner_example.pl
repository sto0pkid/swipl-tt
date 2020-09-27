:- use_module('reader.pl', [parse/2]).
:- use_module('generator.pl', [gen_rules/2]).
:- use_module('rule_formatter.pl', [format2/3]).
:- use_module('util.pl', [write_to/2]).

example(Parsed, Rules) :- 
	parse("example.tt", Parsed),
	maplist(gen_rules, Parsed, Rules),
	format2(type_decl, (Parsed, Rules), Output),
	write_to("generated_rules.pl", Output).
