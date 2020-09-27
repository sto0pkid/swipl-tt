:- use_module('reader.pl', [parse/2]).
:- use_module('generator.pl', [gen_rules/2]).
:- use_module('rule_formatter.pl', [format2/3]).
:- use_module('util.pl', [write_to/2]).

stt2_to_prolog(Input_Path) :-
	parse(Input_Path, Parsed),
	maplist(gen_rules, Parsed, Rules),
	format2(type_decls, (Parsed, Rules), Output),
	write(Output).
