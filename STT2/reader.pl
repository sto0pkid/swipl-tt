:- use_module('./parser.pl',[]).
:- use_module('./swipl_stt_judgements6.pl',[gen_rules/2]).
:- use_module('./util.pl', [tuple_to_list/2]).

parse(File_Path, Parsed) :-
	open(File_Path, read, Stream),
	read_string(Stream, _, Input_String),
	string_codes(Input_String, Input_Codes),
	phrase(parser:well_formed(Parsed), Input_Codes).

example(Parsed, Types_Rules) :- 
	parse("parser_example.tt", Parsed),
	maplist(gen_rules, Parsed, Types_Rules),
	maplist(
		[Decl, Type_Rules, Type_Rules_Str]>>(
			maplist(
				[Rule_Type, Rules_Str]>>(
					get_dict(Rule_Type, Type_Rules, X),
					write_rules(Rule_Type-X, Rules_Str)
				),
				[formation, introduction, elimination, beta, eta],
				Type_Rules_Strs
			),
			get_dict(name, Decl, Name),
			format(string(Comment), "/*~n * ~w~n */", [Name]),
			atomics_to_string([Comment | Type_Rules_Strs],"\n\n\n",Type_Rules_Str)
		),
		Parsed,
		Types_Rules,
		Types_Rules_Strs
	),
	atomics_to_string(Types_Rules_Strs, "\n\n\n\n", Output),
	open("generated_rules.pl",write,Stream),
	write(Stream, Output),
	close(Stream).

write_rules(Type-Rules, Rules_Str) :-
	maplist(write_rule, Rules, Rules_Strs),
	atomics_to_string(Rules_Strs, "\n\n", Rules_Str0),
	format(string(Rules_Str), "% ~w~n~w",[Type, Rules_Str0]).

write_rule((Head :- Body), Rule_Str) :-
	!,
	tuple_to_list(Body, Body_List),
	maplist(
		[Body_Item, Body_Item_Str]>>(
			format(string(Body_Item_Str), "\t~w", [Body_Item])
		), 
		Body_List, 
		Body_Strs
	),
	atomics_to_string(Body_Strs, "\n", Body_Str),
	format(string(Rule_Str), "~w :-\n~w.", [Head, Body_Str]).

write_rule(Head, Rule_Str) :-
	format(string(Rule_Str), "~w.", [Head]).
