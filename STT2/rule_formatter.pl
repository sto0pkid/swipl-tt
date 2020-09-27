:- module(rule_formatter, [format2/3]).

:- use_module('util.pl', [tuple_to_list/2]).

format2(type_decl, (Parsed, Types_Rules), Output) :-
	maplist(
		[Decl, Type_Rules, Type_Rules_Str]>>(
			maplist(
				[Rule_Type, Rules_Str]>>(
					get_dict(Rule_Type, Type_Rules, X),
					format2(rules, Rule_Type-X, Rules_Str)
				),
				[formation, introduction, elimination, beta, eta],
				Type_Rules_Strs
			),
			get_dict(name, Decl, Name),
			format(string(Comment), "/*~n * ~w~n */", [Name]),
			atomics_to_string([Comment | Type_Rules_Strs],"\n\n\n",Type_Rules_Str)
		),
		Parsed, Types_Rules, Types_Rules_Strs
	),
	atomics_to_string(Types_Rules_Strs, "\n\n\n\n", Output).


format2(rule_head, Head,Head).

format2(rule_body, Body, Body_Str) :-
	tuple_to_list(Body, Body_List),
	maplist(
		[Body_Item, Body_Item_Str]>>(
			format(string(Body_Item_Str), "\t~w", [Body_Item])
		), 
		Body_List, Body_Strs
	),
	atomics_to_string(Body_Strs, "\n", Body_Str).


format2(rules, Type-Rules, Rules_Str) :-
	maplist(format2(rule), Rules, Rules_Strs),
	atomics_to_string(Rules_Strs, "\n\n", Rules_Str0),
	format(string(Rules_Str), "% ~w~n~w",[Type, Rules_Str0]).

format2(rule, (Head :- Body), Rule_Str) :-
	!,
	format2(rule_body, Body, Body_Str),
	format2(rule_head, Head, Head_Str),
	format(string(Rule_Str), "~w :-\n~w.", [Head_Str, Body_Str]).

format2(rule, Head, Rule_Str) :-
	format(string(Rule_Str), "~w.", [Head]).
