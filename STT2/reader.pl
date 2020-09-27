:- module(reader, [parse/2]).

:- use_module('./tt_lang_dcg.pl',[]).
:- use_module('./util.pl', [read_from/2]).

parse(File_Path, Parsed) :-
	read_from(File_Path, Input_String),
	string_codes(Input_String, Input_Codes),
	phrase(parser:well_formed(Parsed), Input_Codes).
