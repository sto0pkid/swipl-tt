:- use_module(library(dcg/basics)).
:- use_module(library(dcg/high_order)).
/*
data name(T1,...,Tk):
	intro1 : ArgT11 -> ... -> ArgT1(N_1) -> name(T1, ..., Tk)
	...
	introM : ArgTM1 -> ... -> ArgT(N_M) -> name(T1, ..., Tk)
*/

any([]) --> [].
any([L|Ls]) --> [L], any(Ls).

alpha --> [C], {code_type(C, alpha)}.
alpha(C) --> [C], {code_type(C, alpha)}.

alphanum --> alpha ; digit.
alphanum(C) --> alpha(C) ; digit(C).

id_sym --> alphanum ; "_" ; "-".

id_sym(Sym) --> alphanum(Sym).
id_sym(95) --> "_".
id_sym(47) --> "-".

id_syms --> id_sym.
id_syms --> id_sym, id_syms.

id_syms([]) --> [].
id_syms([Sym | Rest]) --> id_sym(Sym), id_syms(Rest).

id([First | Rest]) --> alpha(First), id_syms(Rest).

id --> alpha, id_syms.

term(Name, Args) --> 
	id(Name_Codes),
	sequence(
		("(", whites),
		id,
		(whites,",",whites),
		(whites, ")"),
		Args_Codes
	),
	{
		atom_codes(Name, Name_Codes),
		maplist(atom_codes, Args, Args_Codes)
	}.
arg_types(Arg_Types) --> 
	sequence(
		id,
		(whites,"->",whites),
		Arg_Types_Codes
	),
	{maplist(atom_codes, Arg_Types, Arg_Types_Codes)}.

form(Name, Params) --> "data", white, whites, term(Name, Params), whites, ":", whites.

intro(Name:Arg_Types) --> 
	"\t", id(Name_Codes), whites, ":", whites, arg_types(Arg_Types), whites, ("\n" ; eos),
	{atom_codes(Name, Name_Codes)}.

intros([]) --> [].
intros([Intro | Intros]) --> intro(Intro),  intros(Intros).

decl(_{name:Name,params:Params,intros:Intros}) --> form(Name, Params), "\n", intros(Intros).

example(Decl) :-
	string_codes("data n_ame(arg1, arg2,arg3) :\n\tintro1:nat  ->nat -> bool\n\tintro2:nat -> nat", Codes),
	phrase(decl(Decl), Codes).
