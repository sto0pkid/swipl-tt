:- module(
	util, 
	[
		list_to_tuple/2,
		tuple_to_list/2,
		write_to/2,
		read_from/2
	]).

list_to_tuple([], true). % hmmm...
list_to_tuple([X], X) :- !.
list_to_tuple([X | Xs], (X, Xs_Tuple)) :-
	list_to_tuple(Xs, Xs_Tuple).

tuple_to_list(X, [X]) :- var(X), !. % hmmm...
tuple_to_list((X, Rest), [X | LRest]) :-
	!,
	tuple_to_list(Rest, LRest).
tuple_to_list(X, [X]).

write_to(File_Path, X) :-
	open(File_Path, write, Stream),
	write(Stream, X),
	close(Stream).

read_from(File_Path, X) :-
	open(File_Path, read, Stream),
	read_string(Stream, _, X),
	close(Stream).
