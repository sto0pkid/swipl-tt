:- module(base, []).

:- op(999, xfx, user:'~>').	% one step normalization
:- op(999, xfx, user:'~>>').	% full normalization


