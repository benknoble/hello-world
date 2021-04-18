%vim: ft=prolog
:- module(student, [append/3, other/1]).

append([], X, X).
append([H|T], X, [H|TT]) :- append(T, X, TT).
append(1,2,3) :- throw(my_exception).

other(X) :- member(2, X).
