% vim: ft=prolog

:- module(boggle, [make_board/2, board_has_word/2]).

:- use_module(library(assoc)). % assoc-list (AVL trees) predicates
:- use_module(library(clpfd)). % #= and related constraints
:- use_module(library(lists)). % member
:- use_module(library(apply)). % maplist, foldl
:- use_module(library(yall)). % [x]>>f(x) lambda syntax

product(As, Bs, Cs) :-
    findall(A-B, (member(A, As), member(B, Bs)), Cs).

range(N, L) :-
    NN #= N-1,
    bagof(X, between(0, NN, X), L).

coords(N, Coords) :-
    range(N, ToN),
    product(ToN, ToN, Coords).

square(Xss, N) :-
    length(Xss, N),
    maplist([Xs]>>length(Xs, N), Xss).

make_board_fold_helper(Chars, X-Y, Acc, New) :-
    nth0(X, Chars, Row),
    nth0(Y, Row, Char),
    put_assoc(X-Y, Acc, Char, New).

make_board(Chars, B) :-
    square(Chars, N),
    coords(N, Coords),
    empty_assoc(B0),
    foldl(make_board_fold_helper(Chars), Coords, B0, B).

% +B, ?W
board_has_word(B, W) :-
    assoc_to_keys(B, Cs),
    member(C, Cs),
    board_has_word(B, W, C).

board_has_word(_, [], _).

board_has_word(B, [First|W], X-Y) :-
    get_assoc(X-Y, B, First),
    member(DX, [-1, 0, 1]),
    member(DY, [-1, 0, 1]),
    NewX #= X + DX,
    NewY #= Y + DY,
    del_assoc(X-Y, B, _, NewB),
    board_has_word(NewB, W, NewX-NewY).
