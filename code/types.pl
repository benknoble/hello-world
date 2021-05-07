% vim: ft=prolog

% typing relies on occurs check
:- set_prolog_flag(occurs_check, true).

% name(x) is variable reference
% proc(x, b) is λx.b (i.e., function with parameter x and body b)
% func(t1, t2) is the function type t1 → t2
% invoke(f, a) is f of a (i.e., f applied to a)

% % for cleaner syntax, use
% :- op(700, xfy, ->). % t1 -> t2 replaces func(t1, t2)
% :- op(900, xfx, :). % x : t replaces type/2, type(x, t)
% :- op(910, xfx, =>). % Env => x : t replaces type/3, type(Env, x, t).
% :- op(920, xfx, in_env). % x in_env Env replaces in_env(x, Env).
% :- op(300, yfx, $). % f $ x replaces invoke(f, a).

in_env(X, [X|_]) :- !. % only keep the first occurrence, no backtracking
in_env(X, [_|L]) :- in_env(X, L).

type(Env, name(X), T) :-
    in_env(type(X, T), Env).
    % !. % see cut in in_env: only first occurrence, no backtracking

type(Env, proc(X, B), func(T1, T2)) :-
    type([type(X, T1) | Env], B, T2).

type(Env, invoke(F, A), Tresult) :-
    type(Env, F, func(Targ, Tresult)),
    type(Env, A, Targ).

type(Env, pair(A, B), tuple(Ta, Tb)) :-
    type(Env, A, Ta),
    type(Env, B, Tb).

type(Env, first(X), T) :-
    type(Env, X, tuple(T, _)).

type(Env, second(X), T) :-
    type(Env, X, tuple(_, T)).

% base rules
% unit value
type(_, (/), unit).

% explicit type markers
type(Env, as(X, T), T) :- 
    type(Env, X, T).

type(Env, zerop(X), bool) :-
    type(Env, X, int).

type(Env, if(Test, Consequent, Alternate), T) :-
    type(Env, Test, bool),
    type(Env, Consequent, T),
    type(Env, Alternate, T).

% type(_, X, int) :- X in inf..sup.

type(_, 0, int).
% shorthands
type(_, 1, int).
type(_, 2, int).
type(_, 3, int).
type(_, 4, int).
type(_, 5, int).
type(_, 6, int).
type(_, 7, int).
type(_, 8, int).
type(_, 9, int).
type(_, 10, int).

type(Env, add1(X), int) :-
    type(Env, X, int).

type(Env, -(X, Y), int) :-
    type(Env, X, int),
    type(Env, Y, int).

type(_, nil, list(_)).
type(Env, cons(Head, Tail), list(T)) :-
    type(Env, Head, T),
    type(Env, Tail, list(T)).

type(Env, nilp(L), bool) :-
    type(Env, L, list(_)).

type(Env, head(L), T) :-
    type(Env, L, list(T)).

type(Env, tail(L), list(T)) :-
    type(Env, L, list(T)).
