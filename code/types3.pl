%vim:ft=prolog

:- set_prolog_flag(occurs_check, true).

type(N, _, int) :- catch(N in inf..sup, error(type_error(integer, N), _), false).
type(plus(L, R), Env, int) :- type(L, Env, int), type(R, Env, int).
type(zerop(X), Env, bool) :- type(X, Env, int).
type(if(Ts, Th, El), Env, T) :- type(Ts, Env, bool), type(Th, Env, T), type(El, Env, T).
type(nil, _, list(_)).
type(cons(H, T), Env, list(Ts)) :- type(H, Env, Ts), type(T, Env, list(Ts)).
type(nilp(L), Env, bool) :- type(L, Env, list(_)).
type(head(L), Env, T) :- type(L, Env, list(T)).
type(tail(L), Env, list(T)) :- type(L, Env, list(T)).
type(pair(A, B), Env, tuple(Ta, Tb)) :-
    type(A, Env, Ta),
    type(B, Env, Tb).

type(first(X), Env, T) :-
    type(X, Env, tuple(T, _)).

type(second(X), Env, T) :-
    type(X, Env, tuple(_, T)).

type(name(X), Env, T) :-
    in_env(binding(X, T), Env).

type(proc(X, B), Env, func(Tin, Tout)) :-
    type(B, [binding(X, Tin) | Env], Tout).

type(invoke(F, A), Env, Tresult) :-
    type(F, Env, func(Targ, Tresult)),
    type(A, Env, Targ).

% strict Z combinator is un-typable
% type(proc(f, invoke(proc(x, invoke(name(f), proc(v, invoke(invoke(name(x), name(x)), name(v))))),
%                     proc(x, invoke(name(f), proc(v, invoke(invoke(name(x), name(x)), name(v))))))),
% [], T).

% % but "fix" is
% type(fix(F), Env, T) :-
%     type(F, Env, func(T, T)).

% here's map
% type(fix(proc(self, proc(f, proc(xs,
%   if(nilp(name(xs)),
%      nil,
%      cons(invoke(name(f), head(name(xs))),
%           invoke(invoke(name(self), name(f)),
%                  tail(name(xs))))))))),
% [], T)

in_env(Binding, [Binding|_]) :- !. % only keep the first occurrence, no backtracking
in_env(Binding, [_|L]) :- in_env(Binding, L).
