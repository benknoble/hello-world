% vim: ft=prolog
:- set_prolog_flag(occurs_check, true).

:- op(700, xfy, ->).
:- op(900, xfx, :).
:- op(910, xfx, =>).
:- op(920, xfx, in).
:- op(300, yfx, $).

X in [X | _] :- !.
X in [_ | L] :- X in L.

/* STLC */

Γ => var(X) : Ty :-
    (X:Ty) in Γ, !.

Γ => lam(X, T2) : Ty1 -> Ty2 :-
    [X:Ty1 | Γ] => T2 : Ty2.

Γ => T1 $ T2 : Ty2 :-
    Γ => T1 : Ty1 -> Ty2,
    Γ => T2 : Ty1.
