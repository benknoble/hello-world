% vim: ft=prolog

human(socrates).

mortal(X) :- human(X).

gen([true], true).
gen([G], (G -> P)) :- clause(G, Body), gen([Body], P).
gen([G1|T], (P1, T1)) :- gen(G1, P1), gen(T, T1).
