%vim: ft=prolog
:- module(grade, []).
:- set_prolog_flag(autoload, user).
:- use_module(student).
:- use_module(library(debug)).

test(Message, Goal) :- write('test: '), writeln(Message), assertion(Goal).

go :-
    test("empty lists", student:append([], [], [])),
    % test("special case", student:append(1, 2, 3)),
    % test("failure", student:append([1,2,3], [4,5,6], [])),
    % test("use of non-imported predicates", student:other([1,2])),
    test("normal", student:append([1,2], [3,4], [1,2,3,4])),
    halt(0).

prolog:assertion_failed(Reason, Goal) :-
    write(Reason), write(' '), writeln(Goal),
    halt(1).
