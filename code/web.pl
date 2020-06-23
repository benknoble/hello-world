% vim: ft=prolog
:- use_module(library(http/http_open)).
:- use_module(library(sgml)).
:- use_module(library(xpath)).

hacker_title(Title) :-
    http_open("https://news.ycombinator.com", S, []),
    load_html(stream(S), DOM, []),
    xpath(DOM, //a(@class = storylink, text), Title).
