% vim: ft=prolog

/*
Valero's 5k Fun Run was held yesterday in the downtown district. Determine the
shirt color and hometown of each of the top runners, and match each to their
finishing time.

CLUES

1. Mathew finished 1 minute after Anthony.
2. The contestant in the white shirt was either Anthony or the runner who
   finished in 22 minutes.
3. The competitor from Kamrar finished sometime after the runner from Pierson.
4. Salvador finished 1 minute after the runner in the maroon shirt.
5. Greg finished 1 minute before the competitor in the white shirt.
6. The contestant from Corinth didn't wear the pink shirt.
7. The contestant who finished in 22 minutes was either the contestant from
   Kamrar or the contestant in the pink shirt.
8. The competitor who finished in 23 minutes wasn't from Corinth.
*/

:- use_module(library(lists)).

% Sol = [[Name, Color, Town] times 4]
% the list is ordered by finish time, which is then mapped to 21,22,23,24
solve(Sol) :-

    Sol = [[Name1, Color1, Town1],
           [Name2, Color2, Town2],
           [Name3, Color3, Town3],
           [Name4, Color4, Town4]],

    % puzzle constraints
    permutation([Name1, Name2, Name3, Name4], [anthony, greg, mathew, salvador]),
    permutation([Color1, Color2, Color3, Color4], [aquamarine, maroon, pink, white]),
    permutation([Town1, Town2, Town3, Town4], [corinth, janesville, kamrar, pierson]),

    %1
    nextto([anthony, _, _], [mathew, _, _], Sol),
    %2
    (member([anthony, white, _], Sol) ; nth1(2, Sol, [_, white, _])),
    %3
    (append(Left, Right, Sol),
        member([_, _, pierson], Left),
        member([_, _, kamrar], Right)),
    %4
    nextto([_, maroon, _], [salvador, _, _], Sol),
    %5
    nextto([greg, _, _], [_, white, _], Sol),
    %6
    \+member([_, pink, corinth], Sol),
    %7
    (nth1(2, Sol, [_, _, kamrar]) ; nth1(2, Sol, [_, pink, _])),
    %8
    \+nth1(3, Sol, [_, _, corinth]).
