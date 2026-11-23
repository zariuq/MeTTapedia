:- module(compiler_pass_reference, [run/2]).
:- use_module(library(chr)).
:- use_module(library(http/json)).
:- chr_constraint constant/2, add/3, input/1, seen/1.

same_input @ constant(A,X) \ add(N,A,A) <=> Z is X+X, constant(N,Z).
two_inputs @ constant(A,X), constant(B,Y) \ add(N,A,B) <=>
    A \== B | Z is X+Y, constant(N,Z).
note_constant @ constant(N,_) ==> seen(N).

post([], _).
post([[Node,Name|Args]|Rest], Needed) :-
    ( memberchk(Node, Needed) -> Goal =.. [Name|Args], call(Goal) ; true ),
    post(Rest, Needed).

run(Needed, Seeds) :-
    post(Seeds, Needed),
    findall([Name|Args], (find_chr_constraint(C), C =.. [Name|Args]), Rows),
    msort(Rows, Sorted),
    json_write(current_output, Sorted), nl.
