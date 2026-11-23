:- module(gold_finite_terms, [same/2, value/2, wire/2, observed/2]).
:- use_module(library(chr)).
:- chr_constraint same/2, value/2, wire/2, observed/2.

% All admitted inputs are finite terms; binding must not introduce a cycle.
bind @ same(Left, Right) <=> unify_with_occurs_check(Left, Right).
agree @ value(Key, Kept) \ value(Key, Other) <=> same(Kept, Other).
forward @ wire(From, To), value(From, Value) ==> value(To, Value).
publish @ value(Key, Value) ==> observed(Key, Value).
