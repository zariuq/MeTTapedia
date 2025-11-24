% Comments and odd identifiers; exercises lexer stripping of % lines
% The proof is trivial but forces ~ and disjunction handling.
fof(excluded_middle, axiom, ![X]: big_Q(X) | ~ big_Q(X)).
fof(assert_false, axiom, ~ big_Q(c0)).
fof(force_true, axiom, big_Q(c0)).
fof(goal, conjecture, $false).
