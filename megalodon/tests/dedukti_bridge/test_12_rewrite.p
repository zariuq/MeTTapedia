% Functional equivalence: f(X)<->g(X), f(a), ~g(a) is inconsistent
fof(def_f, axiom, ![X]: (f(X) <=> g(X))).
fof(fa, axiom, f(a)).
fof(ng, axiom, ~g(a)).
fof(goal, conjecture, $false).
