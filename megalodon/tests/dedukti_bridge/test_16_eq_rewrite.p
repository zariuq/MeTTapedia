% Equality rewrite use: a=b, substitution axiom, p(b), ~p(a)
fof(eq_ab, axiom, a = b).
fof(subst, axiom, ![X,Y]: X = Y => ((p(X) => p(Y)) & (p(Y) => p(X)))).
fof(subst_direct, axiom, a = b => (p(b) => p(a))).
fof(p_at_b, axiom, p(b)).
fof(goal, conjecture, ~p(a)).
