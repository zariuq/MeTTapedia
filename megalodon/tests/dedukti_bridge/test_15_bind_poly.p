% Typed binders: symmetry plus a Skolemized exists
fof(sym, axiom, ![X,Y]: X = Y => Y = X).
fof(exists_wit, axiom, ?[Z]: h(Z) = Z).
fof(goal, conjecture, $false | $false).  % trivial unsat to force processing
