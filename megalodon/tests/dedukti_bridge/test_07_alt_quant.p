% Alternating quantifiers: !X p(X) and ?Y ~p(Y) are inconsistent
fof(all_p, axiom, ![X]: p(X)).
fof(ex_not_p, axiom, ?[Y]: ~ p(Y)).
fof(goal, conjecture, $false).
