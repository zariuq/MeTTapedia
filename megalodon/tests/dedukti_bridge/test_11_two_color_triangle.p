% 2-coloring a triangle is impossible; stresses clause load beyond toy size
fof(coloring_a, axiom, red(a) | blue(a)).
fof(coloring_b, axiom, red(b) | blue(b)).
fof(coloring_c, axiom, red(c) | blue(c)).
fof(no_both_a, axiom, ~(red(a) & blue(a))).
fof(no_both_b, axiom, ~(red(b) & blue(b))).
fof(no_both_c, axiom, ~(red(c) & blue(c))).
fof(edge_ab, axiom, edge(a,b)).
fof(edge_bc, axiom, edge(b,c)).
fof(edge_ca, axiom, edge(c,a)).
fof(edge_sym1, axiom, edge(a,b) => edge(b,a)).
fof(edge_sym2, axiom, edge(b,c) => edge(c,b)).
fof(edge_sym3, axiom, edge(c,a) => edge(a,c)).
fof(edge_constraint1, axiom, edge(a,b) => ((~red(a) | ~red(b)) & (~blue(a) | ~blue(b)))).
fof(edge_constraint2, axiom, edge(b,c) => ((~red(b) | ~red(c)) & (~blue(b) | ~blue(c)))).
fof(edge_constraint3, axiom, edge(c,a) => ((~red(c) | ~red(a)) & (~blue(c) | ~blue(a)))).
fof(goal, conjecture, $false).
