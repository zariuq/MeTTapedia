% TPTP problem for triangle_free_no_3clique
%
% Given: triangle_free (no x,y,z with R(x,y), R(y,z), R(x,z))
% Given: A 3-clique exists (a,b,c all distinct and all pairwise R-related)
% Goal: False

% Triangle-free property
fof(triangle_free, axiom,
    ![X,Y,Z]: ~(r(X,Y) & r(Y,Z) & r(X,Z))).

% 3-clique witness: three distinct elements
fof(distinct_ab, axiom, a != b).
fof(distinct_bc, axiom, b != c).
fof(distinct_ac, axiom, a != c).

% All pairs in the clique are related
fof(clique_ab, axiom, r(a,b)).
fof(clique_bc, axiom, r(b,c)).
fof(clique_ac, axiom, r(a,c)).

% Goal: derive contradiction
fof(goal, conjecture, $false).
