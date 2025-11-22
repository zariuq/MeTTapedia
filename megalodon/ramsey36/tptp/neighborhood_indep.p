% Neighborhood Independence Lemma
%
% In a triangle-free graph, the neighborhood of any vertex is an independent set.
%
% Proof: If v is adjacent to both x and y, and x is adjacent to y,
%        then {v, x, y} form a triangle. Contradiction.

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% Goal: neighbors of any vertex are pairwise non-adjacent
% Stated as: if v is adjacent to both x and y (and x != y), then x and y are not adjacent
fof(neighborhood_indep, conjecture,
    ![V,X,Y]: ((adj(V,X) & adj(V,Y) & X != Y) => ~adj(X,Y))).
