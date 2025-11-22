% Degree Bound from No K-Independent Set
%
% If a triangle-free graph has no k-independent set,
% then every vertex has degree < k.
%
% Proof: Suppose vertex v has k neighbors n1, ..., nk.
% By neighborhood independence (triangle-free), n1, ..., nk are pairwise non-adjacent.
% So {n1, ..., nk} is a k-independent set. Contradiction.

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% Triangle-free implies neighbors of any vertex are independent
fof(neighbors_indep, axiom,
    ![V,X,Y]: ((adj(V,X) & adj(V,Y) & X != Y) => ~adj(X,Y))).

% No 5-independent set (for testing with k=5)
fof(no_5_indep, axiom,
    ![A,B,C,D,E]:
    ((A != B & A != C & A != D & A != E &
      B != C & B != D & B != E &
      C != D & C != E &
      D != E) =>
     (adj(A,B) | adj(A,C) | adj(A,D) | adj(A,E) |
      adj(B,C) | adj(B,D) | adj(B,E) |
      adj(C,D) | adj(C,E) |
      adj(D,E)))).

% 5 distinct vertices representing neighbors of v
fof(distinct_neighbors, axiom,
    n1 != n2 & n1 != n3 & n1 != n4 & n1 != n5 &
    n2 != n3 & n2 != n4 & n2 != n5 &
    n3 != n4 & n3 != n5 &
    n4 != n5).

% v is adjacent to all of n1, n2, n3, n4, n5
fof(v_adj_all, axiom,
    adj(v, n1) & adj(v, n2) & adj(v, n3) & adj(v, n4) & adj(v, n5)).

% v is distinct from its neighbors
fof(v_distinct, axiom,
    v != n1 & v != n2 & v != n3 & v != n4 & v != n5).

% Goal: derive contradiction
% The 5 neighbors form a 5-independent set (by neighbors_indep),
% contradicting no_5_indep
fof(goal, conjecture, $false).
