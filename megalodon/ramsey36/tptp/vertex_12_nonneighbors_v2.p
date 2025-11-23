% TPTP: Verify vertex_has_12_nonneighbors
%
% In 18-vertex triangle-free graph with no 6-indep:
% Every vertex has degree <= 5, hence >= 12 non-neighbors
%
% The key: if v has 6+ neighbors, they form a 6-indep set (triangle-free)

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% No 6-independent set
fof(no_6_indep, axiom,
  ![A,B,C,D,E,F]:
    ((A != B & A != C & A != D & A != E & A != F &
      B != C & B != D & B != E & B != F &
      C != D & C != E & C != F &
      D != E & D != F &
      E != F) =>
     (adj(A,B) | adj(A,C) | adj(A,D) | adj(A,E) | adj(A,F) |
      adj(B,C) | adj(B,D) | adj(B,E) | adj(B,F) |
      adj(C,D) | adj(C,E) | adj(C,F) |
      adj(D,E) | adj(D,F) |
      adj(E,F)))).

% Suppose v0 has 6 distinct neighbors n1-n6
fof(distinct_neighbors, axiom,
  n1 != n2 & n1 != n3 & n1 != n4 & n1 != n5 & n1 != n6 &
  n2 != n3 & n2 != n4 & n2 != n5 & n2 != n6 &
  n3 != n4 & n3 != n5 & n3 != n6 &
  n4 != n5 & n4 != n6 &
  n5 != n6).

fof(v0_adj_n1, axiom, adj(v0, n1)).
fof(v0_adj_n2, axiom, adj(v0, n2)).
fof(v0_adj_n3, axiom, adj(v0, n3)).
fof(v0_adj_n4, axiom, adj(v0, n4)).
fof(v0_adj_n5, axiom, adj(v0, n5)).
fof(v0_adj_n6, axiom, adj(v0, n6)).

% Goal: derive contradiction
% The neighbors n1-n6 are pairwise non-adjacent (by triangle-free)
% Hence they form a 6-indep set, contradicting no_6_indep

fof(goal, conjecture, $false).
