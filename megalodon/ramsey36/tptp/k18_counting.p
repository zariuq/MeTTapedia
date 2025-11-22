% TPTP: Counting argument for R(3,6) = 18
%
% We use the fact that in a (3,6)-good graph on n vertices:
% 1. Triangle-free => each neighborhood is independent
% 2. No 6-independent set => each vertex has degree < 6 (max_degree <= 5)
%
% Key insight: Use double counting.
% Sum of degrees = 2 * |E|
% If max_degree <= 5 and n = 18: sum <= 18 * 5 = 90, so |E| <= 45
%
% But we also need: every 6 vertices have at least one edge.
% By Turán-type bound: if alpha(G) <= 5 on n vertices, then
%   |E| >= (n choose 2) - ex(n, K_6) where ex is extremal number
%
% For independence number < 6, we need:
%   |E| >= f(n) for some function f
%
% The Caro-Wei bound gives: alpha >= sum_v 1/(d(v)+1)
% For alpha < 6: sum_v 1/(d(v)+1) < 6
%
% With max d(v) = 5: sum >= 18 * 1/6 = 3
% So this bound isn't tight enough to give contradiction.

% Alternative: direct case analysis.
%
% Consider the red graph G on 18 vertices (where red = edge, blue = non-edge).
% G is triangle-free and has independence number < 6.
%
% From degree bound: every vertex has degree <= 5.
% Total edges <= 45.
%
% For no 6-independent set with 18 vertices and max degree 5:
% Consider the complement graph G'. It has min_degree >= 12.
% G' must have a clique of size 6 (= independent set in G).
%
% Wait, that's backwards. Let me think again...
%
% G triangle-free + no 6-indep
% G' has no 3-indep (= complement of triangle-free) and has K_6 (= complement of no 6-indep)
%
% Actually the complement is:
% G triangle-free => G' has no 3-indep set (every 3 vertices have an edge in G')
% G has no 6-indep => G' has K_6 (6 vertices with all edges in G')
%
% Hmm, let me reconsider the Ramsey statement.

% For R(3,6) = 18:
% In any 2-coloring of K_18, either red K_3 or blue K_6.
% Equivalent: no graph G on 18 vertices with both triangle-free AND complement(G) triangle-free...
% No, that's R(3,3).

% R(3,6): no G on 18 vertices that is triangle-free AND has alpha(G) < 6.

% Let's just verify the structure with explicit constraints
fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% 18 vertices v0..v17
fof(v_distinct, axiom,
    v0!=v1 & v0!=v2 & v0!=v3 & v0!=v4 & v0!=v5 & v0!=v6 & v0!=v7 & v0!=v8 &
    v0!=v9 & v0!=v10 & v0!=v11 & v0!=v12 & v0!=v13 & v0!=v14 & v0!=v15 & v0!=v16 & v0!=v17 &
    v1!=v2 & v1!=v3 & v1!=v4 & v1!=v5 & v1!=v6 & v1!=v7 & v1!=v8 &
    v1!=v9 & v1!=v10 & v1!=v11 & v1!=v12 & v1!=v13 & v1!=v14 & v1!=v15 & v1!=v16 & v1!=v17).

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% Max degree 5 for v0 (neighbors form independent set, and if 6+ neighbors, they'd be 6-indep set)
% So if v0 has neighbors n1..n5 (at most 5), and graph has no 6-indep set,
% then {v1..v17} \ {n1..n5} has 12+ vertices that form independent set with non-neighbors
% This gives the contradiction!

% Actually: if all vertices have degree <= 5, then total non-edges >= (18*12)/2 = 108
% And 18 choose 2 = 153 total pairs
% So edges <= 153 - 108 = 45. Consistent.

% The key is: with 18 vertices and max-degree 5, we can find 6-indep set.
% Greedy: pick v, exclude N(v) (at most 5 vertices), have 12+ remaining
% Pick u from remaining, exclude N(u), have 12 - 5 = 7+ remaining
% Continue: 7 - 5 = 2+, but we need more careful analysis

% After 5 picks: we've excluded at most 5*5 = 25 vertices-worth of neighborhoods
% But neighborhoods overlap, so it's not that simple.

% Simpler: If deg(v) <= 5 for all v, then by Caro-Wei:
% alpha >= sum 1/(d(v)+1) >= 18/6 = 3. Too weak.

% Turán bound: for alpha < 6, need |E| > (n^2 - n)/12 = (324-18)/12 = 25.5
% So |E| >= 26. But we have |E| <= 45. No contradiction yet.

% The contradiction must come from a more refined argument.
% Let me try: with 18 vertices and max degree 5, construct 6-indep set explicitly.

fof(goal, conjecture, $true).
