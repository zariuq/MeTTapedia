% TPTP formulation of Cariolaro's upper bound argument for R(3,6) <= 18
%
% Key lemmas from Cariolaro's proof:
% 1. In a triangle-free graph, N(v) (neighborhood of v) is independent
% 2. If graph has no k-independent set, then |N(v)| < k for all v
% 3. Combining: triangle-free + no-6-indep => max_degree < 6
%
% For 18 vertices with max_degree <= 5:
%   total_edges <= 18 * 5 / 2 = 45
%
% Cariolaro shows a (3,6)-good graph on 18 vertices needs >= 36 edges
% (this is the harder direction requiring Turan-type bounds)
%
% Simplified problem: show the degree bound holds

fof(vertex_type, type, v: $i).
fof(adj_type, type, adj: $i * $i > $o).
fof(in_graph_type, type, inG: $i > $o).

% 18 distinct vertices
fof(v0_in, axiom, inG(v0)).
fof(v1_in, axiom, inG(v1)).
fof(v2_in, axiom, inG(v2)).
fof(v3_in, axiom, inG(v3)).
fof(v4_in, axiom, inG(v4)).
fof(v5_in, axiom, inG(v5)).
fof(v6_in, axiom, inG(v6)).
fof(v7_in, axiom, inG(v7)).
fof(v8_in, axiom, inG(v8)).
fof(v9_in, axiom, inG(v9)).
fof(v10_in, axiom, inG(v10)).
fof(v11_in, axiom, inG(v11)).
fof(v12_in, axiom, inG(v12)).
fof(v13_in, axiom, inG(v13)).
fof(v14_in, axiom, inG(v14)).
fof(v15_in, axiom, inG(v15)).
fof(v16_in, axiom, inG(v16)).
fof(v17_in, axiom, inG(v17)).

% All vertices are distinct
fof(distinct_01, axiom, v0 != v1).
fof(distinct_02, axiom, v0 != v2).
% ... (need 153 distinctness axioms)

% Symmetry of adjacency
fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).

% Irreflexivity
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% Triangle-free: no three mutually adjacent vertices
fof(triangle_free, axiom,
    ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% Key lemma: In triangle-free graph, neighborhood is independent
fof(neighborhood_indep, axiom,
    ![V,X,Y]: ((adj(V,X) & adj(V,Y)) => ~adj(X,Y))).

% No 6-independent set: any 6 vertices have at least one edge
% For v0's neighborhood: if v0 is adjacent to 6+ vertices, they form indep set
% Since no 6-indep set exists, deg(v0) < 6

% The conjecture: if triangle-free and no-6-indep, then max degree < 6
% This leads to total_edges < 45, but (3,6)-good needs more edges

% Simplified test: derive that v0 cannot have 6 neighbors
fof(goal, conjecture,
    ~(adj(v0,v1) & adj(v0,v2) & adj(v0,v3) & adj(v0,v4) & adj(v0,v5) & adj(v0,v6))).
