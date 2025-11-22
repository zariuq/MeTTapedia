% TPTP problem for good_graph_contradiction
% Goal: For any symmetric R on 18 vertices, if R is triangle-free and has no
% 6-independent set, derive False.
%
% This is the core of R(3,6) = 18: no such graph exists.
%
% Key insight from Cariolaro's proof:
% - A (3,6)-good graph on n vertices has >= n(n-1)/4 edges (degree argument)
% - Each vertex in triangle-free graph has independent neighborhood
% - Combined constraints force contradiction at n=18

% Vertices: 0-17 (18 vertices)
tff(vertex_type, type, v: $int > $tType).

% Adjacency relation (symmetric, irreflexive)
tff(adj_type, type, adj: ($int * $int) > $o).

% Symmetry
tff(adj_sym, axiom, ![X:$int, Y:$int]: (adj(X,Y) => adj(Y,X))).

% Irreflexivity
tff(adj_irref, axiom, ![X:$int]: ~adj(X,X)).

% Vertices are in range 0-17
tff(vertex_in_range, axiom, ![X:$int]: ((0 <= X & X < 18) => $true)).

% Triangle-free: no x,y,z with all three edges
tff(triangle_free, axiom,
    ![X:$int, Y:$int, Z:$int]:
      ((0 <= X & X < 18 & 0 <= Y & Y < 18 & 0 <= Z & Z < 18) =>
       ~(adj(X,Y) & adj(Y,Z) & adj(X,Z)))).

% No 6-independent set: for any 6 distinct vertices, at least one edge
% This is the complement of: exists 6 distinct vertices with no edges between them
%
% We assert: for all 6-tuples of distinct vertices in 0..17,
% at least one pair is adjacent

% Due to complexity, we encode this as:
% For every choice of 6 vertices a<b<c<d<e<f from 0..17,
% at least one of the 15 pairs is an edge

% Example for first 6-subset {0,1,2,3,4,5}:
tff(no_indep_0_1_2_3_4_5, axiom,
    (adj(0,1) | adj(0,2) | adj(0,3) | adj(0,4) | adj(0,5) |
     adj(1,2) | adj(1,3) | adj(1,4) | adj(1,5) |
     adj(2,3) | adj(2,4) | adj(2,5) |
     adj(3,4) | adj(3,5) |
     adj(4,5))).

% ... (would need all C(18,6) = 18564 such axioms for full problem)

% Derive contradiction
tff(goal, conjecture, $false).
