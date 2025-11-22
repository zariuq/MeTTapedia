% TPTP: Ramsey recursion argument for R(3,6) <= 18
%
% Key insight: Pick any vertex v in K_18. It has 17 neighbors.
% Color edges: red_degree(v) + blue_degree(v) = 17
%
% Case 1: red_degree(v) >= 6
%   The red neighborhood of v has 6+ vertices.
%   In that neighborhood, either:
%   - Two vertices are red-connected (with v, forms red K_3) ✓
%   - No two are red-connected (6 vertices form blue K_6 in complement)
%   But wait, we need R(2,6) = 6 here: among 6 vertices, either red edge or blue K_6
%
% Case 2: blue_degree(v) >= 14
%   The blue neighborhood has 14+ vertices.
%   Among these 14 vertices, by R(3,5) = 14:
%   Either red K_3 exists, or blue K_5 exists.
%   If blue K_5 exists in N_blue(v), add v to get blue K_6. ✓
%
% Case 3: red_degree(v) <= 5 AND blue_degree(v) <= 13
%   Then red_degree(v) + blue_degree(v) <= 18, but we have 17 neighbors
%   Actually 5 + 13 = 18 > 17, so this is possible!
%
% Need: red_deg + blue_deg = 17
% If red_deg <= 5, then blue_deg >= 12
% If blue_deg >= 12, in those 12 vertices we need either red K_3 or blue K_5
% R(3,5) = 14 > 12, so this doesn't immediately give contradiction

% The tighter argument: use R(3,5) = 14
% For any v: either red_deg(v) >= 4 or blue_deg(v) >= 14
%
% Case A: blue_deg >= 14
%   By R(3,5) = 14, the blue neighborhood has red K_3 or blue K_5
%   Blue K_5 + v = blue K_6 ✓
%   Red K_3 in blue neighborhood is just red K_3 ✓
%
% Case B: red_deg >= 4 for all vertices, and some vertex has blue_deg < 14
%   Then red_deg >= 4 for that vertex
%   But wait, in triangle-free red graph, red neighborhood is independent
%   So red neighborhood of size 4 means those 4 vertices have no red edges between them
%
% This suggests the argument needs R(3,5) = 14 critically

fof(vertex, type, v: $i).
fof(red, type, red: $i * $i > $o).
fof(blue, type, blue: $i * $i > $o).

% Exactly one color per edge (for distinct vertices)
fof(edge_coloring, axiom, ![X,Y]: (X != Y => (red(X,Y) <=> ~blue(X,Y)))).

% Symmetry
fof(red_sym, axiom, ![X,Y]: (red(X,Y) => red(Y,X))).
fof(blue_sym, axiom, ![X,Y]: (blue(X,Y) => blue(Y,X))).

% 18 vertices: v0..v17
fof(vertices, axiom,
    v0 != v1 & v0 != v2 & v0 != v3 & v0 != v4 & v0 != v5 & v0 != v6 & v0 != v7 &
    v0 != v8 & v0 != v9 & v0 != v10 & v0 != v11 & v0 != v12 & v0 != v13 & v0 != v14 &
    v0 != v15 & v0 != v16 & v0 != v17).

% No red triangle
fof(no_red_K3, axiom, ![X,Y,Z]: ~(red(X,Y) & red(Y,Z) & red(X,Z))).

% No blue K_6 (would need 15 axioms for each pair in a 6-set)
% For now, just state the goal

% Goal: derive contradiction (meaning either red K_3 or blue K_6 must exist)
fof(goal, conjecture, $false).
