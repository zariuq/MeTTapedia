% R(3,4) > 8: Lower bound witness
%
% We construct an 8-vertex graph that is:
% 1. Triangle-free (no K_3)
% 2. Has no 4-independent set (alpha <= 3)
%
% Construction: Circulant graph C_8(1,4)
% Vertices: 0, 1, 2, 3, 4, 5, 6, 7
% Edges: i ~ j iff |i-j| mod 8 in {1, 7} or |i-j| = 4
% This gives 3-regular graph where each vertex connects to i+1, i-1, i+4
%
% Actually, we use a different construction that works:
% The Paley-like graph on Z_8 with specific edge set

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% 8 distinct vertices
fof(distinct, axiom,
    v0!=v1 & v0!=v2 & v0!=v3 & v0!=v4 & v0!=v5 & v0!=v6 & v0!=v7 &
    v1!=v2 & v1!=v3 & v1!=v4 & v1!=v5 & v1!=v6 & v1!=v7 &
    v2!=v3 & v2!=v4 & v2!=v5 & v2!=v6 & v2!=v7 &
    v3!=v4 & v3!=v5 & v3!=v6 & v3!=v7 &
    v4!=v5 & v4!=v6 & v4!=v7 &
    v5!=v6 & v5!=v7 &
    v6!=v7).

% Explicit edge definition for the witness graph
% Using the circulant C_8(1,4): each vertex i connects to i+1, i-1, i+4 (mod 8)
% This is 3-regular and triangle-free

% Edges from vertex 0: 0-1, 0-7, 0-4
fof(e_0_1, axiom, adj(v0, v1)).
fof(e_0_7, axiom, adj(v0, v7)).
fof(e_0_4, axiom, adj(v0, v4)).

% Edges from vertex 1: 1-2, 1-0, 1-5
fof(e_1_2, axiom, adj(v1, v2)).
fof(e_1_5, axiom, adj(v1, v5)).

% Edges from vertex 2: 2-3, 2-1, 2-6
fof(e_2_3, axiom, adj(v2, v3)).
fof(e_2_6, axiom, adj(v2, v6)).

% Edges from vertex 3: 3-4, 3-2, 3-7
fof(e_3_4, axiom, adj(v3, v4)).
fof(e_3_7, axiom, adj(v3, v7)).

% Edges from vertex 4: 4-5, 4-3, 4-0
fof(e_4_5, axiom, adj(v4, v5)).

% Edges from vertex 5: 5-6, 5-4, 5-1
fof(e_5_6, axiom, adj(v5, v6)).

% Edges from vertex 6: 6-7, 6-5, 6-2
fof(e_6_7, axiom, adj(v6, v7)).

% Edges from vertex 7: 7-0, 7-6, 7-3 (already covered)

% Non-edges (explicit for C_8(1,4))
% 0 not adjacent to: 2, 3, 5, 6
fof(ne_0_2, axiom, ~adj(v0, v2)).
fof(ne_0_3, axiom, ~adj(v0, v3)).
fof(ne_0_5, axiom, ~adj(v0, v5)).
fof(ne_0_6, axiom, ~adj(v0, v6)).

% 1 not adjacent to: 3, 4, 6, 7
fof(ne_1_3, axiom, ~adj(v1, v3)).
fof(ne_1_4, axiom, ~adj(v1, v4)).
fof(ne_1_6, axiom, ~adj(v1, v6)).
fof(ne_1_7, axiom, ~adj(v1, v7)).

% 2 not adjacent to: 0, 4, 5, 7
fof(ne_2_4, axiom, ~adj(v2, v4)).
fof(ne_2_5, axiom, ~adj(v2, v5)).
fof(ne_2_7, axiom, ~adj(v2, v7)).

% 3 not adjacent to: 0, 1, 5, 6
fof(ne_3_5, axiom, ~adj(v3, v5)).
fof(ne_3_6, axiom, ~adj(v3, v6)).

% 4 not adjacent to: 1, 2, 6, 7
fof(ne_4_6, axiom, ~adj(v4, v6)).
fof(ne_4_7, axiom, ~adj(v4, v7)).

% 5 not adjacent to: 2, 3, 7, 0
fof(ne_5_7, axiom, ~adj(v5, v7)).

% Goal 1: Verify this graph is consistent (satisfiable)
% fof(goal_sat, conjecture, $true).

% Alternative goal: Verify triangle-free (should be theorem if graph is correct)
% fof(goal_tf, conjecture, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).
