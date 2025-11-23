% TPTP: Degree parity contradiction on 9 vertices
%
% In a 9-vertex graph that is:
% 1. Triangle-free
% 2. Has no 4-independent set
% 3. Every vertex has at most 3 neighbors (since 4 neighbors would be 4-indep by triangle-free)
% 4. Every vertex has at most 5 non-neighbors (since 6 non-neighbors gives 4-indep by R(3,4)<9)
%
% This means every vertex has degree in {3,4,5} but also in the complement:
% - Non-neighbors of v is an independent set (triangle-free means neighbors are indep,
%   and no-4-indep means non-neighbors can't be too big)
%
% Route B structure: Show this configuration is impossible via degree constraints.
% The handshake lemma implies sum of degrees is even.
% With 9 vertices, if all have odd degree, sum is odd - contradiction.

fof(sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(irref, axiom, ![X]: ~adj(X,X)).

% 9 distinct vertices
fof(vertices, axiom,
    v0 != v1 & v0 != v2 & v0 != v3 & v0 != v4 & v0 != v5 & v0 != v6 & v0 != v7 & v0 != v8 &
    v1 != v2 & v1 != v3 & v1 != v4 & v1 != v5 & v1 != v6 & v1 != v7 & v1 != v8 &
    v2 != v3 & v2 != v4 & v2 != v5 & v2 != v6 & v2 != v7 & v2 != v8 &
    v3 != v4 & v3 != v5 & v3 != v6 & v3 != v7 & v3 != v8 &
    v4 != v5 & v4 != v6 & v4 != v7 & v4 != v8 &
    v5 != v6 & v5 != v7 & v5 != v8 &
    v6 != v7 & v6 != v8 &
    v7 != v8).

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% No 4-independent set (any 4 distinct vertices have at least one edge)
fof(no_4_indep, axiom,
    ![A,B,C,D]: ((A != B & A != C & A != D & B != C & B != D & C != D) =>
                 (adj(A,B) | adj(A,C) | adj(A,D) | adj(B,C) | adj(B,D) | adj(C,D)))).

% Degree bound from triangle-free + no-4-indep:
% - If v has 4+ neighbors, neighbors form 4-indep set (triangle-free makes them pairwise non-adjacent)
% - So max degree is 3
fof(max_deg_3, axiom,
    ![V,N1,N2,N3,N4]: ((N1 != N2 & N1 != N3 & N1 != N4 & N2 != N3 & N2 != N4 & N3 != N4) =>
                       ~(adj(V,N1) & adj(V,N2) & adj(V,N3) & adj(V,N4)))).

% Non-neighbor bound from R(3,4)=9:
% - If v has 6+ non-neighbors on a 9-vertex graph, those 6 are in an 8-vertex triangle-free graph
% - R(3,4)=9 implies this 8-vertex subgraph has a 4-indep set, contradiction
% Actually in a 9-vertex graph, v has 8 other vertices. If max degree is 3, min non-neighbors is 5.
% If degree is exactly 3, non-neighbors is 5. The 5 non-neighbors + triangle-free constraint...

% Actually the key constraint for Route B is:
% On 9 vertices, triangle-free, no-4-indep implies:
% - Max degree 3 (from 4 neighbors being 4-indep)
% - But also min degree must be considered
%
% Key insight: In Route B, we show contradiction via parity
% With 9 vertices, sum of degrees = 2 * edges
% If all degrees are odd (like 3), then sum = 9 * 3 = 27, which is odd
% But 2 * edges is even - contradiction!

% So we need to show: if every vertex has degree 3, that's impossible
% Actually we need to verify the degree constraints more carefully...

% Let's try: assume each vertex has exactly 3 neighbors
fof(deg_3_v0, hypothesis, ?[A,B,C]: (adj(v0,A) & adj(v0,B) & adj(v0,C) & A != B & A != C & B != C &
    ![D]: (D != v0 & D != A & D != B & D != C => ~adj(v0,D)))).
fof(deg_3_v1, hypothesis, ?[A,B,C]: (adj(v1,A) & adj(v1,B) & adj(v1,C) & A != B & A != C & B != C &
    ![D]: (D != v1 & D != A & D != B & D != C => ~adj(v1,D)))).
fof(deg_3_v2, hypothesis, ?[A,B,C]: (adj(v2,A) & adj(v2,B) & adj(v2,C) & A != B & A != C & B != C &
    ![D]: (D != v2 & D != A & D != B & D != C => ~adj(v2,D)))).
fof(deg_3_v3, hypothesis, ?[A,B,C]: (adj(v3,A) & adj(v3,B) & adj(v3,C) & A != B & A != C & B != C &
    ![D]: (D != v3 & D != A & D != B & D != C => ~adj(v3,D)))).
fof(deg_3_v4, hypothesis, ?[A,B,C]: (adj(v4,A) & adj(v4,B) & adj(v4,C) & A != B & A != C & B != C &
    ![D]: (D != v4 & D != A & D != B & D != C => ~adj(v4,D)))).
fof(deg_3_v5, hypothesis, ?[A,B,C]: (adj(v5,A) & adj(v5,B) & adj(v5,C) & A != B & A != C & B != C &
    ![D]: (D != v5 & D != A & D != B & D != C => ~adj(v5,D)))).
fof(deg_3_v6, hypothesis, ?[A,B,C]: (adj(v6,A) & adj(v6,B) & adj(v6,C) & A != B & A != C & B != C &
    ![D]: (D != v6 & D != A & D != B & D != C => ~adj(v6,D)))).
fof(deg_3_v7, hypothesis, ?[A,B,C]: (adj(v7,A) & adj(v7,B) & adj(v7,C) & A != B & A != C & B != C &
    ![D]: (D != v7 & D != A & D != B & D != C => ~adj(v7,D)))).
fof(deg_3_v8, hypothesis, ?[A,B,C]: (adj(v8,A) & adj(v8,B) & adj(v8,C) & A != B & A != C & B != C &
    ![D]: (D != v8 & D != A & D != B & D != C => ~adj(v8,D)))).

% Goal: derive contradiction from the above
fof(goal, conjecture, $false).
