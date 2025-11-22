% R(3,4) = 9 via recursive bound
%
% R(3,4) ≤ R(2,4) + R(3,3) = 4 + 6 = 10
% More precisely: R(3,4) ≤ R(3,3) + R(2,4) - 1 = 6 + 4 - 1 = 9
%
% Proof of R(3,4) ≤ 9 by induction:
% Given 9 vertices, pick vertex v with degree d.
%
% Case 1: d ≥ R(2,4) = 4
%   N(v) has ≥ 4 vertices
%   Either N(v) has an edge (with v forms triangle) or N(v) is 4-independent
%
% Case 2: d ≤ 3, so non-neighbors ≥ 9 - 1 - 3 = 5 ≤ R(3,3) - 1 = 5
%   Actually need: non-neighbors ≥ R(3,3) = 6
%   If d ≤ 2: non-neighbors ≥ 6, among which either K3 or I3
%     If I3 in non-neighbors, with v gives I4
%   If d = 3: non-neighbors = 5 < 6, can't use R(3,3) directly
%
% The tight analysis:
% - If d ≥ 4: neighbors ≥ 4, either edge (triangle with v) or I4
% - If d ≤ 3: neighbors ≤ 3, non-neighbors ≥ 5
%   Need to show 5 vertices triangle-free has 3-indep, then add v for 4-indep
%   R(3,3) = 6 > 5, so can't use directly
%   But: in graph on 5 vertices, either triangle exists or max_deg ≤ 1
%   If max_deg ≤ 1 on 5 vertices: at most 2 edges, easy to find 3-indep

% Let me encode the specific case: 9 vertices, triangle-free, show 4-indep exists

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% 9 distinct vertices
fof(distinct, axiom,
    v1!=v2 & v1!=v3 & v1!=v4 & v1!=v5 & v1!=v6 & v1!=v7 & v1!=v8 & v1!=v9 &
    v2!=v3 & v2!=v4 & v2!=v5 & v2!=v6 & v2!=v7 & v2!=v8 & v2!=v9 &
    v3!=v4 & v3!=v5 & v3!=v6 & v3!=v7 & v3!=v8 & v3!=v9 &
    v4!=v5 & v4!=v6 & v4!=v7 & v4!=v8 & v4!=v9 &
    v5!=v6 & v5!=v7 & v5!=v8 & v5!=v9 &
    v6!=v7 & v6!=v8 & v6!=v9 &
    v7!=v8 & v7!=v9 &
    v8!=v9).

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% No 4-independent set
fof(no_4_indep, axiom,
    ![A,B,C,D]:
    ((A != B & A != C & A != D & B != C & B != D & C != D) =>
     (adj(A,B) | adj(A,C) | adj(A,D) | adj(B,C) | adj(B,D) | adj(C,D)))).

% Goal: contradiction (no such graph exists)
fof(goal, conjecture, $false).
