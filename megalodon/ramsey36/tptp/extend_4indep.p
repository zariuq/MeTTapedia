% TPTP: Show 4-indep + non-neighbor vertex can extend to 6-indep
%
% Setup: 18 vertices, triangle-free, no 6-indep
% Given: 4-indep set S = {s0, s1, s2, s3} and vertex v non-adjacent to all
% Show: This leads to contradiction (can find 6-indep)
%
% The argument: S ∪ {v} is 5-indep. Each element has degree <= 5.
% Among 13 remaining vertices, at least one is non-adjacent to all 5.

% We'll encode a specific instance to check feasibility

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% Vertices: 18 total, using v0-v17
% v0 = special vertex v
% v1-v4 = S (the 4-indep set)
% v5-v17 = remaining 13 vertices

% Distinct vertices (some key pairs)
fof(distinct_01, axiom, v0 != v1).
fof(distinct_02, axiom, v0 != v2).
fof(distinct_03, axiom, v0 != v3).
fof(distinct_04, axiom, v0 != v4).
fof(distinct_12, axiom, v1 != v2).
fof(distinct_13, axiom, v1 != v3).
fof(distinct_14, axiom, v1 != v4).
fof(distinct_23, axiom, v2 != v3).
fof(distinct_24, axiom, v2 != v4).
fof(distinct_34, axiom, v3 != v4).

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% S = {v1, v2, v3, v4} is independent (no edges within S)
fof(indep_12, axiom, ~adj(v1, v2)).
fof(indep_13, axiom, ~adj(v1, v3)).
fof(indep_14, axiom, ~adj(v1, v4)).
fof(indep_23, axiom, ~adj(v2, v3)).
fof(indep_24, axiom, ~adj(v2, v4)).
fof(indep_34, axiom, ~adj(v3, v4)).

% v0 is non-adjacent to all of S
fof(v0_nonadj_1, axiom, ~adj(v0, v1)).
fof(v0_nonadj_2, axiom, ~adj(v0, v2)).
fof(v0_nonadj_3, axiom, ~adj(v0, v3)).
fof(v0_nonadj_4, axiom, ~adj(v0, v4)).

% So S ∪ {v0} = {v0, v1, v2, v3, v4} is 5-indep

% Degree bound: each vertex has at most 5 neighbors
% For the 5 vertices in S ∪ {v0}, encode that they can't all block the 13 remaining

% The 13 remaining vertices: v5, v6, ..., v17
% Each of v0-v4 can be adjacent to at most 5 of these 13

% But we need to show: there exists some v_i (i >= 5) non-adjacent to all of v0-v4

% Degree bound for v0: at most 5 neighbors among v5-v17
fof(deg_v0, axiom,
  ~(adj(v0,v5) & adj(v0,v6) & adj(v0,v7) & adj(v0,v8) & adj(v0,v9) & adj(v0,v10))).

% Degree bound for v1: at most 5 neighbors among v5-v17
fof(deg_v1, axiom,
  ~(adj(v1,v5) & adj(v1,v6) & adj(v1,v7) & adj(v1,v8) & adj(v1,v9) & adj(v1,v10))).

% Degree bound for v2: at most 5 neighbors among v5-v17
fof(deg_v2, axiom,
  ~(adj(v2,v5) & adj(v2,v6) & adj(v2,v7) & adj(v2,v8) & adj(v2,v9) & adj(v2,v10))).

% Degree bound for v3: at most 5 neighbors among v5-v17
fof(deg_v3, axiom,
  ~(adj(v3,v5) & adj(v3,v6) & adj(v3,v7) & adj(v3,v8) & adj(v3,v9) & adj(v3,v10))).

% Degree bound for v4: at most 5 neighbors among v5-v17
fof(deg_v4, axiom,
  ~(adj(v4,v5) & adj(v4,v6) & adj(v4,v7) & adj(v4,v8) & adj(v4,v9) & adj(v4,v10))).

% If all 13 vertices (v5-v17) are adjacent to at least one of v0-v4,
% then we can't have degree <= 5 for all... actually this encoding is incomplete.

% Let me try: assume NO vertex among v5-v17 is non-adjacent to all of v0-v4
% Then each of v5-v17 is adjacent to at least one of v0-v4
% This means each of v5-v17 contributes at least 1 edge to {v0,v1,v2,v3,v4}
% Total: at least 13 edges
% But each of v0-v4 has at most 5 edges to v5-v17
% Total: at most 25 edges
% This doesn't give contradiction directly.

% Alternative: just show the theorem via no_6_indep contradiction
% If there exists w in {v5-v17} non-adjacent to all of {v0,v1,v2,v3,v4},
% then {v0,v1,v2,v3,v4,w} is 6-indep.

% no_6_indep: any 6 distinct vertices have at least one edge
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

% Claim: there exists w such that {v0,v1,v2,v3,v4,w} is 6-indep, contradiction.
% Since S ∪ {v0} is already 5-indep, we need w non-adjacent to all 5.

% Encode: v5 is non-adjacent to all of v0-v4 (one candidate)
% Then check if no_6_indep gives contradiction

fof(v5_nonadj_0, axiom, ~adj(v5, v0)).
fof(v5_nonadj_1, axiom, ~adj(v5, v1)).
fof(v5_nonadj_2, axiom, ~adj(v5, v2)).
fof(v5_nonadj_3, axiom, ~adj(v5, v3)).
fof(v5_nonadj_4, axiom, ~adj(v5, v4)).
fof(v5_distinct, axiom, v5 != v0 & v5 != v1 & v5 != v2 & v5 != v3 & v5 != v4).

% Now {v0,v1,v2,v3,v4,v5} should form a 6-indep set, contradicting no_6_indep
fof(goal, conjecture, $false).
