% R(3,6) <= 18 proof using R(3,4)=9 as axiom
%
% Key axiom: R(3,4) = 9 means any triangle-free graph on 9+ vertices has 4-indep set
%
% Setup:
% - 18 vertices: v0,...,v17
% - v0 has 5 neighbors {v1,...,v5} (max degree case, WLOG)
% - T = {v6,...,v17} are non-neighbors of v0 (12 vertices)
% - T is triangle-free (subgraph of triangle-free graph)
% - By R(3,4)=9 axiom: T has 4-indep set, say {v6,v7,v8,v9} (WLOG)
% - So {v0,v6,v7,v8,v9} is 5-indep (v0 non-adj to all of T)
%
% Question: Can we find 6th vertex non-adj to {v0,v6,v7,v8,v9}?
% Remaining candidates: T \ {v6,v7,v8,v9} = {v10,...,v17} (8 vertices)
% Each vi in T has degree ≤ 5.
% For NO 6th to exist: all 8 must be adj to at least one of {v6,v7,v8,v9}
% But {v6,v7,v8,v9} have total capacity 4*5 = 20 edges, enough for 8 vertices.
%
% The key constraint: edges among {v10,...,v17} + edges to {v6,v7,v8,v9}
% must satisfy max_degree 5 AND triangle-free.

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% 13 key vertices: v0 and T = {v6,...,v17}
fof(distinct_key, axiom,
    v0!=v6 & v0!=v7 & v0!=v8 & v0!=v9 & v0!=v10 & v0!=v11 & v0!=v12 & v0!=v13 & v0!=v14 & v0!=v15 & v0!=v16 & v0!=v17 &
    v6!=v7 & v6!=v8 & v6!=v9 & v6!=v10 & v6!=v11 & v6!=v12 & v6!=v13 & v6!=v14 & v6!=v15 & v6!=v16 & v6!=v17 &
    v7!=v8 & v7!=v9 & v7!=v10 & v7!=v11 & v7!=v12 & v7!=v13 & v7!=v14 & v7!=v15 & v7!=v16 & v7!=v17 &
    v8!=v9 & v8!=v10 & v8!=v11 & v8!=v12 & v8!=v13 & v8!=v14 & v8!=v15 & v8!=v16 & v8!=v17 &
    v9!=v10 & v9!=v11 & v9!=v12 & v9!=v13 & v9!=v14 & v9!=v15 & v9!=v16 & v9!=v17 &
    v10!=v11 & v10!=v12 & v10!=v13 & v10!=v14 & v10!=v15 & v10!=v16 & v10!=v17 &
    v11!=v12 & v11!=v13 & v11!=v14 & v11!=v15 & v11!=v16 & v11!=v17 &
    v12!=v13 & v12!=v14 & v12!=v15 & v12!=v16 & v12!=v17 &
    v13!=v14 & v13!=v15 & v13!=v16 & v13!=v17 &
    v14!=v15 & v14!=v16 & v14!=v17 &
    v15!=v16 & v15!=v17 &
    v16!=v17).

% Triangle-free (restricted to our vertices for efficiency)
fof(tf_678, axiom, ~(adj(v6,v7) & adj(v7,v8) & adj(v6,v8))).
fof(tf_679, axiom, ~(adj(v6,v7) & adj(v7,v9) & adj(v6,v9))).
fof(tf_689, axiom, ~(adj(v6,v8) & adj(v8,v9) & adj(v6,v9))).
fof(tf_789, axiom, ~(adj(v7,v8) & adj(v8,v9) & adj(v7,v9))).
% ... (abbreviated for key vertices)

% v0 is non-adjacent to all of T
fof(v0_not_in_T, axiom,
    ~adj(v0,v6) & ~adj(v0,v7) & ~adj(v0,v8) & ~adj(v0,v9) &
    ~adj(v0,v10) & ~adj(v0,v11) & ~adj(v0,v12) & ~adj(v0,v13) &
    ~adj(v0,v14) & ~adj(v0,v15) & ~adj(v0,v16) & ~adj(v0,v17)).

% R(3,4)=9 axiom applied: {v6,v7,v8,v9} is 4-independent in T
fof(r34_indep, axiom,
    ~adj(v6,v7) & ~adj(v6,v8) & ~adj(v6,v9) &
    ~adj(v7,v8) & ~adj(v7,v9) &
    ~adj(v8,v9)).

% So {v0,v6,v7,v8,v9} is 5-independent
% (v0 non-adj to v6,v7,v8,v9 by v0_not_in_T, and v6,v7,v8,v9 pairwise non-adj by r34_indep)

% Max degree 5 for each vertex in T
% v6: can have at most 5 neighbors among {v10,...,v17} ∪ {v1,...,v5}
% Since we're focusing on T, encode: v6 has ≤5 neighbors in T \ {v6}
fof(max_deg_v6_T, axiom, ~(adj(v6,v10) & adj(v6,v11) & adj(v6,v12) & adj(v6,v13) & adj(v6,v14) & adj(v6,v15))).
fof(max_deg_v7_T, axiom, ~(adj(v7,v10) & adj(v7,v11) & adj(v7,v12) & adj(v7,v13) & adj(v7,v14) & adj(v7,v15))).
fof(max_deg_v8_T, axiom, ~(adj(v8,v10) & adj(v8,v11) & adj(v8,v12) & adj(v8,v13) & adj(v8,v14) & adj(v8,v15))).
fof(max_deg_v9_T, axiom, ~(adj(v9,v10) & adj(v9,v11) & adj(v9,v12) & adj(v9,v13) & adj(v9,v14) & adj(v9,v15))).

% For NO 6th independent vertex: each of v10,...,v17 is adj to at least one of v6,v7,v8,v9
fof(v10_blocked, axiom, adj(v10,v6) | adj(v10,v7) | adj(v10,v8) | adj(v10,v9)).
fof(v11_blocked, axiom, adj(v11,v6) | adj(v11,v7) | adj(v11,v8) | adj(v11,v9)).
fof(v12_blocked, axiom, adj(v12,v6) | adj(v12,v7) | adj(v12,v8) | adj(v12,v9)).
fof(v13_blocked, axiom, adj(v13,v6) | adj(v13,v7) | adj(v13,v8) | adj(v13,v9)).
fof(v14_blocked, axiom, adj(v14,v6) | adj(v14,v7) | adj(v14,v8) | adj(v14,v9)).
fof(v15_blocked, axiom, adj(v15,v6) | adj(v15,v7) | adj(v15,v8) | adj(v15,v9)).
fof(v16_blocked, axiom, adj(v16,v6) | adj(v16,v7) | adj(v16,v8) | adj(v16,v9)).
fof(v17_blocked, axiom, adj(v17,v6) | adj(v17,v7) | adj(v17,v8) | adj(v17,v9)).

% Goal: derive contradiction
% The max_deg constraints should conflict with blocking all 8 vertices
fof(goal, conjecture, $false).
