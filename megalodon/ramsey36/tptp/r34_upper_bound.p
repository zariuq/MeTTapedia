% R(3,4) <= 9: Upper bound proof
%
% Statement: Any graph on 9 vertices contains either K_3 (triangle) or I_4 (4-independent set).
%
% Proof approach: Assume 9 vertices, triangle-free, no 4-independent set. Derive contradiction.
%
% Key steps:
% 1. If any vertex has degree >= 4, its neighbors form 4-independent set (triangle-free)
% 2. So every vertex has degree <= 3
% 3. Pick vertex v with degree d <= 3. Non-neighbors T has |T| >= 9-1-3 = 5 vertices.
% 4. Among T, if there's 3-independent set I3, then {v} ∪ I3 is 4-independent.
% 5. So T has no 3-independent set, meaning it's "dense" for 5 vertices.
% 6. A 5-vertex triangle-free graph with α <= 2 must be C_5.
% 7. Each neighbor of v must connect to T to satisfy degree constraints, leading to triangle.
%
% This file attempts the full proof for ATP verification.

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% 9 distinct vertices: v0 through v8
fof(distinct, axiom,
    v0!=v1 & v0!=v2 & v0!=v3 & v0!=v4 & v0!=v5 & v0!=v6 & v0!=v7 & v0!=v8 &
    v1!=v2 & v1!=v3 & v1!=v4 & v1!=v5 & v1!=v6 & v1!=v7 & v1!=v8 &
    v2!=v3 & v2!=v4 & v2!=v5 & v2!=v6 & v2!=v7 & v2!=v8 &
    v3!=v4 & v3!=v5 & v3!=v6 & v3!=v7 & v3!=v8 &
    v4!=v5 & v4!=v6 & v4!=v7 & v4!=v8 &
    v5!=v6 & v5!=v7 & v5!=v8 &
    v6!=v7 & v6!=v8 &
    v7!=v8).

% Domain closure
fof(domain, axiom, ![X]: (X=v0 | X=v1 | X=v2 | X=v3 | X=v4 | X=v5 | X=v6 | X=v7 | X=v8)).

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% No 4-independent set: every 4 distinct vertices have at least one edge
fof(no_4_indep, axiom,
    ![A,B,C,D]: ((A!=B & A!=C & A!=D & B!=C & B!=D & C!=D) =>
                 (adj(A,B) | adj(A,C) | adj(A,D) | adj(B,C) | adj(B,D) | adj(C,D)))).

% Goal: Contradiction (no such graph exists)
fof(goal, conjecture, $false).
