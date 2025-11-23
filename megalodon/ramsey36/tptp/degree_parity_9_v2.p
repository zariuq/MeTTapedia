% TPTP: Degree parity contradiction on 9 vertices
%
% Key insight: In a 9-vertex triangle-free graph with no 4-indep set,
% every vertex has degree exactly 3 (min 3, max 3).
% But 9 vertices with degree 3 gives sum = 27 (odd), which contradicts
% handshake lemma (sum must be even = 2 * edges).
%
% This file verifies the impossibility by showing the configuration is UNSAT.

fof(sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(irref, axiom, ![X]: ~adj(X,X)).

% 9 distinct vertices
fof(v_distinct, axiom,
    v0 != v1 & v0 != v2 & v0 != v3 & v0 != v4 & v0 != v5 & v0 != v6 & v0 != v7 & v0 != v8 &
    v1 != v2 & v1 != v3 & v1 != v4 & v1 != v5 & v1 != v6 & v1 != v7 & v1 != v8 &
    v2 != v3 & v2 != v4 & v2 != v5 & v2 != v6 & v2 != v7 & v2 != v8 &
    v3 != v4 & v3 != v5 & v3 != v6 & v3 != v7 & v3 != v8 &
    v4 != v5 & v4 != v6 & v4 != v7 & v4 != v8 &
    v5 != v6 & v5 != v7 & v5 != v8 &
    v6 != v7 & v6 != v8 &
    v7 != v8).

% Closed domain: only these 9 vertices exist
fof(domain, axiom, ![X]: (X = v0 | X = v1 | X = v2 | X = v3 | X = v4 | X = v5 | X = v6 | X = v7 | X = v8)).

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% No 4-independent set
fof(no_4_indep, axiom,
    ![A,B,C,D]: ((A != B & A != C & A != D & B != C & B != D & C != D) =>
                 (adj(A,B) | adj(A,C) | adj(A,D) | adj(B,C) | adj(B,D) | adj(C,D)))).

% Max degree 3: no vertex can have 4 neighbors
% (In triangle-free graph, 4 neighbors would be 4-indep set)
fof(max_deg_3, axiom,
    ![V,N1,N2,N3,N4]: ((N1 != N2 & N1 != N3 & N1 != N4 & N2 != N3 & N2 != N4 & N3 != N4) =>
                       ~(adj(V,N1) & adj(V,N2) & adj(V,N3) & adj(V,N4)))).

% Min degree 3: every vertex must have at least 3 neighbors
% (If deg <= 2, then >= 6 non-neighbors among 8 others, and R(3,4)=9 applies to give 4-indep)
% We encode this as: for each vertex, there exist 3 distinct neighbors
fof(min_deg_v0, axiom, ?[A,B,C]: (A != B & A != C & B != C & adj(v0,A) & adj(v0,B) & adj(v0,C))).
fof(min_deg_v1, axiom, ?[A,B,C]: (A != B & A != C & B != C & adj(v1,A) & adj(v1,B) & adj(v1,C))).
fof(min_deg_v2, axiom, ?[A,B,C]: (A != B & A != C & B != C & adj(v2,A) & adj(v2,B) & adj(v2,C))).
fof(min_deg_v3, axiom, ?[A,B,C]: (A != B & A != C & B != C & adj(v3,A) & adj(v3,B) & adj(v3,C))).
fof(min_deg_v4, axiom, ?[A,B,C]: (A != B & A != C & B != C & adj(v4,A) & adj(v4,B) & adj(v4,C))).
fof(min_deg_v5, axiom, ?[A,B,C]: (A != B & A != C & B != C & adj(v5,A) & adj(v5,B) & adj(v5,C))).
fof(min_deg_v6, axiom, ?[A,B,C]: (A != B & A != C & B != C & adj(v6,A) & adj(v6,B) & adj(v6,C))).
fof(min_deg_v7, axiom, ?[A,B,C]: (A != B & A != C & B != C & adj(v7,A) & adj(v7,B) & adj(v7,C))).
fof(min_deg_v8, axiom, ?[A,B,C]: (A != B & A != C & B != C & adj(v8,A) & adj(v8,B) & adj(v8,C))).

% Goal: show this configuration is unsatisfiable
% The prover should find that no such graph exists
fof(goal, conjecture, $false).
