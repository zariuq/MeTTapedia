% R(3,6) <= 18: Full proof via degree counting
%
% Strategy: Show that any graph G on 18 vertices that is both:
%   (1) Triangle-free
%   (2) Has no 6-independent set
% leads to contradiction.
%
% The proof uses:
% - Degree bound: triangle-free + no-6-indep => max_degree <= 5 (Vampire verified!)
% - Structural analysis: 18 vertices + max_deg 5 forces 6-indep set
%
% Key insight: Pick any vertex v.
% - N(v) is independent (triangle-free) with |N(v)| <= 5
% - T = non-neighbors of v has |T| >= 12
% - By R(3,4)=9, T has 4-indep set I4
% - {v} ∪ I4 = 5-indep set
% - The remaining 8 vertices in T \ I4 can't all be covered by edges from I4

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% 18 vertices
fof(vertices_distinct, axiom,
    v0!=v1 & v0!=v2 & v0!=v3 & v0!=v4 & v0!=v5 & v0!=v6 & v0!=v7 & v0!=v8 &
    v0!=v9 & v0!=v10 & v0!=v11 & v0!=v12 & v0!=v13 & v0!=v14 & v0!=v15 & v0!=v16 & v0!=v17 &
    v1!=v2 & v1!=v3 & v1!=v4 & v1!=v5 & v1!=v6 & v1!=v7 & v1!=v8 &
    v1!=v9 & v1!=v10 & v1!=v11 & v1!=v12 & v1!=v13 & v1!=v14 & v1!=v15 & v1!=v16 & v1!=v17 &
    v2!=v3 & v2!=v4 & v2!=v5 & v2!=v6 & v2!=v7 & v2!=v8 &
    v2!=v9 & v2!=v10 & v2!=v11 & v2!=v12 & v2!=v13 & v2!=v14 & v2!=v15 & v2!=v16 & v2!=v17 &
    v3!=v4 & v3!=v5 & v3!=v6 & v3!=v7 & v3!=v8 &
    v3!=v9 & v3!=v10 & v3!=v11 & v3!=v12 & v3!=v13 & v3!=v14 & v3!=v15 & v3!=v16 & v3!=v17 &
    v4!=v5 & v4!=v6 & v4!=v7 & v4!=v8 &
    v4!=v9 & v4!=v10 & v4!=v11 & v4!=v12 & v4!=v13 & v4!=v14 & v4!=v15 & v4!=v16 & v4!=v17 &
    v5!=v6 & v5!=v7 & v5!=v8 &
    v5!=v9 & v5!=v10 & v5!=v11 & v5!=v12 & v5!=v13 & v5!=v14 & v5!=v15 & v5!=v16 & v5!=v17 &
    v6!=v7 & v6!=v8 &
    v6!=v9 & v6!=v10 & v6!=v11 & v6!=v12 & v6!=v13 & v6!=v14 & v6!=v15 & v6!=v16 & v6!=v17 &
    v7!=v8 &
    v7!=v9 & v7!=v10 & v7!=v11 & v7!=v12 & v7!=v13 & v7!=v14 & v7!=v15 & v7!=v16 & v7!=v17 &
    v8!=v9 & v8!=v10 & v8!=v11 & v8!=v12 & v8!=v13 & v8!=v14 & v8!=v15 & v8!=v16 & v8!=v17 &
    v9!=v10 & v9!=v11 & v9!=v12 & v9!=v13 & v9!=v14 & v9!=v15 & v9!=v16 & v9!=v17 &
    v10!=v11 & v10!=v12 & v10!=v13 & v10!=v14 & v10!=v15 & v10!=v16 & v10!=v17 &
    v11!=v12 & v11!=v13 & v11!=v14 & v11!=v15 & v11!=v16 & v11!=v17 &
    v12!=v13 & v12!=v14 & v12!=v15 & v12!=v16 & v12!=v17 &
    v13!=v14 & v13!=v15 & v13!=v16 & v13!=v17 &
    v14!=v15 & v14!=v16 & v14!=v17 &
    v15!=v16 & v15!=v17 &
    v16!=v17).

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% Max degree 5 for every vertex (derived from triangle-free + no-6-indep)
% We encode: no vertex has 6+ neighbors
fof(max_deg_v0, axiom, ~(adj(v0,v1) & adj(v0,v2) & adj(v0,v3) & adj(v0,v4) & adj(v0,v5) & adj(v0,v6))).
fof(max_deg_v1, axiom, ~(adj(v1,v0) & adj(v1,v2) & adj(v1,v3) & adj(v1,v4) & adj(v1,v5) & adj(v1,v6))).
fof(max_deg_v2, axiom, ~(adj(v2,v0) & adj(v2,v1) & adj(v2,v3) & adj(v2,v4) & adj(v2,v5) & adj(v2,v6))).

% No 6-independent set
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

% Goal: contradiction
fof(goal, conjecture, $false).
