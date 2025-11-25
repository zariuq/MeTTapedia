% can_extend_4indep pigeonhole argument
% We have 5 vertices in an independent set, each with at most 5 neighbors among 13 vertices.
% We want to show: if all 13 are adjacent to at least one of the 5, we get a contradiction.

fof(v1_type, axiom, v(v1)).
fof(v2_type, axiom, v(v2)).
fof(v3_type, axiom, v(v3)).
fof(v4_type, axiom, v(v4)).
fof(v5_type, axiom, v(v5)).

fof(w1_type, axiom, w(w1)).
fof(w2_type, axiom, w(w2)).
fof(w3_type, axiom, w(w3)).
fof(w4_type, axiom, w(w4)).
fof(w5_type, axiom, w(w5)).
fof(w6_type, axiom, w(w6)).
fof(w7_type, axiom, w(w7)).
fof(w8_type, axiom, w(w8)).
fof(w9_type, axiom, w(w9)).
fof(w10_type, axiom, w(w10)).
fof(w11_type, axiom, w(w11)).
fof(w12_type, axiom, w(w12)).
fof(w13_type, axiom, w(w13)).

% The 5 vertices are distinct
fof(v_distinct_12, axiom, v1 != v2).
fof(v_distinct_13, axiom, v1 != v3).
fof(v_distinct_14, axiom, v1 != v4).
fof(v_distinct_15, axiom, v1 != v5).
fof(v_distinct_23, axiom, v2 != v3).
fof(v_distinct_24, axiom, v2 != v4).
fof(v_distinct_25, axiom, v2 != v5).
fof(v_distinct_34, axiom, v3 != v4).
fof(v_distinct_35, axiom, v3 != v5).
fof(v_distinct_45, axiom, v4 != v5).

% The 13 vertices are distinct
fof(w_distinct_1_2, axiom, w1 != w2).
fof(w_distinct_1_3, axiom, w1 != w3).
% ... (many more distinctness axioms)

% The v's and w's are disjoint
fof(disjoint_v1_w, axiom, ![W]: (w(W) => v1 != W)).
fof(disjoint_v2_w, axiom, ![W]: (w(W) => v2 != W)).
fof(disjoint_v3_w, axiom, ![W]: (w(W) => v3 != W)).
fof(disjoint_v4_w, axiom, ![W]: (w(W) => v4 != W)).
fof(disjoint_v5_w, axiom, ![W]: (w(W) => v5 != W)).

% The 5 vertices are mutually non-adjacent (form independent set)
fof(indep_12, axiom, ~r(v1, v2)).
fof(indep_13, axiom, ~r(v1, v3)).
fof(indep_14, axiom, ~r(v1, v4)).
fof(indep_15, axiom, ~r(v1, v5)).
fof(indep_23, axiom, ~r(v2, v3)).
fof(indep_24, axiom, ~r(v2, v4)).
fof(indep_25, axiom, ~r(v2, v5)).
fof(indep_34, axiom, ~r(v3, v4)).
fof(indep_35, axiom, ~r(v3, v5)).
fof(indep_45, axiom, ~r(v4, v5)).

% Symmetry of r
fof(symmetry, axiom, ![X,Y]: (r(X,Y) => r(Y,X))).

% Each of the 5 vertices has at most 5 neighbors among the 13
% This is encoded as: each has at least 8 non-neighbors among the 13
fof(v1_has_8_non_neighbors, axiom,
  ?[A,B,C,D,E,F,G,H]: (
    w(A) & w(B) & w(C) & w(D) & w(E) & w(F) & w(G) & w(H) &
    A != B & A != C & A != D & A != E & A != F & A != G & A != H &
    B != C & B != D & B != E & B != F & B != G & B != H &
    C != D & C != E & C != F & C != G & C != H &
    D != E & D != F & D != G & D != H &
    E != F & E != G & E != H &
    F != G & F != H &
    G != H &
    ~r(v1,A) & ~r(v1,B) & ~r(v1,C) & ~r(v1,D) &
    ~r(v1,E) & ~r(v1,F) & ~r(v1,G) & ~r(v1,H)
  )).

% Similar for v2, v3, v4, v5
fof(v2_has_8_non_neighbors, axiom,
  ?[A,B,C,D,E,F,G,H]: (
    w(A) & w(B) & w(C) & w(D) & w(E) & w(F) & w(G) & w(H) &
    A != B & A != C & A != D & A != E & A != F & A != G & A != H &
    B != C & B != D & B != E & B != F & B != G & B != H &
    C != D & C != E & C != F & C != G & C != H &
    D != E & D != F & D != G & D != H &
    E != F & E != G & E != H &
    F != G & F != H &
    G != H &
    ~r(v2,A) & ~r(v2,B) & ~r(v2,C) & ~r(v2,D) &
    ~r(v2,E) & ~r(v2,F) & ~r(v2,G) & ~r(v2,H)
  )).

% (Similar for v3, v4, v5... omitted for brevity)

% Assume for contradiction: every w is adjacent to at least one v
fof(all_covered, hypothesis,
  ![W]: (w(W) => (r(v1,W) | r(v2,W) | r(v3,W) | r(v4,W) | r(v5,W)))).

% Goal: derive False (i.e., find a w that is non-adjacent to all v's)
fof(goal, conjecture, $false).
