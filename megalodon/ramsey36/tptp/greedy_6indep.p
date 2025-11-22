% Greedy construction of 6-independent set
%
% Setup: v0 has 5 neighbors {v1,v2,v3,v4,v5} (max degree case)
% Non-neighbors: T = {v6,...,v17} (12 vertices)
%
% Step 1: v0 is in our independent set (trivially independent)
% Step 2: Pick v6 from T. Now {v0, v6} is 2-independent.
% Step 3: Each subsequent pick removes at most 5 vertices from consideration.
%
% After picking v0: 12 vertices in T available
% After picking v6: at most 12 - 5 = 7 available (v6 has ≤5 neighbors in T)
% After picking v7: at most 7 - 5 = 2 available
% We can get at least 4 from T, giving 5-indep with v0.
%
% For 6th: analyze remaining structure.

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% 18 distinct vertices
fof(all_distinct, axiom,
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

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% v0's neighbors are v1,...,v5 (exactly 5)
fof(v0_adj_v1, axiom, adj(v0,v1)).
fof(v0_adj_v2, axiom, adj(v0,v2)).
fof(v0_adj_v3, axiom, adj(v0,v3)).
fof(v0_adj_v4, axiom, adj(v0,v4)).
fof(v0_adj_v5, axiom, adj(v0,v5)).

% v0 is NOT adjacent to v6,...,v17
fof(v0_notadj_v6, axiom, ~adj(v0,v6)).
fof(v0_notadj_v7, axiom, ~adj(v0,v7)).
fof(v0_notadj_v8, axiom, ~adj(v0,v8)).
fof(v0_notadj_v9, axiom, ~adj(v0,v9)).
fof(v0_notadj_v10, axiom, ~adj(v0,v10)).
fof(v0_notadj_v11, axiom, ~adj(v0,v11)).
fof(v0_notadj_v12, axiom, ~adj(v0,v12)).
fof(v0_notadj_v13, axiom, ~adj(v0,v13)).
fof(v0_notadj_v14, axiom, ~adj(v0,v14)).
fof(v0_notadj_v15, axiom, ~adj(v0,v15)).
fof(v0_notadj_v16, axiom, ~adj(v0,v16)).
fof(v0_notadj_v17, axiom, ~adj(v0,v17)).

% Triangle-free means v1,...,v5 are pairwise non-adjacent
% (They're all adjacent to v0, so any edge among them creates triangle)
fof(v1_v5_indep_12, axiom, ~adj(v1,v2)).
fof(v1_v5_indep_13, axiom, ~adj(v1,v3)).
fof(v1_v5_indep_14, axiom, ~adj(v1,v4)).
fof(v1_v5_indep_15, axiom, ~adj(v1,v5)).
fof(v1_v5_indep_23, axiom, ~adj(v2,v3)).
fof(v1_v5_indep_24, axiom, ~adj(v2,v4)).
fof(v1_v5_indep_25, axiom, ~adj(v2,v5)).
fof(v1_v5_indep_34, axiom, ~adj(v3,v4)).
fof(v1_v5_indep_35, axiom, ~adj(v3,v5)).
fof(v1_v5_indep_45, axiom, ~adj(v4,v5)).

% Max degree 5 for vertices in T = {v6,...,v17}
% Each vi has at most 5 neighbors total
fof(max_deg_v6, axiom, ~(adj(v6,v7) & adj(v6,v8) & adj(v6,v9) & adj(v6,v10) & adj(v6,v11) & adj(v6,v12))).
fof(max_deg_v7, axiom, ~(adj(v7,v6) & adj(v7,v8) & adj(v7,v9) & adj(v7,v10) & adj(v7,v11) & adj(v7,v12))).
fof(max_deg_v8, axiom, ~(adj(v8,v6) & adj(v8,v7) & adj(v8,v9) & adj(v8,v10) & adj(v8,v11) & adj(v8,v12))).
fof(max_deg_v9, axiom, ~(adj(v9,v6) & adj(v9,v7) & adj(v9,v8) & adj(v9,v10) & adj(v9,v11) & adj(v9,v12))).

% No 6-independent set among ANY 6 vertices
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

% Goal: derive contradiction
% The setup is: v0 is non-adjacent to 12 vertices {v6,...,v17}
% Triangle-free + max_deg 5 + no-6-indep should contradict
fof(goal, conjecture, $false).
