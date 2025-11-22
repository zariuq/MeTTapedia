% R(3,6) <= 18: Tight proof via edge counting in T
%
% Setup (WLOG):
% - v0 has 5 neighbors (not shown) and 12 non-neighbors T = {t0,...,t11}
% - T is triangle-free with max_degree 5
% - {t0,t1,t2,t3} is 4-indep in T (by R(3,4)=9)
% - For no 6-indep: each of {t4,...,t11} must be adj to some ti, i<4
%
% Edge counting in T:
% - 4 vertices in I = {t0,t1,t2,t3} (independent)
% - 8 vertices in R = {t4,...,t11} (remaining)
% - Each vertex in T has degree <= 5
% - Edges from I to R: at most 4*5 = 20
% - For coverage: each r in R needs at least 1 edge to I
%   => edges I to R >= 8
% - Each r in R has degree <= 5, and must have at least 1 edge to I
%   => edges within R: r has at most 4 edges in R (since >=1 to I)
% - Total edges in R: at most 8*4/2 = 16
%
% But R is also triangle-free! And |R|=8 with triangle-free =>
% By R(3,3)=6 < 8: R has 3-indep set!
%
% Let's say {t4,t5,t6} is 3-indep in R.
% For {v0,t0,t1,t2,t3,t4} to NOT be 6-indep: t4 must be adj to some of {t0,t1,t2,t3}
% Similarly t5, t6.
%
% Key constraint: {t4,t5,t6} is 3-indep in R but each is adj to I.
% What about extending {v0,t0,...,t4} to include t5?
% Need t5 non-adj to all of {t0,t1,t2,t3,t4}.
% But we know t5 is adj to some of {t0,t1,t2,t3} (for blocking).
% So t5 IS adjacent to I.
%
% The real question: among the 8 vertices in R, can we find 2 that are:
%   (a) non-adj to each other
%   (b) non-adj to all of I
% If so, {v0, I, those 2} = 7-indep, contradiction!
% But we need (b) to fail for blocking...
%
% Actually, let me just show the specific edge-counting contradiction.

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% I = {t0,t1,t2,t3} independent (by R(3,4) axiom)
fof(i_indep_01, axiom, ~adj(t0,t1)).
fof(i_indep_02, axiom, ~adj(t0,t2)).
fof(i_indep_03, axiom, ~adj(t0,t3)).
fof(i_indep_12, axiom, ~adj(t1,t2)).
fof(i_indep_13, axiom, ~adj(t1,t3)).
fof(i_indep_23, axiom, ~adj(t2,t3)).

% R = {t4,...,t11} distinct from I
fof(distinct_ir, axiom,
    t0!=t4 & t0!=t5 & t0!=t6 & t0!=t7 & t0!=t8 & t0!=t9 & t0!=t10 & t0!=t11 &
    t1!=t4 & t1!=t5 & t1!=t6 & t1!=t7 & t1!=t8 & t1!=t9 & t1!=t10 & t1!=t11 &
    t2!=t4 & t2!=t5 & t2!=t6 & t2!=t7 & t2!=t8 & t2!=t9 & t2!=t10 & t2!=t11 &
    t3!=t4 & t3!=t5 & t3!=t6 & t3!=t7 & t3!=t8 & t3!=t9 & t3!=t10 & t3!=t11).

fof(distinct_r, axiom,
    t4!=t5 & t4!=t6 & t4!=t7 & t4!=t8 & t4!=t9 & t4!=t10 & t4!=t11 &
    t5!=t6 & t5!=t7 & t5!=t8 & t5!=t9 & t5!=t10 & t5!=t11 &
    t6!=t7 & t6!=t8 & t6!=t9 & t6!=t10 & t6!=t11 &
    t7!=t8 & t7!=t9 & t7!=t10 & t7!=t11 &
    t8!=t9 & t8!=t10 & t8!=t11 &
    t9!=t10 & t9!=t11 &
    t10!=t11).

% Each vertex in I has degree <= 5 IN T (all edges go to R since I is independent)
% t0 can have at most 5 neighbors in R = {t4,...,t11}
fof(deg_t0, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t6) & adj(t0,t7) & adj(t0,t8) & adj(t0,t9))).
fof(deg_t0b, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t6) & adj(t0,t7) & adj(t0,t8) & adj(t0,t10))).
fof(deg_t0c, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t6) & adj(t0,t7) & adj(t0,t8) & adj(t0,t11))).
fof(deg_t0d, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t6) & adj(t0,t7) & adj(t0,t9) & adj(t0,t10))).
fof(deg_t0e, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t6) & adj(t0,t7) & adj(t0,t9) & adj(t0,t11))).
fof(deg_t0f, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t6) & adj(t0,t7) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0g, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t6) & adj(t0,t8) & adj(t0,t9) & adj(t0,t10))).
fof(deg_t0h, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t6) & adj(t0,t8) & adj(t0,t9) & adj(t0,t11))).
fof(deg_t0i, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t6) & adj(t0,t8) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0j, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t6) & adj(t0,t9) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0k, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t7) & adj(t0,t8) & adj(t0,t9) & adj(t0,t10))).
fof(deg_t0l, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t7) & adj(t0,t8) & adj(t0,t9) & adj(t0,t11))).
fof(deg_t0m, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t7) & adj(t0,t8) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0n, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t7) & adj(t0,t9) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0o, axiom, ~(adj(t0,t4) & adj(t0,t5) & adj(t0,t8) & adj(t0,t9) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0p, axiom, ~(adj(t0,t4) & adj(t0,t6) & adj(t0,t7) & adj(t0,t8) & adj(t0,t9) & adj(t0,t10))).
fof(deg_t0q, axiom, ~(adj(t0,t4) & adj(t0,t6) & adj(t0,t7) & adj(t0,t8) & adj(t0,t9) & adj(t0,t11))).
fof(deg_t0r, axiom, ~(adj(t0,t4) & adj(t0,t6) & adj(t0,t7) & adj(t0,t8) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0s, axiom, ~(adj(t0,t4) & adj(t0,t6) & adj(t0,t7) & adj(t0,t9) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0t, axiom, ~(adj(t0,t4) & adj(t0,t6) & adj(t0,t8) & adj(t0,t9) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0u, axiom, ~(adj(t0,t4) & adj(t0,t7) & adj(t0,t8) & adj(t0,t9) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0v, axiom, ~(adj(t0,t5) & adj(t0,t6) & adj(t0,t7) & adj(t0,t8) & adj(t0,t9) & adj(t0,t10))).
fof(deg_t0w, axiom, ~(adj(t0,t5) & adj(t0,t6) & adj(t0,t7) & adj(t0,t8) & adj(t0,t9) & adj(t0,t11))).
fof(deg_t0x, axiom, ~(adj(t0,t5) & adj(t0,t6) & adj(t0,t7) & adj(t0,t8) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0y, axiom, ~(adj(t0,t5) & adj(t0,t6) & adj(t0,t7) & adj(t0,t9) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0z, axiom, ~(adj(t0,t5) & adj(t0,t6) & adj(t0,t8) & adj(t0,t9) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0aa, axiom, ~(adj(t0,t5) & adj(t0,t7) & adj(t0,t8) & adj(t0,t9) & adj(t0,t10) & adj(t0,t11))).
fof(deg_t0ab, axiom, ~(adj(t0,t6) & adj(t0,t7) & adj(t0,t8) & adj(t0,t9) & adj(t0,t10) & adj(t0,t11))).

% For coverage: each vertex in R must be adj to at least one vertex in I
fof(cover_t4, axiom, adj(t4,t0) | adj(t4,t1) | adj(t4,t2) | adj(t4,t3)).
fof(cover_t5, axiom, adj(t5,t0) | adj(t5,t1) | adj(t5,t2) | adj(t5,t3)).
fof(cover_t6, axiom, adj(t6,t0) | adj(t6,t1) | adj(t6,t2) | adj(t6,t3)).
fof(cover_t7, axiom, adj(t7,t0) | adj(t7,t1) | adj(t7,t2) | adj(t7,t3)).
fof(cover_t8, axiom, adj(t8,t0) | adj(t8,t1) | adj(t8,t2) | adj(t8,t3)).
fof(cover_t9, axiom, adj(t9,t0) | adj(t9,t1) | adj(t9,t2) | adj(t9,t3)).
fof(cover_t10, axiom, adj(t10,t0) | adj(t10,t1) | adj(t10,t2) | adj(t10,t3)).
fof(cover_t11, axiom, adj(t11,t0) | adj(t11,t1) | adj(t11,t2) | adj(t11,t3)).

% Goal: contradiction (this specific setup cannot be satisfied)
fof(goal, conjecture, $false).
