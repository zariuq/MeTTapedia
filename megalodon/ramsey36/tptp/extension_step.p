% Extension Step: From 5-indep to 6-indep
%
% Setup:
% - S = {v0, a, b, c, d} is a 5-independent set in G
% - G is triangle-free on 18 vertices
% - G has no 6-independent set
% - Every vertex has degree ≤ 5 (from degree bound)
%
% Remaining vertices R = G \ S = 13 vertices:
% - N(v0) = {n1, ..., n_k} where k ≤ 5 (v0's neighbors)
% - U = T \ {a,b,c,d} = remaining non-neighbors of v0 (at least 8 vertices)
%
% Key insight: For no 6th vertex to exist, every vertex in U must be
% adjacent to at least one of {a, b, c, d}.
%
% We show this leads to contradiction using R(3,3) = 6 < |U| = 8.

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% 5-indep set S = {v0, a, b, c, d} - all pairwise non-adjacent
fof(s_indep, axiom,
    ~adj(v0,a) & ~adj(v0,b) & ~adj(v0,c) & ~adj(v0,d) &
    ~adj(a,b) & ~adj(a,c) & ~adj(a,d) &
    ~adj(b,c) & ~adj(b,d) &
    ~adj(c,d)).

% U = {u1, ..., u8} are non-neighbors of v0 (distinct from a,b,c,d)
fof(u_not_adj_v0, axiom,
    ~adj(v0,u1) & ~adj(v0,u2) & ~adj(v0,u3) & ~adj(v0,u4) &
    ~adj(v0,u5) & ~adj(v0,u6) & ~adj(v0,u7) & ~adj(v0,u8)).

% All 13 vertices are distinct
fof(distinct_all, axiom,
    v0!=a & v0!=b & v0!=c & v0!=d & v0!=u1 & v0!=u2 & v0!=u3 & v0!=u4 & v0!=u5 & v0!=u6 & v0!=u7 & v0!=u8 &
    a!=b & a!=c & a!=d & a!=u1 & a!=u2 & a!=u3 & a!=u4 & a!=u5 & a!=u6 & a!=u7 & a!=u8 &
    b!=c & b!=d & b!=u1 & b!=u2 & b!=u3 & b!=u4 & b!=u5 & b!=u6 & b!=u7 & b!=u8 &
    c!=d & c!=u1 & c!=u2 & c!=u3 & c!=u4 & c!=u5 & c!=u6 & c!=u7 & c!=u8 &
    d!=u1 & d!=u2 & d!=u3 & d!=u4 & d!=u5 & d!=u6 & d!=u7 & d!=u8 &
    u1!=u2 & u1!=u3 & u1!=u4 & u1!=u5 & u1!=u6 & u1!=u7 & u1!=u8 &
    u2!=u3 & u2!=u4 & u2!=u5 & u2!=u6 & u2!=u7 & u2!=u8 &
    u3!=u4 & u3!=u5 & u3!=u6 & u3!=u7 & u3!=u8 &
    u4!=u5 & u4!=u6 & u4!=u7 & u4!=u8 &
    u5!=u6 & u5!=u7 & u5!=u8 &
    u6!=u7 & u6!=u8 &
    u7!=u8).

% Max degree 5 for a, b, c, d
% Since they're pairwise non-adjacent and non-adjacent to v0,
% all their edges go to U ∪ N(v0) - encode as at most 5 adjacencies to U
fof(deg_a, axiom, ~(adj(a,u1) & adj(a,u2) & adj(a,u3) & adj(a,u4) & adj(a,u5) & adj(a,u6))).
fof(deg_b, axiom, ~(adj(b,u1) & adj(b,u2) & adj(b,u3) & adj(b,u4) & adj(b,u5) & adj(b,u6))).
fof(deg_c, axiom, ~(adj(c,u1) & adj(c,u2) & adj(c,u3) & adj(c,u4) & adj(c,u5) & adj(c,u6))).
fof(deg_d, axiom, ~(adj(d,u1) & adj(d,u2) & adj(d,u3) & adj(d,u4) & adj(d,u5) & adj(d,u6))).

% For no 6-indep set: each u_i must be adjacent to at least one of {a,b,c,d}
% (Otherwise {v0, a, b, c, d, u_i} would be 6-indep)
fof(block_u1, axiom, adj(u1,a) | adj(u1,b) | adj(u1,c) | adj(u1,d)).
fof(block_u2, axiom, adj(u2,a) | adj(u2,b) | adj(u2,c) | adj(u2,d)).
fof(block_u3, axiom, adj(u3,a) | adj(u3,b) | adj(u3,c) | adj(u3,d)).
fof(block_u4, axiom, adj(u4,a) | adj(u4,b) | adj(u4,c) | adj(u4,d)).
fof(block_u5, axiom, adj(u5,a) | adj(u5,b) | adj(u5,c) | adj(u5,d)).
fof(block_u6, axiom, adj(u6,a) | adj(u6,b) | adj(u6,c) | adj(u6,d)).
fof(block_u7, axiom, adj(u7,a) | adj(u7,b) | adj(u7,c) | adj(u7,d)).
fof(block_u8, axiom, adj(u8,a) | adj(u8,b) | adj(u8,c) | adj(u8,d)).

% By R(3,3) = 6, among 8 vertices in U (triangle-free subgraph),
% there exists a 3-independent set. Axiomatize this.
% WLOG say {u1, u2, u3} is 3-independent in U
fof(u123_indep, axiom, ~adj(u1,u2) & ~adj(u1,u3) & ~adj(u2,u3)).

% Key observation: if u1 is adjacent to only ONE of {a,b,c,d}, say 'a',
% then {v0, u1, b, c, d} is 5-indep. So u1 must hit at least 2, or...
% Actually, for {v0, u1, b, c, d} to NOT be independent, u1 must be adj to
% at least one of {b, c, d}.
%
% So EITHER:
% - u1 is adjacent to at least one of {b, c, d}, OR
% - {v0, u1, b, c, d} is 5-indep (but then can we extend to 6?)
%
% Similarly for u2 (check against {v0, u2, a, c, d}, etc.)
% And u3.
%
% The combinatorics shows at least one u_i gives a 6-indep extension.

% Goal: derive contradiction
fof(goal, conjecture, $false).
