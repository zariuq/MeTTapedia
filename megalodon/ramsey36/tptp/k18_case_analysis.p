% TPTP: Case analysis for R(3,6) <= 18
%
% In K_18, pick vertex v0. It has 17 neighbors.
% Let r = red_degree(v0), b = blue_degree(v0). Then r + b = 17.
%
% Key known bounds:
%   R(2,6) = 6: among 6 vertices, red edge or they're all blue-independent
%   R(3,5) = 14: among 14 vertices, red K_3 or blue K_5
%
% Case 1: r >= 6 (red degree at least 6)
%   Red neighborhood N_r has 6+ vertices.
%   Among these 6+ vertices, by R(2,6) = 6:
%   Either there's a red edge (forming red K_3 with v0), or
%   There's no red edge (so these 6 form blue K_6 as they're all blue-connected)
%
% Case 2: r <= 5, so b >= 12
%   If b >= 14: Blue neighborhood has 14+ vertices.
%   By R(3,5) = 14: either red K_3, or blue K_5 in N_b.
%   Blue K_5 in N_b + v0 = blue K_6 ✓
%
% Case 3: r <= 5 and b <= 13, meaning 12 <= b <= 13
%   This is the hard case. We have:
%   - Red neighborhood of size <= 5 (forms independent set since no red triangle)
%   - Blue neighborhood of size 12 or 13
%   - Need to show either red K_3 in blue neighborhood, or blue K_5 there
%
%   Since R(3,5) = 14 and we only have 12-13 blue neighbors, can't directly apply.
%   Need more refined argument here.

% For case 3, the approach is:
% Consider vertex v1 in blue neighborhood of v0.
% v1's red degree in the blue neighborhood is at most 4 (else red N(v1) has 5 vertices
% which form blue K_5 since triangle-free).
% So v1 has at least 11-4=7 blue neighbors within N_b(v0).
% Continue this analysis...

% For now, let's verify Case 1: r >= 6 implies result
fof(red_sym, axiom, ![X,Y]: (red(X,Y) => red(Y,X))).
fof(blue_sym, axiom, ![X,Y]: (blue(X,Y) => blue(Y,X))).

% Edge coloring: distinct vertices are either red or blue connected
fof(edge_coloring, axiom, ![X,Y]: (X != Y => (red(X,Y) <=> ~blue(X,Y)))).

% Vertices n1..n6 are the 6 red neighbors of v0
fof(red_neighbors, axiom,
    red(v0,n1) & red(v0,n2) & red(v0,n3) & red(v0,n4) & red(v0,n5) & red(v0,n6)).

% All distinct
fof(distinct, axiom,
    v0 != n1 & v0 != n2 & v0 != n3 & v0 != n4 & v0 != n5 & v0 != n6 &
    n1 != n2 & n1 != n3 & n1 != n4 & n1 != n5 & n1 != n6 &
    n2 != n3 & n2 != n4 & n2 != n5 & n2 != n6 &
    n3 != n4 & n3 != n5 & n3 != n6 &
    n4 != n5 & n4 != n6 &
    n5 != n6).

% No red triangle
fof(no_red_K3, axiom, ![X,Y,Z]: ~(red(X,Y) & red(Y,Z) & red(X,Z))).

% In particular, n1..n6 form an independent set in red graph
% This means all pairs among n1..n6 are non-red, hence blue

% R(2,6) = 6 means: among any 6 vertices, either red edge or no red edges
% Since n1..n6 can't have red edges (would form red K_3 with v0),
% all pairs are blue, forming blue K_6!

% Goal: blue K_6 exists among n1..n6
fof(goal, conjecture,
    blue(n1,n2) & blue(n1,n3) & blue(n1,n4) & blue(n1,n5) & blue(n1,n6) &
    blue(n2,n3) & blue(n2,n4) & blue(n2,n5) & blue(n2,n6) &
    blue(n3,n4) & blue(n3,n5) & blue(n3,n6) &
    blue(n4,n5) & blue(n4,n6) &
    blue(n5,n6)).
