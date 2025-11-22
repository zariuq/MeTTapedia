% Simplified: If V has 6 neighbors N1..N6, and neighbors are pairwise
% non-adjacent (triangle-free), then {N1..N6} is a 6-independent set.
% If no 6-indep exists, contradiction.

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).

% Triangle-free implies neighbors of V are pairwise non-adjacent
fof(n1_not_adj_n2, axiom, ~adj(n1,n2)).
fof(n1_not_adj_n3, axiom, ~adj(n1,n3)).
fof(n1_not_adj_n4, axiom, ~adj(n1,n4)).
fof(n1_not_adj_n5, axiom, ~adj(n1,n5)).
fof(n1_not_adj_n6, axiom, ~adj(n1,n6)).
fof(n2_not_adj_n3, axiom, ~adj(n2,n3)).
fof(n2_not_adj_n4, axiom, ~adj(n2,n4)).
fof(n2_not_adj_n5, axiom, ~adj(n2,n5)).
fof(n2_not_adj_n6, axiom, ~adj(n2,n6)).
fof(n3_not_adj_n4, axiom, ~adj(n3,n4)).
fof(n3_not_adj_n5, axiom, ~adj(n3,n5)).
fof(n3_not_adj_n6, axiom, ~adj(n3,n6)).
fof(n4_not_adj_n5, axiom, ~adj(n4,n5)).
fof(n4_not_adj_n6, axiom, ~adj(n4,n6)).
fof(n5_not_adj_n6, axiom, ~adj(n5,n6)).

% All distinct
fof(distinct, axiom,
    n1 != n2 & n1 != n3 & n1 != n4 & n1 != n5 & n1 != n6 &
    n2 != n3 & n2 != n4 & n2 != n5 & n2 != n6 &
    n3 != n4 & n3 != n5 & n3 != n6 &
    n4 != n5 & n4 != n6 &
    n5 != n6).

% No 6-independent set: any 6 distinct vertices have at least one edge
% Applied to n1..n6:
fof(no_6_indep, axiom,
    adj(n1,n2) | adj(n1,n3) | adj(n1,n4) | adj(n1,n5) | adj(n1,n6) |
    adj(n2,n3) | adj(n2,n4) | adj(n2,n5) | adj(n2,n6) |
    adj(n3,n4) | adj(n3,n5) | adj(n3,n6) |
    adj(n4,n5) | adj(n4,n6) |
    adj(n5,n6)).

% Goal: derive contradiction
fof(goal, conjecture, $false).
