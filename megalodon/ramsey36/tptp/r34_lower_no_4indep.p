% R(3,4) > 8: Verify witness graph C_8(1,4) has no 4-independent set
%
% This file verifies that the circulant graph C_8(1,4) has independence number <= 3.
% Expected result: Theorem (no 4-independent set exists)

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% 8 distinct vertices
fof(distinct, axiom,
    v0!=v1 & v0!=v2 & v0!=v3 & v0!=v4 & v0!=v5 & v0!=v6 & v0!=v7 &
    v1!=v2 & v1!=v3 & v1!=v4 & v1!=v5 & v1!=v6 & v1!=v7 &
    v2!=v3 & v2!=v4 & v2!=v5 & v2!=v6 & v2!=v7 &
    v3!=v4 & v3!=v5 & v3!=v6 & v3!=v7 &
    v4!=v5 & v4!=v6 & v4!=v7 &
    v5!=v6 & v5!=v7 &
    v6!=v7).

% Domain closure
fof(domain, axiom, ![X]: (X=v0 | X=v1 | X=v2 | X=v3 | X=v4 | X=v5 | X=v6 | X=v7)).

% C_8(1,4) edges
fof(e01, axiom, adj(v0,v1)).
fof(e07, axiom, adj(v0,v7)).
fof(e04, axiom, adj(v0,v4)).
fof(e12, axiom, adj(v1,v2)).
fof(e15, axiom, adj(v1,v5)).
fof(e23, axiom, adj(v2,v3)).
fof(e26, axiom, adj(v2,v6)).
fof(e34, axiom, adj(v3,v4)).
fof(e37, axiom, adj(v3,v7)).
fof(e45, axiom, adj(v4,v5)).
fof(e56, axiom, adj(v5,v6)).
fof(e67, axiom, adj(v6,v7)).

% Non-edges
fof(n02, axiom, ~adj(v0,v2)).
fof(n03, axiom, ~adj(v0,v3)).
fof(n05, axiom, ~adj(v0,v5)).
fof(n06, axiom, ~adj(v0,v6)).
fof(n13, axiom, ~adj(v1,v3)).
fof(n14, axiom, ~adj(v1,v4)).
fof(n16, axiom, ~adj(v1,v6)).
fof(n17, axiom, ~adj(v1,v7)).
fof(n24, axiom, ~adj(v2,v4)).
fof(n25, axiom, ~adj(v2,v5)).
fof(n27, axiom, ~adj(v2,v7)).
fof(n35, axiom, ~adj(v3,v5)).
fof(n36, axiom, ~adj(v3,v6)).
fof(n46, axiom, ~adj(v4,v6)).
fof(n47, axiom, ~adj(v4,v7)).
fof(n57, axiom, ~adj(v5,v7)).

% Goal: No 4-independent set exists
% A 4-independent set is 4 pairwise non-adjacent vertices
fof(no_4_indep, conjecture,
    ![A,B,C,D]: (
        (A!=B & A!=C & A!=D & B!=C & B!=D & C!=D) =>
        (adj(A,B) | adj(A,C) | adj(A,D) | adj(B,C) | adj(B,D) | adj(C,D))
    )).
