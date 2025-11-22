% TPTP: R(3,4) = 9 implies 4-independent set exists in triangle-free graph on 9+ vertices
%
% By R(3,4) = 9: Any graph on 9 vertices has either K_3 (triangle) or independent set of size 4.
% In a triangle-free graph on 9 vertices, the first option is excluded.
% Therefore, a 4-independent set must exist.

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% 9 distinct vertices
fof(distinct, axiom,
    v1!=v2 & v1!=v3 & v1!=v4 & v1!=v5 & v1!=v6 & v1!=v7 & v1!=v8 & v1!=v9 &
    v2!=v3 & v2!=v4 & v2!=v5 & v2!=v6 & v2!=v7 & v2!=v8 & v2!=v9 &
    v3!=v4 & v3!=v5 & v3!=v6 & v3!=v7 & v3!=v8 & v3!=v9 &
    v4!=v5 & v4!=v6 & v4!=v7 & v4!=v8 & v4!=v9 &
    v5!=v6 & v5!=v7 & v5!=v8 & v5!=v9 &
    v6!=v7 & v6!=v8 & v6!=v9 &
    v7!=v8 & v7!=v9 &
    v8!=v9).

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% R(3,4) = 9: On any 9 distinct vertices, either K_3 or I_4 exists
% Since we assume triangle-free, I_4 must exist
% Encode as: for any 4 vertices from the 9, at least one pair has no edge
% (This is the contrapositive of: if all 4-sets have an edge, then K_3 exists)

% Actually, let's encode R(3,4)=9 directly by listing all 4-independent set possibilities
% and asserting one exists (since triangle is ruled out)

% Goal: There exist 4 pairwise non-adjacent vertices
fof(goal, conjecture,
    ?[A,B,C,D]: (
        (A = v1 | A = v2 | A = v3 | A = v4 | A = v5 | A = v6 | A = v7 | A = v8 | A = v9) &
        (B = v1 | B = v2 | B = v3 | B = v4 | B = v5 | B = v6 | B = v7 | B = v8 | B = v9) &
        (C = v1 | C = v2 | C = v3 | C = v4 | C = v5 | C = v6 | C = v7 | C = v8 | C = v9) &
        (D = v1 | D = v2 | D = v3 | D = v4 | D = v5 | D = v6 | D = v7 | D = v8 | D = v9) &
        A != B & A != C & A != D & B != C & B != D & C != D &
        ~adj(A,B) & ~adj(A,C) & ~adj(A,D) & ~adj(B,C) & ~adj(B,D) & ~adj(C,D))).
