% R(3,4) <= 9: Degree bound lemma
%
% In a triangle-free graph with no 4-independent set, every vertex has degree <= 3.
% Proof: If deg(v) >= 4, then v's 4+ neighbors are pairwise non-adjacent (triangle-free),
%        forming a 4-independent set, contradiction.
%
% Expected: Theorem (contradiction from deg >= 4)

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% Assume triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% Assume no 4-independent set
fof(no_4_indep, axiom,
    ![A,B,C,D]: ((A!=B & A!=C & A!=D & B!=C & B!=D & C!=D) =>
                 (adj(A,B) | adj(A,C) | adj(A,D) | adj(B,C) | adj(B,D) | adj(C,D)))).

% Suppose vertex v has 4 distinct neighbors
fof(v_exists, axiom, ?[V]: $true).
fof(four_neighbors, axiom,
    ?[V,N1,N2,N3,N4]: (
        N1!=N2 & N1!=N3 & N1!=N4 & N2!=N3 & N2!=N4 & N3!=N4 &
        V!=N1 & V!=N2 & V!=N3 & V!=N4 &
        adj(V,N1) & adj(V,N2) & adj(V,N3) & adj(V,N4)
    )).

% Goal: Contradiction
fof(goal, conjecture, $false).
