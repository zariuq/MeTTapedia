% TPTP problem: In a triangle-free graph with no 6-independent set,
% no vertex can have 6+ neighbors (since neighbors form independent set)

% Adjacency predicate
fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% Triangle-free
fof(triangle_free, axiom,
    ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% In triangle-free graph, neighbors of any vertex are pairwise non-adjacent
% This is a direct consequence of triangle_free
fof(neighbors_indep, axiom,
    ![V,X,Y]: ((adj(V,X) & adj(V,Y) & X != Y) => ~adj(X,Y))).

% No 6-independent set exists
% For any 6 distinct vertices, at least one pair is adjacent
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

% Goal: No vertex can have 6 distinct neighbors
% (because those 6 neighbors would form a 6-independent set)
fof(max_degree_5, conjecture,
    ![V,N1,N2,N3,N4,N5,N6]:
      ((N1 != N2 & N1 != N3 & N1 != N4 & N1 != N5 & N1 != N6 &
        N2 != N3 & N2 != N4 & N2 != N5 & N2 != N6 &
        N3 != N4 & N3 != N5 & N3 != N6 &
        N4 != N5 & N4 != N6 &
        N5 != N6) =>
       ~(adj(V,N1) & adj(V,N2) & adj(V,N3) & adj(V,N4) & adj(V,N5) & adj(V,N6)))).
