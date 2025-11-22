% R(3,4) <= 9: Case analysis for degree 3 vertex
%
% Given 9 vertices, triangle-free, no 4-indep, and vertex v with degree exactly 3.
% v has 3 neighbors {a,b,c} (independent) and 5 non-neighbors {d,e,f,g,h}.
%
% Key insight: Among the 5 non-neighbors, if there's a 3-independent set I3,
% then {v} ∪ I3 is 4-independent (since v is non-adjacent to all of I3).
%
% So the 5 non-neighbors must have no 3-independent set, i.e., alpha({d,e,f,g,h}) <= 2.
% But a 5-vertex triangle-free graph with alpha <= 2 must be... very constrained.
%
% Actually: A 5-vertex graph with no K_3 and no I_3 is exactly C_5 (5-cycle).
% C_5 is the unique such graph! But C_5 is 2-regular.
%
% We'll show: the constraints from the neighbors {a,b,c} lead to contradiction.

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% 9 distinct vertices
fof(distinct_9, axiom,
    v!=a & v!=b & v!=c & v!=d & v!=e & v!=f & v!=g & v!=h &
    a!=b & a!=c & a!=d & a!=e & a!=f & a!=g & a!=h &
    b!=c & b!=d & b!=e & b!=f & b!=g & b!=h &
    c!=d & c!=e & c!=f & c!=g & c!=h &
    d!=e & d!=f & d!=g & d!=h &
    e!=f & e!=g & e!=h &
    f!=g & f!=h &
    g!=h).

% Domain closure
fof(domain, axiom, ![X]: (X=v | X=a | X=b | X=c | X=d | X=e | X=f | X=g | X=h)).

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% No 4-independent set
fof(no_4_indep, axiom,
    ![A,B,C,D]: ((A!=B & A!=C & A!=D & B!=C & B!=D & C!=D) =>
                 (adj(A,B) | adj(A,C) | adj(A,D) | adj(B,C) | adj(B,D) | adj(C,D)))).

% v has exactly 3 neighbors: a, b, c
fof(v_adj_a, axiom, adj(v,a)).
fof(v_adj_b, axiom, adj(v,b)).
fof(v_adj_c, axiom, adj(v,c)).
fof(v_not_adj_d, axiom, ~adj(v,d)).
fof(v_not_adj_e, axiom, ~adj(v,e)).
fof(v_not_adj_f, axiom, ~adj(v,f)).
fof(v_not_adj_g, axiom, ~adj(v,g)).
fof(v_not_adj_h, axiom, ~adj(v,h)).

% Goal: Contradiction (no such configuration exists)
fof(goal, conjecture, $false).
