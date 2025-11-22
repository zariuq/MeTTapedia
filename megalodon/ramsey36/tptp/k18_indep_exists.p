% TPTP: On 18 vertices with max degree 5, a 6-independent set must exist
%
% This is the key lemma for R(3,6) <= 18:
% If a graph on 18 vertices is triangle-free and has no 6-independent set,
% then by our earlier proof, max_degree <= 5.
% But with 18 vertices and max_degree <= 5, a 6-independent set MUST exist.
% Contradiction!
%
% Proof sketch:
% Use greedy algorithm. Start with v1. Exclude N(v1) (at most 5 vertices).
% Have 17 - 5 = 12 remaining vertices to choose from.
% Pick v2 from remaining. Exclude N(v2) ∩ remaining (at most 5).
% Have 12 - 5 = 7 remaining.
% Pick v3. Have 7 - 5 = 2 remaining.
% Pick v4. Now we might be stuck...
%
% Better: use fractional relaxation or probabilistic argument.
% Or: Caro-Wei gives alpha >= sum 1/(d_i + 1) >= 18/6 = 3. Too weak.
%
% Actually, the tight bound comes from the Lovász theta function or
% more refined counting.
%
% Let me try a specific construction.
% Suppose max_degree = 5. Then min_degree in complement >= 12.
% Complement has n=18 vertices, min_degree 12.
% By Dirac's theorem (if n >= 3 and min_deg >= n/2), complement has Hamiltonian cycle.
% 18/2 = 9, and 12 >= 9, so complement is Hamiltonian.
%
% But we want: complement has NO K_6 (which would mean original has 6-indep set).
% Actually we want to FIND K_6 in complement.
%
% Turán: complement has >= C(18,2) - 45 = 153 - 45 = 108 edges.
% ex(18, K_6) = edges in T(18, 5) = ?
% T(n, r) has n vertices in r parts, sizes floor(n/r) or ceil(n/r).
% T(18, 5) has parts of sizes 4, 4, 4, 3, 3 (sum = 18).
% Edges = C(18,2) - (C(4,2)*3 + C(3,2)*2) = 153 - (6*3 + 3*2) = 153 - 24 = 129.
%
% So ex(18, K_6) = 129. If complement has > 129 edges, it has K_6.
% We have complement edges >= 108. Not enough!
%
% So the edge counting alone doesn't work. We need the triangle-free structure.

% Key insight: In triangle-free graph with no 6-indep, neighbors of any vertex
% are independent. So if vertex v has 5 neighbors, those 5 plus any non-neighbor
% of v that is also not adjacent to any of the 5 neighbors would give 6-indep set.

% With 18 vertices, v has 5 neighbors, 12 non-neighbors.
% For no 6-indep: each of the 12 non-neighbors must be adjacent to at least one of the 5 neighbors.
% Total edges from 5 neighbors to the 12 non-neighbors: at most 5 * 5 = 25.
% (Each of the 5 neighbors has degree <= 5, already used 1 edge to v, so 4 edges left, but wait...)
% Actually the 5 neighbors have edges among themselves and to the 12 non-neighbors.
% Since triangle-free, the 5 neighbors have no edges among themselves.
% So each of the 5 neighbors has degree <= 5, with 1 edge to v, leaving 4 edges to non-neighbors.
% Total edges to non-neighbors: at most 5 * 4 = 20.
%
% We need to cover 12 non-neighbors with these 20 edges.
% 12 non-neighbors, each needs at least 1 edge from the 5 neighbors: doable with 12 edges.
% So 20 >= 12. No contradiction yet.
%
% But wait, the 12 non-neighbors also have degree <= 5 each.
% And they form a subgraph. Let's analyze that subgraph.

% Let S = {v's 5 neighbors}, T = {12 non-neighbors of v}.
% Edges within S: 0 (triangle-free, all in N(v)).
% Edges S to T: let's call this e_ST. Each s in S has degree <= 5, one edge to v, so <= 4 to T.
% e_ST <= 20.
%
% Edges within T: let's call this e_TT.
% T must not have 6-indep set! So among 12 vertices, no 6 independent.
% Turán: ex(12, K_6) in complement = ex(12, independent_6) in original.
% For alpha(T) < 6: edges in T >= f(12, 5).
%
% Actually, Ramsey: R(3,6) = 18 means among 18 vertices there's triangle or 6-indep.
% R(3,5) = 14 means among 14 vertices there's triangle or 5-indep.
% For 12 vertices: R(3,5) = 14 > 12, so we can't use it directly.
%
% But R(3,4) = 9 < 12. So among 12 vertices, either triangle or 4-indep set.
% In T (subgraph of triangle-free graph), T is also triangle-free.
% So T has 4-indep set. Let's call it I4 = {a, b, c, d} ⊆ T.
%
% Now consider: I4 has no edges among them (independent in T).
% Are they also independent from S? Each element of I4 is a non-neighbor of v.
% If any element of I4 is non-adjacent to all of S, then {v} ∪ I4 ∪ {that element} = 6-indep. Wait, v is adjacent to S, not I4.
% If a ∈ I4 is non-adjacent to all of S, then {a} ∪ S = 6 vertices, but S are all adjacent to v...
%
% Let me reconsider. We want 6-indep set in the whole graph (not just T).
% I4 = {a,b,c,d} are pairwise non-adjacent in T.
% v is non-adjacent to all of I4 (they're in T = non-neighbors of v).
% So {v, a, b, c, d} are pairwise non-adjacent? Let me check:
% - v non-adj to a,b,c,d ✓ (they're non-neighbors)
% - a,b,c,d pairwise non-adj ✓ (they're independent set in T)
% So {v, a, b, c, d} = 5-indep set!
%
% Now we need one more vertex to make 6-indep.
% We need w such that w is non-adjacent to v, a, b, c, d.
% w is non-adjacent to v: w ∈ T.
% w is non-adjacent to a, b, c, d: w is not in N(a) ∪ N(b) ∪ N(c) ∪ N(d) within T.
%
% |T| = 12. Each of a,b,c,d has degree <= 5 in whole graph.
% In T, each has degree <= 5 (could be less if some edges go to S).
% Let d_T(a) = degree of a within T. We have d_T(a) + e(a,S) + adj(a,v) <= 5.
% Since adj(a,v) = 0 (a is non-neighbor of v), d_T(a) + e(a,S) <= 5.
%
% So d_T(a) <= 5.
% |N_T(a) ∪ N_T(b) ∪ N_T(c) ∪ N_T(d)| <= d_T(a) + d_T(b) + d_T(c) + d_T(d) <= 20.
%
% Vertices in T not in I4 and not in any N_T(x) for x in I4:
% |T| - |I4| - |N_T(a) ∪ ...| >= 12 - 4 - 20 = -12. Negative!
%
% So this counting doesn't immediately give us a 6th vertex.
% But the neighborhoods might overlap!
%
% |N_T(a) ∪ N_T(b) ∪ N_T(c) ∪ N_T(d)| could be much less than 20 if they overlap.
% Since a,b,c,d are pairwise non-adjacent, none of them is in another's neighborhood.
% The neighborhoods are disjoint from I4.
%
% Hmm, this needs more careful analysis. Let me just test with Vampire.

% Formulation: 12 vertices in T, triangle-free, max degree 5 each,
% has 4-indep set I4. Find 5th vertex non-adjacent to I4.

fof(adj_sym, axiom, ![X,Y]: (adj(X,Y) => adj(Y,X))).
fof(adj_irref, axiom, ![X]: ~adj(X,X)).

% 12 vertices t1..t12
fof(t_distinct, axiom,
    t1!=t2 & t1!=t3 & t1!=t4 & t1!=t5 & t1!=t6 & t1!=t7 & t1!=t8 & t1!=t9 & t1!=t10 & t1!=t11 & t1!=t12 &
    t2!=t3 & t2!=t4 & t2!=t5 & t2!=t6 & t2!=t7 & t2!=t8 & t2!=t9 & t2!=t10 & t2!=t11 & t2!=t12 &
    t3!=t4 & t3!=t5 & t3!=t6 & t3!=t7 & t3!=t8 & t3!=t9 & t3!=t10 & t3!=t11 & t3!=t12 &
    t4!=t5 & t4!=t6 & t4!=t7 & t4!=t8 & t4!=t9 & t4!=t10 & t4!=t11 & t4!=t12 &
    t5!=t6 & t5!=t7 & t5!=t8 & t5!=t9 & t5!=t10 & t5!=t11 & t5!=t12 &
    t6!=t7 & t6!=t8 & t6!=t9 & t6!=t10 & t6!=t11 & t6!=t12 &
    t7!=t8 & t7!=t9 & t7!=t10 & t7!=t11 & t7!=t12 &
    t8!=t9 & t8!=t10 & t8!=t11 & t8!=t12 &
    t9!=t10 & t9!=t11 & t9!=t12 &
    t10!=t11 & t10!=t12 &
    t11!=t12).

% Triangle-free
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).

% Max degree 5 for each vertex (simplified: just for t1..t4)
fof(max_deg_t1, axiom,
    ~(adj(t1,t2) & adj(t1,t3) & adj(t1,t4) & adj(t1,t5) & adj(t1,t6) & adj(t1,t7))).
fof(max_deg_t2, axiom,
    ~(adj(t2,t1) & adj(t2,t3) & adj(t2,t4) & adj(t2,t5) & adj(t2,t6) & adj(t2,t7))).
fof(max_deg_t3, axiom,
    ~(adj(t3,t1) & adj(t3,t2) & adj(t3,t4) & adj(t3,t5) & adj(t3,t6) & adj(t3,t7))).
fof(max_deg_t4, axiom,
    ~(adj(t4,t1) & adj(t4,t2) & adj(t4,t3) & adj(t4,t5) & adj(t4,t6) & adj(t4,t7))).

% No 5-independent set (to force structure)
fof(no_5_indep, axiom,
    ![A,B,C,D,E]:
    ((A != B & A != C & A != D & A != E & B != C & B != D & B != E & C != D & C != E & D != E) =>
    (adj(A,B) | adj(A,C) | adj(A,D) | adj(A,E) | adj(B,C) | adj(B,D) | adj(B,E) | adj(C,D) | adj(C,E) | adj(D,E)))).

% Goal: find 4-independent set (by R(3,4)=9 < 12, this must exist in triangle-free graph on 12 vertices)
fof(goal, conjecture,
    ?[A,B,C,D]: (A != B & A != C & A != D & B != C & B != D & C != D &
                  ~adj(A,B) & ~adj(A,C) & ~adj(A,D) & ~adj(B,C) & ~adj(B,D) & ~adj(C,D))).
