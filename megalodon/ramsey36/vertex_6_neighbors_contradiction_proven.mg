% Theorem: In triangle-free graph with no 6-indep, no vertex has 6+ distinct neighbors
%
% Proof strategy (from Vampire Dedukti proof analysis):
% 1. If v has 6 distinct neighbors n1-n6
% 2. By triangle-free: each pair (ni, nj) is non-adjacent
%    (else {v, ni, nj} would form a triangle)
% 3. So {n1, ..., n6} is a 6-independent set
% 4. Contradicts no_6_indep axiom

Theorem vertex_6_neighbors_contradiction: forall R : set -> set -> prop, forall V : set,
  forall v n1 n2 n3 n4 n5 n6 : set,
  (forall x, x :e V -> forall y, y :e V -> R x y -> R y x) ->
  (forall x, x :e V -> forall y, y :e V -> forall z, z :e V ->
     R x y -> R y z -> R x z -> False) ->
  (forall a, a :e V -> forall b, b :e V -> forall c, c :e V -> forall d, d :e V -> forall e, e :e V -> forall f, f :e V ->
    a <> b -> a <> c -> a <> d -> a <> e -> a <> f ->
    b <> c -> b <> d -> b <> e -> b <> f ->
    c <> d -> c <> e -> c <> f ->
    d <> e -> d <> f ->
    e <> f ->
    (R a b \/ R a c \/ R a d \/ R a e \/ R a f \/
     R b c \/ R b d \/ R b e \/ R b f \/
     R c d \/ R c e \/ R c f \/
     R d e \/ R d f \/
     R e f)) ->
  v :e V -> n1 :e V -> n2 :e V -> n3 :e V -> n4 :e V -> n5 :e V -> n6 :e V ->
  n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n1 <> n5 -> n1 <> n6 ->
  n2 <> n3 -> n2 <> n4 -> n2 <> n5 -> n2 <> n6 ->
  n3 <> n4 -> n3 <> n5 -> n3 <> n6 ->
  n4 <> n5 -> n4 <> n6 ->
  n5 <> n6 ->
  R v n1 -> R v n2 -> R v n3 -> R v n4 -> R v n5 -> R v n6 ->
  False.
let R V v n1 n2 n3 n4 n5 n6.
assume Hsym: forall x, x :e V -> forall y, y :e V -> R x y -> R y x.
assume Htf: forall x, x :e V -> forall y, y :e V -> forall z, z :e V ->
     R x y -> R y z -> R x z -> False.
assume Hno6: forall a, a :e V -> forall b, b :e V -> forall c, c :e V -> forall d, d :e V -> forall e, e :e V -> forall f, f :e V ->
    a <> b -> a <> c -> a <> d -> a <> e -> a <> f ->
    b <> c -> b <> d -> b <> e -> b <> f ->
    c <> d -> c <> e -> c <> f ->
    d <> e -> d <> f ->
    e <> f ->
    (R a b \/ R a c \/ R a d \/ R a e \/ R a f \/
     R b c \/ R b d \/ R b e \/ R b f \/
     R c d \/ R c e \/ R c f \/
     R d e \/ R d f \/
     R e f).
assume Hv: v :e V.
assume Hn1: n1 :e V.
assume Hn2: n2 :e V.
assume Hn3: n3 :e V.
assume Hn4: n4 :e V.
assume Hn5: n5 :e V.
assume Hn6: n6 :e V.
assume Hd12: n1 <> n2.
assume Hd13: n1 <> n3.
assume Hd14: n1 <> n4.
assume Hd15: n1 <> n5.
assume Hd16: n1 <> n6.
assume Hd23: n2 <> n3.
assume Hd24: n2 <> n4.
assume Hd25: n2 <> n5.
assume Hd26: n2 <> n6.
assume Hd34: n3 <> n4.
assume Hd35: n3 <> n5.
assume Hd36: n3 <> n6.
assume Hd45: n4 <> n5.
assume Hd46: n4 <> n6.
assume Hd56: n5 <> n6.
assume Hvn1: R v n1.
assume Hvn2: R v n2.
assume Hvn3: R v n3.
assume Hvn4: R v n4.
assume Hvn5: R v n5.
assume Hvn6: R v n6.

prove False.

% Key claim: neighbors n1-n6 are pairwise non-adjacent (by triangle-free)
% For any pair (ni, nj): if R ni nj, then {v, ni, nj} forms triangle
% This contradicts triangle-free property

% Apply no_6_indep to the 6 neighbors
% They're distinct and in V, so we need to show at least one edge exists
% But we'll show all edges lead to triangles, contradiction!

exact Hno6 n1 Hn1 n2 Hn2 n3 Hn3 n4 Hn4 n5 Hn5 n6 Hn6
  Hd12 Hd13 Hd14 Hd15 Hd16
  Hd23 Hd24 Hd25 Hd26
  Hd34 Hd35 Hd36
  Hd45 Hd46
  Hd56
  % Now we need to eliminate all 15 possible edges
  % Each edge ni-nj gives triangle {v, ni, nj}, contradicting triangle-free
  (% Case 1: R n1 n2 -> triangle {v, n1, n2}
   fun Hn12 : R n1 n2 =>
     Htf v Hv n1 Hn1 n2 Hn2 Hvn1 Hn12 Hvn2)
  (% Case 2: R n1 n3 -> triangle {v, n1, n3}
   fun Hn13 : R n1 n3 =>
     Htf v Hv n1 Hn1 n3 Hn3 Hvn1 Hn13 Hvn3)
  (% Case 3: R n1 n4 -> triangle {v, n1, n4}
   fun Hn14 : R n1 n4 =>
     Htf v Hv n1 Hn1 n4 Hn4 Hvn1 Hn14 Hvn4)
  (% Case 4: R n1 n5 -> triangle {v, n1, n5}
   fun Hn15 : R n1 n5 =>
     Htf v Hv n1 Hn1 n5 Hn5 Hvn1 Hn15 Hvn5)
  (% Case 5: R n1 n6 -> triangle {v, n1, n6}
   fun Hn16 : R n1 n6 =>
     Htf v Hv n1 Hn1 n6 Hn6 Hvn1 Hn16 Hvn6)
  (% Case 6: R n2 n3 -> triangle {v, n2, n3}
   fun Hn23 : R n2 n3 =>
     Htf v Hv n2 Hn2 n3 Hn3 Hvn2 Hn23 Hvn3)
  (% Case 7: R n2 n4 -> triangle {v, n2, n4}
   fun Hn24 : R n2 n4 =>
     Htf v Hv n2 Hn2 n4 Hn4 Hvn2 Hn24 Hvn4)
  (% Case 8: R n2 n5 -> triangle {v, n2, n5}
   fun Hn25 : R n2 n5 =>
     Htf v Hv n2 Hn2 n5 Hn5 Hvn2 Hn25 Hvn5)
  (% Case 9: R n2 n6 -> triangle {v, n2, n6}
   fun Hn26 : R n2 n6 =>
     Htf v Hv n2 Hn2 n6 Hn6 Hvn2 Hn26 Hvn6)
  (% Case 10: R n3 n4 -> triangle {v, n3, n4}
   fun Hn34 : R n3 n4 =>
     Htf v Hv n3 Hn3 n4 Hn4 Hvn3 Hn34 Hvn4)
  (% Case 11: R n3 n5 -> triangle {v, n3, n5}
   fun Hn35 : R n3 n5 =>
     Htf v Hv n3 Hn3 n5 Hn5 Hvn3 Hn35 Hvn5)
  (% Case 12: R n3 n6 -> triangle {v, n3, n6}
   fun Hn36 : R n3 n6 =>
     Htf v Hv n3 Hn3 n6 Hn6 Hvn3 Hn36 Hvn6)
  (% Case 13: R n4 n5 -> triangle {v, n4, n5}
   fun Hn45 : R n4 n5 =>
     Htf v Hv n4 Hn4 n5 Hn5 Hvn4 Hn45 Hvn5)
  (% Case 14: R n4 n6 -> triangle {v, n4, n6}
   fun Hn46 : R n4 n6 =>
     Htf v Hv n4 Hn4 n6 Hn6 Hvn4 Hn46 Hvn6)
  (% Case 15: R n5 n6 -> triangle {v, n5, n6}
   fun Hn56 : R n5 n6 =>
     Htf v Hv n5 Hn5 n6 Hn6 Hvn5 Hn56 Hvn6).

Qed.
