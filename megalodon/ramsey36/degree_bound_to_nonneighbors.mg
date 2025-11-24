(* Connecting vertex_degree_bound to vertex_has_12_nonneighbors *)

(* Import vertex_degree_bound theorem *)
Axiom vertex_6_neighbors_contradiction:
  forall R : set -> set -> prop,
  forall V : set,
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

(* Strategy:
   - vertex_degree_bound says: no vertex can have 6 neighbors
   - Therefore: every vertex has at most 5 neighbors
   - Therefore: every vertex has at least 18 - 1 - 5 = 12 non-neighbors

   To prove this formally, we need to:
   1. Show that if v has < 12 non-neighbors, then v has >= 6 neighbors
   2. Pick 6 distinct neighbors and apply vertex_6_neighbors_contradiction
*)

Theorem vertex_has_12_nonneighbors_sketch : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  (forall x, x :e 18 -> forall y, y :e 18 -> forall z, z :e 18 ->
     R x y -> R y z -> R x z -> False) ->
  (forall a, a :e 18 -> forall b, b :e 18 -> forall c, c :e 18 -> forall d, d :e 18 -> forall e, e :e 18 -> forall f, f :e 18 ->
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
  forall v :e 18, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T.
Admitted.

(* TODO: This requires:
   1. Cardinality arithmetic: |18 \ {v}| = 17
   2. Partition: neighbors(v) ∪ non-neighbors(v) = 18 \ {v}
   3. Counting: |neighbors(v)| + |non-neighbors(v)| = 17
   4. Contrapositive: if |non-neighbors(v)| < 12, then |neighbors(v)| >= 6
   5. Extract 6 distinct neighbors and apply vertex_6_neighbors_contradiction
*)
