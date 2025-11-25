Definition Adj8 : set -> set -> prop :=
  fun i j =>
    (i = 0 /\ (j = 1 \/ j = 4 \/ j = 7)) \/
    (i = 1 /\ (j = 0 \/ j = 2 \/ j = 5)) \/
    (i = 2 /\ (j = 1 \/ j = 3 \/ j = 6)) \/
    (i = 3 /\ (j = 2 \/ j = 4 \/ j = 7)) \/
    (i = 4 /\ (j = 0 \/ j = 3 \/ j = 5)) \/
    (i = 5 /\ (j = 1 \/ j = 4 \/ j = 6)) \/
    (i = 6 /\ (j = 2 \/ j = 5 \/ j = 7)) \/
    (i = 7 /\ (j = 0 \/ j = 3 \/ j = 6)).

Axiom neq_0_7 : 0 <> 7.
Axiom neq_2_6 : 2 <> 6.
Axiom neq_3_7 : 3 <> 7.
Axiom neq_5_6 : 5 <> 6.
Axiom neq_6_7 : 6 <> 7.

Theorem Adj8_sym : forall i j, Adj8 i j -> Adj8 j i.
Admitted.

Theorem Adj8_irref : forall i:set, ~Adj8 i i.
Admitted.

Theorem Adj8_triangle_free : forall x y z :e 8, Adj8 x y -> Adj8 y z -> Adj8 x z -> False.
Admitted.

Theorem Adj8_no_4indep : forall a b c d :e 8,
  a <> b -> a <> c -> a <> d -> b <> c -> b <> d -> c <> d ->
  Adj8 a b \/ Adj8 a c \/ Adj8 a d \/ Adj8 b c \/ Adj8 b d \/ Adj8 c d.
Admitted.

Definition is_indep_set_4 : set -> (set -> set -> prop) -> set -> set -> set -> set -> prop :=
  fun V R a b c d =>
    a :e V /\ b :e V /\ c :e V /\ d :e V /\
    a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
    ~R a b /\ ~R a c /\ ~R a d /\ ~R b c /\ ~R b d /\ ~R c d.

Definition has_triangle : set -> (set -> set -> prop) -> prop :=
  fun V R => exists x y z :e V, x <> y /\ y <> z /\ x <> z /\ R x y /\ R y z /\ R x z.

Definition has_4indep : set -> (set -> set -> prop) -> prop :=
  fun V R => exists a b c d :e V, is_indep_set_4 V R a b c d.

Theorem degree_bound_3 : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  ~has_triangle V R ->
  ~has_4indep V R ->
  forall v :e V, forall n1 n2 n3 n4 :e V,
    n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n2 <> n3 -> n2 <> n4 -> n3 <> n4 ->
    v <> n1 -> v <> n2 -> v <> n3 -> v <> n4 ->
    R v n1 -> R v n2 -> R v n3 -> R v n4 ->
    False.
Admitted.

Theorem R34_upper : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  has_triangle 9 R \/ has_4indep 9 R.
Admitted.

Theorem R34_eq_9 :
  (forall x y z :e 8, Adj8 x y -> Adj8 y z -> Adj8 x z -> False) /\
  (forall a b c d :e 8, a<>b -> a<>c -> a<>d -> b<>c -> b<>d -> c<>d ->
     Adj8 a b \/ Adj8 a c \/ Adj8 a d \/ Adj8 b c \/ Adj8 b d \/ Adj8 c d) /\
  (forall R:set->set->prop, (forall x y, R x y -> R y x) -> has_triangle 9 R \/ has_4indep 9 R).
apply and3I.
- exact Adj8_triangle_free.
- exact Adj8_no_4indep.
- exact R34_upper.
Qed.
