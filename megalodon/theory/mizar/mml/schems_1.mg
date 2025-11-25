Theorem Schemat0 : forall P:set -> prop, (forall a:set, P a) -> exists a:set, P a.
admit.
Qed.

Theorem Schemat3 : forall S:set -> set -> prop,
  (exists a:set, forall b:set, S a b) -> forall b:set, exists a:set, S a b.
admit.
Qed.

Theorem Schemat8 : forall P Q:set -> prop,
  (forall a:set, P a -> Q a) -> (forall a:set, P a) -> forall a:set, Q a.
admit.
Qed.

Theorem Schemat9 : forall P Q:set -> prop,
  (forall a:set, P a <-> Q a) ->
  ((forall a:set, P a) <-> (forall a:set, Q a)).
admit.
Qed.

Theorem Schemat17 : forall P:set -> prop, forall T:prop,
  (forall a:set, P a -> T) -> (forall a:set, P a) -> T.
admit.
Qed.

Theorem Schemat18a : forall P Q:set -> prop,
  ((exists a:set, P a) \/ (forall b:set, Q b)) ->
  exists a:set, forall b:set, P a \/ Q b.
admit.
Qed.

Theorem Schemat18b : forall P Q:set -> prop,
  (exists a:set, forall b:set, P a \/ Q b) ->
  (exists a:set, P a) \/ (forall b:set, Q b).
admit.
Qed.

Theorem Schemat20b : forall P Q:set -> prop,
  (forall b:set, exists a:set, P a \/ Q b) ->
  exists a:set, forall b:set, P a \/ Q b.
admit.
Qed.

Theorem Schemat22a : forall P Q:set -> prop,
  (exists a:set, P a) /\ (forall b:set, Q b) ->
  forall b:set, exists a:set, P a /\ Q b.
admit.
Qed.

Theorem Schemat22b : forall P Q:set -> prop,
  (forall b:set, exists a:set, P a /\ Q b) ->
  (exists a:set, P a) /\ (forall b:set, Q b).
admit.
Qed.

Theorem Schemat23b : forall P Q:set -> prop,
  (forall b:set, exists a:set, P a /\ Q b) ->
  exists a:set, forall b:set, P a /\ Q b.
admit.
Qed.

Theorem Schemat28 : forall S:set -> set -> prop,
  (forall a b:set, S a b) -> exists b:set, forall a:set, S a b.
admit.
Qed.

Theorem Schemat30 : forall S:set -> set -> prop,
  (exists a:set, forall b:set, S a b) -> exists a:set, S a a.
admit.
Qed.

Theorem Schemat31 : forall S:set -> set -> prop,
  (forall a:set, S a a) -> forall a:set, exists b:set, S b a.
admit.
Qed.

Theorem Schemat33 : forall S:set -> set -> prop,
  (forall a:set, S a a) -> forall a:set, exists b:set, S a b.
admit.
Qed.

Theorem Schemat36 : forall S:set -> set -> prop,
  (forall b:set, exists a:set, S a b) -> exists a:set, exists b:set, S a b.
admit.
Qed.
