Definition log_bound : set -> set -> prop :=
  fun m k => k :e omega /\ k :e m /\ 1 :e k.

Definition poly_size : set -> set -> prop :=
  fun size k => size :e omega /\ size c= k.

Definition DecoderBounded : set -> set -> prop :=
  fun m i => exists k, exists size,
    k :e omega /\ size :e omega /\ log_bound m k /\ poly_size size k.

Definition LocalTreeLike : set -> set -> set -> prop :=
  fun m i k => m :e omega /\ i :e m /\ k :e omega /\ log_bound m k.

Definition UnitPropWorks : set -> set -> set -> prop :=
  fun m i k => LocalTreeLike m i k.

Definition ConditionalDetermines : set -> set -> set -> prop :=
  fun m i k => UnitPropWorks m i k.

Definition LocalDecoderCorrect : set -> set -> set -> prop :=
  fun m i k => ConditionalDetermines m i k.

Theorem revised_premise_tree_like :
  forall m, m :e omega -> 100 :e m ->
  forall i, i :e m ->
  forall k, k :e omega -> log_bound m k ->
  LocalTreeLike m i k.
Admitted.

Theorem revised_premise_unit_prop :
  forall m i k, LocalTreeLike m i k -> UnitPropWorks m i k.
Admitted.

Theorem revised_premise_conditional :
  forall m i k, UnitPropWorks m i k -> ConditionalDetermines m i k.
Admitted.

Theorem revised_premise_decoder_correct :
  forall m i k, ConditionalDetermines m i k -> LocalDecoderCorrect m i k.
Admitted.

Theorem revised_premise_circuit_size :
  forall m i k, LocalDecoderCorrect m i k ->
  exists size, size :e omega /\ poly_size size k.
Admitted.

Theorem revised_chain :
  forall m, m :e omega -> 100 :e m ->
  forall i, i :e m ->
  forall k, k :e omega -> log_bound m k ->
  LocalTreeLike m i k ->
  (forall m' i' k', LocalTreeLike m' i' k' -> UnitPropWorks m' i' k') ->
  (forall m' i' k', UnitPropWorks m' i' k' -> ConditionalDetermines m' i' k') ->
  (forall m' i' k', ConditionalDetermines m' i' k' -> LocalDecoderCorrect m' i' k') ->
  (forall m' i' k', LocalDecoderCorrect m' i' k' -> exists size, size :e omega /\ poly_size size k') ->
  exists size, size :e omega /\ poly_size size k.
let m.
assume Hm : m :e omega.
assume Hlarge : 100 :e m.
let i.
assume Hi : i :e m.
let k.
assume Hk : k :e omega.
assume Hlog : log_bound m k.
assume Htree : LocalTreeLike m i k.
assume Hup : forall m' i' k', LocalTreeLike m' i' k' -> UnitPropWorks m' i' k'.
assume Hcond : forall m' i' k', UnitPropWorks m' i' k' -> ConditionalDetermines m' i' k'.
assume Hdec : forall m' i' k', ConditionalDetermines m' i' k' -> LocalDecoderCorrect m' i' k'.
assume Hcirc : forall m' i' k', LocalDecoderCorrect m' i' k' -> exists size, size :e omega /\ poly_size size k'.
prove exists size, size :e omega /\ poly_size size k.
claim Hc1 : UnitPropWorks m i k.
{ exact (Hup m i k Htree). }
claim Hc2 : ConditionalDetermines m i k.
{ exact (Hcond m i k Hc1). }
claim Hc3 : LocalDecoderCorrect m i k.
{ exact (Hdec m i k Hc2). }
exact (Hcirc m i k Hc3).
Qed.

Definition revised_premises : prop :=
  (forall m' i' k', LocalTreeLike m' i' k' -> UnitPropWorks m' i' k') /\
  (forall m' i' k', UnitPropWorks m' i' k' -> ConditionalDetermines m' i' k') /\
  (forall m' i' k', ConditionalDetermines m' i' k' -> LocalDecoderCorrect m' i' k') /\
  (forall m' i' k', LocalDecoderCorrect m' i' k' -> exists size, size :e omega /\ poly_size size k').
