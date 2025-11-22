Definition log_bound : set -> set -> prop :=
  fun m k => k :e omega /\ k :e m /\ 1 :e k.

Definition LocalVVSystem : set -> set -> set -> prop :=
  fun m i k => m :e omega /\ i :e m /\ k :e omega /\ log_bound m k.

Definition SystemSolvableByGE : set -> set -> set -> prop :=
  fun m i k => LocalVVSystem m i k.

Definition PlantedAssignment : set -> set -> prop :=
  fun m sigma => m :e omega /\ sigma :e m.

Definition GESolutionMatchesPlanted : set -> set -> set -> set -> prop :=
  fun m i k sigma => SystemSolvableByGE m i k /\ PlantedAssignment m sigma.

Definition LocalNeighborhoodTreeLike : set -> set -> set -> prop :=
  fun m i k => m :e omega /\ i :e m /\ k :e omega.

Definition BPConvergesLocally : set -> set -> set -> prop :=
  fun m i k => LocalNeighborhoodTreeLike m i k.

Definition BPMarginalCorrect : set -> set -> set -> prop :=
  fun m i k => BPConvergesLocally m i k.

Definition VVFromBPCorrect : set -> set -> set -> prop :=
  fun m i k => BPMarginalCorrect m i k.

Definition GEPreservesBPInfo : set -> set -> set -> prop :=
  fun m i k => VVFromBPCorrect m i k.

Theorem deep_premise_tree_like :
  forall m, m :e omega -> 100 :e m ->
  forall i, i :e m ->
  forall k, k :e omega -> log_bound m k ->
  LocalNeighborhoodTreeLike m i k.
Admitted.

Theorem deep_premise_bp_converges :
  forall m i k, LocalNeighborhoodTreeLike m i k -> BPConvergesLocally m i k.
Admitted.

Theorem deep_premise_bp_marginal :
  forall m i k, BPConvergesLocally m i k -> BPMarginalCorrect m i k.
Admitted.

Theorem deep_premise_vv_from_bp :
  forall m i k, BPMarginalCorrect m i k -> VVFromBPCorrect m i k.
Admitted.

Theorem deep_premise_ge_preserves :
  forall m i k, VVFromBPCorrect m i k -> GEPreservesBPInfo m i k.
Admitted.

Theorem correctness_chain :
  forall m, m :e omega -> 100 :e m ->
  forall i, i :e m ->
  forall k, k :e omega -> log_bound m k ->
  LocalNeighborhoodTreeLike m i k ->
  (forall m' i' k', LocalNeighborhoodTreeLike m' i' k' -> BPConvergesLocally m' i' k') ->
  (forall m' i' k', BPConvergesLocally m' i' k' -> BPMarginalCorrect m' i' k') ->
  (forall m' i' k', BPMarginalCorrect m' i' k' -> VVFromBPCorrect m' i' k') ->
  (forall m' i' k', VVFromBPCorrect m' i' k' -> GEPreservesBPInfo m' i' k') ->
  GEPreservesBPInfo m i k.
let m.
assume Hm : m :e omega.
assume Hlarge : 100 :e m.
let i.
assume Hi : i :e m.
let k.
assume Hk : k :e omega.
assume Hlog : log_bound m k.
assume Htree : LocalNeighborhoodTreeLike m i k.
assume Hconv : forall m' i' k', LocalNeighborhoodTreeLike m' i' k' -> BPConvergesLocally m' i' k'.
assume Hmarg : forall m' i' k', BPConvergesLocally m' i' k' -> BPMarginalCorrect m' i' k'.
assume Hvv : forall m' i' k', BPMarginalCorrect m' i' k' -> VVFromBPCorrect m' i' k'.
assume Hge : forall m' i' k', VVFromBPCorrect m' i' k' -> GEPreservesBPInfo m' i' k'.
prove GEPreservesBPInfo m i k.
claim Hc1 : BPConvergesLocally m i k.
{ exact (Hconv m i k Htree). }
claim Hc2 : BPMarginalCorrect m i k.
{ exact (Hmarg m i k Hc1). }
claim Hc3 : VVFromBPCorrect m i k.
{ exact (Hvv m i k Hc2). }
exact (Hge m i k Hc3).
Qed.

Definition correctness_premises : prop :=
  (forall m' i' k', LocalNeighborhoodTreeLike m' i' k' -> BPConvergesLocally m' i' k') /\
  (forall m' i' k', BPConvergesLocally m' i' k' -> BPMarginalCorrect m' i' k') /\
  (forall m' i' k', BPMarginalCorrect m' i' k' -> VVFromBPCorrect m' i' k') /\
  (forall m' i' k', VVFromBPCorrect m' i' k' -> GEPreservesBPInfo m' i' k').
