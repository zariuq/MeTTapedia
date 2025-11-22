Definition log_bound : set -> set -> prop :=
  fun m k => k :e omega /\ k :e m /\ 1 :e k.

Definition poly_size : set -> set -> prop :=
  fun size k => size :e omega /\ size c= k.

Definition DecoderBounded : set -> set -> prop :=
  fun m i => exists k, exists size,
    k :e omega /\ size :e omega /\ log_bound m k /\ poly_size size k.

Definition LocalVVSystem : set -> set -> set -> prop :=
  fun m i k => m :e omega /\ i :e m /\ k :e omega /\ log_bound m k.

Definition SystemConsistent : set -> set -> set -> prop :=
  fun m i k => LocalVVSystem m i k.

Definition SystemSolvableByGE : set -> set -> set -> prop :=
  fun m i k => SystemConsistent m i k.

Definition GESolutionCorrect : set -> set -> set -> prop :=
  fun m i k => SystemSolvableByGE m i k.

Definition GECircuitSize : set -> set -> set -> prop :=
  fun m i k => exists size, size :e omega /\ poly_size size k.

Theorem sub_premise_local_system :
  forall m, m :e omega -> 100 :e m ->
  forall i, i :e m ->
  forall k, k :e omega -> log_bound m k ->
  LocalVVSystem m i k.
Admitted.

Theorem sub_premise_consistent :
  forall m i k, LocalVVSystem m i k -> SystemConsistent m i k.
Admitted.

Theorem sub_premise_ge_solvable :
  forall m i k, SystemConsistent m i k -> SystemSolvableByGE m i k.
Admitted.

Theorem sub_premise_ge_correct :
  forall m i k, SystemSolvableByGE m i k -> GESolutionCorrect m i k.
Admitted.

Theorem sub_premise_ge_circuit :
  forall m i k, GESolutionCorrect m i k -> GECircuitSize m i k.
Admitted.

Theorem premise_ge_size_decomposed :
  forall m, m :e omega -> 100 :e m ->
  forall i, i :e m ->
  forall k, k :e omega -> log_bound m k ->
  LocalVVSystem m i k ->
  (forall m' i' k', LocalVVSystem m' i' k' -> SystemConsistent m' i' k') ->
  (forall m' i' k', SystemConsistent m' i' k' -> SystemSolvableByGE m' i' k') ->
  (forall m' i' k', SystemSolvableByGE m' i' k' -> GESolutionCorrect m' i' k') ->
  (forall m' i' k', GESolutionCorrect m' i' k' -> GECircuitSize m' i' k') ->
  exists size, size :e omega /\ poly_size size k.
let m.
assume Hm : m :e omega.
assume Hlarge : 100 :e m.
let i.
assume Hi : i :e m.
let k.
assume Hk : k :e omega.
assume Hlog : log_bound m k.
assume Hlocal : LocalVVSystem m i k.
assume Hcons : forall m' i' k', LocalVVSystem m' i' k' -> SystemConsistent m' i' k'.
assume Hsolv : forall m' i' k', SystemConsistent m' i' k' -> SystemSolvableByGE m' i' k'.
assume Hcorr : forall m' i' k', SystemSolvableByGE m' i' k' -> GESolutionCorrect m' i' k'.
assume Hcirc : forall m' i' k', GESolutionCorrect m' i' k' -> GECircuitSize m' i' k'.
prove exists size, size :e omega /\ poly_size size k.
claim Hc1 : SystemConsistent m i k.
{ exact (Hcons m i k Hlocal). }
claim Hc2 : SystemSolvableByGE m i k.
{ exact (Hsolv m i k Hc1). }
claim Hc3 : GESolutionCorrect m i k.
{ exact (Hcorr m i k Hc2). }
claim Hc4 : GECircuitSize m i k.
{ exact (Hcirc m i k Hc3). }
prove exists size, size :e omega /\ poly_size size k.
exact Hc4.
Qed.

Theorem premise_k_exists :
  forall m, m :e omega -> 100 :e m ->
  exists k, k :e omega /\ log_bound m k.
Admitted.

Theorem construct_decoder_bounded :
  forall m k size, k :e omega -> size :e omega ->
    log_bound m k -> poly_size size k ->
    forall i, DecoderBounded m i.
Admitted.

Theorem decoder_bound_from_decomposed :
  forall m, m :e omega -> 100 :e m ->
  forall i, i :e m ->
  (exists k, k :e omega /\ log_bound m k) ->
  (forall k, k :e omega -> log_bound m k -> LocalVVSystem m i k) ->
  (forall m' i' k', LocalVVSystem m' i' k' -> SystemConsistent m' i' k') ->
  (forall m' i' k', SystemConsistent m' i' k' -> SystemSolvableByGE m' i' k') ->
  (forall m' i' k', SystemSolvableByGE m' i' k' -> GESolutionCorrect m' i' k') ->
  (forall m' i' k', GESolutionCorrect m' i' k' -> GECircuitSize m' i' k') ->
  DecoderBounded m i.
let m.
assume Hm : m :e omega.
assume Hlarge : 100 :e m.
let i.
assume Hi : i :e m.
assume Hk_ex : exists k, k :e omega /\ log_bound m k.
assume Hlocal : forall k, k :e omega -> log_bound m k -> LocalVVSystem m i k.
assume Hcons : forall m' i' k', LocalVVSystem m' i' k' -> SystemConsistent m' i' k'.
assume Hsolv : forall m' i' k', SystemConsistent m' i' k' -> SystemSolvableByGE m' i' k'.
assume Hcorr : forall m' i' k', SystemSolvableByGE m' i' k' -> GESolutionCorrect m' i' k'.
assume Hcirc : forall m' i' k', GESolutionCorrect m' i' k' -> GECircuitSize m' i' k'.
prove DecoderBounded m i.
apply (exandE_i (fun k => k :e omega) (fun k => log_bound m k) Hk_ex (DecoderBounded m i)).
let k.
assume Hk1 : k :e omega.
assume Hk2 : log_bound m k.
claim Hloc : LocalVVSystem m i k.
{ exact (Hlocal k Hk1 Hk2). }
claim Hsize : exists size, size :e omega /\ poly_size size k.
{ exact (premise_ge_size_decomposed m Hm Hlarge i Hi k Hk1 Hk2 Hloc Hcons Hsolv Hcorr Hcirc). }
apply (exandE_i (fun size => size :e omega) (fun size => poly_size size k) Hsize (DecoderBounded m i)).
let size.
assume Hs1 : size :e omega.
assume Hs2 : poly_size size k.
exact (construct_decoder_bounded m k size Hk1 Hs1 Hk2 Hs2 i).
Qed.

Definition sub_premises : prop :=
  (forall m' i' k', LocalVVSystem m' i' k' -> SystemConsistent m' i' k') /\
  (forall m' i' k', SystemConsistent m' i' k' -> SystemSolvableByGE m' i' k') /\
  (forall m' i' k', SystemSolvableByGE m' i' k' -> GESolutionCorrect m' i' k') /\
  (forall m' i' k', GESolutionCorrect m' i' k' -> GECircuitSize m' i' k').

Definition conclusion_main : prop :=
  forall m, m :e omega -> 100 :e m -> forall i, i :e m -> DecoderBounded m i.
