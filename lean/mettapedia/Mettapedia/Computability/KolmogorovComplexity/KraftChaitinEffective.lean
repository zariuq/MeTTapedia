import Mettapedia.Computability.KolmogorovComplexity.KraftChaitinStream

/-!
# Effectivity of online Kraft–Chaitin request streams

`KraftChaitinStream.lean` reduces effectivity of its induced prefix machine
to computability of one search step.  This file discharges that operational
obligation from the natural data-level premise: the request value and request
length are primitive recursive in the condition and stream index.

The proof does not replace the verified allocator.  It gives that allocator
an extensionally equal, index-based presentation assembled from the standard
primitive-recursive list operations, then lifts it through the stream-state
recursion and the unbounded readback search.
-/

namespace KolmogorovComplexity

namespace KraftChaitin

/-! ## Primitive-recursive presentation of one allocation step -/

/-- The first frontier position whose prefix is short enough for a request. -/
def allocIndex (frontier : List BinString) (requestedLength : Nat) : Nat :=
  frontier.findIdx fun pfx => decide (pfx.length ≤ requestedLength)

/-- Index-based presentation of `allocStep`. -/
def allocStepIndexed (frontier : List BinString) (requestedLength : Nat) :
    Option (BinString × List BinString) :=
  let index := allocIndex frontier requestedLength
  match frontier[index]? with
  | none => none
  | some pfx =>
      let depth := requestedLength - pfx.length
      some
        (pfx ++ List.replicate depth false,
          frontier.take index ++ siblingsOf pfx depth ++ frontier.drop (index + 1))

theorem allocIndex_nil (requestedLength : Nat) :
    allocIndex [] requestedLength = 0 := by
  rfl

theorem allocIndex_cons_of_le {pfx : BinString} {frontier : List BinString}
    {requestedLength : Nat} (h : pfx.length ≤ requestedLength) :
    allocIndex (pfx :: frontier) requestedLength = 0 := by
  simp [allocIndex, List.findIdx_cons, h]

theorem allocIndex_cons_of_not_le {pfx : BinString} {frontier : List BinString}
    {requestedLength : Nat} (h : ¬ pfx.length ≤ requestedLength) :
    allocIndex (pfx :: frontier) requestedLength =
      allocIndex frontier requestedLength + 1 := by
  simp [allocIndex, List.findIdx_cons, h]

/-- The index-based presentation is exactly the verified recursive allocator. -/
theorem allocStepIndexed_eq_allocStep
    (frontier : List BinString) (requestedLength : Nat) :
    allocStepIndexed frontier requestedLength =
      allocStep frontier requestedLength := by
  induction frontier with
  | nil => rfl
  | cons pfx frontier ih =>
      by_cases h : pfx.length ≤ requestedLength
      · simp [allocStepIndexed, allocStep, allocIndex_cons_of_le h, h]
      · simp only [allocStepIndexed, allocStep, if_neg h,
          allocIndex_cons_of_not_le h, List.getElem?_cons_succ,
          List.take_succ_cons, List.drop_succ_cons]
        rw [← ih]
        unfold allocStepIndexed
        generalize hselected : frontier[allocIndex frontier requestedLength]? = selected
        cases selected <;> simp [hselected, List.append_assoc]

/-- A run of `false` bits, separated out to expose primitive recursion. -/
def falseBits : Nat → BinString
  | 0 => []
  | n + 1 => false :: falseBits n

@[simp] theorem falseBits_eq_replicate (n : Nat) :
    falseBits n = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [falseBits, List.replicate_succ, ih]

theorem falseBits_primrec : Primrec falseBits := by
  exact (Primrec.nat_rec₁ ([] : BinString)
    ((Primrec.list_cons.comp (Primrec.const false) Primrec₂.right).to₂)).of_eq
      fun n => by induction n <;> simp [falseBits, *]

/-- The retained sibling frontier is primitive recursive in its prefix and
split depth. -/
theorem siblingsOf_primrec : Primrec₂ siblingsOf := by
  let step : BinString → Nat × List BinString → List BinString :=
    fun pfx state =>
      (pfx ++ falseBits state.1 ++ [true]) :: state.2
  have hstep : Primrec₂ step := by
    exact (Primrec.list_cons.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp
          Primrec.fst
          (falseBits_primrec.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.const ([true] : BinString)))
      (Primrec.snd.comp Primrec.snd)).to₂
  refine (Primrec.nat_rec (Primrec.const []) hstep).of_eq ?_
  intro pfx depth
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change
        (pfx ++ falseBits depth ++ [true]) ::
            Nat.rec [] (fun n previous => step pfx (n, previous)) depth =
          (pfx ++ List.replicate depth false ++ [true]) :: siblingsOf pfx depth
      rw [ih, falseBits_eq_replicate]

/-- The first admissible frontier index is primitive recursive. -/
theorem allocIndex_primrec : Primrec₂ allocIndex := by
  have h : Primrec fun input : List BinString × Nat =>
      input.1.findIdx fun pfx => decide (pfx.length ≤ input.2) := by
    apply Primrec.list_findIdx Primrec.fst
    exact (Primrec.nat_le.decide.comp₂
      (Primrec.list_length.comp Primrec₂.right)
      (Primrec.snd.comp Primrec₂.left))
  exact h.to₂

/-- The index-based one-step allocator is primitive recursive. -/
theorem allocStepIndexed_primrec : Primrec₂ allocStepIndexed := by
  let index : List BinString × Nat → Nat := fun input =>
    allocIndex input.1 input.2
  have hindex : Primrec index :=
    allocIndex_primrec.comp Primrec.fst Primrec.snd
  have hselected : Primrec fun input : List BinString × Nat =>
      input.1[index input]? :=
    Primrec.list_getElem?.comp Primrec.fst hindex
  have h : Primrec fun input : List BinString × Nat =>
      allocStepIndexed input.1 input.2 := by
    unfold allocStepIndexed
    have hraw := Primrec.option_casesOn hselected
      (Primrec.const (none : Option (BinString × List BinString)))
      ((Primrec.option_some.comp
        (Primrec.pair
          (Primrec.list_append.comp
            Primrec₂.right
            (falseBits_primrec.comp
              (Primrec.nat_sub.comp
                (Primrec.snd.comp Primrec₂.left)
                (Primrec.list_length.comp Primrec₂.right))))
          (Primrec.list_append.comp
            (Primrec.list_append.comp
              (Primrec.list_take.comp
                (hindex.comp Primrec₂.left)
                (Primrec.fst.comp Primrec₂.left))
              (siblingsOf_primrec.comp
                Primrec₂.right
                (Primrec.nat_sub.comp
                  (Primrec.snd.comp Primrec₂.left)
                  (Primrec.list_length.comp Primrec₂.right))))
            (Primrec.list_drop.comp
              (Primrec.succ.comp (hindex.comp Primrec₂.left))
              (Primrec.fst.comp Primrec₂.left))))).to₂)
    exact hraw.of_eq fun input => by
      dsimp only
      cases input.1[index input]? <;>
        simp [index, falseBits_eq_replicate, Nat.succ_eq_add_one,
          List.append_assoc]
  exact h.to₂

/-- The verified recursive allocator is primitive recursive. -/
theorem allocStep_primrec : Primrec₂ allocStep :=
  allocStepIndexed_primrec.of_eq allocStepIndexed_eq_allocStep

/-! ## Effective request streams -/

/-- A request stream is effective when its two observable fields are
primitive recursive in the condition and stream index.  The `Request`
structure itself need not participate in the encoding. -/
structure EffectiveRequestStream
    (requests : BinString → Nat → Request BinString) : Prop where
  value_primrec : Primrec₂ fun condition index =>
    (requests condition index).value
  requestedLength_primrec : Primrec₂ fun condition index =>
    (requests condition index).requestedLength

/-- Pair representation of allocator state used only for the computability
proof. -/
abbrev StatePair := List BinString × List BinString

/-- Pair-level presentation of `advance`. -/
def advancePair (state : StatePair) (requestedLength : Nat) : StatePair :=
  match allocStep state.2 requestedLength with
  | none => state
  | some (code, frontier') => (code :: state.1, frontier')

theorem advancePair_primrec : Primrec₂ advancePair := by
  have hstep : Primrec fun input : StatePair × Nat =>
      allocStep input.1.2 input.2 :=
    allocStep_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hsuccess : Primrec₂ fun (input : StatePair × Nat)
      (result : BinString × List BinString) =>
      (result.1 :: input.1.1, result.2) := by
    exact (Primrec.pair
      (Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd)).to₂
  have h : Primrec fun input : StatePair × Nat =>
      advancePair input.1 input.2 := by
    unfold advancePair
    exact (Primrec.option_casesOn hstep Primrec.fst hsuccess).of_eq fun input => by
      cases hresult : allocStep input.1.2 input.2 with
      | none => rfl
      | some result => cases result; rfl
  exact h.to₂

/-- Pair-level stream state, driven only by the request-length projection. -/
def streamStatePair
    (requests : BinString → Nat → Request BinString)
    (condition : BinString) : Nat → StatePair
  | 0 => ([], [[]])
  | count + 1 =>
      advancePair (streamStatePair requests condition count)
        (requests condition count).requestedLength

theorem streamStatePair_eq
    (requests : BinString → Nat → Request BinString)
    (condition : BinString) (count : Nat) :
    streamStatePair requests condition count =
      ((streamState requests condition count).allocated,
        (streamState requests condition count).frontier) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [streamStatePair, streamState]
      rw [ih]
      unfold advancePair advance
      cases allocStep (streamState requests condition count).frontier
          (requests condition count).requestedLength <;> rfl

/-- Effective request lengths make the complete finite allocator state
primitive recursive. -/
theorem streamStatePair_primrec
    {requests : BinString → Nat → Request BinString}
    (effective : EffectiveRequestStream requests) :
    Primrec₂ (streamStatePair requests) := by
  let step : BinString → Nat × StatePair → StatePair :=
    fun condition state =>
      advancePair state.2
        (requests condition state.1).requestedLength
  have hstep : Primrec₂ step := by
    exact (advancePair_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      (effective.requestedLength_primrec.comp
        Primrec.fst (Primrec.fst.comp Primrec.snd))).to₂
  refine (Primrec.nat_rec (Primrec.const (([], [[]]) : StatePair)) hstep).of_eq ?_
  intro condition count
  induction count with
  | zero => rfl
  | succ count ih =>
      change
        step condition
            (count,
              Nat.rec (([], [[]]) : StatePair)
                (fun index previous => step condition (index, previous)) count) =
          advancePair (streamStatePair requests condition count)
            (requests condition count).requestedLength
      rw [ih]

/-- Operational code assignment read through the primitive-recursive pair
state. -/
def streamCodePair
    (requests : BinString → Nat → Request BinString)
    (condition : BinString) (index : Nat) : Option BinString :=
  match allocStep (streamStatePair requests condition index).2
      (requests condition index).requestedLength with
  | none => none
  | some (code, _frontier') => some code

theorem streamCodePair_eq
    (requests : BinString → Nat → Request BinString)
    (condition : BinString) (index : Nat) :
    streamCodePair requests condition index =
      streamCode requests condition index := by
  unfold streamCodePair streamCode
  rw [streamStatePair_eq]
  rfl

/-- Every code lookup of an effective request stream is primitive recursive. -/
theorem streamCode_primrec
    {requests : BinString → Nat → Request BinString}
    (effective : EffectiveRequestStream requests) :
    Primrec₂ (streamCode requests) := by
  have hstate : Primrec fun input : BinString × Nat =>
      streamStatePair requests input.1 input.2 :=
    (streamStatePair_primrec effective).comp Primrec.fst Primrec.snd
  have hstep : Primrec fun input : BinString × Nat =>
      allocStep (streamStatePair requests input.1 input.2).2
        (requests input.1 input.2).requestedLength :=
    allocStep_primrec.comp (Primrec.snd.comp hstate)
      (effective.requestedLength_primrec.comp Primrec.fst Primrec.snd)
  have hpair : Primrec fun input : BinString × Nat =>
      streamCodePair requests input.1 input.2 := by
    unfold streamCodePair
    exact (Primrec.option_casesOn hstep (Primrec.const none)
      ((Primrec.option_some.comp (Primrec.fst.comp Primrec₂.right)).to₂)).of_eq
        fun input => by
          cases hresult : allocStep (streamStatePair requests input.1 input.2).2
              (requests input.1 input.2).requestedLength with
          | none => rfl
          | some result => cases result; rfl
  exact hpair.to₂.of_eq fun condition index =>
    streamCodePair_eq requests condition index

/-! ## The computable search step and effective machine -/

/-- The bounded readback step is primitive recursive for every effective
request stream. -/
theorem kcSearchStep_primrec
    {requests : BinString → Nat → Request BinString}
    (effective : EffectiveRequestStream requests) :
    Primrec₂ (fun input : BinString × BinString => fun index =>
      kcSearchStep requests input.1 input.2 index) := by
  have hcode : Primrec fun input : (BinString × BinString) × Nat =>
      streamCode requests input.1.2 input.2 :=
    (streamCode_primrec effective).comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hsuccess : Primrec₂ fun (input : (BinString × BinString) × Nat)
      (code : BinString) =>
      if code = input.1.1 then
        some (requests input.1.2 input.2).value
      else none := by
    apply Primrec.ite
    · exact Primrec.eq.comp
        (Primrec.snd)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    · exact (Primrec.option_some.comp
        (effective.value_primrec.comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))).to₂
    · exact Primrec.const none
  have h : Primrec fun input : (BinString × BinString) × Nat =>
      kcSearchStep requests input.1.1 input.1.2 input.2 := by
    unfold kcSearchStep
    exact (Primrec.option_casesOn hcode (Primrec.const none) hsuccess).of_eq
      fun input => by
        cases hresult : streamCode requests input.1.2 input.2 with
        | none => rfl
        | some code => rfl
  exact h.to₂

/-- A budgeted effective request stream induces an effective conditional
prefix-free machine. -/
theorem kcMachine_effective
    {requests : BinString → Nat → Request BinString}
    (budget : KraftBudget requests)
    (effective : EffectiveRequestStream requests) :
    Partrec₂ fun program condition =>
      Part.ofOption ((kcMachine requests budget).compute program condition) :=
  kcMachine_effective_of_searchStep budget
    (kcSearchStep_primrec effective).to_comp

/-! ## Positive and negative controls -/

/-- An effective geometric stream.  Values use the already executable unary
bit representation; requested lengths retain the convergent `1,2,3,...`
profile. -/
def effectiveGeometricRequests (_condition : BinString) (index : Nat) :
    Request BinString where
  value := falseBits index
  requestedLength := index + 1

theorem effectiveGeometricRequests_effective :
    EffectiveRequestStream effectiveGeometricRequests where
  value_primrec := falseBits_primrec.comp₂ Primrec₂.right
  requestedLength_primrec :=
    Primrec.succ.comp₂ Primrec₂.right

theorem effectiveGeometricRequests_requestedLengths
    (condition : BinString) (count : Nat) :
    requestedLengthsUpTo effectiveGeometricRequests condition count =
      requestedLengthsUpTo geometricRequests condition count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [requestedLengthsUpTo, effectiveGeometricRequests,
        geometricRequests]
      rw [ih]

theorem effectiveGeometricRequests_kraftBudget :
    KraftBudget effectiveGeometricRequests := by
  intro condition count L hlengths
  rw [effectiveGeometricRequests_requestedLengths] at hlengths ⊢
  exact geometricRequests_kraftBudget condition count L hlengths

/-- Positive control: the complete infinite geometric construction induces
an effective conditional prefix-free machine. -/
theorem effectiveGeometricMachine_effective :
    Partrec₂ fun program condition =>
      Part.ofOption
        ((kcMachine effectiveGeometricRequests
          effectiveGeometricRequests_kraftBudget).compute program condition) :=
  kcMachine_effective effectiveGeometricRequests_kraftBudget
    effectiveGeometricRequests_effective

/-- A computable request generator can still violate Kraft capacity. -/
def effectiveOverfullRequests (_condition : BinString) (index : Nat) :
    Request BinString where
  value := falseBits index
  requestedLength := 1

theorem effectiveOverfullRequests_effective :
    EffectiveRequestStream effectiveOverfullRequests where
  value_primrec := falseBits_primrec.comp₂ Primrec₂.right
  requestedLength_primrec := Primrec₂.const 1

/-- Negative control: effectivity alone does not manufacture a prefix code;
three one-bit requests exceed the binary Kraft budget. -/
theorem effectiveOverfullRequests_not_kraftBudget :
    ¬ KraftBudget effectiveOverfullRequests := by
  intro budget
  have h := budget [] 3 1 (by
    norm_num [requestedLengthsUpTo, effectiveOverfullRequests])
  norm_num [requestedLengthsUpTo, effectiveOverfullRequests] at h

#print axioms allocStep_primrec
#print axioms streamStatePair_primrec
#print axioms streamCode_primrec
#print axioms kcSearchStep_primrec
#print axioms kcMachine_effective
#print axioms effectiveGeometricMachine_effective
#print axioms effectiveOverfullRequests_not_kraftBudget

end KraftChaitin

end KolmogorovComplexity
