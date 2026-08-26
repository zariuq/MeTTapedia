import Mettapedia.Computability.KolmogorovComplexity.DyadicThresholdCoding
import Mathlib.Data.List.Perm.Subperm

/-!
# Effective discrete dyadic semimeasures

This file gives a constructive presentation of a lower-semicomputable discrete
subprobability.  At stage `s`, `numerator condition s code / 2^s` is the mass
currently assigned to the canonically encoded output `code`.

The finite stage budget and dyadic monotonicity are kept in `Nat`.  Threshold
crossings are consequently decidable, and the first-crossing relation emits
each `(code, threshold)` request at most once.
-/

namespace KolmogorovComplexity

namespace KraftChaitin

/-- Effective finite-support dyadic approximations to a condition-indexed
discrete subprobability. -/
structure EffectiveDiscreteDyadic where
  numerator : BinString → Nat → Nat → Nat
  numerator_primrec : Primrec fun input : (BinString × Nat) × Nat =>
    numerator input.1.1 input.1.2 input.2
  support : ∀ condition stage code,
    stage < code → numerator condition stage code = 0
  budget : ∀ condition stage,
    ((List.range (stage + 1)).map (numerator condition stage)).sum ≤ 2 ^ stage
  monotone : ∀ condition stage code,
    2 * numerator condition stage code ≤ numerator condition (stage + 1) code

/-- Each individual finite-stage numerator is bounded by the common
denominator. -/
theorem EffectiveDiscreteDyadic.numerator_le_pow
    (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (stage code : Nat) :
    approximation.numerator condition stage code ≤ 2 ^ stage := by
  by_cases hcode : code ≤ stage
  · have hmem : approximation.numerator condition stage code ∈
        (List.range (stage + 1)).map
          (approximation.numerator condition stage) := by
      exact List.mem_map.mpr
        ⟨code, List.mem_range.mpr (by omega), rfl⟩
    exact (List.single_le_sum
      (fun _numerator _hmem => Nat.zero_le _) _ hmem).trans
        (approximation.budget condition stage)
  · rw [approximation.support condition stage code (Nat.lt_of_not_ge hcode)]
    exact Nat.zero_le _

/-- A dyadic threshold has been crossed at a finite stage. -/
def ThresholdCrossed (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (stage code threshold : Nat) : Prop :=
  code ≤ stage ∧ threshold ≤ stage ∧
    2 ^ (stage - threshold) ≤ approximation.numerator condition stage code

/-- Decidable presentation of `ThresholdCrossed`. -/
def thresholdCrossedTest (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (stage code threshold : Nat) : Bool :=
  (decide (code ≤ stage) && decide (threshold ≤ stage)) &&
    decide (2 ^ (stage - threshold) ≤
      approximation.numerator condition stage code)

@[simp] theorem thresholdCrossedTest_eq_true_iff
    (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (stage code threshold : Nat) :
    thresholdCrossedTest approximation condition stage code threshold = true ↔
      ThresholdCrossed approximation condition stage code threshold := by
  simp [thresholdCrossedTest, ThresholdCrossed]
  tauto

@[simp] theorem thresholdCrossedTest_eq_false_iff
    (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (stage code threshold : Nat) :
    thresholdCrossedTest approximation condition stage code threshold = false ↔
      ¬ ThresholdCrossed approximation condition stage code threshold := by
  constructor
  · intro hfalse hcrossed
    have htrue := thresholdCrossedTest_eq_true_iff
      approximation condition stage code threshold |>.2 hcrossed
    rw [htrue] at hfalse
    contradiction
  · intro hnot
    cases htest : thresholdCrossedTest approximation condition stage code threshold
    · rfl
    · exact (hnot ((thresholdCrossedTest_eq_true_iff
        approximation condition stage code threshold).1 htest)).elim

/-- A crossing is new at stage zero, or was absent at the immediately
preceding stage.  Monotonicity will imply uniqueness across all stages. -/
def FirstThresholdCrossing (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (stage code threshold : Nat) : Prop :=
  ThresholdCrossed approximation condition stage code threshold ∧
    (stage = 0 ∨
      ¬ ThresholdCrossed approximation condition (stage - 1) code threshold)

def firstThresholdCrossingTest (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (stage code threshold : Nat) : Bool :=
  thresholdCrossedTest approximation condition stage code threshold &&
    (decide (stage = 0) ||
      !thresholdCrossedTest approximation condition (stage - 1) code threshold)

@[simp] theorem firstThresholdCrossingTest_eq_true_iff
    (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (stage code threshold : Nat) :
    firstThresholdCrossingTest approximation condition stage code threshold = true ↔
      FirstThresholdCrossing approximation condition stage code threshold := by
  simp [firstThresholdCrossingTest, FirstThresholdCrossing,
    thresholdCrossedTest_eq_false_iff]

/-- Once crossed, a threshold remains crossed at the next dyadic stage. -/
theorem thresholdCrossed_succ
    {approximation : EffectiveDiscreteDyadic}
    {condition : BinString} {stage code threshold : Nat}
    (h : ThresholdCrossed approximation condition stage code threshold) :
    ThresholdCrossed approximation condition (stage + 1) code threshold := by
  rcases h with ⟨hcode, hthreshold, hmass⟩
  refine ⟨by omega, by omega, ?_⟩
  have hmono := approximation.monotone condition stage code
  have hexponent : stage + 1 - threshold = stage - threshold + 1 := by omega
  rw [hexponent, pow_succ]
  omega

/-- Threshold crossing persists to every later stage. -/
theorem thresholdCrossed_mono
    {approximation : EffectiveDiscreteDyadic}
    {condition : BinString} {first later code threshold : Nat}
    (h : ThresholdCrossed approximation condition first code threshold)
    (hle : first ≤ later) :
    ThresholdCrossed approximation condition later code threshold := by
  exact Nat.le_induction (m := first)
    (P := fun stage _hle =>
      ThresholdCrossed approximation condition stage code threshold)
    h (fun _stage _hle crossed => thresholdCrossed_succ crossed) later hle

/-- The same code/threshold pair has at most one first-crossing stage. -/
theorem firstThresholdCrossing_stage_unique
    {approximation : EffectiveDiscreteDyadic}
    {condition : BinString} {left right code threshold : Nat}
    (hleft : FirstThresholdCrossing approximation condition left code threshold)
    (hright : FirstThresholdCrossing approximation condition right code threshold) :
    left = right := by
  rcases lt_trichotomy left right with hlt | heq | hgt
  · have hrightPositive : right ≠ 0 := by omega
    have hleftBefore : left ≤ right - 1 := by omega
    have hpersist := thresholdCrossed_mono hleft.1 hleftBefore
    exact (hright.2.resolve_left hrightPositive) hpersist |>.elim
  · exact heq
  · have hleftPositive : left ≠ 0 := by omega
    have hrightBefore : right ≤ left - 1 := by omega
    have hpersist := thresholdCrossed_mono hright.1 hrightBefore
    exact (hleft.2.resolve_left hleftPositive) hpersist |>.elim

/-- A total candidate index encodes a stage and a `(code, threshold)` pair. -/
def thresholdCandidate (index : Nat) : Nat × (Nat × Nat) :=
  (index.unpair.1, index.unpair.2.unpair)

theorem thresholdCandidate_primrec : Primrec thresholdCandidate := by
  exact Primrec.pair
    (Primrec.fst.comp Primrec.unpair)
    (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

/-- Decode only canonical encodings.  Noncanonical naturals are treated as
empty candidate slots. -/
def canonicalDecode (code : Nat) : Option BinString :=
  match Encodable.decode (α := BinString) code with
  | none => none
  | some value => if Encodable.encode value = code then some value else none

theorem canonicalDecode_primrec : Primrec canonicalDecode := by
  have hDecode : Primrec fun code : Nat =>
      Encodable.decode (α := BinString) code := Primrec.decode
  have hBranch : Primrec₂ fun (code : Nat) (value : BinString) =>
      if Encodable.encode value = code then some value else none := by
    apply Primrec₂.mk
    apply Primrec.ite
    · exact Primrec.eq.comp
        (Primrec.encode.comp Primrec.snd) Primrec.fst
    · exact Primrec.option_some.comp Primrec.snd
    · exact Primrec.const none
  exact (Primrec.option_casesOn hDecode (Primrec.const none) hBranch).of_eq
    fun code => by
      unfold canonicalDecode
      cases hdecode : Encodable.decode (α := BinString) code <;> rfl

@[simp] theorem canonicalDecode_encode (value : BinString) :
    canonicalDecode (Encodable.encode value) = some value := by
  simp [canonicalDecode, Encodable.encodek]

/-- One genuine first-crossing event, if the indexed slot is canonical.  The
event retains its numerical key for uniqueness and its decoded output value. -/
def thresholdEventAt (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (index : Nat) :
    Option ((Nat × Nat) × BinString) :=
  let candidate := thresholdCandidate index
  let stage := candidate.1
  let code := candidate.2.1
  let threshold := candidate.2.2
  if firstThresholdCrossingTest approximation condition stage code threshold then
    (canonicalDecode code).map fun value => ((code, threshold), value)
  else none

/-- Every canonical first crossing appears at its explicit paired index. -/
theorem thresholdEventAt_pair
    {approximation : EffectiveDiscreteDyadic}
    {condition value : BinString} {stage threshold : Nat}
    (h : FirstThresholdCrossing approximation condition stage
      (Encodable.encode value) threshold) :
    thresholdEventAt approximation condition
        (Nat.pair stage (Nat.pair (Encodable.encode value) threshold)) =
      some (((Encodable.encode value, threshold), value)) := by
  simp [thresholdEventAt, thresholdCandidate, h, canonicalDecode_encode]

/-! ## Primitive-recursive event and request generation -/

abbrev ThresholdInput := ((BinString × Nat) × Nat) × Nat

/-- Unary presentation of the threshold decision procedure. -/
def thresholdCrossedTestInput (approximation : EffectiveDiscreteDyadic)
    (input : ThresholdInput) : Bool :=
  thresholdCrossedTest approximation input.1.1.1 input.1.1.2
    input.1.2 input.2

/-- Unary presentation of the first-crossing decision procedure. -/
def firstThresholdCrossingTestInput (approximation : EffectiveDiscreteDyadic)
    (input : ThresholdInput) : Bool :=
  firstThresholdCrossingTest approximation input.1.1.1 input.1.1.2
    input.1.2 input.2

theorem thresholdCrossedTest_primrec
    (approximation : EffectiveDiscreteDyadic) :
    Primrec (thresholdCrossedTestInput approximation) := by
  have hCondition : Primrec fun input : ThresholdInput => input.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hStage : Primrec fun input : ThresholdInput => input.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hCode : Primrec fun input : ThresholdInput => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hThreshold : Primrec fun input : ThresholdInput => input.2 :=
    Primrec.snd
  have hCodeLe : Primrec fun input : ThresholdInput =>
      decide (input.1.2 ≤ input.1.1.2) :=
    Primrec.nat_le.decide.comp hCode hStage
  have hThresholdLe : Primrec fun input : ThresholdInput =>
      decide (input.2 ≤ input.1.1.2) :=
    Primrec.nat_le.decide.comp hThreshold hStage
  have hExponent : Primrec fun input : ThresholdInput =>
      input.1.1.2 - input.2 :=
    Primrec.nat_sub.comp hStage hThreshold
  have hPow : Primrec fun input : ThresholdInput =>
      2 ^ (input.1.1.2 - input.2) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) hExponent
  have hNumerator : Primrec fun input : ThresholdInput =>
      approximation.numerator input.1.1.1 input.1.1.2 input.1.2 :=
    approximation.numerator_primrec.comp
      (Primrec.pair (Primrec.pair hCondition hStage) hCode)
  have hMassLe : Primrec fun input : ThresholdInput =>
      decide (2 ^ (input.1.1.2 - input.2) ≤
        approximation.numerator input.1.1.1 input.1.1.2 input.1.2) :=
    Primrec.nat_le.decide.comp hPow hNumerator
  exact Primrec.and.comp (Primrec.and.comp hCodeLe hThresholdLe) hMassLe

theorem firstThresholdCrossingTest_primrec
    (approximation : EffectiveDiscreteDyadic) :
    Primrec (firstThresholdCrossingTestInput approximation) := by
  have hCondition : Primrec fun input : ThresholdInput => input.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hStage : Primrec fun input : ThresholdInput => input.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hCode : Primrec fun input : ThresholdInput => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hThreshold : Primrec fun input : ThresholdInput => input.2 :=
    Primrec.snd
  have hCurrent : Primrec (thresholdCrossedTestInput approximation) :=
    thresholdCrossedTest_primrec approximation
  have hStageZero : Primrec fun input : ThresholdInput =>
      decide (input.1.1.2 = 0) :=
    Primrec.eq.decide.comp hStage (Primrec.const 0)
  have hPreviousInput : Primrec fun input : ThresholdInput =>
      (((input.1.1.1, input.1.1.2 - 1), input.1.2), input.2) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.pair hCondition
          (Primrec.nat_sub.comp hStage (Primrec.const 1))) hCode)
      hThreshold
  have hPrevious := hCurrent.comp hPreviousInput
  exact Primrec.and.comp hCurrent
    (Primrec.or.comp hStageZero (Primrec.not.comp hPrevious))

/-- Stage component of the candidate selected by a paired input. -/
def thresholdInputStage (input : BinString × Nat) : Nat :=
  (thresholdCandidate input.2).1

/-- Output-code component of the candidate selected by a paired input. -/
def thresholdInputCode (input : BinString × Nat) : Nat :=
  (thresholdCandidate input.2).2.1

/-- Threshold component of the candidate selected by a paired input. -/
def thresholdInputThreshold (input : BinString × Nat) : Nat :=
  (thresholdCandidate input.2).2.2

/-- Input tuple expected by the first-crossing decision procedure. -/
def thresholdDecisionInput (input : BinString × Nat) : ThresholdInput :=
  (((input.1, thresholdInputStage input), thresholdInputCode input),
    thresholdInputThreshold input)

/-- First-crossing decision for the candidate selected by a paired input. -/
def thresholdEventDecision (approximation : EffectiveDiscreteDyadic)
    (input : BinString × Nat) : Bool :=
  firstThresholdCrossingTestInput approximation (thresholdDecisionInput input)

/-- Decode the selected output code and retain the numerical event key. -/
def thresholdEventPayload (input : BinString × Nat) :
    Option ((Nat × Nat) × BinString) :=
  (canonicalDecode (thresholdInputCode input)).map fun value =>
    ((thresholdInputCode input, thresholdInputThreshold input), value)

/-- Paired presentation used by the unary `Primrec` API.  Naming each
intermediate keeps the primitive-recursion certificate small under kernel
normalization. -/
def thresholdEventAtPair (approximation : EffectiveDiscreteDyadic)
    (input : BinString × Nat) : Option ((Nat × Nat) × BinString) :=
  bif thresholdEventDecision approximation input then
    thresholdEventPayload input
  else none

@[simp] theorem thresholdEventAtPair_eq
    (approximation : EffectiveDiscreteDyadic) (input : BinString × Nat) :
    thresholdEventAtPair approximation input =
      thresholdEventAt approximation input.1 input.2 := by
  cases hdecision : thresholdEventDecision approximation input <;>
    simp [thresholdEventAtPair, thresholdEventAt, thresholdEventDecision,
      thresholdDecisionInput, thresholdEventPayload, thresholdInputStage,
      thresholdInputCode, thresholdInputThreshold,
      firstThresholdCrossingTestInput]

theorem thresholdInputStage_primrec : Primrec thresholdInputStage := by
  exact Primrec.fst.comp (thresholdCandidate_primrec.comp Primrec.snd)

theorem thresholdInputCode_primrec : Primrec thresholdInputCode := by
  exact Primrec.fst.comp
    (Primrec.snd.comp (thresholdCandidate_primrec.comp Primrec.snd))

theorem thresholdInputThreshold_primrec : Primrec thresholdInputThreshold := by
  exact Primrec.snd.comp
    (Primrec.snd.comp (thresholdCandidate_primrec.comp Primrec.snd))

theorem thresholdDecisionInput_primrec : Primrec thresholdDecisionInput := by
  exact Primrec.pair
    (Primrec.pair
      (Primrec.pair Primrec.fst thresholdInputStage_primrec)
      thresholdInputCode_primrec)
    thresholdInputThreshold_primrec

theorem thresholdEventPayload_primrec : Primrec thresholdEventPayload := by
  have hDecode : Primrec fun input : BinString × Nat =>
      canonicalDecode (thresholdInputCode input) :=
    canonicalDecode_primrec.comp thresholdInputCode_primrec
  exact Primrec.option_map hDecode
    ((Primrec.pair
      (Primrec.pair
        (thresholdInputCode_primrec.comp Primrec₂.left)
        (thresholdInputThreshold_primrec.comp Primrec₂.left))
      Primrec₂.right).to₂)

theorem thresholdEventAt_primrec
    (approximation : EffectiveDiscreteDyadic) :
    Primrec (thresholdEventAtPair approximation) := by
  have hFirst : Primrec (thresholdEventDecision approximation) :=
    (firstThresholdCrossingTest_primrec approximation).comp
      thresholdDecisionInput_primrec
  exact Primrec.cond hFirst thresholdEventPayload_primrec (Primrec.const none)

/-- Totalize the genuine event enumeration with a geometric filler request.
The filler at index `i` has length `i + 2`; genuine events retain their
threshold length `ell + 2`. -/
def discreteDyadicRequests (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (index : Nat) : Request BinString :=
  match thresholdEventAt approximation condition index with
  | some ((_code, threshold), value) =>
      ⟨value, threshold + 2⟩
  | none =>
      ⟨falseBits index, index + 2⟩

theorem discreteDyadicRequests_effective
    (approximation : EffectiveDiscreteDyadic) :
    EffectiveRequestStream (discreteDyadicRequests approximation) := by
  have hEvent : Primrec fun input : BinString × Nat =>
      thresholdEventAt approximation input.1 input.2 :=
    (thresholdEventAt_primrec approximation).of_eq fun input =>
      thresholdEventAtPair_eq approximation input
  constructor
  · have hValue : Primrec fun input : BinString × Nat =>
        (discreteDyadicRequests approximation input.1 input.2).value := by
      exact (Primrec.option_casesOn hEvent
        (falseBits_primrec.comp Primrec.snd)
        ((Primrec.snd.comp Primrec.snd).to₂)).of_eq fun input => by
          unfold discreteDyadicRequests
          cases thresholdEventAt approximation input.1 input.2 <;> rfl
    exact hValue.to₂
  · have hDefault : Primrec fun input : BinString × Nat => input.2 + 2 :=
      Primrec.nat_add.comp Primrec.snd (Primrec.const 2)
    have hSuccess : Primrec₂ fun (_input : BinString × Nat)
        (event : (Nat × Nat) × BinString) => event.1.2 + 2 := by
      exact (Primrec.nat_add.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const 2)).to₂
    have hLength : Primrec fun input : BinString × Nat =>
        (discreteDyadicRequests approximation input.1 input.2).requestedLength := by
      exact (Primrec.option_casesOn hEvent hDefault hSuccess).of_eq fun input => by
        unfold discreteDyadicRequests
        cases thresholdEventAt approximation input.1 input.2 <;> rfl
    exact hLength.to₂

/-! ## Finite-prefix Kraft accounting -/

/-- Retain only the numerical code/length key of a genuine event. -/
def thresholdKeyAt (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (index : Nat) : Option (Nat × Nat) :=
  (thresholdEventAt approximation condition index).map fun event =>
    (event.1.1, event.1.2 + 2)

/-- Genuine event keys appearing in the first `count` candidate slots. -/
def thresholdKeysUpTo (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (count : Nat) : List (Nat × Nat) :=
  (List.range count).filterMap (thresholdKeyAt approximation condition)

/-- All reserve-bit threshold keys available at one finite dyadic stage. -/
def stageCodingKeys (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (level : Nat) : List (Nat × Nat) :=
  (List.range (level + 1)).flatMap fun code =>
    (codingLengths level (approximation.numerator condition level code)).map
      fun length => (code, length)

theorem thresholdCandidate_injective : Function.Injective thresholdCandidate := by
  intro left right h
  have hp := congrArg
    (fun candidate => Nat.pair candidate.1
      (Nat.pair candidate.2.1 candidate.2.2)) h
  simpa [thresholdCandidate, Nat.pair_unpair] using hp

/-- A genuine key remembers a unique first-crossing stage through its source
candidate. -/
theorem thresholdKeyAt_some
    {approximation : EffectiveDiscreteDyadic}
    {condition : BinString} {index code length : Nat}
    (h : thresholdKeyAt approximation condition index = some (code, length)) :
    ∃ stage threshold,
      thresholdCandidate index = (stage, (code, threshold)) ∧
      length = threshold + 2 ∧
      FirstThresholdCrossing approximation condition stage code threshold := by
  unfold thresholdKeyAt at h
  generalize hc : thresholdCandidate index = candidate
  obtain ⟨stage, code', threshold⟩ := candidate
  cases htest : firstThresholdCrossingTest approximation condition stage code' threshold
  · simp [thresholdEventAt, hc, htest] at h
  · cases hdecode : canonicalDecode code'
    · simp [thresholdEventAt, hc, htest, hdecode] at h
    · rename_i value
      simp [thresholdEventAt, hc, htest, hdecode] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨stage, threshold, ?_, rfl, ?_⟩
      · rfl
      · exact (firstThresholdCrossingTest_eq_true_iff
          approximation condition stage code' threshold).1 htest

/-- First-crossing keys are never emitted twice. -/
theorem thresholdKeysUpTo_nodup
    (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (count : Nat) :
    (thresholdKeysUpTo approximation condition count).Nodup := by
  unfold thresholdKeysUpTo
  apply List.Nodup.filterMap
  · intro left right key hleft hright
    obtain ⟨leftStage, leftThreshold, hleftCandidate, hleftLength,
      hleftFirst⟩ := thresholdKeyAt_some hleft
    obtain ⟨rightStage, rightThreshold, hrightCandidate, hrightLength,
      hrightFirst⟩ := thresholdKeyAt_some hright
    have hthreshold : leftThreshold = rightThreshold := by omega
    subst rightThreshold
    have hstage : leftStage = rightStage :=
      firstThresholdCrossing_stage_unique hleftFirst hrightFirst
    subst rightStage
    exact thresholdCandidate_injective (hleftCandidate.trans hrightCandidate.symm)
  · exact List.nodup_range

/-- Every event in a finite candidate prefix embeds into the threshold table
at the final prefix stage. -/
theorem thresholdKeysUpTo_subset_stageCodingKeys
    (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (count : Nat) :
    thresholdKeysUpTo approximation condition count ⊆
      stageCodingKeys approximation condition count := by
  intro key hkey
  simp only [thresholdKeysUpTo, List.mem_filterMap] at hkey
  obtain ⟨index, hindex, hkeyAt⟩ := hkey
  obtain ⟨stage, threshold, hcandidate, hlength, hfirst⟩ :=
    thresholdKeyAt_some hkeyAt
  have hstageIndex : stage ≤ index := by
    have hstageEq : (thresholdCandidate index).1 = stage :=
      congrArg Prod.fst hcandidate
    calc
      stage = (thresholdCandidate index).1 := hstageEq.symm
      _ ≤ index := by
        simpa [thresholdCandidate] using Nat.unpair_left_le index
  have hindexCount : index < count := List.mem_range.mp hindex
  have hstageCount : stage ≤ count := by omega
  have hpersist := thresholdCrossed_mono hfirst.1 hstageCount
  rcases hpersist with ⟨hcode, hthreshold, hmass⟩
  have hlengthMem : threshold + 2 ∈
      codingLengths count (approximation.numerator condition count key.1) := by
    exact codingLength_mem hthreshold hmass
  rcases key with ⟨code, length⟩
  simp only at hlength hcode hlengthMem ⊢
  subst length
  simp only [stageCodingKeys, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨code, by omega, threshold + 2, hlengthMem, rfl⟩

/-- Forgetting code labels recovers exactly the batch of coding lengths. -/
theorem stageCodingKeys_lengths
    (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (level : Nat) :
    (stageCodingKeys approximation condition level).map Prod.snd =
      batchCodingLengths level
        ((List.range (level + 1)).map
          (approximation.numerator condition level)) := by
  simp [stageCodingKeys, batchCodingLengths, List.map_flatMap,
    List.flatMap_map, Function.comp_def]

/-- Rational Kraft mass of a code-labelled length table. -/
def rationalKeyMass (keys : List (Nat × Nat)) : ℚ :=
  (keys.map fun key => (1 : ℚ) / (2 : ℚ) ^ key.2).sum

theorem rationalKeyMass_eq_lengthMass (keys : List (Nat × Nat)) :
    rationalKeyMass keys = rationalLengthMass (keys.map Prod.snd) := by
  simp [rationalKeyMass, rationalLengthMass, List.map_map, Function.comp_def]

/-- Removing labelled requests cannot increase rational Kraft mass. -/
theorem rationalKeyMass_le_of_subperm {left right : List (Nat × Nat)}
    (h : List.Subperm left right) : rationalKeyMass left ≤ rationalKeyMass right := by
  rcases List.subperm_iff.mp h with ⟨middle, hperm, hsub⟩
  have hsubWeight := hsub.map
    (fun key : Nat × Nat => (1 : ℚ) / (2 : ℚ) ^ key.2)
  have hle := hsubWeight.sum_le_sum (by
    intro weight hweight
    simp only [List.mem_map] at hweight
    obtain ⟨key, _hkey, rfl⟩ := hweight
    positivity)
  have heq : rationalKeyMass middle = rationalKeyMass right := by
    simpa [rationalKeyMass] using
      (hperm.map
        (fun key : Nat × Nat => (1 : ℚ) / (2 : ℚ) ^ key.2)).sum_eq
  exact hle.trans_eq heq

theorem thresholdKeysUpTo_mass_le_stage
    (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (count : Nat) :
    rationalKeyMass (thresholdKeysUpTo approximation condition count) ≤
      rationalKeyMass (stageCodingKeys approximation condition count) := by
  apply rationalKeyMass_le_of_subperm
  exact (thresholdKeysUpTo_nodup approximation condition count).subperm
    (thresholdKeysUpTo_subset_stageCodingKeys approximation condition count)

/-- Genuine first-crossing requests use at most the half of Kraft space
reserved for the discrete semimeasure. -/
theorem thresholdKeysUpTo_mass_le_half
    (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (count : Nat) :
    rationalKeyMass (thresholdKeysUpTo approximation condition count) ≤
      (1 : ℚ) / 2 := by
  refine (thresholdKeysUpTo_mass_le_stage approximation condition count).trans ?_
  rw [rationalKeyMass_eq_lengthMass,
    stageCodingKeys_lengths approximation condition count]
  apply rationalLengthMass_batchCodingLengths_le_half
  exact approximation.budget condition count

/-- Geometric filler lengths occupying the other reserved half of Kraft
space. -/
def fillerLengthsUpTo (count : Nat) : List Nat :=
  (List.range count).map fun index => index + 2

theorem fillerLengthsUpTo_mass_exact (count : Nat) :
    rationalLengthMass (fillerLengthsUpTo count) =
      (1 : ℚ) / 2 - (1 : ℚ) / (2 : ℚ) ^ (count + 1) := by
  induction count with
  | zero => norm_num [fillerLengthsUpTo, rationalLengthMass]
  | succ count ih =>
      rw [show fillerLengthsUpTo (count + 1) =
          fillerLengthsUpTo count ++ [count + 2] by
        simp [fillerLengthsUpTo, List.range_succ]]
      simp only [rationalLengthMass, List.map_append, List.map_singleton,
        List.sum_append, List.sum_singleton]
      rw [← rationalLengthMass, ih]
      rw [show count + 1 + 1 = count + 2 by omega,
        show count + 2 = (count + 1) + 1 by omega, pow_succ]
      field_simp
      ring

theorem fillerLengthsUpTo_mass_le_half (count : Nat) :
    rationalLengthMass (fillerLengthsUpTo count) ≤ (1 : ℚ) / 2 := by
  rw [fillerLengthsUpTo_mass_exact]
  have hnonneg : 0 ≤ (1 : ℚ) / (2 : ℚ) ^ (count + 1) := by
    positivity
  linarith

/-- Every request prefix is bounded by the genuine-event mass plus the full
geometric filler mass.  A genuine event uses its threshold request; an empty
candidate slot uses its filler request. -/
theorem discreteDyadicRequests_mass_le_events_add_fillers
    (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (count : Nat) :
    rationalLengthMass
        (requestedLengthsUpTo (discreteDyadicRequests approximation)
          condition count) ≤
      rationalKeyMass (thresholdKeysUpTo approximation condition count) +
        rationalLengthMass (fillerLengthsUpTo count) := by
  induction count with
  | zero => simp [requestedLengthsUpTo, thresholdKeysUpTo, fillerLengthsUpTo,
      rationalLengthMass, rationalKeyMass]
  | succ count ih =>
      cases hevent : thresholdEventAt approximation condition count with
      | none =>
          simp [requestedLengthsUpTo, discreteDyadicRequests, hevent,
            thresholdKeysUpTo, thresholdKeyAt, fillerLengthsUpTo,
            List.range_succ, rationalLengthMass, rationalKeyMass] at ih ⊢
          linarith [ih]
      | some event =>
          obtain ⟨⟨code, threshold⟩, value⟩ := event
          simp [requestedLengthsUpTo, discreteDyadicRequests, hevent,
            thresholdKeysUpTo, thresholdKeyAt, fillerLengthsUpTo,
            List.range_succ, rationalLengthMass, rationalKeyMass] at ih ⊢
          have hfill : 0 ≤ (1 : ℚ) / (2 : ℚ) ^ (count + 2) := by
            positivity
          have hfill' : 0 ≤ ((2 : ℚ) ^ (count + 2))⁻¹ := by
            exact inv_nonneg.mpr (by positivity)
          linarith [ih, hfill']

/-- The complete totalized request stream satisfies the rational Kraft
bound: genuine events and filler slots each consume at most one half. -/
theorem discreteDyadicRequests_rationalBudget
    (approximation : EffectiveDiscreteDyadic)
    (condition : BinString) (count : Nat) :
    rationalLengthMass
        (requestedLengthsUpTo (discreteDyadicRequests approximation)
          condition count) ≤ 1 := by
  calc
    rationalLengthMass
          (requestedLengthsUpTo (discreteDyadicRequests approximation)
            condition count)
        ≤ rationalKeyMass (thresholdKeysUpTo approximation condition count) +
            rationalLengthMass (fillerLengthsUpTo count) :=
          discreteDyadicRequests_mass_le_events_add_fillers
            approximation condition count
    _ ≤ (1 : ℚ) / 2 + (1 : ℚ) / 2 := add_le_add
          (thresholdKeysUpTo_mass_le_half approximation condition count)
          (fillerLengthsUpTo_mass_le_half count)
    _ = 1 := by norm_num

theorem discreteDyadicRequests_kraftBudget
    (approximation : EffectiveDiscreteDyadic) :
    KraftBudget (discreteDyadicRequests approximation) := by
  apply kraftBudget_of_rational
  exact discreteDyadicRequests_rationalBudget approximation

/-- Effective prefix-free machine induced by one discrete dyadic
subprobability approximation. -/
noncomputable def discreteDyadicMachine
    (approximation : EffectiveDiscreteDyadic) : ConditionalPrefixFreeMachine :=
  kcMachine (discreteDyadicRequests approximation)
    (discreteDyadicRequests_kraftBudget approximation)

theorem discreteDyadicMachine_effective
    (approximation : EffectiveDiscreteDyadic) :
    Partrec₂ fun program condition =>
      Part.ofOption ((discreteDyadicMachine approximation).compute
        program condition) := by
  exact kcMachine_effective
    (discreteDyadicRequests_kraftBudget approximation)
    (discreteDyadicRequests_effective approximation)

/-- Every crossing has a least crossing stage. -/
theorem exists_firstThresholdCrossing_of_crossed
    {approximation : EffectiveDiscreteDyadic}
    {condition : BinString} {stage code threshold : Nat}
    (h : ThresholdCrossed approximation condition stage code threshold) :
    ∃ first ≤ stage,
      FirstThresholdCrossing approximation condition first code threshold := by
  let witness : ∃ candidate,
      thresholdCrossedTest approximation condition candidate code threshold = true :=
    ⟨stage, (thresholdCrossedTest_eq_true_iff
      approximation condition stage code threshold).2 h⟩
  let first := Nat.find witness
  have hfirst : ThresholdCrossed approximation condition first code threshold :=
    (thresholdCrossedTest_eq_true_iff
      approximation condition first code threshold).1 (Nat.find_spec witness)
  have hfirstLe : first ≤ stage := Nat.find_min' witness
    ((thresholdCrossedTest_eq_true_iff
      approximation condition stage code threshold).2 h)
  refine ⟨first, hfirstLe, hfirst, ?_⟩
  by_cases hzero : first = 0
  · exact Or.inl hzero
  · refine Or.inr ?_
    intro hprevious
    have hminimal : first ≤ first - 1 :=
      Nat.find_min' witness ((thresholdCrossedTest_eq_true_iff
        approximation condition (first - 1) code threshold).2 hprevious)
    omega

/-- Discrete coding theorem at a first crossing: threshold `ell` yields a
conditional prefix description of length at most `ell + 2`. -/
theorem discreteDyadicMachine_complexity_of_firstCrossing
    {approximation : EffectiveDiscreteDyadic}
    {condition value : BinString} {stage threshold : Nat}
    (h : FirstThresholdCrossing approximation condition stage
      (Encodable.encode value) threshold) :
    Kc[discreteDyadicMachine approximation](value | condition) ≤
      threshold + 2 := by
  let index := Nat.pair stage (Nat.pair (Encodable.encode value) threshold)
  have hevent : thresholdEventAt approximation condition index =
      some (((Encodable.encode value, threshold), value)) := by
    exact thresholdEventAt_pair h
  have hbound := kcMachine_complexity_le_requestedLength
    (discreteDyadicRequests_kraftBudget approximation) condition index
  simpa [discreteDyadicMachine, discreteDyadicRequests, hevent] using hbound

/-- A first crossing supplies an actual program, not only a numerical bound
under the zero-for-unrepresented complexity convention. -/
theorem discreteDyadicMachine_hasProgram_of_firstCrossing
    {approximation : EffectiveDiscreteDyadic}
    {condition value : BinString} {stage threshold : Nat}
    (h : FirstThresholdCrossing approximation condition stage
      (Encodable.encode value) threshold) :
    HasProgram (discreteDyadicMachine approximation) condition value := by
  let index := Nat.pair stage (Nat.pair (Encodable.encode value) threshold)
  have hevent : thresholdEventAt approximation condition index =
      some (((Encodable.encode value, threshold), value)) := by
    exact thresholdEventAt_pair h
  obtain ⟨program, _hlength, hcompute⟩ := kcMachine_realizes_request
    (discreteDyadicRequests_kraftBudget approximation) condition index
  refine ⟨program, ?_⟩
  unfold IsProgram
  simpa [discreteDyadicMachine, discreteDyadicRequests, hevent] using hcompute

/-- Discrete coding theorem for any finite threshold crossing. -/
theorem discreteDyadicMachine_complexity_of_crossed
    {approximation : EffectiveDiscreteDyadic}
    {condition value : BinString} {stage threshold : Nat}
    (h : ThresholdCrossed approximation condition stage
      (Encodable.encode value) threshold) :
    Kc[discreteDyadicMachine approximation](value | condition) ≤
      threshold + 2 := by
  obtain ⟨first, _hfirstLe, hfirst⟩ :=
    exists_firstThresholdCrossing_of_crossed h
  exact discreteDyadicMachine_complexity_of_firstCrossing hfirst

/-- Any finite crossing supplies an actual program. -/
theorem discreteDyadicMachine_hasProgram_of_crossed
    {approximation : EffectiveDiscreteDyadic}
    {condition value : BinString} {stage threshold : Nat}
    (h : ThresholdCrossed approximation condition stage
      (Encodable.encode value) threshold) :
    HasProgram (discreteDyadicMachine approximation) condition value := by
  obtain ⟨_first, _hfirstLe, hfirst⟩ :=
    exists_firstThresholdCrossing_of_crossed h
  exact discreteDyadicMachine_hasProgram_of_firstCrossing hfirst

/-! ## Positive and negative controls -/

theorem sum_range_single_zero (count mass : Nat) :
    ((List.range (count + 1)).map fun code =>
      if code = 0 then mass else 0).sum = mass := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [show List.range (count + 1 + 1) =
          List.range (count + 1) ++ [count + 1] by
        exact List.range_succ]
      simp [ih]

/-- Nontrivial positive control: all dyadic mass is concentrated on canonical
code zero at every stage. -/
def pointMassDyadic : EffectiveDiscreteDyadic where
  numerator := fun _condition stage code =>
    if code = 0 then 2 ^ stage else 0
  numerator_primrec := by
    have hStage : Primrec fun input : (BinString × Nat) × Nat => input.1.2 :=
      Primrec.snd.comp Primrec.fst
    have hCode : Primrec fun input : (BinString × Nat) × Nat => input.2 :=
      Primrec.snd
    have hCodeZero : PrimrecPred fun input : (BinString × Nat) × Nat =>
        input.2 = 0 :=
      Primrec.eq.comp hCode (Primrec.const 0)
    have hPow : Primrec fun input : (BinString × Nat) × Nat => 2 ^ input.1.2 :=
      (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) hStage
    exact Primrec.ite hCodeZero hPow (Primrec.const 0)
  support := by
    intro condition stage code hcode
    have hne : code ≠ 0 := by omega
    simp [hne]
  budget := by
    intro condition stage
    rw [sum_range_single_zero stage (2 ^ stage)]
  monotone := by
    intro condition stage code
    by_cases hcode : code = 0
    · subst code
      simp only [ite_true]
      rw [pow_succ]
      omega
    · simp [hcode]

example : ThresholdCrossed pointMassDyadic [] 3 0 3 := by
  norm_num [ThresholdCrossed, pointMassDyadic]

/-- Negative control: an unsupported code receives no mass and crosses no
threshold. -/
example : ¬ ThresholdCrossed pointMassDyadic [] 3 4 0 := by
  norm_num [ThresholdCrossed, pointMassDyadic]

/-- Negative control: two full-mass outputs cannot satisfy the finite-stage
subprobability budget. -/
example : ¬ (([2, 2] : List Nat).sum ≤ 2 ^ 1) := by norm_num

#print axioms thresholdCrossed_mono
#print axioms firstThresholdCrossing_stage_unique
#print axioms thresholdEventAt_pair
#print axioms thresholdEventAt_primrec
#print axioms discreteDyadicRequests_effective
#print axioms discreteDyadicRequests_kraftBudget
#print axioms discreteDyadicMachine_effective
#print axioms discreteDyadicMachine_complexity_of_crossed
#print axioms discreteDyadicMachine_hasProgram_of_crossed

end KraftChaitin

end KolmogorovComplexity
