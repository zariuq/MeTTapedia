import Mettapedia.Computability.KolmogorovComplexity.ConditionalInterpreter
import Mettapedia.Computability.KolmogorovComplexity.SelfDelimitingCode

/-!
# An effective indexed conditional prefix interpreter

Ordinary partial-recursive codes do not have prefix-free program domains.  This
file applies a uniform online trimming construction.  Raw computations are
dovetailed in a canonical order.  A discovered computation is retained exactly
when no earlier discovered computation, at the same condition, used a distinct
prefix-comparable program.  The retained domain is prefix-free.  If the source
code already computes a prefix machine, trimming removes none of its runs.

The construction is intentionally below Solomonoff prediction and AIXI.  It is
the effective enumeration/invariance substrate used by prefix complexity; it
does not assert any policy-optimality theorem.
-/

namespace KolmogorovComplexity

open scoped Classical

/-- Program, auxiliary condition, and output discovered at one dovetailing
event. -/
abbrev ConditionalComputationEvent := BinString × (BinString × BinString)

/-- A primitive Boolean presentation of finite-list prefixhood. -/
def prefixTest (left right : BinString) : Bool :=
  decide (left = right.take left.length)

@[simp] theorem prefixTest_eq_true_iff (left right : BinString) :
    prefixTest left right = true ↔ left <+: right := by
  simp [prefixTest, List.prefix_iff_eq_take]

theorem prefixTest_primrec : Primrec₂ prefixTest := by
  unfold prefixTest
  exact Primrec.eq.decide.comp₂ Primrec₂.left
    (Primrec.list_take.comp₂
      (Primrec.list_length.comp₂
        (Primrec₂.left : Primrec₂ fun left : BinString =>
          fun _right : BinString => left))
      (Primrec₂.right : Primrec₂ fun _left : BinString =>
        fun right : BinString => right))

/-- Propositional form of event conflict. -/
def EventConflict (left right : ConditionalComputationEvent) : Prop :=
  left.2.1 = right.2.1 ∧ left.1 ≠ right.1 ∧
    (left.1 <+: right.1 ∨ right.1 <+: left.1)

/-- Two events conflict when they use distinct prefix-comparable programs at
the same condition.  Outputs do not affect admission. -/
def eventConflictTest
    (left right : ConditionalComputationEvent) : Bool :=
  (decide (left.2.1 = right.2.1) &&
    !decide (left.1 = right.1)) &&
      (prefixTest left.1 right.1 || prefixTest right.1 left.1)

@[simp] theorem eventConflictTest_eq_true_iff
    (left right : ConditionalComputationEvent) :
    eventConflictTest left right = true ↔
      left.2.1 = right.2.1 ∧ left.1 ≠ right.1 ∧
        (left.1 <+: right.1 ∨ right.1 <+: left.1) := by
  simp [eventConflictTest, prefixTest_eq_true_iff]
  tauto

theorem eventConflictTest_primrec : Primrec₂ eventConflictTest := by
  let program : ConditionalComputationEvent → BinString := fun event => event.1
  let condition : ConditionalComputationEvent → BinString := fun event => event.2.1
  have hProgram : Primrec program := Primrec.fst
  have hCondition : Primrec condition := Primrec.fst.comp Primrec.snd
  have hSameCondition : PrimrecRel fun left right : ConditionalComputationEvent =>
      left.2.1 = right.2.1 :=
    Primrec.eq.comp₂
      (hCondition.comp₂ Primrec₂.left) (hCondition.comp₂ Primrec₂.right)
  have hSameProgram : PrimrecRel fun left right : ConditionalComputationEvent =>
      left.1 = right.1 :=
    Primrec.eq.comp₂
      (hProgram.comp₂ Primrec₂.left) (hProgram.comp₂ Primrec₂.right)
  have hPrefix : PrimrecRel fun left right : BinString => left <+: right :=
    (Primrec.eq.comp₂ Primrec₂.left
      (Primrec.list_take.comp₂
        (Primrec.list_length.comp₂ Primrec₂.left) Primrec₂.right)).of_eq
      fun left right => List.prefix_iff_eq_take.symm
  have hLeftPrefix : PrimrecRel fun left right : ConditionalComputationEvent =>
      left.1 <+: right.1 :=
    hPrefix.comp₂
      (hProgram.comp₂ Primrec₂.left) (hProgram.comp₂ Primrec₂.right)
  have hRightPrefix : PrimrecRel fun left right : ConditionalComputationEvent =>
      right.1 <+: left.1 :=
    hPrefix.comp₂
      (hProgram.comp₂ Primrec₂.right) (hProgram.comp₂ Primrec₂.left)
  have hSameConditionTest : Primrec₂ fun left right : ConditionalComputationEvent =>
      decide (left.2.1 = right.2.1) := hSameCondition.decide
  have hDifferentProgramTest : Primrec₂ fun left right : ConditionalComputationEvent =>
      !decide (left.1 = right.1) :=
    Primrec.not.comp₂ hSameProgram.decide
  have hLeftPrefixTest : Primrec₂ fun left right : ConditionalComputationEvent =>
      prefixTest left.1 right.1 :=
    prefixTest_primrec.comp₂
      (hProgram.comp₂ Primrec₂.left) (hProgram.comp₂ Primrec₂.right)
  have hRightPrefixTest : Primrec₂ fun left right : ConditionalComputationEvent =>
      prefixTest right.1 left.1 :=
    prefixTest_primrec.comp₂
      (hProgram.comp₂ Primrec₂.right) (hProgram.comp₂ Primrec₂.left)
  exact Primrec.and.comp₂
    (Primrec.and.comp₂ hSameConditionTest hDifferentProgramTest)
    (Primrec.or.comp₂ hLeftPrefixTest hRightPrefixTest)

/-- The raw event at rank `rank` for partial-recursive code `codeIndex`.
`rank.unpair.1` is the evaluator fuel and `rank.unpair.2` is the encoded
program/condition pair.  Malformed inputs or outputs produce no event. -/
def rawConditionalEventAt (codeIndex rank : Nat) :
    Option ConditionalComputationEvent :=
  let fuel := rank.unpair.1
  let encodedInput := rank.unpair.2
  match Encodable.decode (α := BinString × BinString) encodedInput with
  | none => none
  | some (program, condition) =>
      match Nat.Partrec.Code.evaln fuel
          (Nat.Partrec.Code.ofNatCode codeIndex) encodedInput with
      | none => none
      | some encodedOutput =>
          (Encodable.decode (α := BinString) encodedOutput).map fun output =>
            (program, condition, output)

theorem rawConditionalEventAt_primrec : Primrec₂ rawConditionalEventAt := by
  let Input := Nat × Nat
  let fuel : Input → Nat := fun input => input.2.unpair.1
  let encodedInput : Input → Nat := fun input => input.2.unpair.2
  let code : Input → Nat.Partrec.Code := fun input =>
    Nat.Partrec.Code.ofNatCode input.1
  have hFuel : Primrec fuel := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hEncodedInput : Primrec encodedInput :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hCode : Primrec code :=
    (Primrec.ofNat Nat.Partrec.Code).comp Primrec.fst
  have hDecodedInput : Primrec fun input : Input =>
      Encodable.decode (α := BinString × BinString) (encodedInput input) :=
    Primrec.decode.comp hEncodedInput
  have hEval : Primrec fun input : Input =>
      Nat.Partrec.Code.evaln (fuel input) (code input) (encodedInput input) :=
    Nat.Partrec.Code.primrec_evaln.comp
      ((hFuel.pair hCode).pair hEncodedInput)
  have hEventConstructor : Primrec₂ fun (fields : BinString × BinString)
      (output : BinString) => (fields.1, fields.2, output) := by
    apply Primrec₂.mk
    exact (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  have hAttachDecodedOutput : Primrec₂ fun (fields : BinString × BinString)
      encodedOutput =>
      (Encodable.decode (α := BinString) encodedOutput).map fun output =>
        (fields.1, fields.2, output) :=
    Primrec.map_decode_iff.mpr hEventConstructor
  have hWithOutput : Primrec₂ fun (input : Input)
      (fields : BinString × BinString) =>
      (Nat.Partrec.Code.evaln (fuel input) (code input)
          (encodedInput input)).bind fun encodedOutput =>
        (Encodable.decode (α := BinString) encodedOutput).map fun output =>
          (fields.1, fields.2, output) := by
    apply Primrec₂.mk
    exact Primrec.option_bind (hEval.comp Primrec.fst)
      (hAttachDecodedOutput.comp₂
        (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
  have hRaw : Primrec fun input : Input =>
      (Encodable.decode (α := BinString × BinString)
          (encodedInput input)).bind fun fields =>
        (Nat.Partrec.Code.evaln (fuel input) (code input)
          (encodedInput input)).bind fun encodedOutput =>
          (Encodable.decode (α := BinString) encodedOutput).map fun output =>
            (fields.1, fields.2, output) :=
    Primrec.option_bind hDecodedInput hWithOutput
  exact hRaw.to₂.of_eq fun codeIndex rank => by
    unfold rawConditionalEventAt
    dsimp only [Input, fuel, encodedInput, code]
    cases hInput : Encodable.decode (α := BinString × BinString) rank.unpair.2 with
    | none => simp
    | some fields =>
        obtain ⟨program, condition⟩ := fields
        simp only [Option.bind_some]
        cases hEvalResult : Nat.Partrec.Code.evaln rank.unpair.1
            (Nat.Partrec.Code.ofNatCode codeIndex) rank.unpair.2 with
        | none => simp
        | some encodedOutput => simp

/-! ## Finite-stage trimming -/

/-- Does the raw event at `earlierRank` conflict with `current`? -/
def earlierConflictAt
    (parameters : Nat × ConditionalComputationEvent) (earlierRank : Nat) : Bool :=
  match rawConditionalEventAt parameters.1 earlierRank with
  | none => false
  | some previous => eventConflictTest previous parameters.2

theorem earlierConflictAt_primrec : Primrec₂ earlierConflictAt := by
  apply Primrec₂.mk
  have hRaw : Primrec fun input :
      (Nat × ConditionalComputationEvent) × Nat =>
      rawConditionalEventAt input.1.1 input.2 :=
    rawConditionalEventAt_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hConstructed :=
    Primrec.option_casesOn hRaw (Primrec.const false)
      (eventConflictTest_primrec.comp₂ Primrec₂.right
        (Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.left)))
  exact hConstructed.of_eq fun input => by
    unfold earlierConflictAt
    cases rawConditionalEventAt input.1.1 input.2 <;> rfl

/-- A current event is blocked when some strictly earlier raw event conflicts
with it.  The bounded existential is primitive recursive. -/
def blockedBefore
    (parameters : Nat × ConditionalComputationEvent) (rank : Nat) : Bool :=
  decide (∃ earlierRank ∈ List.range rank,
    earlierConflictAt parameters earlierRank = true)

theorem blockedBefore_primrec : Primrec₂ blockedBefore := by
  have hConflict : PrimrecRel fun earlierRank
      (parameters : Nat × ConditionalComputationEvent) =>
      earlierConflictAt parameters earlierRank = true :=
    (Primrec.eq.comp₂
      (earlierConflictAt_primrec.comp₂ Primrec₂.right Primrec₂.left)
      (Primrec₂.const true))
  have hBounded : PrimrecRel fun
      (parameters : Nat × ConditionalComputationEvent) rank =>
      ∃ earlierRank ∈ List.range rank,
        earlierConflictAt parameters earlierRank = true :=
    hConflict.exists_mem_list.comp₂
      (Primrec.list_range.comp₂ Primrec₂.right) Primrec₂.left
  exact hBounded.decide.of_eq fun parameters rank => rfl

/-- Retain a raw event exactly when it has no earlier conflict. -/
def admittedConditionalEventAt (codeIndex rank : Nat) :
    Option ConditionalComputationEvent :=
  match rawConditionalEventAt codeIndex rank with
  | none => none
  | some current =>
      if blockedBefore (codeIndex, current) rank then none else some current

theorem admittedConditionalEventAt_primrec :
    Primrec₂ admittedConditionalEventAt := by
  apply Primrec₂.mk
  have hRaw : Primrec fun input : Nat × Nat =>
      rawConditionalEventAt input.1 input.2 :=
    rawConditionalEventAt_primrec
  have hBlocked : Primrec₂ fun (input : Nat × Nat)
      (current : ConditionalComputationEvent) =>
      blockedBefore (input.1, current) input.2 :=
    blockedBefore_primrec.comp₂
      (Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.left)
  have hBranch : Primrec₂ fun (input : Nat × Nat)
      (current : ConditionalComputationEvent) =>
      bif blockedBefore (input.1, current) input.2 then none else some current :=
    Primrec.cond hBlocked
      (Primrec₂.const none) (Primrec.option_some.comp₂ Primrec₂.right)
  have hConstructed : Primrec fun input : Nat × Nat =>
      (rawConditionalEventAt input.1 input.2).bind fun current =>
        bif blockedBefore (input.1, current) input.2 then none else some current :=
    Primrec.option_bind hRaw hBranch
  exact hConstructed.of_eq fun input => by
    unfold admittedConditionalEventAt
    cases rawConditionalEventAt input.1 input.2 with
    | none => rfl
    | some current =>
        cases hBlockedValue : blockedBefore (input.1, current) input.2 <;>
          simp [hBlockedValue]

/-- One computable search step for a fixed code/program/condition query. -/
def trimmedSearchStep
    (query : Nat × (BinString × BinString)) (rank : Nat) : Option BinString :=
  match admittedConditionalEventAt query.1 rank with
  | none => none
  | some event =>
      if event.1 = query.2.1 ∧ event.2.1 = query.2.2 then
        some event.2.2
      else none

set_option maxHeartbeats 600000 in
theorem trimmedSearchStep_primrec : Primrec₂ trimmedSearchStep := by
  apply Primrec₂.mk
  have hAdmitted : Primrec fun input :
      (Nat × (BinString × BinString)) × Nat =>
      admittedConditionalEventAt input.1.1 input.2 :=
    admittedConditionalEventAt_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hProgramEq : PrimrecRel fun (input :
      (Nat × (BinString × BinString)) × Nat)
      (event : ConditionalComputationEvent) =>
      event.1 = input.1.2.1 :=
    Primrec.eq.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.fst.comp₂
        (Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.left)))
  have hConditionEq : PrimrecRel fun (input :
      (Nat × (BinString × BinString)) × Nat)
      (event : ConditionalComputationEvent) =>
      event.2.1 = input.1.2.2 :=
    Primrec.eq.comp₂
      (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂
        (Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.left)))
  have hMatches : Primrec₂ fun (input :
      (Nat × (BinString × BinString)) × Nat)
      (event : ConditionalComputationEvent) =>
      decide (event.1 = input.1.2.1 ∧ event.2.1 = input.1.2.2) :=
    (hProgramEq.and hConditionEq).decide
  have hBranch : Primrec₂ fun (input :
      (Nat × (BinString × BinString)) × Nat)
      (event : ConditionalComputationEvent) =>
      bif decide (event.1 = input.1.2.1 ∧ event.2.1 = input.1.2.2) then
        some event.2.2
      else none :=
    Primrec.cond hMatches
      (Primrec.option_some.comp₂
        (Primrec.snd.comp₂ (Primrec.snd.comp₂ Primrec₂.right)))
      (Primrec₂.const none)
  have hConstructed : Primrec fun input :
      (Nat × (BinString × BinString)) × Nat =>
      (admittedConditionalEventAt input.1.1 input.2).bind fun event =>
        bif decide (event.1 = input.1.2.1 ∧ event.2.1 = input.1.2.2) then
          some event.2.2
        else none :=
    Primrec.option_bind hAdmitted hBranch
  exact hConstructed.of_eq fun input => by
    unfold trimmedSearchStep
    cases admittedConditionalEventAt input.1.1 input.2 with
    | none => rfl
    | some event =>
        by_cases hp : event.1 = input.1.2.1
        · by_cases hc : event.2.1 = input.1.2.2
          · simp [hp, hc]
          · simp [hp, hc]
        · simp [hp]

/-- The trimmed partial algorithm searches the admitted event stream. -/
def trimmedConditionalAlgorithm
    (codeIndex : Nat) (program condition : BinString) : Part BinString :=
  Nat.rfindOpt (trimmedSearchStep (codeIndex, program, condition))

theorem trimmedConditionalAlgorithm_partrec :
    Partrec fun input : Nat × (BinString × BinString) =>
      trimmedConditionalAlgorithm input.1 input.2.1 input.2.2 := by
  exact Partrec.rfindOpt trimmedSearchStep_primrec.to_comp

/-! ## Semantic correctness of trimming -/

@[simp] theorem blockedBefore_eq_true_iff
    (parameters : Nat × ConditionalComputationEvent) (rank : Nat) :
    blockedBefore parameters rank = true ↔
      ∃ earlierRank < rank,
        earlierConflictAt parameters earlierRank = true := by
  simp [blockedBefore]

@[simp] theorem admittedConditionalEventAt_eq_some_iff
    (codeIndex rank : Nat) (current : ConditionalComputationEvent) :
    admittedConditionalEventAt codeIndex rank = some current ↔
      rawConditionalEventAt codeIndex rank = some current ∧
        blockedBefore (codeIndex, current) rank = false := by
  constructor
  · intro h
    unfold admittedConditionalEventAt at h
    cases hRaw : rawConditionalEventAt codeIndex rank with
    | none => simp [hRaw] at h
    | some previous =>
        rw [hRaw] at h
        cases hBlocked : blockedBefore (codeIndex, previous) rank with
        | false =>
            simp [hBlocked] at h
            subst current
            exact ⟨rfl, hBlocked⟩
        | true => simp [hBlocked] at h
  · rintro ⟨hRaw, hBlocked⟩
    simp [admittedConditionalEventAt, hRaw, hBlocked]

theorem rawConditionalEventAt_of_admitted
    {codeIndex rank : Nat} {current : ConditionalComputationEvent}
    (h : admittedConditionalEventAt codeIndex rank = some current) :
    rawConditionalEventAt codeIndex rank = some current :=
  (admittedConditionalEventAt_eq_some_iff _ _ _).mp h |>.1

theorem no_earlier_conflict_of_admitted
    {codeIndex earlierRank rank : Nat}
    {previous current : ConditionalComputationEvent}
    (hAdmitted : admittedConditionalEventAt codeIndex rank = some current)
    (hRaw : rawConditionalEventAt codeIndex earlierRank = some previous)
    (hEarlier : earlierRank < rank) :
    ¬ EventConflict previous current := by
  intro hConflict
  have hTest : earlierConflictAt (codeIndex, current) earlierRank = true := by
    simp [earlierConflictAt, hRaw,
      (eventConflictTest_eq_true_iff previous current).2 hConflict]
  have hBlocked : blockedBefore (codeIndex, current) rank = true :=
    (blockedBefore_eq_true_iff _ _).2 ⟨earlierRank, hEarlier, hTest⟩
  have hNotBlocked :=
    (admittedConditionalEventAt_eq_some_iff codeIndex rank current).mp hAdmitted |>.2
  rw [hNotBlocked] at hBlocked
  contradiction

theorem EventConflict.symm
    {left right : ConditionalComputationEvent}
    (h : EventConflict left right) : EventConflict right left := by
  rcases h with ⟨hCondition, hProgram, hPrefix⟩
  exact ⟨hCondition.symm, fun heq => hProgram heq.symm, hPrefix.symm⟩

/-- Two admitted events can never use distinct prefix-comparable programs at
the same condition, regardless of their discovery order. -/
theorem admitted_events_not_conflict
    {codeIndex leftRank rightRank : Nat}
    {left right : ConditionalComputationEvent}
    (hLeft : admittedConditionalEventAt codeIndex leftRank = some left)
    (hRight : admittedConditionalEventAt codeIndex rightRank = some right) :
    ¬ EventConflict left right := by
  intro hConflict
  rcases lt_trichotomy leftRank rightRank with hEarlier | hSame | hLater
  · exact no_earlier_conflict_of_admitted hRight
      (rawConditionalEventAt_of_admitted hLeft) hEarlier hConflict
  · subst rightRank
    have hRawLeft := rawConditionalEventAt_of_admitted hLeft
    have hRawRight := rawConditionalEventAt_of_admitted hRight
    rw [hRawLeft] at hRawRight
    have hEvent : left = right := Option.some.inj hRawRight
    exact hConflict.2.1 (congrArg Prod.fst hEvent)
  · exact no_earlier_conflict_of_admitted hLeft
      (rawConditionalEventAt_of_admitted hRight) hLater hConflict.symm

@[simp] theorem trimmedSearchStep_eq_some_iff
    (codeIndex rank : Nat) (program condition output : BinString) :
    trimmedSearchStep (codeIndex, program, condition) rank = some output ↔
      admittedConditionalEventAt codeIndex rank =
        some (program, condition, output) := by
  unfold trimmedSearchStep
  cases hAdmitted : admittedConditionalEventAt codeIndex rank with
  | none => simp
  | some event =>
      obtain ⟨eventProgram, eventCondition, eventOutput⟩ := event
      by_cases hp : eventProgram = program
      · by_cases hc : eventCondition = condition
        · subst eventProgram
          subst eventCondition
          simp
        · simp [hp, hc]
      · simp [hp]

theorem admitted_event_of_trimmedConditionalAlgorithm_mem
    {codeIndex : Nat} {program condition output : BinString}
    (h : output ∈ trimmedConditionalAlgorithm codeIndex program condition) :
    ∃ rank, admittedConditionalEventAt codeIndex rank =
      some (program, condition, output) := by
  obtain ⟨rank, hStep⟩ := Nat.rfindOpt_spec h
  have hStepEq :
      trimmedSearchStep (codeIndex, program, condition) rank = some output := by
    simpa using hStep
  exact ⟨rank, (trimmedSearchStep_eq_some_iff _ _ _ _ _).mp hStepEq⟩

/-- For a fixed code and condition, the domain of the trimmed partial
algorithm is prefix-free. -/
theorem trimmedConditionalAlgorithm_dom_prefixFree
    (codeIndex : Nat) (condition p q : BinString)
    (hPrefix : p <+: q) (hNe : p ≠ q)
    (hp : (trimmedConditionalAlgorithm codeIndex p condition).Dom) :
    ¬ (trimmedConditionalAlgorithm codeIndex q condition).Dom := by
  intro hq
  let leftOutput := (trimmedConditionalAlgorithm codeIndex p condition).get hp
  let rightOutput := (trimmedConditionalAlgorithm codeIndex q condition).get hq
  have hLeftMem :
      leftOutput ∈ trimmedConditionalAlgorithm codeIndex p condition :=
    Part.get_mem hp
  have hRightMem :
      rightOutput ∈ trimmedConditionalAlgorithm codeIndex q condition :=
    Part.get_mem hq
  obtain ⟨leftRank, hLeft⟩ :=
    admitted_event_of_trimmedConditionalAlgorithm_mem hLeftMem
  obtain ⟨rightRank, hRight⟩ :=
    admitted_event_of_trimmedConditionalAlgorithm_mem hRightMem
  have hConflict : EventConflict
      (p, condition, leftOutput) (q, condition, rightOutput) :=
    ⟨rfl, hNe, Or.inl hPrefix⟩
  exact admitted_events_not_conflict hLeft hRight hConflict

/-! ## An effective conditional prefix machine -/

/-- Classical presentation of the effective partial search as an `Option`.
The `Option` value is only an interface to `ConditionalPrefixFreeMachine`;
`trimmedConditionalCompute_partrec` below proves that converting it back to a
partial value recovers the executable search exactly. -/
noncomputable def trimmedConditionalCompute
    (codeIndex : Nat) (program condition : BinString) : Option BinString :=
  (trimmedConditionalAlgorithm codeIndex program condition).toOption

/-- The online-trimmed machine denoted by a partial-recursive code. -/
noncomputable def trimmedConditionalPrefixMachine
    (codeIndex : Nat) : ConditionalPrefixFreeMachine where
  compute := trimmedConditionalCompute codeIndex
  prefix_free := by
    intro condition p q hPrefix hNe hp
    have hpDom : (trimmedConditionalAlgorithm codeIndex p condition).Dom := by
      by_contra hNotDom
      have hNone : trimmedConditionalCompute codeIndex p condition = none :=
        Part.toOption_eq_none_iff.mpr hNotDom
      exact hp hNone
    have hqNotDom := trimmedConditionalAlgorithm_dom_prefixFree
      codeIndex condition p q hPrefix hNe hpDom
    exact Part.toOption_eq_none_iff.mpr hqNotDom

/-- The Option-valued machine interface denotes the same partial-recursive
function as the trimmed search. -/
theorem trimmedConditionalCompute_partrec :
    Partrec fun input : Nat × (BinString × BinString) =>
      Part.ofOption
        (trimmedConditionalCompute input.1 input.2.1 input.2.2) := by
  exact trimmedConditionalAlgorithm_partrec.of_eq fun input =>
    (Part.of_toOption
      (trimmedConditionalAlgorithm input.1 input.2.1 input.2.2)).symm

/-- Named unary presentation of the effective trimmed machine interface. -/
noncomputable def trimmedConditionalComputePart
    (input : Nat × (BinString × BinString)) : Part BinString :=
  Part.ofOption
    (trimmedConditionalCompute input.1 input.2.1 input.2.2)

theorem trimmedConditionalComputePart_partrec :
    Partrec trimmedConditionalComputePart := by
  apply trimmedConditionalCompute_partrec.of_eq
  intro input
  rfl

theorem trimmedConditionalPrefixMachine_effective (codeIndex : Nat) :
    Partrec₂ fun program condition =>
      Part.ofOption (trimmedConditionalCompute codeIndex program condition) := by
  unfold Partrec₂
  have hCurried : Partrec₂ fun (index : Nat)
      (input : BinString × BinString) =>
      trimmedConditionalAlgorithm index input.1 input.2 :=
    trimmedConditionalAlgorithm_partrec.to₂
  have hSearch : Partrec fun input : BinString × BinString =>
      trimmedConditionalAlgorithm codeIndex input.1 input.2 :=
    hCurried.comp (Computable.const codeIndex) Computable.id
  exact hSearch.of_eq fun input =>
    (Part.of_toOption
      (trimmedConditionalAlgorithm codeIndex input.1 input.2)).symm

/-! ## Preservation of already-prefix-free source machines -/

/-- The numeric partial function obtained by decoding a program/condition pair,
running a conditional machine, and encoding its output.  This is exactly the
representation used by `Partrec` for a two-argument function. -/
def encodedConditionalCompute (M : ConditionalPrefixFreeMachine) : Nat →. Nat :=
  fun encodedInput =>
    Part.bind
      (Part.ofOption
        (Encodable.decode (α := BinString × BinString) encodedInput))
      fun input : BinString × BinString =>
        (Part.ofOption (M.compute input.1 input.2)).map Encodable.encode

theorem ofNatCode_encodeCode (code : Nat.Partrec.Code) :
    Nat.Partrec.Code.ofNatCode (Nat.Partrec.Code.encodeCode code) = code := by
  simpa [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.ofNatCode_eq] using
    (Denumerable.ofNat_encode (α := Nat.Partrec.Code) code)

/-- Every raw event for a code representing `M` is a genuine computation of
`M`.  In particular, malformed numeric encodings cannot manufacture events. -/
theorem source_compute_of_rawConditionalEventAt
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    {rank : Nat} {program condition output : BinString}
    (hRaw : rawConditionalEventAt (Nat.Partrec.Code.encodeCode code) rank =
      some (program, condition, output)) :
    M.compute program condition = some output := by
  unfold rawConditionalEventAt at hRaw
  dsimp only at hRaw
  rw [ofNatCode_encodeCode] at hRaw
  change
    (match Encodable.decode (α := BinString × BinString) rank.unpair.2 with
    | none => none
    | some (rawProgram, rawCondition) =>
        match Nat.Partrec.Code.evaln rank.unpair.1 code rank.unpair.2 with
        | none => none
        | some encodedOutput =>
            (Encodable.decode (α := BinString) encodedOutput).map fun rawOutput =>
              (rawProgram, rawCondition, rawOutput)) =
      some (program, condition, output) at hRaw
  cases hInput : Encodable.decode (α := BinString × BinString) rank.unpair.2 with
  | none =>
      have hImpossible : (none : Option ConditionalComputationEvent) =
          some (program, condition, output) := by
        simpa only [hInput] using hRaw
      simp at hImpossible
  | some input =>
      obtain ⟨rawProgram, rawCondition⟩ := input
      have hAfterInput :
          (match Nat.Partrec.Code.evaln rank.unpair.1 code rank.unpair.2 with
          | none => none
          | some encodedOutput =>
              (Encodable.decode (α := BinString) encodedOutput).map fun rawOutput =>
                (rawProgram, rawCondition, rawOutput)) =
            some (program, condition, output) := by
        simpa only [hInput] using hRaw
      cases hEvaln : Nat.Partrec.Code.evaln rank.unpair.1 code rank.unpair.2 with
      | none =>
          have hImpossible : (none : Option ConditionalComputationEvent) =
              some (program, condition, output) := by
            simpa only [hEvaln] using hAfterInput
          simp at hImpossible
      | some encodedOutput =>
          have hAfterEval :
              (Encodable.decode (α := BinString) encodedOutput).map
                  (fun rawOutput => (rawProgram, rawCondition, rawOutput)) =
                some (program, condition, output) := by
            simpa only [hEvaln] using hAfterInput
          cases hOutput : Encodable.decode (α := BinString) encodedOutput with
          | none =>
              have hImpossible : (none : Option ConditionalComputationEvent) =
                  some (program, condition, output) := by
                simpa only [hOutput, Option.map_none] using hAfterEval
              simp at hImpossible
          | some rawOutput =>
              have hEvent :
                  (rawProgram, rawCondition, rawOutput) =
                    (program, condition, output) := by
                have hSome : some (rawProgram, rawCondition, rawOutput) =
                    some (program, condition, output) := by
                  simpa only [hOutput, Option.map_some] using hAfterEval
                exact Option.some.inj hSome
              obtain ⟨rfl, rfl, rfl⟩ := hEvent
              have hEval : encodedOutput ∈
                  Nat.Partrec.Code.eval code rank.unpair.2 :=
                Nat.Partrec.Code.evaln_sound (by simpa using hEvaln)
              rw [hCode] at hEval
              have hEncoded : encodedOutput ∈
                  (Part.ofOption (M.compute program condition)).map
                    Encodable.encode := by
                simpa [encodedConditionalCompute, hInput] using hEval
              obtain ⟨sourceOutput, hSource, hEncode⟩ :=
                (Part.mem_map_iff Encodable.encode).mp hEncoded
              have hCompute : M.compute program condition = some sourceOutput := by
                simpa using hSource
              have hOutputEq : sourceOutput = output := by
                have hDecoded := congrArg
                  (Encodable.decode (α := BinString)) hEncode
                simpa [hOutput] using hDecoded
              simpa [hOutputEq] using hCompute

/-- Every genuine source computation appears as a raw dovetail event. -/
theorem exists_rawConditionalEventAt_of_source_compute
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    {program condition output : BinString}
    (hCompute : M.compute program condition = some output) :
    ∃ rank, rawConditionalEventAt (Nat.Partrec.Code.encodeCode code) rank =
      some (program, condition, output) := by
  have hEval : Encodable.encode output ∈
      Nat.Partrec.Code.eval code (Encodable.encode (program, condition)) := by
    rw [hCode]
    simp [encodedConditionalCompute, hCompute]
  obtain ⟨fuel, hFuel⟩ := Nat.Partrec.Code.evaln_complete.mp hEval
  refine ⟨Nat.pair fuel (Encodable.encode (program, condition)), ?_⟩
  have hFuelEq : Nat.Partrec.Code.evaln fuel code
      (Encodable.encode (program, condition)) = some (Encodable.encode output) := by
    simpa using hFuel
  unfold rawConditionalEventAt
  simp only [Nat.unpair_pair]
  rw [ofNatCode_encodeCode, hFuelEq]
  simp

/-- If the represented source machine is already prefix-free, none of its raw
events is removed by online trimming. -/
theorem admittedConditionalEventAt_of_source_raw
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    {rank : Nat} {current : ConditionalComputationEvent}
    (hRaw : rawConditionalEventAt (Nat.Partrec.Code.encodeCode code) rank =
      some current) :
    admittedConditionalEventAt (Nat.Partrec.Code.encodeCode code) rank =
      some current := by
  apply (admittedConditionalEventAt_eq_some_iff _ _ _).2
  refine ⟨hRaw, ?_⟩
  cases hBlocked : blockedBefore
      (Nat.Partrec.Code.encodeCode code, current) rank with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨earlierRank, hEarlier, hConflictAt⟩ :=
        (blockedBefore_eq_true_iff _ _).1 hBlocked
      cases hEarlierRaw : rawConditionalEventAt
          (Nat.Partrec.Code.encodeCode code) earlierRank with
      | none => simp [earlierConflictAt, hEarlierRaw] at hConflictAt
      | some previous =>
          have hConflictTest : eventConflictTest previous current = true := by
            simpa [earlierConflictAt, hEarlierRaw] using hConflictAt
          have hConflict : EventConflict previous current :=
            (eventConflictTest_eq_true_iff previous current).1 hConflictTest
          have hPreviousCompute :=
            source_compute_of_rawConditionalEventAt M code hCode hEarlierRaw
          have hCurrentCompute :=
            source_compute_of_rawConditionalEventAt M code hCode hRaw
          rcases hConflict with ⟨hCondition, hProgramsNe, hPrefix | hPrefix⟩
          · have hPreviousHalts :
                M.compute previous.1 current.2.1 ≠ none := by
              rw [← hCondition, hPreviousCompute]
              simp
            have hCurrentNone := M.prefix_free current.2.1
              previous.1 current.1 hPrefix hProgramsNe hPreviousHalts
            rw [hCurrentCompute] at hCurrentNone
            simp at hCurrentNone
          · have hCurrentHalts : M.compute current.1 current.2.1 ≠ none := by
              rw [hCurrentCompute]
              simp
            have hPreviousNone := M.prefix_free current.2.1
              current.1 previous.1 hPrefix
                (fun heq => hProgramsNe heq.symm) hCurrentHalts
            have hPreviousAtCurrent :
                M.compute previous.1 current.2.1 = some previous.2.2 := by
              simpa [hCondition] using hPreviousCompute
            rw [hPreviousAtCurrent] at hPreviousNone
            simp at hPreviousNone

theorem source_compute_of_trimmedConditionalAlgorithm_mem
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    {program condition output : BinString}
    (h : output ∈ trimmedConditionalAlgorithm
      (Nat.Partrec.Code.encodeCode code) program condition) :
    M.compute program condition = some output := by
  obtain ⟨rank, hAdmitted⟩ :=
    admitted_event_of_trimmedConditionalAlgorithm_mem h
  exact source_compute_of_rawConditionalEventAt M code hCode
    (rawConditionalEventAt_of_admitted hAdmitted)

theorem trimmedConditionalAlgorithm_mem_of_source_compute
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    {program condition output : BinString}
    (hCompute : M.compute program condition = some output) :
    output ∈ trimmedConditionalAlgorithm
      (Nat.Partrec.Code.encodeCode code) program condition := by
  obtain ⟨rank, hRaw⟩ :=
    exists_rawConditionalEventAt_of_source_compute M code hCode hCompute
  have hAdmitted := admittedConditionalEventAt_of_source_raw M code hCode hRaw
  have hStep : trimmedSearchStep
      (Nat.Partrec.Code.encodeCode code, program, condition) rank = some output :=
    (trimmedSearchStep_eq_some_iff _ _ _ _ _).2 hAdmitted
  have hDom : (trimmedConditionalAlgorithm
      (Nat.Partrec.Code.encodeCode code) program condition).Dom :=
    Nat.rfindOpt_dom.mpr ⟨rank, output, by simp [hStep]⟩
  let found := (trimmedConditionalAlgorithm
    (Nat.Partrec.Code.encodeCode code) program condition).get hDom
  have hFoundMem : found ∈ trimmedConditionalAlgorithm
      (Nat.Partrec.Code.encodeCode code) program condition :=
    Part.get_mem hDom
  have hFoundCompute := source_compute_of_trimmedConditionalAlgorithm_mem
    M code hCode hFoundMem
  have hFoundEq : found = output := by
    rw [hCompute] at hFoundCompute
    exact (Option.some.inj hFoundCompute).symm
  simpa [hFoundEq] using hFoundMem

/-- A code for an effective source prefix machine is extensionally preserved by
trimming. -/
theorem trimmedConditionalCompute_eq_of_code
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    (program condition : BinString) :
    trimmedConditionalCompute (Nat.Partrec.Code.encodeCode code)
      program condition = M.compute program condition := by
  cases hCompute : M.compute program condition with
  | none =>
      unfold trimmedConditionalCompute
      apply Part.toOption_eq_none_iff.mpr
      intro hDom
      let output := (trimmedConditionalAlgorithm
        (Nat.Partrec.Code.encodeCode code) program condition).get hDom
      have hOutputMem : output ∈ trimmedConditionalAlgorithm
          (Nat.Partrec.Code.encodeCode code) program condition :=
        Part.get_mem hDom
      have hSource := source_compute_of_trimmedConditionalAlgorithm_mem
        M code hCode hOutputMem
      rw [hCompute] at hSource
      simp at hSource
  | some output =>
      unfold trimmedConditionalCompute
      apply Part.toOption_eq_some_iff.mpr
      exact trimmedConditionalAlgorithm_mem_of_source_compute
        M code hCode hCompute

/-- Every effective conditional prefix machine occurs extensionally in the
trimmed enumeration. -/
theorem exists_trimmed_code_eq
    (M : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (M.compute program condition)) :
    ∃ codeIndex, ∀ program condition,
      trimmedConditionalCompute codeIndex program condition =
        M.compute program condition := by
  have hEncoded : Nat.Partrec (encodedConditionalCompute M) := by
    unfold Partrec₂ Partrec at hEffective
    exact hEffective.of_eq fun encodedInput => by
      unfold encodedConditionalCompute
      rfl
  obtain ⟨code, hCode⟩ := (Nat.Partrec.Code.exists_code).1 hEncoded
  exact ⟨Nat.Partrec.Code.encodeCode code,
    trimmedConditionalCompute_eq_of_code M code hCode⟩

/-! ## Effective enumeration and its indexed universal host -/

/-- An effective enumeration of conditional prefix-free machines. -/
structure EffectiveConditionalPFMEnumeration where
  compute : Nat → BinString → BinString → Option BinString
  prefix_free : ∀ index condition program extension,
    program <+: extension → program ≠ extension →
    compute index program condition ≠ none →
    compute index extension condition = none
  effective : Partrec fun input : Nat × (BinString × BinString) =>
    Part.ofOption (compute input.1 input.2.1 input.2.2)

namespace EffectiveConditionalPFMEnumeration

def machineAt (enumeration : EffectiveConditionalPFMEnumeration) (index : Nat) :
    ConditionalPrefixFreeMachine where
  compute := enumeration.compute index
  prefix_free := enumeration.prefix_free index

@[simp] theorem machineAt_compute
    (enumeration : EffectiveConditionalPFMEnumeration) (index : Nat)
    (program condition : BinString) :
    (enumeration.machineAt index).compute program condition =
      enumeration.compute index program condition :=
  rfl

end EffectiveConditionalPFMEnumeration

/-- A host uniformly compiles all machines in one effective enumeration. -/
structure IndexedUniversalConditionalPFM
    (enumeration : EffectiveConditionalPFMEnumeration)
    (host : ConditionalPrefixFreeMachine) where
  compilerPrefix : Nat → BinString
  compute_eq : ∀ index program condition,
    host.compute (compilerPrefix index ++ program) condition =
      enumeration.compute index program condition

namespace IndexedUniversalConditionalPFM

def simulatesCode
    {enumeration : EffectiveConditionalPFMEnumeration}
    {host : ConditionalPrefixFreeMachine}
    (universal : IndexedUniversalConditionalPFM enumeration host)
    (index : Nat) :
    UniformlySimulates host (enumeration.machineAt index) where
  compilerPrefix := universal.compilerPrefix index
  compute_eq := universal.compute_eq index

end IndexedUniversalConditionalPFM

/-- The concrete trimmed enumeration. -/
noncomputable def trimmedConditionalEnumeration :
    EffectiveConditionalPFMEnumeration where
  compute := trimmedConditionalCompute
  prefix_free := by
    intro index condition program extension hPrefix hNe hHalts
    exact (trimmedConditionalPrefixMachine index).prefix_free
      condition program extension hPrefix hNe hHalts
  effective := trimmedConditionalCompute_partrec

/-- The trimmed enumeration contains every effective conditional prefix-free
machine extensionally. -/
theorem trimmedConditionalEnumeration_complete
    (M : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (M.compute program condition)) :
    ∃ index, ∀ program condition,
      trimmedConditionalEnumeration.compute index program condition =
        M.compute program condition :=
  exists_trimmed_code_eq M hEffective

/-- Interpret a self-delimited binary machine index, then run its payload in
the trimmed enumeration. -/
noncomputable def trimmedIndexedHostCompute
    (program condition : BinString) : Option BinString :=
  match e1decode program with
  | none => none
  | some (indexBits, payload) =>
      trimmedConditionalCompute (ofBinaryBits indexBits) payload condition

/-- The prefix-free machine carried by `trimmedIndexedHostCompute`. -/
noncomputable def trimmedIndexedHost : ConditionalPrefixFreeMachine where
  compute := trimmedIndexedHostCompute
  prefix_free := by
    intro condition program extension hPrefix hNe hProgramHalts
    cases hDecode : e1decode program with
    | none => simp [trimmedIndexedHostCompute, hDecode] at hProgramHalts
    | some fields =>
        obtain ⟨indexBits, payload⟩ := fields
        have hPayloadHalts :
            trimmedConditionalCompute (ofBinaryBits indexBits)
              payload condition ≠ none := by
          simpa [trimmedIndexedHostCompute, hDecode] using hProgramHalts
        obtain ⟨suffix, hExtension⟩ := hPrefix
        have hDecodeExtension :
            e1decode extension = some (indexBits, payload ++ suffix) := by
          rw [← hExtension]
          exact e1decode_append_of_success hDecode suffix
        have hPayloadNe : payload ≠ payload ++ suffix := by
          intro hPayload
          apply hNe
          calc
            program = e1encode indexBits ++ payload := e1decode_decompose hDecode
            _ = e1encode indexBits ++ (payload ++ suffix) :=
              congrArg (e1encode indexBits ++ ·) hPayload
            _ = program ++ suffix := by
              rw [e1decode_decompose hDecode, List.append_assoc]
            _ = extension := hExtension
        have hPayloadPrefix : payload <+: payload ++ suffix := ⟨suffix, rfl⟩
        have hExtensionNone :=
          (trimmedConditionalPrefixMachine (ofBinaryBits indexBits)).prefix_free
            condition payload (payload ++ suffix) hPayloadPrefix hPayloadNe
            hPayloadHalts
        change trimmedConditionalCompute (ofBinaryBits indexBits)
          (payload ++ suffix) condition = none at hExtensionNone
        simpa [trimmedIndexedHostCompute, hDecodeExtension] using hExtensionNone

/-- The partial-recursive algorithm underlying `trimmedIndexedHost`.  The
header decoder is total and computable; the payload delegates to the trimmed
partial search. -/
noncomputable def trimmedIndexedHostAlgorithm
    (program condition : BinString) : Part BinString :=
  (Part.ofOption (e1decode program)).bind fun fields =>
    Part.ofOption
      (trimmedConditionalCompute (ofBinaryBits fields.1) fields.2 condition)

/-- Pack the decoded index/payload and the auxiliary condition into the input
format of the trimmed enumeration. -/
def trimmedIndexedHostArguments
    (input : (BinString × BinString) × (BinString × BinString)) :
    Nat × (BinString × BinString) :=
  (ofBinaryBits input.2.1, (input.2.2, input.1.2))

/-- Named composition used by the effective host proof. -/
noncomputable def trimmedIndexedHostRun
    (input : (BinString × BinString) × (BinString × BinString)) :
    Part BinString :=
  trimmedConditionalComputePart (trimmedIndexedHostArguments input)

theorem trimmedIndexedHostArguments_primrec :
    Primrec trimmedIndexedHostArguments := by
  unfold trimmedIndexedHostArguments
  exact Primrec.pair
    (ofBinaryBits_primrec.comp (Primrec.fst.comp Primrec.snd))
    ((Primrec.snd.comp Primrec.snd).pair
      (Primrec.snd.comp Primrec.fst))

theorem trimmedIndexedHostRun_partrec :
    Partrec₂ fun (input : BinString × BinString)
      (fields : BinString × BinString) =>
      Part.ofOption
        (trimmedConditionalCompute
          (ofBinaryBits fields.1) fields.2 input.2) := by
  have hPacked : Partrec trimmedIndexedHostRun :=
    trimmedConditionalComputePart_partrec.comp
      trimmedIndexedHostArguments_primrec.to_comp
  exact hPacked.of_eq fun packed => by
    obtain ⟨input, fields⟩ := packed
    rfl

theorem trimmedIndexedHostAlgorithm_partrec :
    Partrec₂ trimmedIndexedHostAlgorithm := by
  have hDecode : Computable fun input : BinString × BinString =>
      e1decode input.1 :=
    e1decode_primrec.to_comp.comp Computable.fst
  have hParsed : Partrec fun input : BinString × BinString =>
      Part.ofOption (e1decode input.1) :=
    Computable.ofOption hDecode
  exact Partrec.bind hParsed trimmedIndexedHostRun_partrec

@[simp] theorem trimmedIndexedHost_compute
    (program condition : BinString) :
    trimmedIndexedHost.compute program condition =
      match e1decode program with
      | none => none
      | some (indexBits, payload) =>
          trimmedConditionalCompute (ofBinaryBits indexBits)
            payload condition := by
  rfl

/-- The classical `Option` interface of the host denotes exactly its
partial-recursive algorithm. -/
theorem trimmedIndexedHost_part_eq_algorithm
    (program condition : BinString) :
    Part.ofOption (trimmedIndexedHost.compute program condition) =
      trimmedIndexedHostAlgorithm program condition := by
  unfold trimmedIndexedHostAlgorithm
  rw [trimmedIndexedHost_compute]
  cases hDecode : e1decode program with
  | none => simp [Part.ofOption]
  | some fields =>
      obtain ⟨indexBits, payload⟩ := fields
      simp [Part.ofOption, Part.bind_some]

/-- The indexed host is itself an effective conditional prefix machine. -/
theorem trimmedIndexedHost_effective :
    Partrec₂ fun program condition =>
      Part.ofOption (trimmedIndexedHost.compute program condition) :=
  trimmedIndexedHostAlgorithm_partrec.of_eq fun input =>
    (trimmedIndexedHost_part_eq_algorithm input.1 input.2).symm

/-- The concrete host is indexed-universal for the concrete effective
enumeration. -/
noncomputable def trimmedIndexedUniversality :
    IndexedUniversalConditionalPFM trimmedConditionalEnumeration
      trimmedIndexedHost where
  compilerPrefix := fun index => e1encode (binaryBits index)
  compute_eq := by
    intro index program condition
    simp [trimmedIndexedHost, trimmedIndexedHostCompute,
      trimmedConditionalEnumeration,
      e1decode_e1encode_append, ofBinaryBits_binaryBits]

/-- Every effective conditional prefix machine is uniformly simulated by the
concrete indexed host with one fixed compiler prefix. -/
theorem trimmedIndexedHost_simulates_effective
    (M : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (M.compute program condition)) :
    Nonempty (UniformlySimulates trimmedIndexedHost M) := by
  obtain ⟨index, hIndex⟩ :=
    trimmedConditionalEnumeration_complete M hEffective
  exact ⟨{
    compilerPrefix := trimmedIndexedUniversality.compilerPrefix index
    compute_eq := by
      intro program condition
      rw [trimmedIndexedUniversality.compute_eq]
      exact hIndex program condition
  }⟩

#print axioms prefixTest_eq_true_iff
#print axioms eventConflictTest_eq_true_iff
#print axioms rawConditionalEventAt_primrec
#print axioms admittedConditionalEventAt_primrec
#print axioms trimmedConditionalAlgorithm_partrec
#print axioms trimmedConditionalEnumeration_complete
#print axioms trimmedIndexedHost_effective
#print axioms trimmedIndexedHost_simulates_effective

end KolmogorovComplexity
