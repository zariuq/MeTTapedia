import Mettapedia.Computability.KolmogorovComplexity.DiscreteSemimeasureCoding
import Mettapedia.Computability.KolmogorovComplexity.EffectiveConditionalPrefixInterpreter
import Mettapedia.UniversalAI.TimeBoundedAIXI.ProofEnumeration

/-!
# Effective output mass of a conditional prefix machine

For a represented conditional prefix machine, this file builds finite dyadic
approximations to its discrete output mass.  Stage `s` runs every program of
length at most `s` for `s` evaluator steps and retains canonically encoded
outputs whose codes are at most `s`.

The construction is deliberately finite at every stage.  Prefix-freeness of
the source machine gives the exact Kraft budget; monotonicity of bounded
evaluation gives a lower approximation.  Feeding the resulting approximation
to `DiscreteSemimeasureCoding` produces the inner coding machine used by the
conditional lower-chain argument.
-/

namespace KolmogorovComplexity

open scoped Classical
open Mettapedia.UniversalAI.TimeBoundedAIXI

namespace KraftChaitin

/-! ## Bounded machine observations -/

/-- The canonically decoded output of one bounded evaluator run.  The output
code is also bounded by the stage, making every stage finitely supported. -/
def boundedConditionalOutputAt (code : Nat.Partrec.Code)
    (condition : BinString) (stage : Nat) (program : BinString) :
    Option BinString :=
  match Nat.Partrec.Code.evaln stage code
      (Nat.pair (Encodable.encode program) (Encodable.encode condition)) with
  | none => none
  | some encodedOutput =>
      match canonicalDecode encodedOutput with
      | none => none
      | some output =>
          if Encodable.encode output ≤ stage then some output else none

/-- Packed input used by the primitive-recursive bounded observation. -/
abbrev BoundedConditionalOutputInput := (BinString × Nat) × BinString

/-- Bounded conditional execution, canonical decoding, and the finite-support
check are jointly primitive recursive. -/
theorem boundedConditionalOutputAt_primrec (code : Nat.Partrec.Code) :
    Primrec fun input : BoundedConditionalOutputInput =>
      boundedConditionalOutputAt code input.1.1 input.1.2 input.2 := by
  have hCondition : Primrec fun input : BoundedConditionalOutputInput => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hStage : Primrec fun input : BoundedConditionalOutputInput => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hProgram : Primrec fun input : BoundedConditionalOutputInput => input.2 :=
    Primrec.snd
  have hEncodedInput : Primrec fun input : BoundedConditionalOutputInput =>
      Nat.pair (Encodable.encode input.2) (Encodable.encode input.1.1) :=
    Primrec₂.natPair.comp
      (Primrec.encode.comp hProgram) (Primrec.encode.comp hCondition)
  have hEval : Primrec fun input : BoundedConditionalOutputInput =>
      Nat.Partrec.Code.evaln input.1.2 code
        (Nat.pair (Encodable.encode input.2) (Encodable.encode input.1.1)) :=
    Nat.Partrec.Code.primrec_evaln.comp
      ((hStage.pair (Primrec.const code)).pair hEncodedInput)
  have hBranch : Primrec₂ fun (input : BoundedConditionalOutputInput)
      (encodedOutput : Nat) =>
      (canonicalDecode encodedOutput).bind fun output =>
        if Encodable.encode output ≤ input.1.2 then some output else none := by
    apply Primrec₂.mk
    have hDecode : Primrec fun pair : BoundedConditionalOutputInput × Nat =>
        canonicalDecode pair.2 :=
      canonicalDecode_primrec.comp Primrec.snd
    have hAccept : Primrec₂ fun (pair : BoundedConditionalOutputInput × Nat)
        (output : BinString) =>
        if Encodable.encode output ≤ pair.1.1.2 then some output else none := by
      apply Primrec₂.mk
      apply Primrec.ite
      · exact Primrec.nat_le.comp
          (Primrec.encode.comp Primrec.snd)
          (hStage.comp (Primrec.fst.comp Primrec.fst))
      · exact Primrec.option_some.comp Primrec.snd
      · exact Primrec.const none
    exact Primrec.option_bind hDecode hAccept
  exact (Primrec.option_bind hEval hBranch).of_eq fun input => by
    unfold boundedConditionalOutputAt
    cases Nat.Partrec.Code.evaln input.1.2 code
        (Nat.pair (Encodable.encode input.2) (Encodable.encode input.1.1)) with
    | none => rfl
    | some encodedOutput =>
        cases hDecode : canonicalDecode encodedOutput <;> simp [hDecode]

/-- A bounded observation can only expose an output code inside the current
finite support. -/
theorem encode_le_stage_of_boundedConditionalOutputAt
    {code : Nat.Partrec.Code} {condition program output : BinString}
    {stage : Nat}
    (h : boundedConditionalOutputAt code condition stage program = some output) :
    Encodable.encode output ≤ stage := by
  unfold boundedConditionalOutputAt at h
  cases hEval : Nat.Partrec.Code.evaln stage code
      (Nat.pair (Encodable.encode program) (Encodable.encode condition)) with
  | none => simp only [hEval] at h; contradiction
  | some encodedOutput =>
      simp only [hEval] at h
      cases hDecode : canonicalDecode encodedOutput with
      | none => simp only [hDecode] at h; contradiction
      | some decoded =>
          simp only [hDecode] at h
          by_cases hle : Encodable.encode decoded ≤ stage
          · rw [if_pos hle] at h
            have hout : decoded = output := Option.some.inj h
            simpa [← hout] using hle
          · rw [if_neg hle] at h
            contradiction

/-- Bounded evaluation is monotone in its fuel/support stage. -/
theorem boundedConditionalOutputAt_succ
    {code : Nat.Partrec.Code} {condition program output : BinString}
    {stage : Nat}
    (h : boundedConditionalOutputAt code condition stage program = some output) :
    boundedConditionalOutputAt code condition (stage + 1) program = some output := by
  unfold boundedConditionalOutputAt at h ⊢
  cases hEval : Nat.Partrec.Code.evaln stage code
      (Nat.pair (Encodable.encode program) (Encodable.encode condition)) with
  | none => simp only [hEval] at h; contradiction
  | some encodedOutput =>
      simp only [hEval] at h
      have hEvalSucc : Nat.Partrec.Code.evaln (stage + 1) code
          (Nat.pair (Encodable.encode program) (Encodable.encode condition)) =
            some encodedOutput := by
        have hmem : encodedOutput ∈ Nat.Partrec.Code.evaln stage code
            (Nat.pair (Encodable.encode program) (Encodable.encode condition)) := by
          simpa using hEval
        have hmemSucc := Nat.Partrec.Code.evaln_mono
          (Nat.le_succ stage) hmem
        simpa using hmemSucc
      simp only [hEvalSucc]
      cases hDecode : canonicalDecode encodedOutput with
      | none => simp only [hDecode] at h; contradiction
      | some decoded =>
          simp only [hDecode] at h ⊢
          have hle : Encodable.encode decoded ≤ stage := by
            by_contra hnot
            rw [if_neg hnot] at h
            contradiction
          rw [if_pos hle] at h
          have hout : decoded = output := by
            exact Option.some.inj h
          subst output
          rw [if_pos (hle.trans (Nat.le_succ stage))]

theorem boundedConditionalOutputAt_mono
    {code : Nat.Partrec.Code} {condition program output : BinString}
    {first later : Nat}
    (h : boundedConditionalOutputAt code condition first program = some output)
    (hLe : first ≤ later) :
    boundedConditionalOutputAt code condition later program = some output := by
  exact Nat.le_induction (m := first)
    (P := fun stage _ =>
      boundedConditionalOutputAt code condition stage program = some output)
    h (fun _stage _hLe hAt => boundedConditionalOutputAt_succ hAt)
    later hLe

/-! ## First eligible observations -/

/-- A bounded observation is eligible once its source program also fits in
the current finite program universe. -/
def eligibleBoundedConditionalOutputAt (code : Nat.Partrec.Code)
    (condition : BinString) (stage : Nat) (program : BinString) :
    Option BinString :=
  if program.length ≤ stage then
    boundedConditionalOutputAt code condition stage program
  else none

theorem eligibleBoundedConditionalOutputAt_primrec
    (code : Nat.Partrec.Code) :
    Primrec fun input : BoundedConditionalOutputInput =>
      eligibleBoundedConditionalOutputAt code input.1.1 input.1.2 input.2 := by
  apply Primrec.ite
  · exact Primrec.nat_le.comp
      (Primrec.list_length.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  · exact boundedConditionalOutputAt_primrec code
  · exact Primrec.const none

theorem eligibleBoundedConditionalOutputAt_succ
    {code : Nat.Partrec.Code} {condition program output : BinString}
    {stage : Nat}
    (h : eligibleBoundedConditionalOutputAt code condition stage program =
      some output) :
    eligibleBoundedConditionalOutputAt code condition (stage + 1) program =
      some output := by
  unfold eligibleBoundedConditionalOutputAt at h ⊢
  by_cases hLength : program.length ≤ stage
  · rw [if_pos hLength] at h
    rw [if_pos (hLength.trans (Nat.le_succ stage))]
    exact boundedConditionalOutputAt_succ h
  · rw [if_neg hLength] at h
    contradiction

theorem eligibleBoundedConditionalOutputAt_mono
    {code : Nat.Partrec.Code} {condition program output : BinString}
    {first later : Nat}
    (h : eligibleBoundedConditionalOutputAt code condition first program =
      some output) (hLe : first ≤ later) :
    eligibleBoundedConditionalOutputAt code condition later program =
      some output := by
  exact Nat.le_induction (m := first)
    (P := fun stage _ =>
      eligibleBoundedConditionalOutputAt code condition stage program =
        some output)
    h (fun _stage _hLe hAt => eligibleBoundedConditionalOutputAt_succ hAt)
    later hLe

/-- Emit an eligible program exactly at its first eligible bounded stage. -/
def firstEligibleBoundedConditionalOutputAt (code : Nat.Partrec.Code)
    (condition : BinString) (stage : Nat) (program : BinString) :
    Option BinString :=
  if stage = 0 ∨
      eligibleBoundedConditionalOutputAt code condition (stage - 1) program =
        none then
    eligibleBoundedConditionalOutputAt code condition stage program
  else none

theorem firstEligibleBoundedConditionalOutputAt_primrec
    (code : Nat.Partrec.Code) :
    Primrec fun input : BoundedConditionalOutputInput =>
      firstEligibleBoundedConditionalOutputAt code input.1.1 input.1.2
        input.2 := by
  let previousInput : BoundedConditionalOutputInput →
      BoundedConditionalOutputInput := fun input =>
    ((input.1.1, input.1.2 - 1), input.2)
  have hPreviousInput : Primrec previousInput := by
    unfold previousInput
    exact ((Primrec.fst.comp Primrec.fst).pair
      (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.const 1))).pair Primrec.snd
  have hCurrent := eligibleBoundedConditionalOutputAt_primrec code
  have hPrevious : Primrec fun input : BoundedConditionalOutputInput =>
      eligibleBoundedConditionalOutputAt code input.1.1 (input.1.2 - 1)
        input.2 :=
    (eligibleBoundedConditionalOutputAt_primrec code).comp hPreviousInput
  have hZero : PrimrecPred fun input : BoundedConditionalOutputInput =>
      input.1.2 = 0 :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 0)
  have hPreviousNone : PrimrecPred fun input : BoundedConditionalOutputInput =>
      eligibleBoundedConditionalOutputAt code input.1.1 (input.1.2 - 1)
        input.2 = none :=
    Primrec.eq.comp hPrevious (Primrec.const none)
  exact Primrec.ite (hZero.or hPreviousNone) hCurrent (Primrec.const none)

theorem eligible_of_firstEligibleBoundedConditionalOutputAt
    {code : Nat.Partrec.Code} {condition program output : BinString}
    {stage : Nat}
    (h : firstEligibleBoundedConditionalOutputAt code condition stage program =
      some output) :
    eligibleBoundedConditionalOutputAt code condition stage program =
      some output := by
  unfold firstEligibleBoundedConditionalOutputAt at h
  by_cases hAccept : stage = 0 ∨
      eligibleBoundedConditionalOutputAt code condition (stage - 1) program =
        none
  · rw [if_pos hAccept] at h
    exact h
  · rw [if_neg hAccept] at h
    contradiction

theorem previous_none_of_firstEligibleBoundedConditionalOutputAt
    {code : Nat.Partrec.Code} {condition program output : BinString}
    {stage : Nat} (hPositive : stage ≠ 0)
    (h : firstEligibleBoundedConditionalOutputAt code condition stage program =
      some output) :
    eligibleBoundedConditionalOutputAt code condition (stage - 1) program =
      none := by
  unfold firstEligibleBoundedConditionalOutputAt at h
  by_cases hPrevious : eligibleBoundedConditionalOutputAt code condition
      (stage - 1) program = none
  · exact hPrevious
  · rw [if_neg (by exact fun hAccept => hAccept.elim hPositive hPrevious)] at h
    contradiction

/-- Every eligible bounded observation has a least eligible stage, and that
stage is emitted by `firstEligibleBoundedConditionalOutputAt`. -/
theorem exists_firstEligibleBoundedConditionalOutputAt
    {code : Nat.Partrec.Code} {condition program output : BinString}
    {stage : Nat}
    (hEligible : eligibleBoundedConditionalOutputAt code condition stage
      program = some output) :
    ∃ first ≤ stage,
      firstEligibleBoundedConditionalOutputAt code condition first program =
        some output := by
  let existsEligible : ∃ candidate,
      eligibleBoundedConditionalOutputAt code condition candidate program =
        some output := ⟨stage, hEligible⟩
  let first := Nat.find existsEligible
  have hFirstEligible : eligibleBoundedConditionalOutputAt code condition first
      program = some output := Nat.find_spec existsEligible
  have hFirstLe : first ≤ stage := Nat.find_min' existsEligible hEligible
  refine ⟨first, hFirstLe, ?_⟩
  unfold firstEligibleBoundedConditionalOutputAt
  by_cases hZero : first = 0
  · rw [if_pos (Or.inl hZero)]
    exact hFirstEligible
  · have hPreviousNone : eligibleBoundedConditionalOutputAt code condition
        (first - 1) program = none := by
      cases hPrevious : eligibleBoundedConditionalOutputAt code condition
          (first - 1) program with
      | none => rfl
      | some previousOutput =>
          have hPreviousLe : first - 1 ≤ first := Nat.sub_le _ _
          have hPersists := eligibleBoundedConditionalOutputAt_mono
            hPrevious hPreviousLe
          rw [hFirstEligible] at hPersists
          have hOutput : previousOutput = output :=
            (Option.some.inj hPersists).symm
          subst previousOutput
          have hPreviousLt : first - 1 < first := by omega
          exact False.elim
            (Nat.find_min existsEligible hPreviousLt hPrevious)
    rw [if_pos (Or.inr hPreviousNone)]
    exact hFirstEligible

/-- A source program has at most one first eligible observation stage. -/
theorem firstEligibleBoundedConditionalOutputAt_stage_unique
    {code : Nat.Partrec.Code} {condition program : BinString}
    {first later : Nat} {firstOutput laterOutput : BinString}
    (hFirst : firstEligibleBoundedConditionalOutputAt code condition first
      program = some firstOutput)
    (hLater : firstEligibleBoundedConditionalOutputAt code condition later
      program = some laterOutput) :
    first = later := by
  rcases Nat.lt_trichotomy first later with hlt | heq | hgt
  · have hLaterPositive : later ≠ 0 := by omega
    have hFirstBefore : first ≤ later - 1 := by omega
    have hPersists := eligibleBoundedConditionalOutputAt_mono
      (eligible_of_firstEligibleBoundedConditionalOutputAt hFirst) hFirstBefore
    rw [previous_none_of_firstEligibleBoundedConditionalOutputAt
      hLaterPositive hLater] at hPersists
    contradiction
  · exact heq
  · have hFirstPositive : first ≠ 0 := by omega
    have hLaterBefore : later ≤ first - 1 := by omega
    have hPersists := eligibleBoundedConditionalOutputAt_mono
      (eligible_of_firstEligibleBoundedConditionalOutputAt hLater) hLaterBefore
    rw [previous_none_of_firstEligibleBoundedConditionalOutputAt
      hFirstPositive hFirst] at hPersists
    contradiction

/-- A bounded observation of a represented source code is a genuine source
machine computation. -/
theorem source_compute_of_boundedConditionalOutputAt
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    {condition program output : BinString} {stage : Nat}
    (h : boundedConditionalOutputAt code condition stage program = some output) :
    M.compute program condition = some output := by
  unfold boundedConditionalOutputAt at h
  cases hEval : Nat.Partrec.Code.evaln stage code
      (Nat.pair (Encodable.encode program) (Encodable.encode condition)) with
  | none => simp only [hEval] at h; contradiction
  | some encodedOutput =>
      simp only [hEval] at h
      cases hDecode : canonicalDecode encodedOutput with
      | none => simp only [hDecode] at h; contradiction
      | some decoded =>
          simp only [hDecode] at h
          by_cases hle : Encodable.encode decoded ≤ stage
          · rw [if_pos hle] at h
            have hout : decoded = output := Option.some.inj h
            subst decoded
            have hCanonical : Encodable.encode output = encodedOutput := by
              unfold canonicalDecode at hDecode
              cases hRawDecode : Encodable.decode (α := BinString) encodedOutput with
              | none => simp [hRawDecode] at hDecode
              | some rawOutput =>
                  by_cases hcanon : Encodable.encode rawOutput = encodedOutput
                  · simp [hRawDecode, hcanon] at hDecode
                    simpa [hDecode] using hcanon
                  · simp [hRawDecode, hcanon] at hDecode
            have hRaw : rawConditionalEventAt
                (Nat.Partrec.Code.encodeCode code)
                (Nat.pair stage
                  (Nat.pair (Encodable.encode program)
                    (Encodable.encode condition))) =
                  some (program, condition, output) := by
              unfold rawConditionalEventAt
              simp only [Nat.unpair_pair, ofNatCode_encodeCode]
              rw [hEval, ← hCanonical]
              simp
            exact source_compute_of_rawConditionalEventAt M code hCode hRaw
          · rw [if_neg hle] at h
            contradiction

/-! ## Finite program families and their mass -/

/-- Programs observed to halt canonically within the current stage. -/
def activeConditionalPrograms (code : Nat.Partrec.Code)
    (condition : BinString) (stage : Nat) : List BinString :=
  (bitstringsUpTo stage).filter fun program =>
    (boundedConditionalOutputAt code condition stage program).isSome

private theorem bitstringsOfLength_nodup_local :
    ∀ n : Nat, (bitstringsOfLength n).Nodup := by
  intro n
  induction n with
  | zero => simp [bitstringsOfLength]
  | succ n ih =>
      have hnodupEach :
          ∀ xs ∈ bitstringsOfLength n,
            ([false :: xs, true :: xs] : List BinString).Nodup := by
        intro xs _hxs
        simp
      have hdisjoint :
          (bitstringsOfLength n).Pairwise fun xs ys =>
            ([false :: xs, true :: xs] : List BinString).Disjoint
              [false :: ys, true :: ys] := by
        refine List.Nodup.pairwise_of_forall_ne ih ?_
        intro xs _hxs ys _hys hne
        refine (List.disjoint_left).2 ?_
        intro value hvalueLeft hvalueRight
        rcases (by simpa using hvalueLeft) with rfl | rfl
        · have heq : false :: xs = false :: ys ∨
              false :: xs = true :: ys := by
            simpa using hvalueRight
          rcases heq with heq | heq
          · exact hne (List.cons.inj heq).2
          · cases heq
        · have heq : true :: xs = false :: ys ∨
              true :: xs = true :: ys := by
            simpa using hvalueRight
          rcases heq with heq | heq
          · cases heq
          · exact hne (List.cons.inj heq).2
      exact (List.nodup_flatMap).2 ⟨hnodupEach, hdisjoint⟩

private theorem bitstringsUpTo_nodup_local :
    ∀ n : Nat, (bitstringsUpTo n).Nodup := by
  intro n
  induction n with
  | zero =>
      simpa [bitstringsUpTo] using bitstringsOfLength_nodup_local 0
  | succ n ih =>
      have hcross : ∀ left ∈ bitstringsUpTo n,
          ∀ right ∈ bitstringsOfLength (n + 1), left ≠ right := by
        intro left hleft right hright heq
        have hleftLength := length_le_of_mem_bitstringsUpTo hleft
        have hrightLength := length_eq_of_mem_bitstringsOfLength hright
        have hsizes := congrArg List.length heq
        omega
      have happend :
          (bitstringsUpTo n ++ bitstringsOfLength (n + 1)).Nodup := by
        exact (List.nodup_append).2
          ⟨ih, bitstringsOfLength_nodup_local (n + 1), hcross⟩
      simpa [bitstringsUpTo] using happend

/-- The existing finite bitstring enumeration is primitive recursive. -/
private theorem bitstringsOfLength_primrec_local :
    Primrec bitstringsOfLength := by
  let expand : Nat → List BinString → List BinString := fun _stage previous =>
    previous.flatMap fun bits => [false :: bits, true :: bits]
  have hbranch : Primrec fun input : (Nat × List BinString) × BinString =>
      ([false :: input.2, true :: input.2] : List BinString) := by
    have hfalse : Primrec fun input : (Nat × List BinString) × BinString =>
        false :: input.2 :=
      Primrec.list_cons.comp (Primrec.const false) Primrec.snd
    have htrue : Primrec fun input : (Nat × List BinString) × BinString =>
        true :: input.2 :=
      Primrec.list_cons.comp (Primrec.const true) Primrec.snd
    exact Primrec.list_cons.comp hfalse
      (Primrec.list_cons.comp htrue (Primrec.const []))
  have hexpand : Primrec₂ expand := by
    apply Primrec₂.mk
    exact Primrec.list_flatMap Primrec.snd hbranch.to₂
  exact (Primrec.nat_rec₁ ([[]] : List BinString) hexpand).of_eq fun n => by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [bitstringsOfLength, expand]
        rw [← ih]

/-- Enumerating all bitstrings up to a length bound is primitive recursive. -/
private theorem bitstringsUpTo_primrec_local : Primrec bitstringsUpTo := by
  let extend : Nat → List BinString → List BinString := fun stage previous =>
    previous ++ bitstringsOfLength (stage + 1)
  have hextend : Primrec₂ extend := by
    exact Primrec.list_append.comp₂ Primrec₂.right
      (bitstringsOfLength_primrec_local.comp₂
        (Primrec.succ.comp₂ Primrec₂.left))
  exact (Primrec.nat_rec₁ (bitstringsOfLength 0) hextend).of_eq fun n => by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [bitstringsUpTo, extend]
        rw [← ih]

theorem activeConditionalPrograms_nodup
    (code : Nat.Partrec.Code) (condition : BinString) (stage : Nat) :
    (activeConditionalPrograms code condition stage).Nodup := by
  exact (bitstringsUpTo_nodup_local stage).filter _

/-- At a represented prefix machine, the active finite stage is itself a
prefix-free code family. -/
theorem activeConditionalPrograms_prefixFree
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    (condition : BinString) (stage : Nat) :
    PrefixFree
      (↑(activeConditionalPrograms code condition stage).toFinset :
        Set BinString) := by
  intro left hleft right hright hne hprefix
  have hleft' : left ∈ activeConditionalPrograms code condition stage := by
    simpa using hleft
  have hright' : right ∈ activeConditionalPrograms code condition stage := by
    simpa using hright
  simp only [activeConditionalPrograms, List.mem_filter] at hleft' hright'
  obtain ⟨_hleftBound, hleftSome⟩ := hleft'
  obtain ⟨_hrightBound, hrightSome⟩ := hright'
  obtain ⟨leftOutput, hleftOutput⟩ := Option.isSome_iff_exists.mp hleftSome
  obtain ⟨rightOutput, hrightOutput⟩ := Option.isSome_iff_exists.mp hrightSome
  have hleftCompute := source_compute_of_boundedConditionalOutputAt
    M code hCode hleftOutput
  have hrightCompute := source_compute_of_boundedConditionalOutputAt
    M code hCode hrightOutput
  have hleftHalts : M.compute left condition ≠ none := by
    rw [hleftCompute]
    simp
  have hrightNone := M.prefix_free condition left right hprefix hne hleftHalts
  rw [hrightCompute] at hrightNone
  simp at hrightNone

/-- The active finite program family obeys the rational Kraft bound. -/
theorem activeConditionalPrograms_rationalMass_le_one
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    (condition : BinString) (stage : Nat) :
    rationalLengthMass
        ((activeConditionalPrograms code condition stage).map List.length) ≤ 1 := by
  exact rationalLengthMass_map_length_le_one
    (activeConditionalPrograms code condition stage)
    (activeConditionalPrograms_nodup code condition stage)
    (activeConditionalPrograms_prefixFree M code hCode condition stage)

/-! ## Output numerators -/

/-- The common-denominator contribution of one program to one output code. -/
def conditionalOutputContribution (code : Nat.Partrec.Code)
    (condition : BinString) (stage outputCode : Nat)
    (program : BinString) : Nat :=
  match boundedConditionalOutputAt code condition stage program with
  | none => 0
  | some output =>
      if Encodable.encode output = outputCode then
        2 ^ (stage - program.length)
      else 0

/-- Finite-stage numerator of one output code. -/
def conditionalOutputNumerator (code : Nat.Partrec.Code)
    (condition : BinString) (stage outputCode : Nat) : Nat :=
  ((bitstringsUpTo stage).map
    (conditionalOutputContribution code condition stage outputCode)).sum

/-- Packed input for the finite output numerator. -/
abbrev ConditionalOutputNumeratorInput := (BinString × Nat) × Nat

/-- One program's common-denominator contribution is primitive recursive in
the condition, stage, output code, and program. -/
theorem conditionalOutputContribution_primrec (code : Nat.Partrec.Code) :
    Primrec₂ fun (input : ConditionalOutputNumeratorInput) (program : BinString) =>
      conditionalOutputContribution code input.1.1 input.1.2 input.2 program := by
  apply Primrec₂.mk
  have hCondition : Primrec fun input : ConditionalOutputNumeratorInput => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hStage : Primrec fun input : ConditionalOutputNumeratorInput => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hOutputCode : Primrec fun input : ConditionalOutputNumeratorInput => input.2 :=
    Primrec.snd
  have hBounded : Primrec fun pair : ConditionalOutputNumeratorInput × BinString =>
      boundedConditionalOutputAt code pair.1.1.1 pair.1.1.2 pair.2 :=
    boundedConditionalOutputAt_primrec code |>.comp
      (Primrec.pair
        (Primrec.pair
          (hCondition.comp Primrec.fst)
          (hStage.comp Primrec.fst))
        Primrec.snd)
  have hSuccess : Primrec₂ fun
      (pair : ConditionalOutputNumeratorInput × BinString)
      (output : BinString) =>
      if Encodable.encode output = pair.1.2 then
        2 ^ (pair.1.1.2 - pair.2.length)
      else 0 := by
    apply Primrec₂.mk
    have hPackedStage : Primrec fun
        packed : (ConditionalOutputNumeratorInput × BinString) × BinString =>
        packed.1.1.1.2 :=
      hStage.comp (Primrec.fst.comp Primrec.fst)
    have hPackedProgram : Primrec fun
        packed : (ConditionalOutputNumeratorInput × BinString) × BinString =>
        packed.1.2 :=
      Primrec.snd.comp Primrec.fst
    have hPackedOutputCode : Primrec fun
        packed : (ConditionalOutputNumeratorInput × BinString) × BinString =>
        packed.1.1.2 :=
      hOutputCode.comp (Primrec.fst.comp Primrec.fst)
    have hExponent : Primrec fun
        packed : (ConditionalOutputNumeratorInput × BinString) × BinString =>
        packed.1.1.1.2 - packed.1.2.length :=
      Primrec.nat_sub.comp hPackedStage
        (Primrec.list_length.comp hPackedProgram)
    have hPow : Primrec fun
        packed : (ConditionalOutputNumeratorInput × BinString) × BinString =>
        2 ^ (packed.1.1.1.2 - packed.1.2.length) :=
      (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp
        (Primrec.const 2) hExponent
    apply Primrec.ite
    · exact Primrec.eq.comp
        (Primrec.encode.comp Primrec.snd) hPackedOutputCode
    · exact hPow
    · exact Primrec.const 0
  exact (Primrec.option_casesOn hBounded (Primrec.const 0) hSuccess).of_eq
    fun pair => by
      unfold conditionalOutputContribution
      cases hOutput : boundedConditionalOutputAt code pair.1.1.1
          pair.1.1.2 pair.2 <;> simp

/-- The complete finite-stage output numerator is primitive recursive. -/
theorem conditionalOutputNumerator_primrec (code : Nat.Partrec.Code) :
    Primrec fun input : ConditionalOutputNumeratorInput =>
      conditionalOutputNumerator code input.1.1 input.1.2 input.2 := by
  have hStage : Primrec fun input : ConditionalOutputNumeratorInput => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hPrograms : Primrec fun input : ConditionalOutputNumeratorInput =>
      bitstringsUpTo input.1.2 :=
    bitstringsUpTo_primrec_local.comp hStage
  have hStep : Primrec₂ fun (input : ConditionalOutputNumeratorInput)
      (pair : BinString × Nat) =>
      conditionalOutputContribution code input.1.1 input.1.2 input.2 pair.1 +
        pair.2 := by
    exact Primrec.nat_add.comp₂
      (conditionalOutputContribution_primrec code |>.comp₂
        Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hPrograms (Primrec.const 0) hStep).of_eq
    fun input => by
      unfold conditionalOutputNumerator
      induction bitstringsUpTo input.1.2 with
      | nil => rfl
      | cons program programs ih =>
          simp only [List.map_cons, List.sum_cons, List.foldr_cons]
          rw [ih]

/-- No output code outside the stage support receives mass. -/
theorem conditionalOutputNumerator_support
    (code : Nat.Partrec.Code) (condition : BinString) (stage outputCode : Nat)
    (houtside : stage < outputCode) :
    conditionalOutputNumerator code condition stage outputCode = 0 := by
  unfold conditionalOutputNumerator
  apply List.sum_eq_zero
  intro contribution hcontribution
  simp only [List.mem_map] at hcontribution
  obtain ⟨program, _hprogram, rfl⟩ := hcontribution
  unfold conditionalOutputContribution
  cases hBounded : boundedConditionalOutputAt code condition stage program with
  | none => rfl
  | some output =>
      have hencode := encode_le_stage_of_boundedConditionalOutputAt hBounded
      have hne : Encodable.encode output ≠ outputCode := by omega
      simp [hne]

/-- A contribution already present at stage `s` doubles, or is dominated by
the contribution, at stage `s+1`. -/
theorem conditionalOutputContribution_succ
    {code : Nat.Partrec.Code} {condition program : BinString}
    {stage outputCode : Nat}
    (hlength : program.length ≤ stage) :
    2 * conditionalOutputContribution code condition stage outputCode program ≤
      conditionalOutputContribution code condition (stage + 1) outputCode program := by
  unfold conditionalOutputContribution
  cases hBounded : boundedConditionalOutputAt code condition stage program with
  | none => simp
  | some output =>
      have hSucc := boundedConditionalOutputAt_succ hBounded
      simp only [hSucc]
      by_cases hcode : Encodable.encode output = outputCode
      · rw [if_pos hcode, if_pos hcode]
        have hexponent : stage + 1 - program.length =
            stage - program.length + 1 := by omega
        rw [hexponent, pow_succ]
        omega
      · simp [hcode]

/-- Finite-stage output numerators form a dyadic lower approximation. -/
theorem conditionalOutputNumerator_monotone
    (code : Nat.Partrec.Code) (condition : BinString)
    (stage outputCode : Nat) :
    2 * conditionalOutputNumerator code condition stage outputCode ≤
      conditionalOutputNumerator code condition (stage + 1) outputCode := by
  have holdFor : ∀ programs : List BinString,
      (∀ program ∈ programs, program.length ≤ stage) →
      2 * (programs.map
          (conditionalOutputContribution code condition stage outputCode)).sum ≤
        (programs.map
          (conditionalOutputContribution code condition (stage + 1)
            outputCode)).sum := by
    intro programs hlengths
    induction programs with
    | nil => simp
    | cons program programs ih =>
        simp only [List.map_cons, List.sum_cons]
        have hlength := hlengths program List.mem_cons_self
        have hhead := conditionalOutputContribution_succ
          (code := code) (condition := condition) (program := program)
          (stage := stage) (outputCode := outputCode) hlength
        have htail := ih (fun item hitem =>
          hlengths item (List.mem_cons_of_mem _ hitem))
        omega
  have hold := holdFor (bitstringsUpTo stage) fun program hprogram =>
    length_le_of_mem_bitstringsUpTo hprogram
  unfold conditionalOutputNumerator
  change
    2 * ((bitstringsUpTo stage).map
        (conditionalOutputContribution code condition stage outputCode)).sum ≤
      ((bitstringsUpTo (stage + 1)).map
        (conditionalOutputContribution code condition (stage + 1)
          outputCode)).sum
  rw [bitstringsUpTo]
  simp only [List.map_append, List.sum_append]
  exact hold.trans (Nat.le_add_right _ _)

/-- Summing one program's contributions over the complete finite output
support recovers its full common-denominator weight exactly when it is active. -/
theorem sum_conditionalOutputContribution_range
    (code : Nat.Partrec.Code) (condition program : BinString)
    (stage : Nat) :
    ((List.range (stage + 1)).map fun outputCode =>
        conditionalOutputContribution code condition stage outputCode program).sum =
      if (boundedConditionalOutputAt code condition stage program).isSome then
        2 ^ (stage - program.length)
      else 0 := by
  unfold conditionalOutputContribution
  cases hBounded : boundedConditionalOutputAt code condition stage program with
  | none => simp
  | some output =>
      have hencode := encode_le_stage_of_boundedConditionalOutputAt hBounded
      simp only [Option.isSome_some, if_true]
      rw [← List.sum_toFinset _ List.nodup_range]
      simp [Finset.sum_ite_eq, hencode]

/-- Finite double sums over programs and output codes may be exchanged. -/
private theorem sum_map_sum_map_swap
    {Left Right : Type*} (left : List Left) (right : List Right)
    (weight : Left → Right → Nat) :
    (left.map fun a => (right.map fun b => weight a b).sum).sum =
      (right.map fun b => (left.map fun a => weight a b).sum).sum := by
  induction left with
  | nil => simp
  | cons a left ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      simp only [List.sum_map_add]

/-- Summing the output numerator profile is the full weight of the active
programs, with no double counting between output codes. -/
theorem sum_conditionalOutputNumerator_eq_activeWeight
    (code : Nat.Partrec.Code) (condition : BinString) (stage : Nat) :
    ((List.range (stage + 1)).map
        (conditionalOutputNumerator code condition stage)).sum =
      ((bitstringsUpTo stage).map fun program =>
        if (boundedConditionalOutputAt code condition stage program).isSome then
          2 ^ (stage - program.length)
        else 0).sum := by
  unfold conditionalOutputNumerator
  rw [sum_map_sum_map_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro program _hprogram
  exact sum_conditionalOutputContribution_range code condition program stage

/-- Filtering the active programs merely removes the zero terms in the full
finite enumeration. -/
theorem sum_activeWeight_eq_lengthMass
    (code : Nat.Partrec.Code) (condition : BinString) (stage : Nat) :
    ((bitstringsUpTo stage).map fun program =>
        if (boundedConditionalOutputAt code condition stage program).isSome then
          2 ^ (stage - program.length)
        else 0).sum =
      lengthMass stage
        ((activeConditionalPrograms code condition stage).map List.length) := by
  unfold activeConditionalPrograms lengthMass
  have helper : ∀ programs : List BinString,
      (programs.map fun program =>
          if (boundedConditionalOutputAt code condition stage program).isSome then
            2 ^ (stage - program.length)
          else 0).sum =
        (((programs.filter fun program =>
            (boundedConditionalOutputAt code condition stage program).isSome).map
          List.length).map fun length => 2 ^ (stage - length)).sum := by
    intro programs
    induction programs with
    | nil => rfl
    | cons program programs ih =>
        cases hBounded : boundedConditionalOutputAt code condition stage program with
        | none => simp [hBounded, ih]
        | some output => simp [hBounded, ih]
  exact helper (bitstringsUpTo stage)

/-- The exact `Nat` capacity bound for the finite output profile. -/
theorem conditionalOutputNumerator_budget
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    (condition : BinString) (stage : Nat) :
    ((List.range (stage + 1)).map
        (conditionalOutputNumerator code condition stage)).sum ≤ 2 ^ stage := by
  rw [sum_conditionalOutputNumerator_eq_activeWeight,
    sum_activeWeight_eq_lengthMass]
  have hall : ∀ length ∈
      (activeConditionalPrograms code condition stage).map List.length,
      length ≤ stage := by
    intro length hlength
    simp only [List.mem_map] at hlength
    obtain ⟨program, hprogram, rfl⟩ := hlength
    have hprogramAll : program ∈ bitstringsUpTo stage := by
      simp only [activeConditionalPrograms, List.mem_filter] at hprogram
      exact hprogram.1
    exact length_le_of_mem_bitstringsUpTo hprogramAll
  have hratio := lengthMass_div_pow_eq_rationalLengthMass hall
  have hrational := activeConditionalPrograms_rationalMass_le_one
    M code hCode condition stage
  have hden : 0 < (2 : ℚ) ^ stage := by positivity
  have hcast :
      (lengthMass stage
          ((activeConditionalPrograms code condition stage).map List.length) : ℚ) ≤
        (2 : ℚ) ^ stage := by
    apply (div_le_one hden).mp
    rw [hratio]
    exact hrational
  exact_mod_cast hcast

/-! ## Effective output semimeasure -/

/-- The finite output-mass construction as an effective discrete dyadic
semimeasure. -/
def conditionalOutputApproximation
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M) :
    EffectiveDiscreteDyadic where
  numerator := conditionalOutputNumerator code
  numerator_primrec := conditionalOutputNumerator_primrec code
  support := conditionalOutputNumerator_support code
  budget := conditionalOutputNumerator_budget M code hCode
  monotone := conditionalOutputNumerator_monotone code

/-- Every effective conditional prefix machine has a code in the evaluator
representation used by the finite output construction. -/
theorem exists_code_of_conditionalMachine_effective
    (M : ConditionalPrefixFreeMachine)
    (hEffective : Partrec₂ fun program condition =>
      Part.ofOption (M.compute program condition)) :
    ∃ code : Nat.Partrec.Code,
      Nat.Partrec.Code.eval code = encodedConditionalCompute M := by
  have hEncoded : Nat.Partrec (encodedConditionalCompute M) := by
    unfold Partrec₂ Partrec at hEffective
    exact hEffective.of_eq fun encodedInput => by
      unfold encodedConditionalCompute
      rfl
  exact (Nat.Partrec.Code.exists_code).1 hEncoded

/-- Every genuine source computation appears at a finite bounded stage that
also contains its program and canonical output code. -/
theorem exists_boundedConditionalOutputAt_of_source_compute
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    {program condition output : BinString}
    (hCompute : M.compute program condition = some output) :
    ∃ stage,
      program.length ≤ stage ∧ Encodable.encode output ≤ stage ∧
        boundedConditionalOutputAt code condition stage program = some output := by
  have hEval : Encodable.encode output ∈
      Nat.Partrec.Code.eval code
        (Nat.pair (Encodable.encode program) (Encodable.encode condition)) := by
    rw [hCode]
    simp [encodedConditionalCompute, hCompute]
  obtain ⟨fuel, hFuel⟩ := Nat.Partrec.Code.evaln_complete.mp hEval
  let stage := max fuel (max program.length (Encodable.encode output))
  have hFuelLe : fuel ≤ stage := Nat.le_max_left _ _
  have hProgramLe : program.length ≤ stage := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hOutputLe : Encodable.encode output ≤ stage := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hAtStage : Nat.Partrec.Code.evaln stage code
      (Nat.pair (Encodable.encode program) (Encodable.encode condition)) =
        some (Encodable.encode output) := by
    have hMono := Nat.Partrec.Code.evaln_mono hFuelLe hFuel
    simpa using hMono
  refine ⟨stage, hProgramLe, hOutputLe, ?_⟩
  unfold boundedConditionalOutputAt
  simp only [hAtStage, canonicalDecode_encode, if_pos hOutputLe]

/-- One listed program contributes no more than the complete numerator. -/
theorem conditionalOutputContribution_le_numerator
    (code : Nat.Partrec.Code) (condition program : BinString)
    (stage outputCode : Nat)
    (hProgram : program ∈ bitstringsUpTo stage) :
    conditionalOutputContribution code condition stage outputCode program ≤
      conditionalOutputNumerator code condition stage outputCode := by
  unfold conditionalOutputNumerator
  apply List.single_le_sum (fun _contribution _hmem => Nat.zero_le _)
  exact List.mem_map.mpr ⟨program, hProgram, rfl⟩

/-- Every source program crosses the output-mass threshold indexed by its own
length.  This is the concentration step needed by the inner coding machine. -/
theorem exists_conditionalOutputApproximation_crossing
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    {program condition output : BinString}
    (hCompute : M.compute program condition = some output) :
    ∃ stage, ThresholdCrossed (conditionalOutputApproximation M code hCode)
      condition stage (Encodable.encode output) program.length := by
  obtain ⟨stage, hProgramLe, hOutputLe, hBounded⟩ :=
    exists_boundedConditionalOutputAt_of_source_compute M code hCode hCompute
  refine ⟨stage, hOutputLe, hProgramLe, ?_⟩
  have hProgram : program ∈ bitstringsUpTo stage :=
    mem_bitstringsUpTo_of_length_le hProgramLe
  have hContribution := conditionalOutputContribution_le_numerator
    code condition program stage (Encodable.encode output) hProgram
  have hContributionEq :
      conditionalOutputContribution code condition stage
          (Encodable.encode output) program =
        2 ^ (stage - program.length) := by
    simp [conditionalOutputContribution, hBounded]
  rw [hContributionEq] at hContribution
  exact hContribution

/-- The effective output-mass coder associated with a represented conditional
prefix machine. -/
noncomputable def conditionalOutputCodingMachine
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M) :
    ConditionalPrefixFreeMachine :=
  discreteDyadicMachine (conditionalOutputApproximation M code hCode)

/-- The output-mass coder is an effective conditional prefix machine. -/
theorem conditionalOutputCodingMachine_effective
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M) :
    Partrec₂ fun program condition =>
      Part.ofOption
        ((conditionalOutputCodingMachine M code hCode).compute program condition) := by
  exact discreteDyadicMachine_effective
    (conditionalOutputApproximation M code hCode)

/-- Inner coding bound: every source description of an output yields an
output-mass description with at most two additional bits. -/
theorem conditionalOutputCodingMachine_complexity_le
    (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    {program condition output : BinString}
    (hCompute : M.compute program condition = some output) :
    Kc[conditionalOutputCodingMachine M code hCode](output | condition) ≤
      program.length + 2 := by
  obtain ⟨stage, hCrossing⟩ :=
    exists_conditionalOutputApproximation_crossing M code hCode hCompute
  exact discreteDyadicMachine_complexity_of_crossed
    (stage := stage) hCrossing

/-- Output-mass concentration relative to a reference machine that simulates
the effective output coder.  The explicit `+3` absorbs the two-bit dyadic
request overhead and the strict threshold needed for contradiction. -/
theorem conditionalOutputNumerator_concentration
    (M U : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    (simulation : UniformlySimulates U
      (conditionalOutputCodingMachine M code hCode))
    (condition output : BinString) (stage : Nat) :
    conditionalOutputNumerator code condition stage (Encodable.encode output) ≤
      2 ^ (stage + (simulation.compilerPrefix.length + 3) -
        Kc[U](output | condition)) := by
  let mass := conditionalOutputNumerator code condition stage
    (Encodable.encode output)
  let complexity := Kc[U](output | condition)
  let compilerCost := simulation.compilerPrefix.length
  let concentrationCost := compilerCost + 3
  have hMassBound : mass ≤ 2 ^ stage := by
    exact (conditionalOutputApproximation M code hCode).numerator_le_pow
      condition stage (Encodable.encode output)
  by_cases hSmall : complexity ≤ concentrationCost
  · have hExponent : stage ≤ stage + concentrationCost - complexity := by
      omega
    exact hMassBound.trans
      (Nat.pow_le_pow_right (by omega) hExponent)
  · have hCostLt : concentrationCost < complexity := Nat.lt_of_not_ge hSmall
    by_cases hCodeStage : Encodable.encode output ≤ stage
    · let threshold := complexity - concentrationCost
      by_cases hThresholdStage : threshold ≤ stage
      · by_contra hTarget
        have hExponent : stage - threshold =
            stage + concentrationCost - complexity := by
          dsimp [threshold]
          omega
        have hCrossing : ThresholdCrossed
            (conditionalOutputApproximation M code hCode)
            condition stage (Encodable.encode output) threshold := by
          refine ⟨hCodeStage, hThresholdStage, ?_⟩
          rw [hExponent]
          exact (Nat.lt_of_not_ge hTarget).le
        have hCoderHas : HasProgram
            (conditionalOutputCodingMachine M code hCode) condition output := by
          exact discreteDyadicMachine_hasProgram_of_crossed hCrossing
        have hSimulation := simulation.conditionalComplexity_le hCoderHas
        have hCoding := discreteDyadicMachine_complexity_of_crossed hCrossing
        change Kc[conditionalOutputCodingMachine M code hCode](output | condition) ≤
          threshold + 2 at hCoding
        have hTooShort : complexity ≤ threshold + 2 + compilerCost := by
          dsimp [complexity, compilerCost]
          omega
        dsimp [threshold, concentrationCost, compilerCost, complexity] at hTooShort
        omega
      · by_contra hTarget
        have hPowerZero :
            2 ^ (stage + concentrationCost - complexity) = 1 := by
          have hExponentZero : stage + concentrationCost - complexity = 0 := by
            dsimp [threshold] at hThresholdStage
            omega
          rw [hExponentZero]
          rfl
        have hMassPositive : 1 ≤ mass := by
          rw [hPowerZero] at hTarget
          omega
        have hCrossing : ThresholdCrossed
            (conditionalOutputApproximation M code hCode)
            condition stage (Encodable.encode output) stage := by
          refine ⟨hCodeStage, Nat.le_refl _, ?_⟩
          simp only [Nat.sub_self, pow_zero, conditionalOutputApproximation]
          exact hMassPositive
        have hCoderHas : HasProgram
            (conditionalOutputCodingMachine M code hCode) condition output := by
          exact discreteDyadicMachine_hasProgram_of_crossed hCrossing
        have hSimulation := simulation.conditionalComplexity_le hCoderHas
        have hCoding := discreteDyadicMachine_complexity_of_crossed hCrossing
        change Kc[conditionalOutputCodingMachine M code hCode](output | condition) ≤
          stage + 2 at hCoding
        have hTooShort : complexity ≤ stage + 2 + compilerCost := by
          dsimp [complexity, compilerCost]
          omega
        dsimp [threshold, concentrationCost, compilerCost, complexity]
          at hThresholdStage hTooShort
        omega
    · have hOutside := conditionalOutputNumerator_support code condition stage
        (Encodable.encode output) (Nat.lt_of_not_ge hCodeStage)
      rw [hOutside]
      exact Nat.zero_le _

/-- Positive finite output mass witnesses a source program of length at most
the stage.  Consequently, relative to a machine simulating the inner coder,
the output complexity is bounded by the stage plus the exact compiler and
two-bit dyadic overheads. -/
theorem conditionalOutputNumerator_positive_complexity_le
    (M U : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    (simulation : UniformlySimulates U
      (conditionalOutputCodingMachine M code hCode))
    (condition output : BinString) (stage : Nat)
    (hPositive : 0 < conditionalOutputNumerator code condition stage
      (Encodable.encode output)) :
    Kc[U](output | condition) ≤
      stage + 2 + simulation.compilerPrefix.length := by
  have hProgramExists : ∃ program ∈ bitstringsUpTo stage,
      conditionalOutputContribution code condition stage
        (Encodable.encode output) program ≠ 0 := by
    by_contra hnone
    have hzero : conditionalOutputNumerator code condition stage
        (Encodable.encode output) = 0 := by
      unfold conditionalOutputNumerator
      apply List.sum_eq_zero
      intro contribution hcontribution
      obtain ⟨program, hprogram, rfl⟩ := List.mem_map.mp hcontribution
      by_contra hContribution
      exact hnone ⟨program, hprogram, hContribution⟩
    omega
  obtain ⟨program, hProgram, hContribution⟩ := hProgramExists
  have hProgramLength : program.length ≤ stage :=
    length_le_of_mem_bitstringsUpTo hProgram
  have hBounded : boundedConditionalOutputAt code condition stage program =
      some output := by
    unfold conditionalOutputContribution at hContribution
    cases hObservation : boundedConditionalOutputAt code condition stage program with
    | none => simp [hObservation] at hContribution
    | some observed =>
        by_cases hEncoded : Encodable.encode observed = Encodable.encode output
        · have hObserved : observed = output :=
            Encodable.encode_injective hEncoded
          exact congrArg some hObserved
        · simp [hObservation, hEncoded] at hContribution
  have hSource : M.compute program condition = some output :=
    source_compute_of_boundedConditionalOutputAt M code hCode hBounded
  obtain ⟨crossingStage, hCrossing⟩ :=
    exists_conditionalOutputApproximation_crossing M code hCode hSource
  have hCoderHas : HasProgram
      (conditionalOutputCodingMachine M code hCode) condition output :=
    discreteDyadicMachine_hasProgram_of_crossed hCrossing
  have hSimulation := simulation.conditionalComplexity_le hCoderHas
  have hCoding := discreteDyadicMachine_complexity_of_crossed hCrossing
  change Kc[conditionalOutputCodingMachine M code hCode](output | condition) ≤
    program.length + 2 at hCoding
  omega

/-! ## Positive and negative controls -/

/-- Positive control: the coding bound applies directly to every witnessed
source computation. -/
example (M : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (hCode : Nat.Partrec.Code.eval code = encodedConditionalCompute M)
    (program condition output : BinString)
    (hCompute : M.compute program condition = some output) :
    Kc[conditionalOutputCodingMachine M code hCode](output | condition) ≤
      program.length + 2 := by
  exact conditionalOutputCodingMachine_complexity_le M code hCode hCompute

/-- Negative control: a code outside the finite stage support receives no
mass, independently of the represented evaluator. -/
example (code : Nat.Partrec.Code) (condition : BinString) :
    conditionalOutputNumerator code condition 0 1 = 0 := by
  exact conditionalOutputNumerator_support code condition 0 1 (by omega)

#print axioms boundedConditionalOutputAt_primrec
#print axioms firstEligibleBoundedConditionalOutputAt_primrec
#print axioms firstEligibleBoundedConditionalOutputAt_stage_unique
#print axioms conditionalOutputNumerator_primrec
#print axioms conditionalOutputNumerator_budget
#print axioms exists_conditionalOutputApproximation_crossing
#print axioms conditionalOutputCodingMachine_effective
#print axioms conditionalOutputCodingMachine_complexity_le
#print axioms conditionalOutputNumerator_concentration
#print axioms conditionalOutputNumerator_positive_complexity_le

end KraftChaitin

end KolmogorovComplexity
