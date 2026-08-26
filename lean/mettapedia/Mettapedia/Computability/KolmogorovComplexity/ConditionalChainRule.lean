import Mettapedia.Computability.KolmogorovComplexity.ConditionalPrefixBridge
import Mettapedia.Computability.KolmogorovComplexity.SelfDelimitingCode

/-!
# Conditional prefix-complexity chain rules

This file separates the constructive upper chain rule from the effective
Kraft--Chaitin lower bound.  The upper rule is realized by a prefix-free
pairing machine that concatenates a shortest head program with a tail program.
It discovers the boundary by the first halting prefix; no length header is
needed, so a uniform simulation contributes only constant overhead.

The lower rule remains a distinct interface.  Combining a proved upper rule
with a lower-rule witness yields the strong two-sided chain rule consumed by
algorithmic-containment arguments.
-/

namespace KolmogorovComplexity

open scoped Classical

/-- Auxiliary condition for the strong conditional chain rule. -/
def chainCondition (condition head : BinString) (complexityIndex : Nat) : BinString :=
  pairCondition head (pairCondition (binaryBits complexityIndex) condition)

abbrev ChainConditionInput := (BinString × BinString) × Nat

theorem chainCondition_primrec : Primrec fun input : ChainConditionInput =>
    chainCondition input.1.1 input.1.2 input.2 := by
  have hInner : Primrec fun input : ChainConditionInput =>
      pairCondition (binaryBits input.2) input.1.1 :=
    pairCondition_primrec.comp
      (binaryBits_primrec.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  exact pairCondition_primrec.comp
    (Primrec.snd.comp Primrec.fst) hInner

private theorem append_eq_append_prefix
    {left right leftRest rightRest : BinString}
    (h : left ++ leftRest = right ++ rightRest) :
    left <+: right ∨ right <+: left := by
  induction left generalizing right with
  | nil =>
      exact Or.inl ⟨right, rfl⟩
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          exact Or.inr ⟨leftHead :: leftTail, rfl⟩
      | cons rightHead rightTail =>
          simp only [List.cons_append] at h
          injection h with headsEqual tailsEqual
          subst rightHead
          rcases ih tailsEqual with leftPrefix | rightPrefix
          · left
            obtain ⟨suffix, suffixEq⟩ := leftPrefix
            exact ⟨suffix, by simp [suffixEq]⟩
          · right
            obtain ⟨suffix, suffixEq⟩ := rightPrefix
            exact ⟨suffix, by simp [suffixEq]⟩

/-- Any two prefixes of one finite string are comparable. -/
theorem prefixes_comparable {left right whole : BinString}
    (hleft : left <+: whole) (hright : right <+: whole) :
    left <+: right ∨ right <+: left := by
  obtain ⟨leftRest, hleftEq⟩ := hleft
  obtain ⟨rightRest, hrightEq⟩ := hright
  exact append_eq_append_prefix (hleftEq.trans hrightEq.symm)

/-- A successful run of the concatenating pair machine. -/
def ChainPairRun (U : ConditionalPrefixFreeMachine)
    (program condition output : BinString) : Prop :=
  ∃ headProgram tailProgram head tail,
    program = headProgram ++ tailProgram ∧
    IsProgram U headProgram condition head ∧
    IsProgram U tailProgram
      (chainCondition condition head headProgram.length) tail ∧
    output = pairCondition head tail

private theorem halting_prefixes_equal
    {U : ConditionalPrefixFreeMachine}
    {condition left right whole leftOutput rightOutput : BinString}
    (hleftPrefix : left <+: whole) (hrightPrefix : right <+: whole)
    (hleft : IsProgram U left condition leftOutput)
    (hright : IsProgram U right condition rightOutput) :
    left = right := by
  rcases prefixes_comparable hleftPrefix hrightPrefix with hlr | hrl
  · by_contra hne
    have hnone := U.prefix_free condition left right hlr hne (by
      unfold IsProgram at hleft
      rw [hleft]
      simp)
    unfold IsProgram at hright
    rw [hright] at hnone
    simp at hnone
  · by_contra hne
    have hnone := U.prefix_free condition right left hrl (Ne.symm hne) (by
      unfold IsProgram at hright
      rw [hright]
      simp)
    unfold IsProgram at hleft
    rw [hleft] at hnone
    simp at hnone

theorem chainPairRun_output_unique
    {U : ConditionalPrefixFreeMachine}
    {program condition leftOutput rightOutput : BinString}
    (leftRun : ChainPairRun U program condition leftOutput)
    (rightRun : ChainPairRun U program condition rightOutput) :
    leftOutput = rightOutput := by
  rcases leftRun with
    ⟨leftHeadProgram, leftTailProgram, leftHead, leftTail,
      leftProgramEq, leftHeadRun, leftTailRun, leftOutputEq⟩
  rcases rightRun with
    ⟨rightHeadProgram, rightTailProgram, rightHead, rightTail,
      rightProgramEq, rightHeadRun, rightTailRun, rightOutputEq⟩
  have leftPrefix : leftHeadProgram <+: program :=
    ⟨leftTailProgram, leftProgramEq.symm⟩
  have rightPrefix : rightHeadProgram <+: program :=
    ⟨rightTailProgram, rightProgramEq.symm⟩
  have headProgramEq : leftHeadProgram = rightHeadProgram :=
    halting_prefixes_equal leftPrefix rightPrefix leftHeadRun rightHeadRun
  subst rightHeadProgram
  unfold IsProgram at leftHeadRun rightHeadRun
  have headEq : leftHead = rightHead :=
    Option.some.inj (leftHeadRun.symm.trans rightHeadRun)
  subst rightHead
  have tailProgramEq : leftTailProgram = rightTailProgram := by
    apply List.append_cancel_left
    exact leftProgramEq.symm.trans rightProgramEq
  subst rightTailProgram
  unfold IsProgram at leftTailRun rightTailRun
  have tailEq : leftTail = rightTail :=
    Option.some.inj (leftTailRun.symm.trans rightTailRun)
  subst rightTail
  exact leftOutputEq.trans rightOutputEq.symm

/-- The partial output selected by the functional run relation. -/
noncomputable def chainPairCompute (U : ConditionalPrefixFreeMachine)
    (program condition : BinString) : Option BinString :=
  if h : ∃ output, ChainPairRun U program condition output then
    some (Classical.choose h)
  else none

theorem chainPairCompute_eq_some_iff
    {U : ConditionalPrefixFreeMachine}
    {program condition output : BinString} :
    chainPairCompute U program condition = some output ↔
      ChainPairRun U program condition output := by
  classical
  unfold chainPairCompute
  split_ifs with h
  · constructor
    · intro heq
      have hout : Classical.choose h = output := Option.some.inj heq
      simpa [hout] using Classical.choose_spec h
    · intro hrun
      have hout := chainPairRun_output_unique (Classical.choose_spec h) hrun
      rw [hout]
  · constructor
    · simp
    · intro hrun
      exact (h ⟨output, hrun⟩).elim

/-- Prefix-free machine implementing the upper conditional chain rule. -/
noncomputable def chainPairMachine (U : ConditionalPrefixFreeMachine) :
    ConditionalPrefixFreeMachine where
  compute := chainPairCompute U
  prefix_free := by
    intro condition program extension programPrefix programNe extensionHalts
    by_contra extensionDoesNotDiverge
    obtain ⟨programOutput, programOutputEq⟩ :=
      Option.ne_none_iff_exists.mp extensionHalts
    obtain ⟨extensionOutput, extensionOutputEq⟩ :=
      Option.ne_none_iff_exists.mp extensionDoesNotDiverge
    have programRun := chainPairCompute_eq_some_iff.mp programOutputEq.symm
    have extensionRun := chainPairCompute_eq_some_iff.mp extensionOutputEq.symm
    rcases programRun with
      ⟨programHeadCode, programTailCode, programHead, programTail,
        programEq, programHeadRun, programTailRun, _programOutput⟩
    rcases extensionRun with
      ⟨extensionHeadCode, extensionTailCode, extensionHead, extensionTail,
        extensionEq, extensionHeadRun, extensionTailRun, _extensionOutput⟩
    have programHeadPrefix : programHeadCode <+: extension := by
      obtain ⟨suffix, suffixEq⟩ := programPrefix
      refine ⟨programTailCode ++ suffix, ?_⟩
      rw [← List.append_assoc, ← programEq, suffixEq]
    have extensionHeadPrefix : extensionHeadCode <+: extension :=
      ⟨extensionTailCode, extensionEq.symm⟩
    have headCodeEq : programHeadCode = extensionHeadCode :=
      halting_prefixes_equal programHeadPrefix extensionHeadPrefix
        programHeadRun extensionHeadRun
    subst extensionHeadCode
    unfold IsProgram at programHeadRun extensionHeadRun
    have headEq : programHead = extensionHead :=
      Option.some.inj (programHeadRun.symm.trans extensionHeadRun)
    subst extensionHead
    obtain ⟨suffix, suffixEq⟩ := programPrefix
    have tailsEq : programTailCode ++ suffix = extensionTailCode := by
      apply List.append_cancel_left
      exact calc
        programHeadCode ++ (programTailCode ++ suffix) =
            (programHeadCode ++ programTailCode) ++ suffix := by
              rw [List.append_assoc]
        _ = program ++ suffix := by rw [← programEq]
        _ = extension := suffixEq
        _ = programHeadCode ++ extensionTailCode := extensionEq
    have tailPrefix : programTailCode <+: extensionTailCode := ⟨suffix, tailsEq⟩
    have tailNe : programTailCode ≠ extensionTailCode := by
      intro tailEq
      apply programNe
      rw [programEq, extensionEq, tailEq]
    have extensionTailNone := U.prefix_free
      (chainCondition condition programHead programHeadCode.length)
      programTailCode extensionTailCode tailPrefix tailNe (by
        unfold IsProgram at programTailRun
        rw [programTailRun]
        simp)
    unfold IsProgram at extensionTailRun
    rw [extensionTailRun] at extensionTailNone
    simp at extensionTailNone

theorem chainPairMachine_program
    {U : ConditionalPrefixFreeMachine}
    {headProgram tailProgram condition head tail : BinString}
    (headRun : IsProgram U headProgram condition head)
    (tailRun : IsProgram U tailProgram
      (chainCondition condition head headProgram.length) tail) :
    IsProgram (chainPairMachine U) (headProgram ++ tailProgram) condition
      (pairCondition head tail) := by
  unfold IsProgram
  apply chainPairCompute_eq_some_iff.mpr
  exact ⟨headProgram, tailProgram, head, tail, rfl, headRun, tailRun, rfl⟩

/-- Constructive upper half of the conditional prefix-complexity chain rule. -/
structure UpperConditionalChainRule (U : ConditionalPrefixFreeMachine) where
  constant : Nat
  pair_hasProgram : ∀ condition head tail,
    HasProgram U condition head →
    HasProgram U
      (chainCondition condition head Kc[U](head | condition)) tail →
    HasProgram U condition (pairCondition head tail)
  upper : ∀ condition head tail,
    HasProgram U condition head →
    HasProgram U
      (chainCondition condition head Kc[U](head | condition)) tail →
    Kc[U](pairCondition head tail | condition) ≤
      Kc[U](head | condition) +
        Kc[U](tail |
          chainCondition condition head Kc[U](head | condition)) + constant

/-- Effective Kraft--Chaitin lower half of the conditional chain rule. -/
structure LowerConditionalChainRule (U : ConditionalPrefixFreeMachine) where
  constant : Nat
  lower : ∀ condition head tail,
    HasProgram U condition head →
    HasProgram U
      (chainCondition condition head Kc[U](head | condition)) tail →
    Kc[U](head | condition) +
        Kc[U](tail |
          chainCondition condition head Kc[U](head | condition)) ≤
      Kc[U](pairCondition head tail | condition) + constant

/-- The two-sided strong chain rule, with all hidden constants exposed. -/
structure StrongConditionalChainRule (U : ConditionalPrefixFreeMachine) where
  constant : Nat
  pair_hasProgram : ∀ condition head tail,
    HasProgram U condition head →
    HasProgram U
      (chainCondition condition head Kc[U](head | condition)) tail →
    HasProgram U condition (pairCondition head tail)
  upper : ∀ condition head tail,
    HasProgram U condition head →
    HasProgram U
      (chainCondition condition head Kc[U](head | condition)) tail →
    Kc[U](pairCondition head tail | condition) ≤
      Kc[U](head | condition) +
        Kc[U](tail |
          chainCondition condition head Kc[U](head | condition)) + constant
  lower : ∀ condition head tail,
    HasProgram U condition head →
    HasProgram U
      (chainCondition condition head Kc[U](head | condition)) tail →
    Kc[U](head | condition) +
        Kc[U](tail |
          chainCondition condition head Kc[U](head | condition)) ≤
      Kc[U](pairCondition head tail | condition) + constant

/-- A uniform simulation of the concatenating machine proves the upper chain
rule with exactly the compiler-prefix length as its constant. -/
noncomputable def UpperConditionalChainRule.ofPairSimulation
    {U : ConditionalPrefixFreeMachine}
    (simulation : UniformlySimulates U (chainPairMachine U)) :
    UpperConditionalChainRule U where
  constant := simulation.compilerPrefix.length
  pair_hasProgram := by
    intro condition head tail headHas tailHas
    obtain ⟨headProgram, headRun, headLength⟩ :=
      exists_program_of_conditionalComplexity U condition head headHas
    obtain ⟨tailProgram, tailRun, _tailLength⟩ :=
      exists_program_of_conditionalComplexity U
        (chainCondition condition head Kc[U](head | condition)) tail tailHas
    have tailRun' : IsProgram U tailProgram
        (chainCondition condition head headProgram.length) tail := by
      simpa [headLength] using tailRun
    exact simulation.hasProgram
      ⟨headProgram ++ tailProgram,
        chainPairMachine_program headRun tailRun'⟩
  upper := by
    intro condition head tail headHas tailHas
    obtain ⟨headProgram, headRun, headLength⟩ :=
      exists_program_of_conditionalComplexity U condition head headHas
    obtain ⟨tailProgram, tailRun, tailLength⟩ :=
      exists_program_of_conditionalComplexity U
        (chainCondition condition head Kc[U](head | condition)) tail tailHas
    have tailRun' : IsProgram U tailProgram
        (chainCondition condition head headProgram.length) tail := by
      simpa [headLength] using tailRun
    have pairRun := simulation.program
      (chainPairMachine_program headRun tailRun')
    have bound := conditionalComplexity_le_program_length U condition
      (pairCondition head tail)
      (simulation.compilerPrefix ++ (headProgram ++ tailProgram)) pairRun
    simp [List.length_append, headLength, tailLength, Nat.add_assoc,
      Nat.add_comm] at bound ⊢
    exact bound

/-- Strong conditional universality discharges the constructive upper chain
rule by uniformly compiling the concatenating pair machine. -/
noncomputable def UpperConditionalChainRule.ofUniformUniversality
    {U : ConditionalPrefixFreeMachine}
    [UniformlyUniversalConditionalPFM U] :
    UpperConditionalChainRule U :=
  UpperConditionalChainRule.ofPairSimulation
    (UniformlyUniversalConditionalPFM.simulates (U := U) (chainPairMachine U))

/-- Once the lower Kraft--Chaitin bound is supplied, the proved upper rule and
lower rule combine using the maximum of their constants. -/
def StrongConditionalChainRule.ofUpperLower
    {U : ConditionalPrefixFreeMachine}
    (upperRule : UpperConditionalChainRule U)
    (lowerRule : LowerConditionalChainRule U) :
    StrongConditionalChainRule U where
  constant := max upperRule.constant lowerRule.constant
  pair_hasProgram := upperRule.pair_hasProgram
  upper := by
    intro condition head tail headHas tailHas
    have h := upperRule.upper condition head tail headHas tailHas
    have hc : upperRule.constant ≤ max upperRule.constant lowerRule.constant :=
      le_max_left _ _
    omega
  lower := by
    intro condition head tail headHas tailHas
    have h := lowerRule.lower condition head tail headHas tailHas
    have hc : lowerRule.constant ≤ max upperRule.constant lowerRule.constant :=
      le_max_right _ _
    omega

#print axioms chainPairMachine_program
#print axioms UpperConditionalChainRule.ofPairSimulation
#print axioms UpperConditionalChainRule.ofUniformUniversality
#print axioms StrongConditionalChainRule.ofUpperLower

end KolmogorovComplexity
