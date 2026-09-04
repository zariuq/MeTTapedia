import Mettapedia.Languages.Metamath.InferenceNormalStepReflection
import Mettapedia.Languages.Metamath.MM2Transformation

open Mettapedia.GSLT.LanguageDef

/-!
# Proof-occurrence stacks at the Metamath-to-MM2 boundary

A completed normal-proof prefix has two synchronized views.  Its native
Metamath certificate retains an ordered forest of source-pinned proof trees;
the compiled MM2 machine retains one stack cell per root, with the root's
postfix proof position as occurrence identity.

This module defines that boundary representation and proves its append laws.
It does not identify a target execution trace with a source proof: later
macro-step theorems must show that actual MM2 execution establishes these
rows and that every established row reflects to the source forest.
-/

namespace Mettapedia.Languages.Metamath.MM2NormalStackCorrespondence

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK

/-- One stable-boundary MM2 stack row with an explicitly represented source
occurrence.  Active hypotheses use a proof position; assertion roots retain
both their proof position and assertion label. -/
@[simp] def normalStackAtomWithOccurrence (proofOwner : Atom)
    (stackPosition : Nat)
    (formula : ConstantHeadedFormula) (occurrence : Atom) : Atom :=
  .expression
    [.symbol "mm-stack-cell", proofOwner, natAtom stackPosition,
      formulaAtom formula, occurrence]

/-- Active-hypothesis stack row.  Its source occurrence is the exact postfix
proof position. -/
@[simp] def normalStackAtom (proofOwner : Atom) (stackPosition : Nat)
    (formula : ConstantHeadedFormula) (occurrence : Nat) : Atom :=
  normalStackAtomWithOccurrence proofOwner stackPosition formula
    (natAtom occurrence)

/-- Target occurrence attached to the root of a retained generated proof
tree.  Assertion labels remain present because the emitted assertion result
rule records them; endpoint formula equality is not enough. -/
@[simp] def generatedRootOccurrenceAtom
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula} (proofOffset : Nat) :
    GeneratedProvesTree projection target formula → Atom
  | .active _ _ => natAtom proofOffset
  | .assertion (assertion := assertion) _ _ children =>
      normalAssertionOccurrenceAtom
        (proofOffset + children.labels.length) assertion.label

/-- Encode the roots of a retained source proof forest as stable MM2 stack
rows.  `stackOffset` locates the first stack cell; `proofOffset` locates the
first authored label.  Every tree is nonempty, so its root is the final label
of its own postfix interval. -/
def mm2StackRows
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formulas : List ConstantHeadedFormula}
    (proofOwner : Atom) (stackOffset proofOffset : Nat) :
    GeneratedProvesForest projection target formulas → List Atom
  | .nil => []
  | .cons (formula := formula) head tail =>
      normalStackAtomWithOccurrence proofOwner stackOffset formula
          (generatedRootOccurrenceAtom proofOffset head) ::
        mm2StackRows proofOwner (stackOffset + 1)
          (proofOffset + head.labels.length) tail

@[simp] theorem mm2StackRows_length
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas)
    (proofOwner : Atom) (stackOffset proofOffset : Nat) :
    (mm2StackRows proofOwner stackOffset proofOffset forest).length =
      formulas.length := by
  cases forest with
  | nil => rfl
  | cons head tail =>
      simp [mm2StackRows, mm2StackRows_length tail]
termination_by sizeOf forest

/-- Stack representation commutes with exact forest append.  Both the stack
and postfix-proof offsets advance by the exact sizes retained on the source
side. -/
theorem mm2StackRows_append
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {leftFormulas rightFormulas : List ConstantHeadedFormula}
    (left : GeneratedProvesForest projection target leftFormulas)
    (right : GeneratedProvesForest projection target rightFormulas)
    (proofOwner : Atom) (stackOffset proofOffset : Nat) :
    mm2StackRows proofOwner stackOffset proofOffset (left.append right) =
      mm2StackRows proofOwner stackOffset proofOffset left ++
        mm2StackRows proofOwner
          (stackOffset + leftFormulas.length)
          (proofOffset + left.labels.length) right := by
  cases left with
  | nil =>
      simp only [GeneratedProvesForest.append,
        mm2StackRows,
        GeneratedProvesForest.labels, List.length_nil, Nat.add_zero,
        List.nil_append]
  | @cons formula formulas head tail =>
      simp only [GeneratedProvesForest.append,
        mm2StackRows,
        GeneratedProvesForest.labels,
        List.length_cons, List.length_append, List.cons_append]
      rw [mm2StackRows_append tail right]
      rw [show stackOffset + 1 + formulas.length =
        stackOffset + (formulas.length + 1) by omega]
      rw [Nat.add_assoc proofOffset head.labels.length tail.labels.length]

/-- Appending one active-hypothesis tree produces exactly the stack cell
emitted by the generic MM2 hypothesis directive. -/
theorem mm2StackRows_append_active
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas)
    (hypothesis : HypothesisView)
    (member : hypothesis ∈ projection.activeHypotheses)
    (proofOwner : Atom) (stackOffset proofOffset : Nat) :
    mm2StackRows proofOwner stackOffset proofOffset
        (forest.append (.cons (.active hypothesis member) .nil)) =
      mm2StackRows proofOwner stackOffset proofOffset forest ++
        [normalHypothesisStackAtom proofOwner
          (stackOffset + formulas.length) hypothesis
          (proofOffset + forest.labels.length)] := by
  rw [mm2StackRows_append]
  simp [mm2StackRows, normalHypothesisStackAtom]

/-- Replacing an assertion's ordered child suffix by its generated root puts
the root at the next stack position and at the exact postfix occurrence after
all child labels.  This is the stable-boundary shape that the MM2 assertion
macro-step must realize. -/
theorem mm2StackRows_append_assertion
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formulas actuals : List ConstantHeadedFormula}
    {assertion : AssertionView} {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (forest : GeneratedProvesForest projection target formulas)
    (member : assertion ∈ projection.assertions)
    (node : GeneratedAssertionNode projection target assertion actuals
      result substitution)
    (children : GeneratedProvesForest projection target actuals)
    (proofOwner : Atom) (stackOffset proofOffset : Nat) :
    mm2StackRows proofOwner stackOffset proofOffset
        (forest.append (.cons (.assertion member node children) .nil)) =
      mm2StackRows proofOwner stackOffset proofOffset forest ++
        [normalAssertionStackAtom proofOwner
          (stackOffset + formulas.length) result.typecode result.body
          (proofOffset + forest.labels.length + children.labels.length)
          assertion.label] := by
  rw [mm2StackRows_append]
  rfl

/-- Occurrence identity is not recoverable from the formula alone: changing
the root proof position changes the target stack row. -/
theorem normalStackAtom_occurrence_injective
    (proofOwner : Atom) (stackPosition : Nat)
    (formula : ConstantHeadedFormula) :
    Function.Injective (normalStackAtom proofOwner stackPosition formula) := by
  intro left right equal
  apply natAtom_injective
  simpa [normalStackAtom] using equal

theorem normalStackAtom_ne_of_occurrence_ne
    (proofOwner : Atom) (stackPosition : Nat)
    (formula : ConstantHeadedFormula) {left right : Nat}
    (different : left ≠ right) :
    normalStackAtom proofOwner stackPosition formula left ≠
      normalStackAtom proofOwner stackPosition formula right := by
  intro equal
  exact different
    (normalStackAtom_occurrence_injective proofOwner stackPosition formula
      equal)

/-! ## One source-owned assertion-hypothesis step -/

/-- An assertion occurrence in the admitted source state is present in the
compiled execution data, and the actual emitted start directive enters that
same assertion.  The compiler cannot substitute a fixed database here: the
indexed assertion is read directly from `source.state`. -/
theorem admittedSourceAssertion_fires_start
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackTop assertionPosition : Nat)
    (inBounds : assertionPosition < source.state.assertions.length) :
    let assertion := source.state.assertions[assertionPosition]
    assertionHeaderRow scopeOwner assertionPosition assertion ∈
        (transformNormalScope source mm2Target scopeOwner).executionRows ∧
      normalAssertionPopAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertion stackTop ∈
        fireReflectiveSourceExecFact
          (normalAssertionStartPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition stackTop assertionPosition assertion)
          normalAssertionStartDirective := by
  dsimp only [transformNormalScope]
  constructor
  · exact assertionHeaderRow_mem_normalExecutionRows scopeOwner source.state
      assertionPosition inBounds
  · exact normalAssertionStartDirective_fires_pop scopeOwner proofOwner
      proofPosition nextProofPosition stackTop assertionPosition
      source.state.assertions[assertionPosition]

/-- The source-owned assertion entry is not merely a direct rule firing: on
the exact MM2 phase boundary it is selected by the ordinary scheduler and
inhabits the target native type generated by OSLF. -/
theorem admittedSourceAssertion_scheduled_start
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackTop assertionPosition : Nat)
    (inBounds : assertionPosition < source.state.assertions.length) :
    let assertion := source.state.assertions[assertionPosition]
    let phase := normalAssertionStartPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition stackTop assertionPosition assertion
    let target := fireReflectiveSourceExecFact phase
      normalAssertionStartDirective
    assertionHeaderRow scopeOwner assertionPosition assertion ∈
        (transformNormalScope source mm2Target scopeOwner).executionRows ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
          (reflectiveSourceExecExactTargetNativeType target).pred ∧
        normalAssertionPopAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertion stackTop ∈ target := by
  dsimp only [transformNormalScope]
  constructor
  · exact assertionHeaderRow_mem_normalExecutionRows scopeOwner source.state
      assertionPosition inBounds
  · exact normalAssertionStartPhase_inhabits_target_native_type scopeOwner
      proofOwner proofPosition nextProofPosition stackTop assertionPosition
      source.state.assertions[assertionPosition]

/-- One administrative pop edge is licensed on both sides: the hypothesis
successor comes from the selected source assertion, while the stack successor
comes from the dynamically supplied proof-index table.  The emitted MM2 rule
then produces exactly the predecessor cursor. -/
theorem admittedSourceAssertion_pop_edge
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition assertionPosition : Nat)
    (assertionInBounds : assertionPosition < source.state.assertions.length)
    (hypothesisPosition : Nat)
    (hypothesisInBounds :
      hypothesisPosition <
        source.state.assertions[assertionPosition].hypotheses.length)
    (stackPosition proofIndexCapacity : Nat)
    (stackInBounds : stackPosition < proofIndexCapacity) :
    let assertion := source.state.assertions[assertionPosition]
    assertionHypothesisSuccessorRow scopeOwner assertion
          hypothesisPosition ∈
        (transformNormalScope source mm2Target scopeOwner).executionRows ∧
      (.expression
          [.symbol "mm-index-successor", proofOwner, natAtom stackPosition,
            natAtom (stackPosition + 1)] : Atom) ∈
        indexSuccessorRows proofOwner proofIndexCapacity ∧
      normalAssertionPopCursorAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertion.label hypothesisPosition stackPosition ∈
        fireReflectiveSourceExecFact
          (normalAssertionPopPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition assertion.label hypothesisPosition
            (hypothesisPosition + 1) stackPosition (stackPosition + 1))
          normalAssertionPopDirective := by
  dsimp only [transformNormalScope]
  constructor
  · exact assertionHypothesisSuccessorRow_mem_normalExecutionRows scopeOwner
      source.state assertionPosition assertionInBounds hypothesisPosition
      hypothesisInBounds
  · constructor
    · apply (mem_indexSuccessorRows_iff proofOwner proofIndexCapacity _).2
      exact ⟨stackPosition, stackInBounds, rfl⟩
    · exact normalAssertionPopDirective_fires_previous scopeOwner proofOwner
        proofPosition nextProofPosition
        source.state.assertions[assertionPosition].label hypothesisPosition
        (hypothesisPosition + 1) stackPosition (stackPosition + 1)

/-- One source-indexed pop edge is an ordinary scheduled MM2 transition and
inhabits its exact OSLF-generated target type. -/
theorem admittedSourceAssertion_scheduled_pop_edge
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition assertionPosition : Nat)
    (assertionInBounds : assertionPosition < source.state.assertions.length)
    (hypothesisPosition : Nat)
    (hypothesisInBounds :
      hypothesisPosition <
        source.state.assertions[assertionPosition].hypotheses.length)
    (stackPosition proofIndexCapacity : Nat)
    (stackInBounds : stackPosition < proofIndexCapacity) :
    let assertion := source.state.assertions[assertionPosition]
    let phase := normalAssertionPopPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition assertion.label hypothesisPosition
      (hypothesisPosition + 1) stackPosition (stackPosition + 1)
    let target := fireReflectiveSourceExecFact phase
      normalAssertionPopDirective
    assertionHypothesisSuccessorRow scopeOwner assertion
          hypothesisPosition ∈
        (transformNormalScope source mm2Target scopeOwner).executionRows ∧
      (.expression
          [.symbol "mm-index-successor", proofOwner, natAtom stackPosition,
            natAtom (stackPosition + 1)] : Atom) ∈
        indexSuccessorRows proofOwner proofIndexCapacity ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
          (reflectiveSourceExecExactTargetNativeType target).pred ∧
        normalAssertionPopCursorAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertion.label hypothesisPosition stackPosition ∈
            target := by
  dsimp only [transformNormalScope]
  constructor
  · exact assertionHypothesisSuccessorRow_mem_normalExecutionRows scopeOwner
      source.state assertionPosition assertionInBounds hypothesisPosition
      hypothesisInBounds
  · constructor
    · apply (mem_indexSuccessorRows_iff proofOwner proofIndexCapacity _).2
      exact ⟨stackPosition, stackInBounds, rfl⟩
    · exact normalAssertionPopPhase_inhabits_target_native_type scopeOwner
        proofOwner proofPosition nextProofPosition
        source.state.assertions[assertionPosition].label hypothesisPosition
        (hypothesisPosition + 1) stackPosition (stackPosition + 1)

/-- At cursor zero, the same admitted assertion header initializes the exact
ordered hypothesis-fold state. -/
theorem admittedSourceAssertion_fires_begin
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase assertionPosition : Nat)
    (inBounds : assertionPosition < source.state.assertions.length) :
    let assertion := source.state.assertions[assertionPosition]
    assertionHeaderRow scopeOwner assertionPosition assertion ∈
        (transformNormalScope source mm2Target scopeOwner).executionRows ∧
      normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertion.label 0 assertion.hypotheses.length
          stackBase stackBase ∈
        fireReflectiveSourceExecFact
          (normalAssertionBeginPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition stackBase assertionPosition assertion)
          normalAssertionBeginDirective := by
  dsimp only [transformNormalScope]
  constructor
  · exact assertionHeaderRow_mem_normalExecutionRows scopeOwner source.state
      assertionPosition inBounds
  · exact normalAssertionBeginDirective_fires_bind scopeOwner proofOwner
      proofPosition nextProofPosition stackBase assertionPosition
      source.state.assertions[assertionPosition]

/-- At cursor zero, the source-owned assertion header licenses the scheduled
MM2 begin step and its exact OSLF-generated target observation. -/
theorem admittedSourceAssertion_scheduled_begin
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase assertionPosition : Nat)
    (inBounds : assertionPosition < source.state.assertions.length) :
    let assertion := source.state.assertions[assertionPosition]
    let phase := normalAssertionBeginPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition stackBase assertionPosition assertion
    let target := fireReflectiveSourceExecFact phase
      normalAssertionBeginDirective
    assertionHeaderRow scopeOwner assertionPosition assertion ∈
        (transformNormalScope source mm2Target scopeOwner).executionRows ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
          (reflectiveSourceExecExactTargetNativeType target).pred ∧
        normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertion.label 0 assertion.hypotheses.length
          stackBase stackBase ∈ target := by
  dsimp only [transformNormalScope]
  constructor
  · exact assertionHeaderRow_mem_normalExecutionRows scopeOwner source.state
      assertionPosition inBounds
  · exact normalAssertionBeginPhase_inhabits_target_native_type scopeOwner
      proofOwner proofPosition nextProofPosition stackBase assertionPosition
      source.state.assertions[assertionPosition]

/-! ## Exact assertion-suffix pop trace -/

/-- The administrative backward walk over an assertion's mandatory-hypothesis
suffix.  Each constructor contains the exact target observation generated by
OSLF from the scheduled MM2 pop step.  The indices state the important
invariant directly: both the hypothesis cursor and stack cursor decrease once
per step, ending at the retained stack base. -/
inductive NormalAssertionPopDirectiveTrace
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String) :
    Nat → Nat → Nat → Prop
  | nil (stackBase : Nat) :
      NormalAssertionPopDirectiveTrace scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel 0 stackBase stackBase
  | succ (previousHypothesis previousStack stackBase : Nat)
      (nativeStep :
        let source := normalAssertionPopPhaseSpace scopeOwner proofOwner
          proofPosition nextProofPosition assertionLabel previousHypothesis
          (previousHypothesis + 1) previousStack (previousStack + 1)
        let target := fireReflectiveSourceExecFact source
          normalAssertionPopDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalAssertionPopCursorAtom scopeOwner proofOwner proofPosition
            nextProofPosition assertionLabel previousHypothesis previousStack ∈
              target)
      (tail : NormalAssertionPopDirectiveTrace scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel previousHypothesis
        previousStack stackBase) :
      NormalAssertionPopDirectiveTrace scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel (previousHypothesis + 1)
        (previousStack + 1) stackBase

/-- Every finite assertion suffix has an exact scheduled pop trace. -/
theorem normalAssertionPopDirectiveTrace_exact
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisCount stackBase : Nat) :
    NormalAssertionPopDirectiveTrace scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel hypothesisCount
      (stackBase + hypothesisCount) stackBase := by
  induction hypothesisCount with
  | zero =>
      exact NormalAssertionPopDirectiveTrace.nil stackBase
  | succ previousHypothesis inductionHypothesis =>
      have nativeStep := normalAssertionPopPhase_inhabits_target_native_type
        scopeOwner proofOwner proofPosition nextProofPosition assertionLabel
        previousHypothesis (previousHypothesis + 1)
        (stackBase + previousHypothesis) (stackBase + previousHypothesis + 1)
      rw [Nat.add_succ]
      exact NormalAssertionPopDirectiveTrace.succ
          (scopeOwner := scopeOwner) (proofOwner := proofOwner)
          (proofPosition := proofPosition)
          (nextProofPosition := nextProofPosition)
          (assertionLabel := assertionLabel)
          previousHypothesis (stackBase + previousHypothesis) stackBase
          nativeStep inductionHypothesis

/-- The source-owned assertion header, the complete finite pop walk, and the
begin transition form one exact entry macro-trace.  Both endpoint steps and
every interior pop step are ordinary MM2 scheduler events classified through
OSLF; no host-side cursor calculation is inserted into the semantics. -/
theorem admittedSourceAssertion_has_entry_trace
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition assertionPosition stackBase : Nat)
    (inBounds : assertionPosition < source.state.assertions.length) :
    let assertion := source.state.assertions[assertionPosition]
    let stackTop := stackBase + assertion.hypotheses.length
    let startPhase := normalAssertionStartPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition stackTop assertionPosition assertion
    let startTarget := fireReflectiveSourceExecFact startPhase
      normalAssertionStartDirective
    let beginPhase := normalAssertionBeginPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition stackBase assertionPosition assertion
    let beginTarget := fireReflectiveSourceExecFact beginPhase
      normalAssertionBeginDirective
    assertionHeaderRow scopeOwner assertionPosition assertion ∈
        (transformNormalScope source mm2Target scopeOwner).executionRows ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveSourceExecGSLT .leaveInert)).satisfies startPhase
          (reflectiveSourceExecExactTargetNativeType startTarget).pred ∧
      normalAssertionPopAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertion stackTop ∈ startTarget ∧
      NormalAssertionPopDirectiveTrace scopeOwner proofOwner proofPosition
          nextProofPosition assertion.label assertion.hypotheses.length
          stackTop stackBase ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveSourceExecGSLT .leaveInert)).satisfies beginPhase
          (reflectiveSourceExecExactTargetNativeType beginTarget).pred ∧
      normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertion.label 0 assertion.hypotheses.length
          stackBase stackBase ∈ beginTarget := by
  dsimp only
  have start := admittedSourceAssertion_scheduled_start source mm2Target
    scopeOwner proofOwner proofPosition nextProofPosition
    (stackBase + source.state.assertions[assertionPosition].hypotheses.length)
    assertionPosition inBounds
  have begin := admittedSourceAssertion_scheduled_begin source mm2Target
    scopeOwner proofOwner proofPosition nextProofPosition stackBase
    assertionPosition inBounds
  exact ⟨start.1, start.2.1, start.2.2,
    normalAssertionPopDirectiveTrace_exact scopeOwner proofOwner
      proofPosition nextProofPosition
      source.state.assertions[assertionPosition].label
      source.state.assertions[assertionPosition].hypotheses.length stackBase,
    begin.2.1, begin.2.2⟩

/-- The independent floating-hypothesis constructor supplies exactly the
precondition used by the emitted MM2 floating directive.  Its source proof
child is present at the same postfix occurrence that the target retains in
the resulting assertion-child edge. -/
theorem HypothesisInstances.floating_fires_mm2
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {hypothesisLabel typecode variableName : String}
    {hypotheses : List HypothesisView}
    {actual : ConstantHeadedFormula}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances
      (.floating hypothesisLabel typecode variableName :: hypotheses)
      (actual :: actuals)
      (⟨variableName, actual⟩ :: substitution))
    (child : GeneratedProvesTree projection target actual)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase proofOffset : Nat) :
    let childOccurrence := proofOffset + child.labels.length - 1
    normalStackAtom proofOwner stackPosition actual childOccurrence ∈
        normalAssertionFloatingPhaseSpace scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel hypothesisPosition
          nextHypothesisPosition hypothesisEnd stackPosition
          nextStackPosition stackBase hypothesisLabel typecode variableName
          actual.body childOccurrence ∧
      let result := fireReflectiveSourceExecFact
        (normalAssertionFloatingPhaseSpace scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel hypothesisPosition
          nextHypothesisPosition hypothesisEnd stackPosition
          nextStackPosition stackBase hypothesisLabel typecode variableName
          actual.body childOccurrence)
        normalAssertionFloatingDirective
      normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
            nextProofPosition assertionLabel nextHypothesisPosition
            hypothesisEnd nextStackPosition stackBase ∈ result ∧
        normalAssertionSubstitutionAtom proofOwner proofPosition variableName
              actual.body ∈ result ∧
          normalAssertionChildAtom proofOwner proofPosition hypothesisPosition
              childOccurrence ∈ result := by
  cases instances with
  | floating typecode_eq tail =>
      rcases actual with ⟨actualTypecode, actualBody⟩
      change actualTypecode = typecode at typecode_eq
      subst typecode
      constructor
      · simp [normalStackAtom, normalAssertionFloatingPhaseSpace,
          normalAssertionFloatingPhaseAtoms, formulaAtom]
      · exact normalAssertionFloatingDirective_fires_evidence scopeOwner
          proofOwner proofPosition nextProofPosition assertionLabel
          hypothesisPosition nextHypothesisPosition hypothesisEnd
          stackPosition nextStackPosition stackBase hypothesisLabel
          actualTypecode
          variableName actualBody
          (proofOffset + child.labels.length - 1)

/-- The independently authored floating-hypothesis constructor licenses an
ordinary scheduled MM2 transition and its exact OSLF-generated target
observation, retaining both substitution and proof-occurrence evidence. -/
theorem HypothesisInstances.floating_inhabits_mm2_target_native_type
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {hypothesisLabel typecode variableName : String}
    {hypotheses : List HypothesisView}
    {actual : ConstantHeadedFormula}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances
      (.floating hypothesisLabel typecode variableName :: hypotheses)
      (actual :: actuals)
      (⟨variableName, actual⟩ :: substitution))
    (child : GeneratedProvesTree projection target actual)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase proofOffset : Nat) :
    let childOccurrence := proofOffset + child.labels.length - 1
    let phase := normalAssertionFloatingPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode variableName actual.body
      childOccurrence
    let result := fireReflectiveSourceExecFact phase
      normalAssertionFloatingDirective
    normalStackAtom proofOwner stackPosition actual childOccurrence ∈ phase ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
          (reflectiveSourceExecExactTargetNativeType result).pred ∧
        normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
              nextProofPosition assertionLabel nextHypothesisPosition
              hypothesisEnd nextStackPosition stackBase ∈ result ∧
          normalAssertionSubstitutionAtom proofOwner proofPosition variableName
                actual.body ∈ result ∧
            normalAssertionChildAtom proofOwner proofPosition
                hypothesisPosition childOccurrence ∈ result := by
  cases instances with
  | floating typecodeEqual tail =>
      rcases actual with ⟨actualTypecode, actualBody⟩
      change actualTypecode = typecode at typecodeEqual
      subst typecode
      constructor
      · simp [normalStackAtom, normalAssertionFloatingPhaseSpace,
          normalAssertionFloatingPhaseAtoms, formulaAtom]
      · exact normalAssertionFloatingPhase_inhabits_target_native_type
          scopeOwner proofOwner proofPosition nextProofPosition assertionLabel
          hypothesisPosition nextHypothesisPosition hypothesisEnd
          stackPosition nextStackPosition stackBase hypothesisLabel
          actualTypecode variableName actualBody
          (proofOffset + child.labels.length - 1)

/-- The independent essential-hypothesis constructor establishes the exact
typecode precondition for the emitted MM2 body-match request.  Discharging
the requested body match is a separate semantic obligation. -/
theorem HypothesisInstances.essential_starts_mm2_match
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {hypothesisLabel : String} {formula actual : ConstantHeadedFormula}
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances
      (.essential hypothesisLabel formula :: hypotheses)
      (actual :: actuals) substitution)
    (child : GeneratedProvesTree projection target actual)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase proofOffset : Nat) :
    let childOccurrence := proofOffset + child.labels.length - 1
    normalStackAtom proofOwner stackPosition actual childOccurrence ∈
        normalAssertionEssentialPhaseSpace scopeOwner proofOwner
          proofPosition nextProofPosition assertionLabel hypothesisPosition
          nextHypothesisPosition hypothesisEnd stackPosition
          nextStackPosition stackBase hypothesisLabel formula.typecode
          formula.body actual.body childOccurrence ∧
      normalAssertionEssentialMatchAtom scopeOwner proofOwner proofPosition
            nextProofPosition assertionLabel nextHypothesisPosition
            hypothesisEnd nextStackPosition stackBase hypothesisPosition
            childOccurrence formula.body actual.body ∈
        fireReflectiveSourceExecFact
          (normalAssertionEssentialPhaseSpace scopeOwner proofOwner
            proofPosition nextProofPosition assertionLabel
            hypothesisPosition nextHypothesisPosition hypothesisEnd
            stackPosition nextStackPosition stackBase hypothesisLabel
            formula.typecode formula.body actual.body childOccurrence)
          normalAssertionEssentialDirective := by
  cases instances with
  | essential typecode_eq tail =>
      rcases formula with ⟨formulaTypecode, formulaBody⟩
      rcases actual with ⟨actualTypecode, actualBody⟩
      change actualTypecode = formulaTypecode at typecode_eq
      subst actualTypecode
      constructor
      · simp [normalStackAtom, normalAssertionEssentialPhaseSpace,
          normalAssertionEssentialPhaseAtoms, formulaAtom]
      · exact normalAssertionEssentialDirective_fires_match scopeOwner
          proofOwner proofPosition nextProofPosition assertionLabel
          hypothesisPosition nextHypothesisPosition hypothesisEnd
          stackPosition nextStackPosition stackBase hypothesisLabel
          formulaTypecode formulaBody actualBody
          (proofOffset + child.labels.length - 1)

/-- The independent essential-hypothesis constructor licenses an ordinary
scheduled MM2 body-match request and its exact OSLF-generated target type. -/
theorem HypothesisInstances.essential_inhabits_mm2_target_native_type
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {hypothesisLabel : String} {formula actual : ConstantHeadedFormula}
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances
      (.essential hypothesisLabel formula :: hypotheses)
      (actual :: actuals) substitution)
    (child : GeneratedProvesTree projection target actual)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase proofOffset : Nat) :
    let childOccurrence := proofOffset + child.labels.length - 1
    let phase := normalAssertionEssentialPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel formula.typecode formula.body actual.body
      childOccurrence
    let result := fireReflectiveSourceExecFact phase
      normalAssertionEssentialDirective
    normalStackAtom proofOwner stackPosition actual childOccurrence ∈ phase ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
          (reflectiveSourceExecExactTargetNativeType result).pred ∧
        normalAssertionEssentialMatchAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel nextHypothesisPosition
          hypothesisEnd nextStackPosition stackBase hypothesisPosition
          childOccurrence formula.body actual.body ∈ result := by
  cases instances with
  | essential typecodeEqual tail =>
      rcases formula with ⟨formulaTypecode, formulaBody⟩
      rcases actual with ⟨actualTypecode, actualBody⟩
      change actualTypecode = formulaTypecode at typecodeEqual
      subst actualTypecode
      constructor
      · simp [normalStackAtom, normalAssertionEssentialPhaseSpace,
          normalAssertionEssentialPhaseAtoms, formulaAtom]
      · exact normalAssertionEssentialPhase_inhabits_target_native_type
          scopeOwner proofOwner proofPosition nextProofPosition assertionLabel
          hypothesisPosition nextHypothesisPosition hypothesisEnd
          stackPosition nextStackPosition stackBase hypothesisLabel
          formulaTypecode formulaBody actualBody
          (proofOffset + child.labels.length - 1)

/-- An essential hypothesis is read from the exact admitted assertion row,
and the actual emitted MM2 directive starts the corresponding substitution
match while retaining the source child occurrence in its continuation. -/
theorem admittedSourceAssertion_essential_fires_match
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (scopeOwner proofOwner : Atom)
    (assertionPosition : Nat)
    (assertionInBounds : assertionPosition < source.state.assertions.length)
    (hypothesisPosition : Nat)
    (hypothesisInBounds :
      hypothesisPosition <
        source.state.assertions[assertionPosition].hypotheses.length)
    (hypothesisLabel : String) (formula actual : ConstantHeadedFormula)
    (sourceHypothesis :
      source.state.assertions[assertionPosition].hypotheses.get
          ⟨hypothesisPosition, hypothesisInBounds⟩ =
        HypothesisView.essential hypothesisLabel formula)
    (typecode_eq : actual.typecode = formula.typecode)
    (child : GeneratedProvesTree projection target actual)
    (proofPosition nextProofPosition stackPosition stackBase
      proofOffset : Nat) :
    let assertion := source.state.assertions[assertionPosition]
    let childOccurrence := proofOffset + child.labels.length - 1
    assertionHypothesisRow scopeOwner assertion hypothesisPosition
          (.essential hypothesisLabel formula) ∈
        (transformNormalScope source mm2Target scopeOwner).executionRows ∧
      normalStackAtom proofOwner stackPosition actual childOccurrence ∈
          normalAssertionEssentialPhaseSpace scopeOwner proofOwner
            proofPosition nextProofPosition assertion.label
            hypothesisPosition (hypothesisPosition + 1)
            assertion.hypotheses.length stackPosition (stackPosition + 1)
            stackBase hypothesisLabel formula.typecode formula.body
            actual.body childOccurrence ∧
        normalAssertionEssentialMatchAtom scopeOwner proofOwner proofPosition
              nextProofPosition assertion.label (hypothesisPosition + 1)
              assertion.hypotheses.length (stackPosition + 1) stackBase
              hypothesisPosition childOccurrence formula.body actual.body ∈
          fireReflectiveSourceExecFact
            (normalAssertionEssentialPhaseSpace scopeOwner proofOwner
              proofPosition nextProofPosition assertion.label
              hypothesisPosition (hypothesisPosition + 1)
              assertion.hypotheses.length stackPosition (stackPosition + 1)
              stackBase hypothesisLabel formula.typecode formula.body
              actual.body childOccurrence)
            normalAssertionEssentialDirective := by
  dsimp only [transformNormalScope]
  rcases formula with ⟨formulaTypecode, formulaBody⟩
  rcases actual with ⟨actualTypecode, actualBody⟩
  change actualTypecode = formulaTypecode at typecode_eq
  subst actualTypecode
  constructor
  · have sourceRow :=
      assertionHypothesisRow_mem_normalExecutionRows scopeOwner source.state
        assertionPosition assertionInBounds hypothesisPosition
        hypothesisInBounds
    have sourceHypothesis' :
        source.state.assertions[assertionPosition].hypotheses[hypothesisPosition] =
          HypothesisView.essential hypothesisLabel
            ⟨formulaTypecode, formulaBody⟩ := by
      simpa only [List.get_eq_getElem] using sourceHypothesis
    rw [sourceHypothesis'] at sourceRow
    exact sourceRow
  · constructor
    · simp [normalStackAtom, normalAssertionEssentialPhaseSpace,
        normalAssertionEssentialPhaseAtoms, formulaAtom]
    · exact normalAssertionEssentialDirective_fires_match scopeOwner
        proofOwner proofPosition nextProofPosition
        source.state.assertions[assertionPosition].label hypothesisPosition
        (hypothesisPosition + 1)
        source.state.assertions[assertionPosition].hypotheses.length
        stackPosition (stackPosition + 1) stackBase hypothesisLabel
        formulaTypecode formulaBody actualBody
        (proofOffset + child.labels.length - 1)

/-! ## Exact body-substitution directive traces -/

/-- The target representation of a finite Metamath substitution.  These rows
are data consumed by one generic MM2 matcher; no binding-specific executable
rule is generated. -/
def normalSubstitutionRows (proofOwner : Atom) (proofPosition : Nat)
    (substitution : FiniteSubstitution) : List Atom :=
  substitution.map fun binding =>
    normalAssertionSubstitutionAtom proofOwner proofPosition
      binding.variableName binding.replacement.body

/-- Row membership is exactly relational substitution membership at the body
observation used by `BodySubstitution`.  Replacement typecodes remain present
in the source binding and are checked by the floating-hypothesis phase. -/
theorem normalAssertionSubstitutionAtom_mem_normalSubstitutionRows_iff
    (proofOwner : Atom) (proofPosition : Nat)
    (substitution : FiniteSubstitution) (variableName : String)
    (body : List Metamath.Verify.Sym) :
    normalAssertionSubstitutionAtom proofOwner proofPosition variableName body ∈
        normalSubstitutionRows proofOwner proofPosition substitution ↔
      ∃ replacement : ConstantHeadedFormula,
        LookupSemantics substitution variableName replacement ∧
          replacement.body = body := by
  constructor
  · intro member
    rw [normalSubstitutionRows, List.mem_map] at member
    rcases member with ⟨binding, bindingMember, encodedEqual⟩
    rcases binding with ⟨bindingVariable, bindingReplacement⟩
    have payloadEqual :
        (bindingVariable, bindingReplacement.body) =
          (variableName, body) :=
      normalAssertionSubstitutionAtom_injective_payload proofOwner
        proofPosition encodedEqual
    have variableEqual := congrArg Prod.fst payloadEqual
    have bodyEqual := congrArg Prod.snd payloadEqual
    change bindingVariable = variableName at variableEqual
    change bindingReplacement.body = body at bodyEqual
    subst variableName
    subst body
    refine ⟨bindingReplacement, ?_, rfl⟩
    simpa [LookupSemantics] using bindingMember
  · rintro ⟨replacement, member, bodyEqual⟩
    rw [normalSubstitutionRows, List.mem_map]
    refine ⟨⟨variableName, replacement⟩, member, ?_⟩
    simp [bodyEqual]

/-- Exact target directive evidence for consuming a replacement prefix.  The
indices record that the actual prefix is identical and that the residual
actual body is retained for the outer source-body match. -/
inductive NormalBodyPrefixDirectiveTrace
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (sourceTail : List Metamath.Verify.Sym) :
    List Metamath.Verify.Sym → List Metamath.Verify.Sym →
      List Metamath.Verify.Sym → Prop
  | nil (actualBody : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyPrefixNilPhaseSpace proofOwner continuation
          proofPosition sourceTail actualBody
        let target := fireReflectiveSourceExecFact source
          normalBodyPrefixNilDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyMatchAtom proofOwner proofPosition sourceTail actualBody
                continuation ∈ target ∧
            normalBodyMatchReloadAtom proofOwner proofPosition ∈ target) :
      NormalBodyPrefixDirectiveTrace proofOwner continuation proofPosition
        sourceTail [] actualBody actualBody
  | cons (symbol : Metamath.Verify.Sym)
      (replacementTail actualTail finalActual : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyPrefixConsPhaseSpace proofOwner continuation
          proofPosition symbol replacementTail actualTail sourceTail
        let target := fireReflectiveSourceExecFact source
          normalBodyPrefixConsDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyPrefixAtom proofOwner proofPosition replacementTail
                actualTail sourceTail continuation ∈ target ∧
            normalBodyMatchReloadAtom proofOwner proofPosition ∈ target)
      (tail : NormalBodyPrefixDirectiveTrace proofOwner continuation
        proofPosition sourceTail replacementTail actualTail finalActual) :
      NormalBodyPrefixDirectiveTrace proofOwner continuation proofPosition
        sourceTail (symbol :: replacementTail) (symbol :: actualTail)
        finalActual

/-- Every ordinary list prefix has an exact directive trace against itself,
leaving the supplied actual tail untouched. -/
theorem normalBodyPrefixDirectiveTrace_append
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (sourceTail replacement actualTail : List Metamath.Verify.Sym) :
    NormalBodyPrefixDirectiveTrace proofOwner continuation proofPosition
      sourceTail replacement (replacement ++ actualTail) actualTail := by
  induction replacement with
  | nil =>
      exact .nil actualTail
        (normalBodyPrefixNilPhase_inhabits_target_native_type proofOwner continuation
          proofPosition sourceTail actualTail)
  | cons symbol replacementTail inductionHypothesis =>
      exact .cons symbol replacementTail (replacementTail ++ actualTail)
        actualTail
        (normalBodyPrefixConsPhase_inhabits_target_native_type proofOwner continuation
          proofPosition symbol replacementTail
          (replacementTail ++ actualTail) sourceTail)
        inductionHypothesis

/-- Proof-relevant correspondence trace between the source
`BodySubstitution` recursion and the actual emitted MM2 matcher directives.
This deliberately records directive firings rather than identifying their
administrative scheduler steps with source semantic steps. -/
inductive NormalBodyMatchDirectiveTrace
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (substitution : FiniteSubstitution) :
    List Metamath.Verify.Sym → List Metamath.Verify.Sym → Prop
  | nil
      (nativeStep :
        let source := normalBodyMatchNilPhaseSpace proofOwner continuation
          proofPosition
        let target := fireReflectiveSourceExecFact source
          normalBodyMatchNilDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          continuation ∈ target ∧
            normalBodyMatchReloadAtom proofOwner proofPosition ∈ target) :
      NormalBodyMatchDirectiveTrace proofOwner continuation proofPosition
        substitution [] []
  | const (name : String)
      (sourceTail actualTail : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyMatchConstPhaseSpace proofOwner continuation
          proofPosition name sourceTail actualTail
        let target := fireReflectiveSourceExecFact source
          normalBodyMatchConstDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyMatchAtom proofOwner proofPosition sourceTail actualTail
                continuation ∈ target ∧
            normalBodyMatchReloadAtom proofOwner proofPosition ∈ target)
      (tail : NormalBodyMatchDirectiveTrace proofOwner continuation
        proofPosition substitution sourceTail actualTail) :
      NormalBodyMatchDirectiveTrace proofOwner continuation proofPosition
        substitution (.const name :: sourceTail) (.const name :: actualTail)
  | var (name : String) (replacementBody sourceTail actualTail :
      List Metamath.Verify.Sym)
      (row : normalAssertionSubstitutionAtom proofOwner proofPosition name
          replacementBody ∈
        normalSubstitutionRows proofOwner proofPosition substitution)
      (nativeStep :
        let source := normalBodyMatchVariablePhaseSpace proofOwner continuation
          proofPosition name replacementBody sourceTail
          (replacementBody ++ actualTail)
        let target := fireReflectiveSourceExecFact source
          normalBodyMatchVariableDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyPrefixAtom proofOwner proofPosition replacementBody
                (replacementBody ++ actualTail) sourceTail continuation ∈
              target ∧
            normalBodyMatchReloadAtom proofOwner proofPosition ∈ target)
      (prefixTrace : NormalBodyPrefixDirectiveTrace proofOwner continuation
        proofPosition sourceTail replacementBody
          (replacementBody ++ actualTail) actualTail)
      (tail : NormalBodyMatchDirectiveTrace proofOwner continuation
        proofPosition substitution sourceTail actualTail) :
      NormalBodyMatchDirectiveTrace proofOwner continuation proofPosition
        substitution (.var name :: sourceTail)
          (replacementBody ++ actualTail)

/-- Source substitution semantics always constructs a trace through the
actual emitted target directives. -/
theorem normalBodyMatchDirectiveTrace_of_bodySubstitution
    (proofOwner continuation : Atom) (proofPosition : Nat)
    {substitution : FiniteSubstitution}
    {source actual : List Metamath.Verify.Sym}
    (semantics : BodySubstitution substitution source actual) :
    NormalBodyMatchDirectiveTrace proofOwner continuation proofPosition
      substitution source actual := by
  induction semantics with
  | nil =>
      exact .nil
        (normalBodyMatchNilPhase_inhabits_target_native_type proofOwner continuation
          proofPosition)
  | const tail inductionHypothesis =>
      exact .const _ _ _
        (normalBodyMatchConstPhase_inhabits_target_native_type proofOwner continuation
          proofPosition _ _ _)
        inductionHypothesis
  | var binding tail inductionHypothesis =>
      exact .var _ _ _ _
        ((normalAssertionSubstitutionAtom_mem_normalSubstitutionRows_iff
          proofOwner proofPosition substitution _ _).2
          ⟨_, binding, rfl⟩)
        (normalBodyMatchVariablePhase_inhabits_target_native_type proofOwner continuation
          proofPosition _ _ _ _)
        (normalBodyPrefixDirectiveTrace_append proofOwner continuation
          proofPosition _ _ _)
        inductionHypothesis

/-- A target directive trace backed by rows from the supplied substitution
cannot invent a body-substitution result. -/
theorem bodySubstitution_of_normalBodyMatchDirectiveTrace
    (proofOwner continuation : Atom) (proofPosition : Nat)
    {substitution : FiniteSubstitution}
    {source actual : List Metamath.Verify.Sym}
    (trace : NormalBodyMatchDirectiveTrace proofOwner continuation
      proofPosition substitution source actual) :
    BodySubstitution substitution source actual := by
  induction trace with
  | nil fires => exact .nil
  | const name sourceTail actualTail fires tail inductionHypothesis =>
      exact .const inductionHypothesis
  | var name replacementBody sourceTail actualTail row starts prefixTrace tail
      inductionHypothesis =>
      obtain ⟨replacement, binding, bodyEqual⟩ :=
        (normalAssertionSubstitutionAtom_mem_normalSubstitutionRows_iff
          proofOwner proofPosition substitution name replacementBody).1 row
      rw [← bodyEqual]
      exact .var binding inductionHypothesis

/-- The compositional target directive trace is equivalent to the authored
Metamath body-substitution judgment. -/
theorem normalBodyMatchDirectiveTrace_iff_bodySubstitution
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (substitution : FiniteSubstitution)
    (source actual : List Metamath.Verify.Sym) :
    NormalBodyMatchDirectiveTrace proofOwner continuation proofPosition
        substitution source actual ↔
      BodySubstitution substitution source actual :=
  ⟨bodySubstitution_of_normalBodyMatchDirectiveTrace proofOwner continuation
      proofPosition,
    normalBodyMatchDirectiveTrace_of_bodySubstitution proofOwner continuation
      proofPosition⟩

/-! ## Exact assertion-result construction trace -/

/-- Directive evidence for copying one substitution body into the reversed
result accumulator.  The final index records the precise accumulator rather
than merely the existence of some later body-build cursor. -/
inductive NormalBodyBuildPrefixDirectiveTrace
    (proofOwner context : Atom) (proofPosition : Nat)
    (sourceTail : List Metamath.Verify.Sym) :
    List Metamath.Verify.Sym → List Metamath.Verify.Sym →
      List Metamath.Verify.Sym → Prop
  | nil (reversedBody : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyBuildPrefixNilPhaseSpace proofOwner context
          proofPosition sourceTail reversedBody
        let target := fireReflectiveSourceExecFact source
          normalBodyBuildPrefixNilDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyBuildAtom proofOwner proofPosition sourceTail reversedBody
                context ∈ target ∧
            normalBodyBuildReloadAtom proofOwner proofPosition ∈ target) :
      NormalBodyBuildPrefixDirectiveTrace proofOwner context proofPosition
        sourceTail [] reversedBody reversedBody
  | cons (symbol : Metamath.Verify.Sym)
      (replacementTail reversedBody finalReversed :
        List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyBuildPrefixConsPhaseSpace proofOwner context
          proofPosition symbol replacementTail sourceTail reversedBody
        let target := fireReflectiveSourceExecFact source
          normalBodyBuildPrefixConsDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyBuildPrefixAtom proofOwner proofPosition replacementTail
                sourceTail (symbol :: reversedBody) context ∈ target ∧
            normalBodyBuildReloadAtom proofOwner proofPosition ∈ target)
      (tail : NormalBodyBuildPrefixDirectiveTrace proofOwner context
        proofPosition sourceTail replacementTail (symbol :: reversedBody)
        finalReversed) :
      NormalBodyBuildPrefixDirectiveTrace proofOwner context proofPosition
        sourceTail (symbol :: replacementTail) reversedBody finalReversed

/-- Every replacement list follows the emitted prefix directives to its exact
reversed accumulator. -/
theorem normalBodyBuildPrefixDirectiveTrace_exact
    (proofOwner context : Atom) (proofPosition : Nat)
    (sourceTail replacement reversedBody : List Metamath.Verify.Sym) :
    NormalBodyBuildPrefixDirectiveTrace proofOwner context proofPosition
      sourceTail replacement reversedBody
        (replacement.reverse ++ reversedBody) := by
  induction replacement generalizing reversedBody with
  | nil =>
      simpa using
        NormalBodyBuildPrefixDirectiveTrace.nil
          (proofOwner := proofOwner) (context := context)
          (proofPosition := proofPosition) (sourceTail := sourceTail)
          reversedBody
          (normalBodyBuildPrefixNilPhase_inhabits_target_native_type
            proofOwner context proofPosition sourceTail reversedBody)
  | cons symbol replacementTail inductionHypothesis =>
      have tail := inductionHypothesis (symbol :: reversedBody)
      have step :=
        normalBodyBuildPrefixConsPhase_inhabits_target_native_type
          proofOwner context proofPosition symbol replacementTail sourceTail
          reversedBody
      simpa [List.reverse_cons, List.append_assoc] using
        NormalBodyBuildPrefixDirectiveTrace.cons
          (proofOwner := proofOwner) (context := context)
          (proofPosition := proofPosition) (sourceTail := sourceTail)
          symbol replacementTail reversedBody
          (replacementTail.reverse ++ symbol :: reversedBody) step tail

/-- A prefix directive trace cannot invent a different accumulator. -/
theorem NormalBodyBuildPrefixDirectiveTrace.finalReversed_eq
    {proofOwner context : Atom} {proofPosition : Nat}
    {sourceTail replacement reversedBody finalReversed :
      List Metamath.Verify.Sym}
    (trace : NormalBodyBuildPrefixDirectiveTrace proofOwner context
      proofPosition sourceTail replacement reversedBody finalReversed) :
    finalReversed = replacement.reverse ++ reversedBody := by
  induction trace with
  | nil _ _ => simp
  | cons symbol replacementTail reversedBody finalReversed _ _ induction =>
      simpa [List.reverse_cons, List.append_assoc] using induction

/-- Directive evidence for reversing the completed accumulator into the
source-order result body. -/
inductive NormalBodyReverseDirectiveTrace
    (proofOwner context : Atom) (proofPosition : Nat) :
    List Metamath.Verify.Sym → List Metamath.Verify.Sym →
      List Metamath.Verify.Sym → Prop
  | nil (resultBody : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyReverseNilPhaseSpace proofOwner context
          proofPosition resultBody
        let target := fireReflectiveSourceExecFact source
          normalBodyReverseNilDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyBuiltAtom proofOwner proofPosition context resultBody ∈
            target) :
      NormalBodyReverseDirectiveTrace proofOwner context proofPosition
        [] resultBody resultBody
  | cons (head : Metamath.Verify.Sym)
      (reversedTail resultBody finalBody : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyReverseConsPhaseSpace proofOwner context
          proofPosition head reversedTail resultBody
        let target := fireReflectiveSourceExecFact source
          normalBodyReverseConsDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyReverseAtom proofOwner proofPosition reversedTail
                (head :: resultBody) context ∈ target ∧
            normalBodyBuildReloadAtom proofOwner proofPosition ∈ target)
      (tail : NormalBodyReverseDirectiveTrace proofOwner context
        proofPosition reversedTail (head :: resultBody) finalBody) :
      NormalBodyReverseDirectiveTrace proofOwner context proofPosition
        (head :: reversedTail) resultBody finalBody

/-- Reversal directives compute the exact list reversal and suffix append. -/
theorem normalBodyReverseDirectiveTrace_exact
    (proofOwner context : Atom) (proofPosition : Nat)
    (reversedTail resultBody : List Metamath.Verify.Sym) :
    NormalBodyReverseDirectiveTrace proofOwner context proofPosition
      reversedTail resultBody (reversedTail.reverse ++ resultBody) := by
  induction reversedTail generalizing resultBody with
  | nil =>
      simpa using
        NormalBodyReverseDirectiveTrace.nil
          (proofOwner := proofOwner) (context := context)
          (proofPosition := proofPosition) resultBody
          (normalBodyReverseNilPhase_inhabits_target_native_type proofOwner
            context proofPosition resultBody)
  | cons head reversedTail inductionHypothesis =>
      have tail := inductionHypothesis (head :: resultBody)
      have step := normalBodyReverseConsPhase_inhabits_target_native_type
        proofOwner context proofPosition head reversedTail resultBody
      simpa [List.reverse_cons, List.append_assoc] using
        NormalBodyReverseDirectiveTrace.cons
          (proofOwner := proofOwner) (context := context)
          (proofPosition := proofPosition) head reversedTail resultBody
          (reversedTail.reverse ++ head :: resultBody) step tail

/-- A reversal directive trace cannot publish any other result body. -/
theorem NormalBodyReverseDirectiveTrace.finalBody_eq
    {proofOwner context : Atom} {proofPosition : Nat}
    {reversedTail resultBody finalBody : List Metamath.Verify.Sym}
    (trace : NormalBodyReverseDirectiveTrace proofOwner context proofPosition
      reversedTail resultBody finalBody) :
    finalBody = reversedTail.reverse ++ resultBody := by
  induction trace with
  | nil _ _ => simp
  | cons head reversedTail resultBody finalBody _ _ induction =>
      simpa [List.reverse_cons, List.append_assoc] using induction

/-- Proof-relevant correspondence between the authored body-substitution
judgment and the actual result-construction directives.  The accumulator is
indexed explicitly so the theorem can be used compositionally inside an
assertion application. -/
inductive NormalBodyBuildDirectiveTrace
    (proofOwner context : Atom) (proofPosition : Nat)
    (substitution : FiniteSubstitution) :
    List Metamath.Verify.Sym → List Metamath.Verify.Sym →
      List Metamath.Verify.Sym → Prop
  | nil (reversedBody finalBody : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyBuildNilPhaseSpace proofOwner context
          proofPosition reversedBody
        let target := fireReflectiveSourceExecFact source
          normalBodyBuildNilDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyReverseAtom proofOwner proofPosition reversedBody []
                context ∈ target ∧
            normalBodyBuildReloadAtom proofOwner proofPosition ∈ target)
      (reverseTrace : NormalBodyReverseDirectiveTrace proofOwner context
        proofPosition reversedBody [] finalBody) :
      NormalBodyBuildDirectiveTrace proofOwner context proofPosition
        substitution [] reversedBody finalBody
  | const (name : String)
      (sourceTail reversedBody finalBody : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyBuildConstPhaseSpace proofOwner context
          proofPosition name sourceTail reversedBody
        let target := fireReflectiveSourceExecFact source
          normalBodyBuildConstDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyBuildAtom proofOwner proofPosition sourceTail
                (.const name :: reversedBody) context ∈ target ∧
            normalBodyBuildReloadAtom proofOwner proofPosition ∈ target)
      (tail : NormalBodyBuildDirectiveTrace proofOwner context proofPosition
        substitution sourceTail (.const name :: reversedBody) finalBody) :
      NormalBodyBuildDirectiveTrace proofOwner context proofPosition
        substitution (.const name :: sourceTail) reversedBody finalBody
  | var (name : String)
      (replacementBody sourceTail reversedBody afterPrefix finalBody :
        List Metamath.Verify.Sym)
      (row : normalAssertionSubstitutionAtom proofOwner proofPosition name
          replacementBody ∈
        normalSubstitutionRows proofOwner proofPosition substitution)
      (nativeStep :
        let source := normalBodyBuildVariablePhaseSpace proofOwner context
          proofPosition name replacementBody sourceTail reversedBody
        let target := fireReflectiveSourceExecFact source
          normalBodyBuildVariableDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyBuildPrefixAtom proofOwner proofPosition replacementBody
                sourceTail reversedBody context ∈ target ∧
            normalBodyBuildReloadAtom proofOwner proofPosition ∈ target)
      (prefixTrace : NormalBodyBuildPrefixDirectiveTrace proofOwner context
        proofPosition sourceTail replacementBody reversedBody afterPrefix)
      (tail : NormalBodyBuildDirectiveTrace proofOwner context proofPosition
        substitution sourceTail afterPrefix finalBody) :
      NormalBodyBuildDirectiveTrace proofOwner context proofPosition
        substitution (.var name :: sourceTail) reversedBody finalBody

/-- The source semantics constructs a trace through the emitted result
builder for every accumulator.  At the ordinary entry accumulator `[]`, the
published body is exactly the semantic substitution result. -/
theorem normalBodyBuildDirectiveTrace_of_bodySubstitution_acc
    (proofOwner context : Atom) (proofPosition : Nat)
    {substitution : FiniteSubstitution}
    {sourceBody resultBody : List Metamath.Verify.Sym}
    (semantics : BodySubstitution substitution sourceBody resultBody)
    (reversedBody : List Metamath.Verify.Sym) :
    NormalBodyBuildDirectiveTrace proofOwner context proofPosition
      substitution sourceBody reversedBody
        (reversedBody.reverse ++ resultBody) := by
  induction semantics generalizing reversedBody with
  | nil =>
      simpa using
        (NormalBodyBuildDirectiveTrace.nil
          (proofOwner := proofOwner) (context := context)
          (proofPosition := proofPosition) (substitution := substitution)
          reversedBody reversedBody.reverse
          (normalBodyBuildNilPhase_inhabits_target_native_type proofOwner
            context proofPosition reversedBody)
          (by
            simpa using
              (normalBodyReverseDirectiveTrace_exact proofOwner context
                proofPosition reversedBody [])))
  | @const name sourceTail resultTail tail inductionHypothesis =>
      have tailTrace := inductionHypothesis (.const name :: reversedBody)
      have step := normalBodyBuildConstPhase_inhabits_target_native_type
        proofOwner context proofPosition name sourceTail reversedBody
      simpa [List.reverse_cons, List.append_assoc] using
        NormalBodyBuildDirectiveTrace.const
          (proofOwner := proofOwner) (context := context)
          (proofPosition := proofPosition) (substitution := substitution)
          name sourceTail reversedBody
          ((.const name :: reversedBody).reverse ++ resultTail)
          step tailTrace
  | @var name replacement sourceTail resultTail binding tail
      inductionHypothesis =>
      let afterPrefix := replacement.body.reverse ++ reversedBody
      have row : normalAssertionSubstitutionAtom proofOwner proofPosition name
            replacement.body ∈
          normalSubstitutionRows proofOwner proofPosition substitution :=
        (normalAssertionSubstitutionAtom_mem_normalSubstitutionRows_iff
          proofOwner proofPosition substitution name replacement.body).2
          ⟨replacement, binding, rfl⟩
      have step := normalBodyBuildVariablePhase_inhabits_target_native_type
        proofOwner context proofPosition name replacement.body sourceTail
        reversedBody
      have prefixTrace : NormalBodyBuildPrefixDirectiveTrace proofOwner
          context proofPosition sourceTail replacement.body reversedBody
          afterPrefix := by
        exact normalBodyBuildPrefixDirectiveTrace_exact proofOwner context
          proofPosition sourceTail replacement.body reversedBody
      have tailTrace := inductionHypothesis afterPrefix
      simpa [afterPrefix, List.reverse_append, List.append_assoc] using
        NormalBodyBuildDirectiveTrace.var
          (proofOwner := proofOwner) (context := context)
          (proofPosition := proofPosition) (substitution := substitution)
          name replacement.body sourceTail reversedBody afterPrefix
          (afterPrefix.reverse ++ resultTail) row step prefixTrace tailTrace

theorem normalBodyBuildDirectiveTrace_of_bodySubstitution
    (proofOwner context : Atom) (proofPosition : Nat)
    {substitution : FiniteSubstitution}
    {sourceBody resultBody : List Metamath.Verify.Sym}
    (semantics : BodySubstitution substitution sourceBody resultBody) :
    NormalBodyBuildDirectiveTrace proofOwner context proofPosition
      substitution sourceBody [] resultBody := by
  simpa using normalBodyBuildDirectiveTrace_of_bodySubstitution_acc
    proofOwner context proofPosition semantics []

/-- A result-builder directive trace backed by the supplied substitution rows
reflects to a unique semantic output relative to its initial accumulator. -/
theorem NormalBodyBuildDirectiveTrace.reflects_bodySubstitution
    {proofOwner context : Atom} {proofPosition : Nat}
    {substitution : FiniteSubstitution}
    {sourceBody reversedBody finalBody : List Metamath.Verify.Sym}
    (trace : NormalBodyBuildDirectiveTrace proofOwner context proofPosition
      substitution sourceBody reversedBody finalBody) :
    ∃ resultBody,
      BodySubstitution substitution sourceBody resultBody ∧
        finalBody = reversedBody.reverse ++ resultBody := by
  induction trace with
  | nil reversedBody finalBody _ reverseTrace =>
      refine ⟨[], .nil, ?_⟩
      simpa using reverseTrace.finalBody_eq
  | const name sourceTail reversedBody finalBody _ _ induction =>
      obtain ⟨resultTail, semantics, finalEqual⟩ := induction
      refine ⟨.const name :: resultTail, .const semantics, ?_⟩
      simpa [List.reverse_cons, List.append_assoc] using finalEqual
  | var name replacementBody sourceTail reversedBody afterPrefix finalBody
      row _ prefixTrace _ induction =>
      obtain ⟨resultTail, tailSemantics, finalEqual⟩ := induction
      obtain ⟨replacement, binding, bodyEqual⟩ :=
        (normalAssertionSubstitutionAtom_mem_normalSubstitutionRows_iff
          proofOwner proofPosition substitution name replacementBody).1 row
      refine ⟨replacement.body ++ resultTail,
        .var binding tailSemantics, ?_⟩
      have prefixEqual := prefixTrace.finalReversed_eq
      calc
        finalBody = afterPrefix.reverse ++ resultTail := finalEqual
        _ = (replacementBody.reverse ++ reversedBody).reverse ++
              resultTail := by rw [prefixEqual]
        _ = reversedBody.reverse ++ (replacementBody ++ resultTail) := by
              simp [List.reverse_append, List.append_assoc]
        _ = reversedBody.reverse ++ (replacement.body ++ resultTail) := by
              rw [bodyEqual]

/-- Exact two-sided correctness of the result builder at its normal empty
accumulator boundary. -/
theorem normalBodyBuildDirectiveTrace_iff_bodySubstitution
    (proofOwner context : Atom) (proofPosition : Nat)
    (substitution : FiniteSubstitution)
    (sourceBody resultBody : List Metamath.Verify.Sym) :
    NormalBodyBuildDirectiveTrace proofOwner context proofPosition
        substitution sourceBody [] resultBody ↔
      BodySubstitution substitution sourceBody resultBody := by
  constructor
  · intro trace
    obtain ⟨reflectedBody, semantics, finalEqual⟩ :=
      trace.reflects_bodySubstitution
    simp at finalEqual
    subst resultBody
    exact semantics
  · exact normalBodyBuildDirectiveTrace_of_bodySubstitution proofOwner
      context proofPosition

/-! ## Source assertion result correspondence -/

/-- A source-owned generated assertion node supplies exactly the semantic
substitution needed by the generic MM2 result builder.  The completed body is
then published by an ordinary scheduled MM2 rule, and that rule's exact target
is classified by the NTT synthesized by OSLF from the target dynamics.

This is deliberately a macro-step boundary: it relates the source result
judgment to the complete target result-building trace without identifying the
target's administrative reversal and reload steps with source proof steps. -/
theorem GeneratedAssertionNode.result_has_complete_mm2_directive_trace
    (projection : PrefixProjection) (target : ValidatedCalculusLanguageDef)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    {assertion : AssertionView}
    (hassertion : assertion ∈ projection.assertions)
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (node : GeneratedAssertionNode projection target assertion actuals
      result substitution)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase nextTop : Nat) :
    let context := normalAssertionResultContextAtom scopeOwner
      nextProofPosition assertion.label result.typecode stackBase nextTop
    let phase := normalAssertionResultCompletePhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition assertion.label result.typecode
      stackBase nextTop result.body
    let phaseTarget := fireReflectiveSourceExecFact phase
      normalAssertionResultCompleteDirective
    Nonempty
        (HypothesisInstances assertion.hypotheses actuals substitution) ∧
      EssentialMatches substitution assertion.hypotheses actuals ∧
        DVOKSemantics substitution projection.callerFrame assertion.frame ∧
        result.typecode = assertion.formula.typecode ∧
        NormalBodyBuildDirectiveTrace proofOwner context proofPosition
          substitution assertion.formula.body [] result.body ∧
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
            (reflectiveSourceExecExactTargetNativeType phaseTarget).pred ∧
        normalControlAtom scopeOwner proofOwner nextProofPosition nextTop ∈
              phaseTarget ∧
          normalAssertionStackAtom proofOwner stackBase result.typecode
                result.body proofPosition assertion.label ∈ phaseTarget ∧
            normalAssertionReloadAtom proofOwner ∈ phaseTarget := by
  dsimp only
  rcases (assertionRuleApplication_iff_instances projection target
      hprojection hassertion).mp node.application with
    ⟨instances, resultTypecode⟩
  rcases (assertionSideEvidence_nonempty_iff_semantics projection target
      hprojection instances).mp ⟨node.sideEvidence⟩ with
    ⟨essentialMatches, dvSemantics, resultSemantics⟩
  refine ⟨⟨instances⟩, essentialMatches, dvSemantics, resultTypecode, ?_, ?_⟩
  · exact normalBodyBuildDirectiveTrace_of_bodySubstitution proofOwner
      (normalAssertionResultContextAtom scopeOwner nextProofPosition
        assertion.label result.typecode stackBase nextTop)
      proofPosition resultSemantics.2
  · exact normalAssertionResultCompletePhase_inhabits_target_native_type
      scopeOwner proofOwner proofPosition nextProofPosition assertion.label
      result.typecode stackBase nextTop result.body

/-! ## Hypothesis steps under the completed substitution -/

/-- A floating-hypothesis step needs only the independently established
typecode equality.  Stating this without tying the step to the residual
`HypothesisInstances` substitution is essential for the ordered fold: earlier
floating bindings remain available when later essential hypotheses are
checked against the completed substitution. -/
theorem floating_has_complete_mm2_directive_step_of_typecode_eq
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {hypothesisLabel typecode variableName : String}
    {actual : ConstantHeadedFormula}
    (typecodeEqual : actual.typecode = typecode)
    (child : GeneratedProvesTree projection target actual)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase proofOffset : Nat) :
    let childOccurrence := proofOffset + child.labels.length - 1
    let phase := normalAssertionFloatingPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode variableName actual.body
      childOccurrence
    let phaseTarget := fireReflectiveSourceExecFact phase
      normalAssertionFloatingDirective
    normalStackAtom proofOwner stackPosition actual childOccurrence ∈ phase ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
          (reflectiveSourceExecExactTargetNativeType phaseTarget).pred ∧
        normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
              nextProofPosition assertionLabel nextHypothesisPosition
              hypothesisEnd nextStackPosition stackBase ∈ phaseTarget ∧
          normalAssertionSubstitutionAtom proofOwner proofPosition
                variableName actual.body ∈ phaseTarget ∧
            normalAssertionChildAtom proofOwner proofPosition
                hypothesisPosition childOccurrence ∈ phaseTarget := by
  rcases actual with ⟨actualTypecode, actualBody⟩
  change actualTypecode = typecode at typecodeEqual
  subst typecode
  constructor
  · simp [normalStackAtom, normalAssertionFloatingPhaseSpace,
      normalAssertionFloatingPhaseAtoms, formulaAtom]
  · exact normalAssertionFloatingPhase_inhabits_target_native_type
      scopeOwner proofOwner proofPosition nextProofPosition assertionLabel
      hypothesisPosition nextHypothesisPosition hypothesisEnd stackPosition
      nextStackPosition stackBase hypothesisLabel actualTypecode variableName
      actualBody (proofOffset + child.labels.length - 1)

/-- An essential-hypothesis step is checked against the completed
substitution, independently of how the residual `HypothesisInstances` tail
represents only later floating bindings.  This is the compositional form used
by the ordered mandatory-hypothesis fold. -/
theorem essential_has_complete_mm2_directive_trace_of_semantics
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {hypothesisLabel : String} {formula actual : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (typecodeEqual : actual.typecode = formula.typecode)
    (matchSemantics : FormulaSubstitutionSemantics substitution formula actual)
    (child : GeneratedProvesTree projection target actual)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase proofOffset : Nat) :
    let childOccurrence := proofOffset + child.labels.length - 1
    let continuation := normalAssertionEssentialContinuationAtom scopeOwner
      proofOwner proofPosition nextProofPosition assertionLabel
      nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence
    let startPhase := normalAssertionEssentialPhaseSpace scopeOwner proofOwner
          proofPosition nextProofPosition assertionLabel hypothesisPosition
          nextHypothesisPosition hypothesisEnd stackPosition
          nextStackPosition stackBase hypothesisLabel formula.typecode
          formula.body actual.body childOccurrence
    let startTarget := fireReflectiveSourceExecFact startPhase
      normalAssertionEssentialDirective
    normalStackAtom proofOwner stackPosition actual childOccurrence ∈
        startPhase ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveSourceExecGSLT .leaveInert)).satisfies startPhase
          (reflectiveSourceExecExactTargetNativeType startTarget).pred ∧
      normalAssertionEssentialMatchAtom scopeOwner proofOwner proofPosition
            nextProofPosition assertionLabel nextHypothesisPosition
            hypothesisEnd nextStackPosition stackBase hypothesisPosition
            childOccurrence formula.body actual.body ∈ startTarget ∧
      NormalBodyMatchDirectiveTrace proofOwner continuation proofPosition
          substitution formula.body actual.body ∧
        let completePhase := normalAssertionEssentialCompletePhaseSpace
          scopeOwner proofOwner proofPosition nextProofPosition assertionLabel
          nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
          hypothesisPosition childOccurrence
        let completeTarget := fireReflectiveSourceExecFact completePhase
          normalAssertionEssentialCompleteDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies completePhase
            (reflectiveSourceExecExactTargetNativeType completeTarget).pred ∧
          normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
              nextProofPosition assertionLabel nextHypothesisPosition
              hypothesisEnd nextStackPosition stackBase ∈ completeTarget ∧
          normalAssertionChildAtom proofOwner proofPosition hypothesisPosition
                childOccurrence ∈ completeTarget ∧
            normalAssertionReloadAtom proofOwner ∈ completeTarget := by
  rcases formula with ⟨formulaTypecode, formulaBody⟩
  rcases actual with ⟨actualTypecode, actualBody⟩
  change actualTypecode = formulaTypecode at typecodeEqual
  subst actualTypecode
  dsimp only
  have start := normalAssertionEssentialPhase_inhabits_target_native_type
    scopeOwner proofOwner proofPosition nextProofPosition assertionLabel
    hypothesisPosition nextHypothesisPosition hypothesisEnd stackPosition
    nextStackPosition stackBase hypothesisLabel formulaTypecode formulaBody
    actualBody (proofOffset + child.labels.length - 1)
  refine ⟨?_, start.1, start.2, ?_, ?_⟩
  · simp [normalStackAtom, normalAssertionEssentialPhaseSpace,
      normalAssertionEssentialPhaseAtoms, formulaAtom]
  · exact normalBodyMatchDirectiveTrace_of_bodySubstitution proofOwner
      (normalAssertionEssentialContinuationAtom scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel
        nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
        hypothesisPosition (proofOffset + child.labels.length - 1))
      proofPosition matchSemantics.2
  · exact normalAssertionEssentialCompletePhase_inhabits_target_native_type
      scopeOwner proofOwner proofPosition nextProofPosition assertionLabel
      nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition (proofOffset + child.labels.length - 1)

/-- One target floating-hypothesis macro-step, stated independently of the
source proof that licenses it. -/
def NormalFloatingHypothesisDirectiveStep
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {actual : ConstantHeadedFormula}
    (child : GeneratedProvesTree projection target actual)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase proofOffset : Nat)
    (hypothesisLabel typecode variableName : String) : Prop :=
  let childOccurrence := proofOffset + child.labels.length - 1
  let phase := normalAssertionFloatingPhaseSpace scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel hypothesisPosition
    nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
    stackBase hypothesisLabel typecode variableName actual.body
    childOccurrence
  let phaseTarget := fireReflectiveSourceExecFact phase
    normalAssertionFloatingDirective
  normalStackAtom proofOwner stackPosition actual childOccurrence ∈ phase ∧
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
        (reflectiveSourceExecExactTargetNativeType phaseTarget).pred ∧
      normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
            nextProofPosition assertionLabel nextHypothesisPosition
            hypothesisEnd nextStackPosition stackBase ∈ phaseTarget ∧
        normalAssertionSubstitutionAtom proofOwner proofPosition variableName
              actual.body ∈ phaseTarget ∧
          normalAssertionChildAtom proofOwner proofPosition hypothesisPosition
              childOccurrence ∈ phaseTarget

theorem normalFloatingHypothesisDirectiveStep_of_typecode_eq
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {hypothesisLabel typecode variableName : String}
    {actual : ConstantHeadedFormula}
    (typecodeEqual : actual.typecode = typecode)
    (child : GeneratedProvesTree projection target actual)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase proofOffset : Nat) :
    NormalFloatingHypothesisDirectiveStep child scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase proofOffset hypothesisLabel typecode variableName := by
  simpa only [NormalFloatingHypothesisDirectiveStep] using
    floating_has_complete_mm2_directive_step_of_typecode_eq typecodeEqual child
      scopeOwner proofOwner proofPosition nextProofPosition assertionLabel
      hypothesisPosition nextHypothesisPosition hypothesisEnd stackPosition
      nextStackPosition stackBase proofOffset

/-- One target essential-hypothesis macro-step under the completed source
substitution. -/
def NormalEssentialHypothesisDirectiveStep
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formula actual : ConstantHeadedFormula}
    (substitution : FiniteSubstitution)
    (child : GeneratedProvesTree projection target actual)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase proofOffset : Nat)
    (hypothesisLabel : String) : Prop :=
  let childOccurrence := proofOffset + child.labels.length - 1
  let continuation := normalAssertionEssentialContinuationAtom scopeOwner
    proofOwner proofPosition nextProofPosition assertionLabel
    nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
    hypothesisPosition childOccurrence
  let startPhase := normalAssertionEssentialPhaseSpace scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel hypothesisPosition
        nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
        stackBase hypothesisLabel formula.typecode formula.body actual.body
        childOccurrence
  let startTarget := fireReflectiveSourceExecFact startPhase
    normalAssertionEssentialDirective
  normalStackAtom proofOwner stackPosition actual childOccurrence ∈ startPhase ∧
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies startPhase
        (reflectiveSourceExecExactTargetNativeType startTarget).pred ∧
    normalAssertionEssentialMatchAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel nextHypothesisPosition hypothesisEnd
          nextStackPosition stackBase hypothesisPosition childOccurrence
          formula.body actual.body ∈ startTarget ∧
    NormalBodyMatchDirectiveTrace proofOwner continuation proofPosition
        substitution formula.body actual.body ∧
      let completePhase := normalAssertionEssentialCompletePhaseSpace
        scopeOwner proofOwner proofPosition nextProofPosition assertionLabel
        nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
        hypothesisPosition childOccurrence
      let completeTarget := fireReflectiveSourceExecFact completePhase
        normalAssertionEssentialCompleteDirective
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveSourceExecGSLT .leaveInert)).satisfies completePhase
          (reflectiveSourceExecExactTargetNativeType completeTarget).pred ∧
        normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
            nextProofPosition assertionLabel nextHypothesisPosition
            hypothesisEnd nextStackPosition stackBase ∈ completeTarget ∧
        normalAssertionChildAtom proofOwner proofPosition hypothesisPosition
              childOccurrence ∈ completeTarget ∧
          normalAssertionReloadAtom proofOwner ∈ completeTarget

theorem normalEssentialHypothesisDirectiveStep_of_semantics
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {hypothesisLabel : String} {formula actual : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (typecodeEqual : actual.typecode = formula.typecode)
    (matchSemantics : FormulaSubstitutionSemantics substitution formula actual)
    (child : GeneratedProvesTree projection target actual)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase proofOffset : Nat) :
    NormalEssentialHypothesisDirectiveStep (formula := formula) substitution
      child scopeOwner
      proofOwner proofPosition nextProofPosition assertionLabel
      hypothesisPosition nextHypothesisPosition hypothesisEnd stackPosition
      nextStackPosition stackBase proofOffset hypothesisLabel := by
  simpa only [NormalEssentialHypothesisDirectiveStep] using
    essential_has_complete_mm2_directive_trace_of_semantics typecodeEqual
      matchSemantics child scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase proofOffset

/-- Ordered mandatory-hypothesis execution against one completed
substitution.  Every floating binding is required to occur in that completed
substitution; every essential hypothesis is checked against the same fixed
substitution.  Thus recursion over the source constructor never drops an
earlier binding that a later essential hypothesis may need. -/
inductive NormalHypothesisDirectiveTrace
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisEnd stackBase : Nat)
    (completeSubstitution : FiniteSubstitution) :
    (hypotheses : List HypothesisView) →
      (actuals : List ConstantHeadedFormula) →
      FiniteSubstitution →
      GeneratedProvesForest projection target actuals →
      Nat → Nat → Nat → Prop where
  | nil (stackPosition proofOffset : Nat) :
      NormalHypothesisDirectiveTrace scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisEnd stackBase
        completeSubstitution [] [] [] .nil hypothesisEnd
        stackPosition proofOffset
  | floating {label typecode variableName : String}
      {actual : ConstantHeadedFormula}
      {hypotheses : List HypothesisView}
      {actuals : List ConstantHeadedFormula}
      {residualSubstitution : FiniteSubstitution}
      (typecodeEqual : actual.typecode = typecode)
      (child : GeneratedProvesTree projection target actual)
      (childTail : GeneratedProvesForest projection target actuals)
      (hypothesisPosition stackPosition proofOffset : Nat)
      (bindingRow :
        normalAssertionSubstitutionAtom proofOwner proofPosition variableName
            actual.body ∈
          normalSubstitutionRows proofOwner proofPosition completeSubstitution)
      (nativeStep :
        NormalFloatingHypothesisDirectiveStep child scopeOwner proofOwner
          proofPosition nextProofPosition assertionLabel hypothesisPosition
          (hypothesisPosition + 1) hypothesisEnd stackPosition
          (stackPosition + 1) stackBase proofOffset label typecode variableName)
      (tail : NormalHypothesisDirectiveTrace scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel hypothesisEnd stackBase
        completeSubstitution hypotheses actuals residualSubstitution childTail
        (hypothesisPosition + 1) (stackPosition + 1)
        (proofOffset + child.labels.length)) :
      NormalHypothesisDirectiveTrace scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisEnd stackBase
        completeSubstitution
        (.floating label typecode variableName :: hypotheses)
        (actual :: actuals)
        ({ variableName, replacement := actual } :: residualSubstitution)
        (.cons child childTail) hypothesisPosition stackPosition proofOffset
  | essential {label : String} {formula actual : ConstantHeadedFormula}
      {hypotheses : List HypothesisView}
      {actuals : List ConstantHeadedFormula}
      {residualSubstitution : FiniteSubstitution}
      (typecodeEqual : actual.typecode = formula.typecode)
      (matchSemantics :
        FormulaSubstitutionSemantics completeSubstitution formula actual)
      (child : GeneratedProvesTree projection target actual)
      (childTail : GeneratedProvesForest projection target actuals)
      (hypothesisPosition stackPosition proofOffset : Nat)
      (nativeStep :
        NormalEssentialHypothesisDirectiveStep
          (formula := formula) completeSubstitution child scopeOwner proofOwner
          proofPosition nextProofPosition assertionLabel hypothesisPosition
          (hypothesisPosition + 1) hypothesisEnd stackPosition
          (stackPosition + 1) stackBase proofOffset label)
      (tail : NormalHypothesisDirectiveTrace scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel hypothesisEnd stackBase
        completeSubstitution hypotheses actuals residualSubstitution childTail
        (hypothesisPosition + 1) (stackPosition + 1)
        (proofOffset + child.labels.length)) :
      NormalHypothesisDirectiveTrace scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisEnd stackBase
        completeSubstitution (.essential label formula :: hypotheses)
        (actual :: actuals) residualSubstitution (.cons child childTail)
        hypothesisPosition stackPosition proofOffset

private theorem normalHypothesisDirectiveTrace_of_semantics_aux
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisEnd stackBase : Nat)
    (completeSubstitution : FiniteSubstitution)
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {residualSubstitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals residualSubstitution)
    (essentialChecks : EssentialMatches completeSubstitution hypotheses actuals)
    (children : GeneratedProvesForest projection target actuals)
    (residualSubset : ∀ binding, binding ∈ residualSubstitution →
      binding ∈ completeSubstitution)
    (hypothesisPosition stackPosition proofOffset : Nat)
    (positionEnd : hypothesisPosition + hypotheses.length = hypothesisEnd) :
    NormalHypothesisDirectiveTrace scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel hypothesisEnd stackBase
      completeSubstitution hypotheses actuals residualSubstitution children
      hypothesisPosition stackPosition proofOffset := by
  induction instances generalizing hypothesisPosition stackPosition
      proofOffset with
  | nil =>
      cases children
      simp at positionEnd
      subst hypothesisPosition
      exact NormalHypothesisDirectiveTrace.nil stackPosition proofOffset
  | @floating label typecode variableName actual hypotheses actuals
      residualSubstitution typecodeEqual tail inductionHypothesis =>
      cases children with
      | cons child childTail =>
          have bindingMember :
              ({ variableName, replacement := actual } : FormulaBinding) ∈
                completeSubstitution :=
            residualSubset { variableName, replacement := actual } (by simp)
          have bindingRow :
              normalAssertionSubstitutionAtom proofOwner proofPosition
                    variableName actual.body ∈
                normalSubstitutionRows proofOwner proofPosition
                  completeSubstitution :=
            (normalAssertionSubstitutionAtom_mem_normalSubstitutionRows_iff
              proofOwner proofPosition completeSubstitution variableName
              actual.body).2
              ⟨actual, by simpa [LookupSemantics] using bindingMember, rfl⟩
          have tailSubset : ∀ binding, binding ∈ residualSubstitution →
              binding ∈ completeSubstitution := by
            intro binding member
            exact residualSubset binding (by simp [member])
          have tailEnd :
              hypothesisPosition + 1 + hypotheses.length = hypothesisEnd := by
            simp only [List.length_cons] at positionEnd
            omega
          exact NormalHypothesisDirectiveTrace.floating typecodeEqual child
            childTail hypothesisPosition stackPosition proofOffset bindingRow
            (normalFloatingHypothesisDirectiveStep_of_typecode_eq
              typecodeEqual child scopeOwner proofOwner proofPosition
              nextProofPosition assertionLabel hypothesisPosition
              (hypothesisPosition + 1) hypothesisEnd stackPosition
              (stackPosition + 1) stackBase proofOffset)
            (inductionHypothesis essentialChecks childTail tailSubset
              (hypothesisPosition + 1) (stackPosition + 1)
              (proofOffset + child.labels.length) tailEnd)
  | @essential label formula actual hypotheses actuals residualSubstitution
      typecodeEqual tail inductionHypothesis =>
      cases children with
      | cons child childTail =>
          have tailEnd :
              hypothesisPosition + 1 + hypotheses.length = hypothesisEnd := by
            simp only [List.length_cons] at positionEnd
            omega
          exact NormalHypothesisDirectiveTrace.essential typecodeEqual
            essentialChecks.1 child childTail hypothesisPosition stackPosition
            proofOffset
            (normalEssentialHypothesisDirectiveStep_of_semantics
              typecodeEqual essentialChecks.1 child scopeOwner proofOwner
              proofPosition nextProofPosition assertionLabel
              hypothesisPosition (hypothesisPosition + 1) hypothesisEnd
              stackPosition (stackPosition + 1) stackBase proofOffset)
            (inductionHypothesis essentialChecks.2 childTail residualSubset
              (hypothesisPosition + 1) (stackPosition + 1)
              (proofOffset + child.labels.length) tailEnd)

/-- Independent mandatory-hypothesis semantics construct the complete ordered
MM2 directive trace, with every target step classified by OSLF-derived NTT
evidence and every child proof occurrence retained. -/
theorem normalHypothesisDirectiveTrace_of_semantics
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (stackBase : Nat)
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    (substitution : FiniteSubstitution)
    (instances : HypothesisInstances hypotheses actuals substitution)
    (essentialChecks : EssentialMatches substitution hypotheses actuals)
    (children : GeneratedProvesForest projection target actuals)
    (hypothesisPosition stackPosition proofOffset : Nat) :
    NormalHypothesisDirectiveTrace scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel
      (hypothesisPosition + hypotheses.length) stackBase substitution
      hypotheses actuals substitution children hypothesisPosition
      stackPosition proofOffset := by
  exact normalHypothesisDirectiveTrace_of_semantics_aux scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel
    (hypothesisPosition + hypotheses.length) stackBase
    substitution instances essentialChecks children (fun _ member => member)
    hypothesisPosition stackPosition proofOffset rfl

/-- An ordered target trace cannot invent mandatory-hypothesis success.  It
recovers both the exact residual floating substitution and every essential
hypothesis check against the fixed completed substitution. -/
theorem NormalHypothesisDirectiveTrace.reflects_semantics
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {scopeOwner proofOwner : Atom}
    {proofPosition nextProofPosition : Nat} {assertionLabel : String}
    {hypothesisEnd stackBase : Nat}
    {completeSubstitution : FiniteSubstitution}
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {residualSubstitution : FiniteSubstitution}
    {children : GeneratedProvesForest projection target actuals}
    {hypothesisPosition stackPosition proofOffset : Nat}
    (trace : NormalHypothesisDirectiveTrace scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisEnd stackBase
      completeSubstitution hypotheses actuals residualSubstitution children
      hypothesisPosition stackPosition proofOffset) :
    HypothesisInstances hypotheses actuals residualSubstitution ∧
      EssentialMatches completeSubstitution hypotheses actuals := by
  induction trace with
  | nil =>
      exact ⟨HypothesisInstances.nil, trivial⟩
  | floating typecodeEqual child childTail hypothesisPosition stackPosition
      proofOffset bindingRow nativeStep tail inductionHypothesis =>
      exact ⟨HypothesisInstances.floating typecodeEqual
          inductionHypothesis.1,
        inductionHypothesis.2⟩
  | essential typecodeEqual matchSemantics child childTail
      hypothesisPosition stackPosition proofOffset nativeStep tail
      inductionHypothesis =>
      exact ⟨HypothesisInstances.essential typecodeEqual
          inductionHypothesis.1,
        matchSemantics, inductionHypothesis.2⟩

/-- At the exact ordered boundary, the scheduled MM2 hypothesis trace exists
if and only if the independently authored Metamath hypothesis judgments hold.
The forward direction is the no-invention half; the backward direction
constructs every target step with its OSLF-derived native-type evidence. -/
theorem normalHypothesisDirectiveTrace_iff_semantics
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (stackBase : Nat)
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    (substitution : FiniteSubstitution)
    (children : GeneratedProvesForest projection target actuals)
    (hypothesisPosition stackPosition proofOffset : Nat) :
    NormalHypothesisDirectiveTrace scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel
        (hypothesisPosition + hypotheses.length) stackBase substitution
        hypotheses actuals substitution children hypothesisPosition
        stackPosition proofOffset ↔
      HypothesisInstances hypotheses actuals substitution ∧
        EssentialMatches substitution hypotheses actuals := by
  constructor
  · intro trace
    exact trace.reflects_semantics
  · rintro ⟨instances, essentialChecks⟩
    exact normalHypothesisDirectiveTrace_of_semantics scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel stackBase substitution
      instances essentialChecks children hypothesisPosition stackPosition
      proofOffset

/-- The hypothesis portion of an exact source-owned assertion node traverses
the generic scheduled MM2 hypothesis machine.  The theorem consumes the real
generated rule application and side-condition derivations; it does not assume
a separately supplied or pre-approved substitution. -/
theorem GeneratedAssertionNode.hypotheses_have_complete_mm2_directive_trace
    (projection : PrefixProjection) (target : ValidatedCalculusLanguageDef)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    {assertion : AssertionView}
    (hassertion : assertion ∈ projection.assertions)
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (node : GeneratedAssertionNode projection target assertion actuals
      result substitution)
    (children : GeneratedProvesForest projection target actuals)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase : Nat)
    (hypothesisPosition stackPosition proofOffset : Nat) :
    NormalHypothesisDirectiveTrace scopeOwner proofOwner proofPosition
      nextProofPosition assertion.label
      (hypothesisPosition + assertion.hypotheses.length) stackBase
      substitution assertion.hypotheses actuals substitution children
      hypothesisPosition stackPosition proofOffset := by
  rcases (assertionRuleApplication_iff_instances projection target
      hprojection hassertion).mp node.application with
    ⟨instances, _resultTypecode⟩
  rcases (assertionSideEvidence_nonempty_iff_semantics projection target
      hprojection instances).mp ⟨node.sideEvidence⟩ with
    ⟨essentialMatches, _dvSemantics, _resultSemantics⟩
  exact normalHypothesisDirectiveTrace_of_semantics scopeOwner proofOwner
    proofPosition nextProofPosition assertion.label stackBase substitution
    instances essentialMatches children hypothesisPosition stackPosition
    proofOffset

/-! ## Ordered disjoint-variable directive traces -/

/-- The persistent DV-rule reload is itself a scheduled target event and is
classified by the NTT synthesized from the supplied MM2 operational GSLT. -/
def NormalDVReloadDirectiveStep (proofOwner : Atom)
    (proofPosition : Nat) : Prop :=
  let source := normalDVReloadPhaseSpace proofOwner proofPosition
  let target := fireReflectiveSourceExecFact source normalDVReloadDirective
  (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred

def NormalDVRightConstDirectiveStep
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable constantName : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVRightConstPhaseSpace scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd leftVariable
    constantName leftTail rightTail rightBody sourceBody context
  let target := fireReflectiveSourceExecFact source
    normalDVRightConstDirective
  (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd leftVariable leftTail rightTail rightBody
          sourceBody context ∈ target ∧
      normalDVReloadAtom proofOwner proofPosition ∈ target

def NormalDVRightVariableDirectiveStep
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVRightVariablePhaseSpace scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd leftVariable
    rightVariable leftTail rightTail rightBody sourceBody context
  let target := fireReflectiveSourceExecFact source
    normalDVRightVariableDirective
  (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd leftVariable leftTail rightTail rightBody
          sourceBody context ∈ target ∧
      normalDVReloadAtom proofOwner proofPosition ∈ target

def NormalDVRightNilDirectiveStep
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVRightNilPhaseSpace scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd leftVariable
    leftTail rightBody sourceBody context
  let target := fireReflectiveSourceExecFact source normalDVRightNilDirective
  (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd leftTail rightBody sourceBody context ∈
        target ∧
      normalDVReloadAtom proofOwner proofPosition ∈ target

/-- Exact scheduled traversal of one right replacement body for a fixed left
variable occurrence.  Constants are administrative skips; every variable
constructor requires membership in the source-derived caller-DV table before
the target step can be included in the trace. -/
inductive NormalDVRightDirectiveTrace
    (callerDV : List (String × String))
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : List Metamath.Verify.Sym → Prop where
  | nil
      (nativeStep : NormalDVRightNilDirectiveStep scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd leftVariable
        leftTail rightBody sourceBody context)
      (reloadStep : NormalDVReloadDirectiveStep proofOwner proofPosition) :
      NormalDVRightDirectiveTrace callerDV scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd leftVariable
        leftTail rightBody sourceBody context []
  | const (constantName : String) (rightTail : List Metamath.Verify.Sym)
      (nativeStep : NormalDVRightConstDirectiveStep scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd leftVariable
        constantName leftTail rightTail rightBody sourceBody context)
      (reloadStep : NormalDVReloadDirectiveStep proofOwner proofPosition)
      (tail : NormalDVRightDirectiveTrace callerDV scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd leftVariable
        leftTail rightBody sourceBody context rightTail) :
      NormalDVRightDirectiveTrace callerDV scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd leftVariable
        leftTail rightBody sourceBody context (.const constantName :: rightTail)
  | var (rightVariable : String)
      (rightTail : List Metamath.Verify.Sym)
      (callerRow : callerDVRow scopeOwner leftVariable rightVariable ∈
        callerDVRowsOfPairs scopeOwner callerDV)
      (nativeStep : NormalDVRightVariableDirectiveStep scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd leftVariable
        rightVariable leftTail rightTail rightBody sourceBody context)
      (reloadStep : NormalDVReloadDirectiveStep proofOwner proofPosition)
      (tail : NormalDVRightDirectiveTrace callerDV scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd leftVariable
        leftTail rightBody sourceBody context rightTail) :
      NormalDVRightDirectiveTrace callerDV scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd leftVariable
        leftTail rightBody sourceBody context (.var rightVariable :: rightTail)

/-- The source Cartesian-product condition constructs every scheduled right
scan and reload step, with no caller-DV fact added by the proof. -/
theorem normalDVRightDirectiveTrace_of_semantics
    (callerDV : List (String × String))
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) (rightScan : List Metamath.Verify.Sym)
    (semantics : AllWithSemantics callerDV leftVariable
      (BodyVariables rightScan)) :
    NormalDVRightDirectiveTrace callerDV scopeOwner proofOwner proofPosition
      assertionLabel nextPairPosition pairEnd leftVariable leftTail rightBody
      sourceBody context rightScan := by
  induction rightScan with
  | nil =>
      exact NormalDVRightDirectiveTrace.nil
        (normalDVRightNilPhase_inhabits_target_native_type scopeOwner
          proofOwner proofPosition assertionLabel nextPairPosition pairEnd
          leftVariable leftTail rightBody sourceBody context)
        (normalDVReloadPhase_inhabits_target_native_type proofOwner
          proofPosition)
  | cons symbol rightTail inductionHypothesis =>
      cases symbol with
      | const constantName =>
          have tailSemantics : AllWithSemantics callerDV leftVariable
              (BodyVariables rightTail) := by
            simpa [BodyVariables] using semantics
          exact NormalDVRightDirectiveTrace.const constantName rightTail
            (normalDVRightConstPhase_inhabits_target_native_type scopeOwner
              proofOwner proofPosition assertionLabel nextPairPosition pairEnd
              leftVariable constantName leftTail rightTail rightBody
              sourceBody context)
            (normalDVReloadPhase_inhabits_target_native_type proofOwner
              proofPosition)
            (inductionHypothesis tailSemantics)
      | var rightVariable =>
          have relation : DVRelation callerDV leftVariable rightVariable :=
            semantics rightVariable (by simp [BodyVariables])
          have tailSemantics : AllWithSemantics callerDV leftVariable
              (BodyVariables rightTail) := by
            intro right member
            exact semantics right (by simp [BodyVariables, member])
          exact NormalDVRightDirectiveTrace.var rightVariable rightTail
            ((callerDVRow_mem_callerDVRowsOfPairs_iff scopeOwner callerDV
              leftVariable rightVariable).2 relation)
            (normalDVRightVariablePhase_inhabits_target_native_type scopeOwner
              proofOwner proofPosition assertionLabel nextPairPosition pairEnd
              leftVariable rightVariable leftTail rightTail rightBody
              sourceBody context)
            (normalDVReloadPhase_inhabits_target_native_type proofOwner
              proofPosition)
            (inductionHypothesis tailSemantics)

/-- A complete target right scan reflects to the exact source `AllWith`
condition.  In particular, every variable branch reflects through membership
in the source-derived caller-DV table. -/
theorem NormalDVRightDirectiveTrace.reflects_semantics
    {callerDV : List (String × String)}
    {scopeOwner proofOwner : Atom} {proofPosition : Nat}
    {assertionLabel : String} {nextPairPosition pairEnd : Nat}
    {leftVariable : String}
    {leftTail rightBody sourceBody : List Metamath.Verify.Sym}
    {context : Atom} {rightScan : List Metamath.Verify.Sym}
    (trace : NormalDVRightDirectiveTrace callerDV scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd leftVariable
      leftTail rightBody sourceBody context rightScan) :
    AllWithSemantics callerDV leftVariable (BodyVariables rightScan) := by
  induction trace with
  | nil =>
      intro right member
      simp [BodyVariables] at member
  | const constantName rightTail nativeStep reloadStep tail
      inductionHypothesis =>
      simpa [BodyVariables] using inductionHypothesis
  | var rightVariable rightTail callerRow nativeStep reloadStep tail
      inductionHypothesis =>
      intro right member
      simp only [BodyVariables, List.mem_cons] at member
      rcases member with equal | member
      · subst right
        exact (callerDVRow_mem_callerDVRowsOfPairs_iff scopeOwner callerDV
          leftVariable rightVariable).1 callerRow
      · exact inductionHypothesis right member

theorem normalDVRightDirectiveTrace_iff_semantics
    (callerDV : List (String × String))
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) (rightScan : List Metamath.Verify.Sym) :
    NormalDVRightDirectiveTrace callerDV scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable leftTail rightBody
        sourceBody context rightScan ↔
      AllWithSemantics callerDV leftVariable (BodyVariables rightScan) := by
  constructor
  · exact NormalDVRightDirectiveTrace.reflects_semantics
  · exact normalDVRightDirectiveTrace_of_semantics callerDV scopeOwner
      proofOwner proofPosition assertionLabel nextPairPosition pairEnd
      leftVariable leftTail rightBody sourceBody context rightScan

def NormalDVLeftConstDirectiveStep
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVLeftConstPhaseSpace scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd constantName
    leftTail rightBody sourceBody context
  let target := fireReflectiveSourceExecFact source
    normalDVLeftConstDirective
  (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd leftTail rightBody sourceBody context ∈
        target ∧
      normalDVReloadAtom proofOwner proofPosition ∈ target

def NormalDVLeftVariableDirectiveStep
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVLeftVariablePhaseSpace scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd leftVariable
    leftTail rightBody sourceBody context
  let target := fireReflectiveSourceExecFact source
    normalDVLeftVariableDirective
  (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd leftVariable leftTail rightBody rightBody
          sourceBody context ∈ target ∧
      normalDVReloadAtom proofOwner proofPosition ∈ target

def NormalDVLeftNilDirectiveStep
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVLeftNilPhaseSpace scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd rightBody sourceBody
    context
  let target := fireReflectiveSourceExecFact source normalDVLeftNilDirective
  (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVNextPairAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd sourceBody context ∈ target ∧
      normalDVReloadAtom proofOwner proofPosition ∈ target

/-- Exact scheduled traversal of one left replacement body.  Each selected
left variable triggers a complete right-body traversal, so this trace realizes
the source Cartesian-product condition rather than merely checking endpoints. -/
inductive NormalDVLeftDirectiveTrace
    (callerDV : List (String × String))
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : List Metamath.Verify.Sym → Prop where
  | nil
      (nativeStep : NormalDVLeftNilDirectiveStep scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd rightBody
        sourceBody context)
      (reloadStep : NormalDVReloadDirectiveStep proofOwner proofPosition) :
      NormalDVLeftDirectiveTrace callerDV scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context []
  | const (constantName : String) (leftTail : List Metamath.Verify.Sym)
      (nativeStep : NormalDVLeftConstDirectiveStep scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd constantName
        leftTail rightBody sourceBody context)
      (reloadStep : NormalDVReloadDirectiveStep proofOwner proofPosition)
      (tail : NormalDVLeftDirectiveTrace callerDV scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd rightBody
        sourceBody context leftTail) :
      NormalDVLeftDirectiveTrace callerDV scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context
        (.const constantName :: leftTail)
  | var (leftVariable : String) (leftTail : List Metamath.Verify.Sym)
      (nativeStep : NormalDVLeftVariableDirectiveStep scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd leftVariable
        leftTail rightBody sourceBody context)
      (reloadStep : NormalDVReloadDirectiveStep proofOwner proofPosition)
      (right : NormalDVRightDirectiveTrace callerDV scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd leftVariable
        leftTail rightBody sourceBody context rightBody)
      (tail : NormalDVLeftDirectiveTrace callerDV scopeOwner proofOwner
        proofPosition assertionLabel nextPairPosition pairEnd rightBody
        sourceBody context leftTail) :
      NormalDVLeftDirectiveTrace callerDV scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context
        (.var leftVariable :: leftTail)

theorem normalDVLeftDirectiveTrace_of_semantics
    (callerDV : List (String × String))
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) (leftScan : List Metamath.Verify.Sym)
    (semantics : AllPairsSemantics callerDV (BodyVariables leftScan)
      (BodyVariables rightBody)) :
    NormalDVLeftDirectiveTrace callerDV scopeOwner proofOwner proofPosition
      assertionLabel nextPairPosition pairEnd rightBody sourceBody context
      leftScan := by
  induction leftScan with
  | nil =>
      exact NormalDVLeftDirectiveTrace.nil
        (normalDVLeftNilPhase_inhabits_target_native_type scopeOwner proofOwner
          proofPosition assertionLabel nextPairPosition pairEnd rightBody
          sourceBody context)
        (normalDVReloadPhase_inhabits_target_native_type proofOwner
          proofPosition)
  | cons symbol leftTail inductionHypothesis =>
      cases symbol with
      | const constantName =>
          have tailSemantics : AllPairsSemantics callerDV
              (BodyVariables leftTail) (BodyVariables rightBody) := by
            simpa [BodyVariables] using semantics
          exact NormalDVLeftDirectiveTrace.const constantName leftTail
            (normalDVLeftConstPhase_inhabits_target_native_type scopeOwner
              proofOwner proofPosition assertionLabel nextPairPosition pairEnd
              constantName leftTail rightBody sourceBody context)
            (normalDVReloadPhase_inhabits_target_native_type proofOwner
              proofPosition)
            (inductionHypothesis tailSemantics)
      | var leftVariable =>
          have rightSemantics : AllWithSemantics callerDV leftVariable
              (BodyVariables rightBody) :=
            semantics leftVariable (by simp [BodyVariables])
          have tailSemantics : AllPairsSemantics callerDV
              (BodyVariables leftTail) (BodyVariables rightBody) := by
            intro left member
            exact semantics left (by simp [BodyVariables, member])
          exact NormalDVLeftDirectiveTrace.var leftVariable leftTail
            (normalDVLeftVariablePhase_inhabits_target_native_type scopeOwner
              proofOwner proofPosition assertionLabel nextPairPosition pairEnd
              leftVariable leftTail rightBody sourceBody context)
            (normalDVReloadPhase_inhabits_target_native_type proofOwner
              proofPosition)
            (normalDVRightDirectiveTrace_of_semantics callerDV scopeOwner
              proofOwner proofPosition assertionLabel nextPairPosition pairEnd
              leftVariable leftTail rightBody sourceBody context rightBody
              rightSemantics)
            (inductionHypothesis tailSemantics)

theorem NormalDVLeftDirectiveTrace.reflects_semantics
    {callerDV : List (String × String)}
    {scopeOwner proofOwner : Atom} {proofPosition : Nat}
    {assertionLabel : String} {nextPairPosition pairEnd : Nat}
    {rightBody sourceBody : List Metamath.Verify.Sym}
    {context : Atom} {leftScan : List Metamath.Verify.Sym}
    (trace : NormalDVLeftDirectiveTrace callerDV scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd rightBody
      sourceBody context leftScan) :
    AllPairsSemantics callerDV (BodyVariables leftScan)
      (BodyVariables rightBody) := by
  induction trace with
  | nil =>
      intro left member
      simp [BodyVariables] at member
  | const constantName leftTail nativeStep reloadStep tail
      inductionHypothesis =>
      simpa [BodyVariables] using inductionHypothesis
  | var leftVariable leftTail nativeStep reloadStep right tail
      inductionHypothesis =>
      intro left member
      simp only [BodyVariables, List.mem_cons] at member
      rcases member with equal | member
      · subst left
        exact right.reflects_semantics
      · exact inductionHypothesis left member

theorem normalDVLeftDirectiveTrace_iff_semantics
    (callerDV : List (String × String))
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) (leftScan : List Metamath.Verify.Sym) :
    NormalDVLeftDirectiveTrace callerDV scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context
        leftScan ↔
      AllPairsSemantics callerDV (BodyVariables leftScan)
        (BodyVariables rightBody) := by
  constructor
  · exact NormalDVLeftDirectiveTrace.reflects_semantics
  · exact normalDVLeftDirectiveTrace_of_semantics callerDV scopeOwner
      proofOwner proofPosition assertionLabel nextPairPosition pairEnd
      rightBody sourceBody context leftScan

def NormalDVPairBeginDirectiveStep
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVPairBeginPhaseSpace scopeOwner proofOwner
    proofPosition assertionLabel pairPosition nextPairPosition pairEnd
    leftVariable rightVariable leftBody rightBody sourceBody context
  let target := fireReflectiveSourceExecFact source
    normalDVPairBeginDirective
  (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd leftBody rightBody sourceBody context ∈
        target ∧
      normalDVReloadAtom proofOwner proofPosition ∈ target

def NormalDVCompleteDirectiveStep
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) : Prop :=
  let source := normalDVCompletePhaseSpace scopeOwner proofOwner
    proofPosition assertionLabel pairEnd sourceBody context
  let target := fireReflectiveSourceExecFact source normalDVCompleteDirective
  (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalBodyBuildAtom proofOwner proofPosition sourceBody [] context ∈ target

/-- Exact traversal of the ordered callee-DV list.  The trace keeps both
substitution lookups, each Cartesian-product scan, every reload event, and the
terminal transition into result-body construction. -/
inductive NormalDVListsDirectiveTrace
    (callerDV : List (String × String))
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom)
    (substitution : FiniteSubstitution) :
    List (String × String) → Nat → Prop where
  | nil
      (nativeStep : NormalDVCompleteDirectiveStep scopeOwner proofOwner
        proofPosition assertionLabel pairEnd sourceBody context) :
      NormalDVListsDirectiveTrace callerDV scopeOwner proofOwner proofPosition
        assertionLabel pairEnd sourceBody context substitution [] pairEnd
  | cons (leftVariable rightVariable : String)
      (calleeTail : List (String × String))
      (leftReplacement rightReplacement : ConstantHeadedFormula)
      (pairPosition : Nat)
      (leftLookup : LookupSemantics substitution leftVariable leftReplacement)
      (rightLookup : LookupSemantics substitution rightVariable
        rightReplacement)
      (leftRow : normalAssertionSubstitutionAtom proofOwner proofPosition
          leftVariable leftReplacement.body ∈
        normalSubstitutionRows proofOwner proofPosition substitution)
      (rightRow : normalAssertionSubstitutionAtom proofOwner proofPosition
          rightVariable rightReplacement.body ∈
        normalSubstitutionRows proofOwner proofPosition substitution)
      (variablesDistinct : leftVariable ≠ rightVariable)
      (nativeStep : NormalDVPairBeginDirectiveStep scopeOwner proofOwner
        proofPosition assertionLabel pairPosition (pairPosition + 1) pairEnd
        leftVariable rightVariable leftReplacement.body rightReplacement.body
        sourceBody context)
      (reloadStep : NormalDVReloadDirectiveStep proofOwner proofPosition)
      (leftTrace : NormalDVLeftDirectiveTrace callerDV scopeOwner proofOwner
        proofPosition assertionLabel (pairPosition + 1) pairEnd
        rightReplacement.body sourceBody context leftReplacement.body)
      (tail : NormalDVListsDirectiveTrace callerDV scopeOwner proofOwner
        proofPosition assertionLabel pairEnd sourceBody context substitution
        calleeTail (pairPosition + 1)) :
      NormalDVListsDirectiveTrace callerDV scopeOwner proofOwner proofPosition
        assertionLabel pairEnd sourceBody context substitution
        ((leftVariable, rightVariable) :: calleeTail) pairPosition

theorem normalDVListsDirectiveTrace_of_semantics
    (callerDV : List (String × String))
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom)
    (substitution : FiniteSubstitution)
    (calleeDV : List (String × String)) (pairPosition : Nat)
    (positionEnd : pairPosition + calleeDV.length = pairEnd)
    (namesDistinct : DVPairNamesDistinct calleeDV)
    (semantics : DVListsSemantics substitution callerDV calleeDV) :
    NormalDVListsDirectiveTrace callerDV scopeOwner proofOwner proofPosition
      assertionLabel pairEnd sourceBody context substitution calleeDV
      pairPosition := by
  induction calleeDV generalizing pairPosition with
  | nil =>
      simp at positionEnd
      subst pairPosition
      exact NormalDVListsDirectiveTrace.nil
        (normalDVCompletePhase_inhabits_target_native_type scopeOwner
          proofOwner proofPosition assertionLabel pairEnd sourceBody context)
  | cons pair calleeTail inductionHypothesis =>
      rcases pair with ⟨leftVariable, rightVariable⟩
      rcases semantics (leftVariable, rightVariable) (by simp) with
        ⟨leftReplacement, rightReplacement, leftLookup, rightLookup,
          pairSemantics⟩
      have variablesDistinct : leftVariable ≠ rightVariable :=
        namesDistinct (leftVariable, rightVariable) (by simp)
      have tailDistinct : DVPairNamesDistinct calleeTail := by
        intro pair member
        exact namesDistinct pair (by simp [member])
      have tailSemantics : DVListsSemantics substitution callerDV
          calleeTail := by
        intro pair member
        exact semantics pair (by simp [member])
      have tailEnd : pairPosition + 1 + calleeTail.length = pairEnd := by
        simp only [List.length_cons] at positionEnd
        omega
      have leftRow : normalAssertionSubstitutionAtom proofOwner proofPosition
            leftVariable leftReplacement.body ∈
          normalSubstitutionRows proofOwner proofPosition substitution :=
        (normalAssertionSubstitutionAtom_mem_normalSubstitutionRows_iff
          proofOwner proofPosition substitution leftVariable
          leftReplacement.body).2
          ⟨leftReplacement, leftLookup, rfl⟩
      have rightRow : normalAssertionSubstitutionAtom proofOwner proofPosition
            rightVariable rightReplacement.body ∈
          normalSubstitutionRows proofOwner proofPosition substitution :=
        (normalAssertionSubstitutionAtom_mem_normalSubstitutionRows_iff
          proofOwner proofPosition substitution rightVariable
          rightReplacement.body).2
          ⟨rightReplacement, rightLookup, rfl⟩
      exact NormalDVListsDirectiveTrace.cons leftVariable rightVariable
        calleeTail leftReplacement rightReplacement pairPosition leftLookup
        rightLookup leftRow rightRow variablesDistinct
        (normalDVPairBeginPhase_inhabits_target_native_type scopeOwner
          proofOwner proofPosition assertionLabel pairPosition
          (pairPosition + 1) pairEnd leftVariable rightVariable
          leftReplacement.body rightReplacement.body sourceBody context
          variablesDistinct)
        (normalDVReloadPhase_inhabits_target_native_type proofOwner
          proofPosition)
        (normalDVLeftDirectiveTrace_of_semantics callerDV scopeOwner
          proofOwner proofPosition assertionLabel (pairPosition + 1) pairEnd
          rightReplacement.body sourceBody context leftReplacement.body
          pairSemantics)
        (inductionHypothesis (pairPosition := pairPosition + 1) tailEnd
          tailDistinct tailSemantics)

theorem NormalDVListsDirectiveTrace.reflects_semantics
    {callerDV : List (String × String)}
    {scopeOwner proofOwner : Atom} {proofPosition : Nat}
    {assertionLabel : String} {pairEnd : Nat}
    {sourceBody : List Metamath.Verify.Sym} {context : Atom}
    {substitution : FiniteSubstitution}
    {calleeDV : List (String × String)} {pairPosition : Nat}
    (trace : NormalDVListsDirectiveTrace callerDV scopeOwner proofOwner
      proofPosition assertionLabel pairEnd sourceBody context substitution
      calleeDV pairPosition) :
    DVListsSemantics substitution callerDV calleeDV := by
  induction trace with
  | nil =>
      intro pair member
      simp at member
  | cons leftVariable rightVariable calleeTail leftReplacement
      rightReplacement pairPosition leftLookup rightLookup leftRow rightRow
      _variablesDistinct nativeStep reloadStep leftTrace tail
      inductionHypothesis =>
      intro pair member
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · cases equal
        exact ⟨leftReplacement, rightReplacement, leftLookup, rightLookup,
          leftTrace.reflects_semantics⟩
      · exact inductionHypothesis pair member

theorem normalDVListsDirectiveTrace_iff_semantics
    (callerDV : List (String × String))
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom)
    (substitution : FiniteSubstitution)
    (calleeDV : List (String × String)) (pairPosition : Nat)
    (positionEnd : pairPosition + calleeDV.length = pairEnd)
    (namesDistinct : DVPairNamesDistinct calleeDV) :
    NormalDVListsDirectiveTrace callerDV scopeOwner proofOwner proofPosition
        assertionLabel pairEnd sourceBody context substitution calleeDV
        pairPosition ↔
      DVListsSemantics substitution callerDV calleeDV := by
  constructor
  · exact NormalDVListsDirectiveTrace.reflects_semantics
  · exact normalDVListsDirectiveTrace_of_semantics callerDV scopeOwner
      proofOwner proofPosition assertionLabel pairEnd sourceBody context
      substitution calleeDV pairPosition positionEnd namesDistinct

/-- Every callee pair in an assertion admitted by the authored presentation
has distinct endpoints.  This is extracted from the presentation's actual
validation gate rather than assumed by the MM2 trace. -/
theorem generatedAssertion_dvPairNamesDistinct
    (projection : PrefixProjection) (target : ValidatedCalculusLanguageDef)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    {assertion : AssertionView}
    (hassertion : assertion ∈ projection.assertions) :
    DVPairNamesDistinct assertion.frame.dj.toList := by
  have projectionValid : prefixProjectionValid projection = true :=
    prefixProjectionValid_of_calculusLanguageDefOfProjection?_eq_some projection
      target.1 hprojection
  simp only [prefixProjectionValid, Bool.and_eq_true] at projectionValid
  have assertionValid : assertionViewValid projection.declaredConstants
      projection.declaredVariables assertion = true :=
    List.all_eq_true.mp projectionValid.1.2 assertion hassertion
  simp only [assertionViewValid, Bool.and_eq_true] at assertionValid
  have frameValid : frameProjectionValid assertion.frame
      assertion.hypotheses = true := assertionValid.1.1.1
  simp only [frameProjectionValid, Bool.and_eq_true] at frameValid
  have dvValid : frameDVValid assertion.frame
      (floatingVariableNames assertion.hypotheses) = true := frameValid.2
  simp only [frameDVValid] at dvValid
  apply dvPairNamesDistinct_of_strictOrderAll assertion.frame.dj.toList
  apply List.all_eq_true.mpr
  intro pair pairMember
  have pairValid := List.all_eq_true.mp dvValid pair pairMember
  simp only [Bool.and_eq_true] at pairValid
  exact pairValid.1.1

/-- The DV part of a source-owned generated assertion node traverses the
actual finish transition, every ordered callee pair, both replacement bodies,
and the final result-builder transition. -/
theorem GeneratedAssertionNode.dv_has_complete_mm2_directive_trace
    (projection : PrefixProjection) (target : ValidatedCalculusLanguageDef)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    {assertion : AssertionView}
    (hassertion : assertion ∈ projection.assertions)
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (node : GeneratedAssertionNode projection target assertion actuals
      result substitution)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat)
    (hypothesisEnd stackEnd stackBase nextTop : Nat) :
    let pairEnd := assertion.frame.dj.toList.length
    let context := normalAssertionResultContextAtom scopeOwner
      nextProofPosition assertion.label result.typecode stackBase nextTop
    let finishPhase := normalAssertionFinishPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition assertion.label hypothesisEnd stackEnd
      stackBase result.typecode assertion.formula.body pairEnd nextTop
    let finishTarget := fireReflectiveSourceExecFact finishPhase
      normalAssertionFinishDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies finishPhase
        (reflectiveSourceExecExactTargetNativeType finishTarget).pred ∧
      normalDVNextPairAtom scopeOwner proofOwner proofPosition assertion.label
            0 pairEnd assertion.formula.body context ∈ finishTarget ∧
        normalDVReloadAtom proofOwner proofPosition ∈ finishTarget ∧
          NormalDVListsDirectiveTrace projection.callerFrame.dj.toList
            scopeOwner proofOwner proofPosition assertion.label pairEnd
            assertion.formula.body context substitution
            assertion.frame.dj.toList 0 := by
  dsimp only
  rcases (assertionRuleApplication_iff_instances projection target
      hprojection hassertion).mp node.application with
    ⟨instances, _resultTypecode⟩
  rcases (assertionSideEvidence_nonempty_iff_semantics projection target
      hprojection instances).mp ⟨node.sideEvidence⟩ with
    ⟨_essentialMatches, dvSemantics, _resultSemantics⟩
  have finish := normalAssertionFinishPhase_inhabits_target_native_type
    scopeOwner proofOwner proofPosition nextProofPosition assertion.label
    hypothesisEnd stackEnd stackBase result.typecode assertion.formula.body
    assertion.frame.dj.toList.length nextTop
  refine ⟨finish.1, finish.2.1, finish.2.2, ?_⟩
  exact normalDVListsDirectiveTrace_of_semantics
    projection.callerFrame.dj.toList scopeOwner proofOwner proofPosition
    assertion.label assertion.frame.dj.toList.length assertion.formula.body
    (normalAssertionResultContextAtom scopeOwner nextProofPosition
      assertion.label result.typecode stackBase nextTop)
    substitution assertion.frame.dj.toList 0
      (by
        simp only [Nat.zero_add, Array.length_toList]
        exact rfl)
    (generatedAssertion_dvPairNamesDistinct projection target hprojection
      hassertion)
    dvSemantics

def NormalAssertionFinishDirectiveStep
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat)
    (assertionLabel : String) (hypothesisEnd stackEnd stackBase : Nat)
    (resultTypecode : String) (sourceBody : List Metamath.Verify.Sym)
    (pairEnd : Nat) : Prop :=
  let context := normalAssertionResultContextAtom scopeOwner nextProofPosition
    assertionLabel resultTypecode stackBase (stackBase + 1)
  let source := normalAssertionFinishPhaseSpace scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel hypothesisEnd stackEnd
    stackBase resultTypecode sourceBody pairEnd (stackBase + 1)
  let target := fireReflectiveSourceExecFact source
    normalAssertionFinishDirective
  (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVNextPairAtom scopeOwner proofOwner proofPosition assertionLabel 0
          pairEnd sourceBody context ∈ target ∧
      normalDVReloadAtom proofOwner proofPosition ∈ target

def NormalAssertionPublishDirectiveStep
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat)
    (assertionLabel resultTypecode : String) (stackBase : Nat)
    (resultBody : List Metamath.Verify.Sym) : Prop :=
  let source := normalAssertionResultCompletePhaseSpace scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel resultTypecode stackBase
    (stackBase + 1) resultBody
  let target := fireReflectiveSourceExecFact source
    normalAssertionResultCompleteDirective
  (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalControlAtom scopeOwner proofOwner nextProofPosition
          (stackBase + 1) ∈ target ∧
      normalAssertionStackAtom proofOwner stackBase resultTypecode resultBody
            proofPosition assertionLabel ∈ target ∧
        normalAssertionReloadAtom proofOwner ∈ target

/-- The complete scheduled MM2 macro-trace for one Metamath assertion
application after its ordered child proofs are present.  It records the exact
hypothesis, DV, result-building, and publication phases and their OSLF-derived
native types. -/
structure NormalAssertionApplicationDirectiveTrace
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (callerFrame : Mettapedia.Languages.Metamath.MMLean4Bridge.RuntimeFrame)
    (assertion : AssertionView)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (children : GeneratedProvesForest projection target actuals)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase proofOffset : Nat)
    (substitution : FiniteSubstitution) : Prop where
  hypotheses : NormalHypothesisDirectiveTrace scopeOwner proofOwner
    proofPosition nextProofPosition assertion.label
    (0 + assertion.hypotheses.length) stackBase substitution
    assertion.hypotheses actuals substitution children 0 stackBase proofOffset
  resultTypecode : assertion.formula.typecode = result.typecode
  finish : NormalAssertionFinishDirectiveStep scopeOwner proofOwner
    proofPosition nextProofPosition assertion.label assertion.hypotheses.length
    (stackBase + assertion.hypotheses.length) stackBase result.typecode
    assertion.formula.body assertion.frame.dj.toList.length
  dv : NormalDVListsDirectiveTrace callerFrame.dj.toList scopeOwner proofOwner
    proofPosition assertion.label assertion.frame.dj.toList.length
    assertion.formula.body
    (normalAssertionResultContextAtom scopeOwner nextProofPosition
      assertion.label result.typecode stackBase (stackBase + 1))
    substitution assertion.frame.dj.toList 0
  resultBuild : NormalBodyBuildDirectiveTrace proofOwner
    (normalAssertionResultContextAtom scopeOwner nextProofPosition
      assertion.label result.typecode stackBase (stackBase + 1))
    proofPosition substitution assertion.formula.body [] result.body
  publish : NormalAssertionPublishDirectiveStep scopeOwner proofOwner
    proofPosition nextProofPosition assertion.label result.typecode stackBase
    result.body

/-- The scheduled target assertion macro-trace exists exactly when the
independent Metamath assertion-application semantics holds.  The backward
direction is compilation; the forward direction is no-invention. -/
theorem normalAssertionApplicationDirectiveTrace_nonempty_iff_semantics
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (callerFrame : Mettapedia.Languages.Metamath.MMLean4Bridge.RuntimeFrame)
    (assertion : AssertionView)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (children : GeneratedProvesForest projection target actuals)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase proofOffset : Nat)
    (pairNamesDistinct : DVPairNamesDistinct assertion.frame.dj.toList) :
    (∃ substitution : FiniteSubstitution,
      NormalAssertionApplicationDirectiveTrace callerFrame assertion actuals
        result children scopeOwner proofOwner proofPosition nextProofPosition
        stackBase proofOffset substitution) ↔
      AssertionApplicationSemantics callerFrame assertion actuals result := by
  constructor
  · rintro ⟨substitution, trace⟩
    have hypothesisSemantics := trace.hypotheses.reflects_semantics
    have dvSemantics := trace.dv.reflects_semantics
    have resultSemantics : FormulaSubstitutionSemantics substitution
        assertion.formula result :=
      ⟨trace.resultTypecode,
        (normalBodyBuildDirectiveTrace_iff_bodySubstitution proofOwner
          (normalAssertionResultContextAtom scopeOwner nextProofPosition
            assertion.label result.typecode stackBase (stackBase + 1))
          proofPosition substitution assertion.formula.body result.body).mp
            trace.resultBuild⟩
    exact ⟨substitution, hypothesisSemantics.1, hypothesisSemantics.2,
      dvSemantics, resultSemantics⟩
  · rintro ⟨substitution, instances, essentialMatches, dvSemantics,
      resultSemantics⟩
    refine ⟨substitution, ?_⟩
    refine
      { hypotheses := normalHypothesisDirectiveTrace_of_semantics scopeOwner
          proofOwner proofPosition nextProofPosition assertion.label stackBase
          substitution instances essentialMatches children 0 stackBase
          proofOffset
        resultTypecode := resultSemantics.1
        finish := ?_
        dv := ?_
        resultBuild := normalBodyBuildDirectiveTrace_of_bodySubstitution
          proofOwner
          (normalAssertionResultContextAtom scopeOwner nextProofPosition
            assertion.label result.typecode stackBase (stackBase + 1))
          proofPosition resultSemantics.2
        publish := normalAssertionResultCompletePhase_inhabits_target_native_type
          scopeOwner proofOwner proofPosition nextProofPosition assertion.label
          result.typecode stackBase (stackBase + 1) result.body }
    · exact normalAssertionFinishPhase_inhabits_target_native_type scopeOwner
        proofOwner proofPosition nextProofPosition assertion.label
        assertion.hypotheses.length
        (stackBase + assertion.hypotheses.length) stackBase result.typecode
        assertion.formula.body assertion.frame.dj.toList.length
        (stackBase + 1)
    · exact normalDVListsDirectiveTrace_of_semantics callerFrame.dj.toList
        scopeOwner proofOwner proofPosition assertion.label
        assertion.frame.dj.toList.length assertion.formula.body
        (normalAssertionResultContextAtom scopeOwner nextProofPosition
          assertion.label result.typecode stackBase (stackBase + 1))
        substitution assertion.frame.dj.toList 0
        (by
          simp only [Nat.zero_add, Array.length_toList]
          exact rfl)
        pairNamesDistinct dvSemantics

/-- The existing generated Metamath node and the complete scheduled MM2
macro-trace have exactly the same assertion-application content. -/
theorem generatedAssertionNode_nonempty_iff_normalAssertionDirectiveTrace
    (projection : PrefixProjection) (target : ValidatedCalculusLanguageDef)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    {assertion : AssertionView}
    (hassertion : assertion ∈ projection.assertions)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (children : GeneratedProvesForest projection target actuals)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase proofOffset : Nat) :
    Nonempty
        (Σ substitution : FiniteSubstitution,
          GeneratedAssertionNode projection target assertion actuals result
            substitution) ↔
      (∃ substitution : FiniteSubstitution,
        NormalAssertionApplicationDirectiveTrace projection.callerFrame
          assertion actuals result children scopeOwner proofOwner proofPosition
          nextProofPosition stackBase proofOffset substitution) := by
  exact (generatedAssertionNode_nonempty_iff_semantics projection target
    hprojection hassertion actuals result).trans
      (normalAssertionApplicationDirectiveTrace_nonempty_iff_semantics
        projection.callerFrame assertion actuals result children scopeOwner
        proofOwner proofPosition nextProofPosition stackBase proofOffset
        (generatedAssertion_dvPairNamesDistinct projection target hprojection
          hassertion)).symm

/-- A concrete source-owned assertion node determines the complete scheduled
MM2 assertion macro-trace with the very same substitution.  This is the
proof-relevant forward half used when recursively compiling a whole normal
proof tree; no existentially chosen replacement substitution is introduced. -/
theorem GeneratedAssertionNode.has_complete_mm2_application_trace
    (projection : PrefixProjection) (target : ValidatedCalculusLanguageDef)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    {assertion : AssertionView}
    (hassertion : assertion ∈ projection.assertions)
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (node : GeneratedAssertionNode projection target assertion actuals
      result substitution)
    (children : GeneratedProvesForest projection target actuals)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase proofOffset : Nat) :
    NormalAssertionApplicationDirectiveTrace projection.callerFrame assertion
      actuals result children scopeOwner proofOwner proofPosition
      nextProofPosition stackBase proofOffset substitution := by
  have hypotheses :=
    _root_.Mettapedia.Languages.Metamath.MM2NormalStackCorrespondence.GeneratedAssertionNode.hypotheses_have_complete_mm2_directive_trace
      projection target hprojection hassertion node children scopeOwner
      proofOwner proofPosition nextProofPosition stackBase 0 stackBase
      proofOffset
  have dv :=
    _root_.Mettapedia.Languages.Metamath.MM2NormalStackCorrespondence.GeneratedAssertionNode.dv_has_complete_mm2_directive_trace
      projection target hprojection hassertion node scopeOwner proofOwner
      proofPosition nextProofPosition assertion.hypotheses.length
      (stackBase + assertion.hypotheses.length) stackBase (stackBase + 1)
  have resultTrace :=
    _root_.Mettapedia.Languages.Metamath.MM2NormalStackCorrespondence.GeneratedAssertionNode.result_has_complete_mm2_directive_trace
      projection target hprojection hassertion node scopeOwner proofOwner
      proofPosition nextProofPosition stackBase (stackBase + 1)
  exact
    { hypotheses := hypotheses
      resultTypecode := resultTrace.2.2.2.1.symm
      finish := ⟨dv.1, dv.2.1, dv.2.2.1⟩
      dv := dv.2.2.2
      resultBuild := resultTrace.2.2.2.2.1
      publish := resultTrace.2.2.2.2.2 }

/-- One independently authored essential-hypothesis instance, together with
its `FormulaSubstitutionSemantics`, traverses the actual emitted start,
generic body-match, and completion directives.  The theorem compares this
semantic macro-step without equating MM2's administrative scheduler trace to
one source step. -/
theorem HypothesisInstances.essential_has_complete_mm2_directive_trace
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {hypothesisLabel : String} {formula actual : ConstantHeadedFormula}
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances
      (.essential hypothesisLabel formula :: hypotheses)
      (actual :: actuals) substitution)
    (matchSemantics : FormulaSubstitutionSemantics substitution formula actual)
    (child : GeneratedProvesTree projection target actual)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase proofOffset : Nat) :
    let childOccurrence := proofOffset + child.labels.length - 1
    let continuation := normalAssertionEssentialContinuationAtom scopeOwner
      proofOwner proofPosition nextProofPosition assertionLabel
      nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence
    let startPhase := normalAssertionEssentialPhaseSpace scopeOwner proofOwner
          proofPosition nextProofPosition assertionLabel hypothesisPosition
          nextHypothesisPosition hypothesisEnd stackPosition
          nextStackPosition stackBase hypothesisLabel formula.typecode
          formula.body actual.body childOccurrence
    let startTarget := fireReflectiveSourceExecFact startPhase
      normalAssertionEssentialDirective
    normalStackAtom proofOwner stackPosition actual childOccurrence ∈
        startPhase ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveSourceExecGSLT .leaveInert)).satisfies startPhase
          (reflectiveSourceExecExactTargetNativeType startTarget).pred ∧
      normalAssertionEssentialMatchAtom scopeOwner proofOwner proofPosition
            nextProofPosition assertionLabel nextHypothesisPosition
            hypothesisEnd nextStackPosition stackBase hypothesisPosition
            childOccurrence formula.body actual.body ∈ startTarget ∧
      NormalBodyMatchDirectiveTrace proofOwner continuation proofPosition
          substitution formula.body actual.body ∧
        let completePhase := normalAssertionEssentialCompletePhaseSpace
          scopeOwner proofOwner proofPosition nextProofPosition assertionLabel
          nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
          hypothesisPosition childOccurrence
        let result := fireReflectiveSourceExecFact completePhase
          normalAssertionEssentialCompleteDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies completePhase
            (reflectiveSourceExecExactTargetNativeType result).pred ∧
          normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
              nextProofPosition assertionLabel nextHypothesisPosition
              hypothesisEnd nextStackPosition stackBase ∈ result ∧
          normalAssertionChildAtom proofOwner proofPosition hypothesisPosition
                childOccurrence ∈ result ∧
            normalAssertionReloadAtom proofOwner ∈ result := by
  dsimp only
  have starts :=
    Mettapedia.Languages.Metamath.MM2NormalStackCorrespondence.HypothesisInstances.essential_inhabits_mm2_target_native_type
      instances child scopeOwner proofOwner proofPosition nextProofPosition
      assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
      stackPosition nextStackPosition stackBase proofOffset
  refine ⟨starts.1, starts.2.1, starts.2.2, ?_, ?_⟩
  · exact normalBodyMatchDirectiveTrace_of_bodySubstitution proofOwner
      (normalAssertionEssentialContinuationAtom scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel
        nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
        hypothesisPosition (proofOffset + child.labels.length - 1))
      proofPosition matchSemantics.2
  · exact normalAssertionEssentialCompletePhase_inhabits_target_native_type
      scopeOwner proofOwner proofPosition nextProofPosition assertionLabel
      nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition (proofOffset + child.labels.length - 1)

/-! ## Exact normal-proof terminal boundary -/

/-- A retained source proof tree determines the exact final stack occurrence
required by the generic MM2 acceptance rule.  At that boundary, ordinary MM2
scheduling produces the exact OSLF target type and terminal observation.  This
theorem deliberately does not claim that the whole emitted program has already
been lifted to this boundary. -/
theorem GeneratedProvesTree.terminal_inhabits_mm2_target_native_type
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    (scopeOwner proofOwner theoremLabel : Atom) :
    let occurrence := generatedRootOccurrenceAtom 0 tree
    let phase := normalAcceptPhaseSpace scopeOwner proofOwner theoremLabel
      (formulaAtom formula) occurrence tree.labels.length
    let result := fireReflectiveSourceExecFact phase normalAcceptDirective
    normalStackAtomWithOccurrence proofOwner 0 formula occurrence ∈ phase ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
          (reflectiveSourceExecExactTargetNativeType result).pred ∧
        normalAcceptedAtom scopeOwner proofOwner theoremLabel
          (formulaAtom formula) occurrence ∈ result := by
  dsimp only
  constructor
  · simp [normalAcceptPhaseSpace]
  · exact normalAcceptPhase_inhabits_target_native_type scopeOwner
      proofOwner theoremLabel (formulaAtom formula)
      (generatedRootOccurrenceAtom 0 tree) tree.labels.length

/-! ## Discriminating examples -/

example {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (hypothesis : HypothesisView)
    (member : hypothesis ∈ projection.activeHypotheses)
    (proofOwner : Atom) :
    ((.cons (.active hypothesis member) .nil :
        GeneratedProvesForest projection target [hypothesis.formula])
      |> mm2StackRows proofOwner 0 0) =
      [normalHypothesisStackAtom proofOwner 0 hypothesis 0] := by
  simp [mm2StackRows,
    normalHypothesisStackAtom]

example (proofOwner : Atom) (formula : ConstantHeadedFormula) :
    normalStackAtom proofOwner 0 formula 0 ≠
      normalStackAtom proofOwner 0 formula 1 := by
  exact normalStackAtom_ne_of_occurrence_ne proofOwner 0 formula
    (by decide)

example (proofOwner : Atom) (formula : ConstantHeadedFormula) :
    normalAssertionStackAtom proofOwner 0 formula.typecode formula.body 7
        "left" ≠
      normalAssertionStackAtom proofOwner 0 formula.typecode formula.body 7
        "right" := by
  intro equal
  have labelsEqual :=
    (normalAssertionStackAtom_occurrence_injective proofOwner 0
      formula.typecode formula.body 7 7 "left" "right" equal).2
  contradiction

example (proofOwner : Atom) :
    normalAssertionChildAtom proofOwner 7 2 11 ≠
      normalAssertionChildAtom proofOwner 7 2 12 := by
  intro equal
  have := normalAssertionChildAtom_occurrence_injective proofOwner 7 2 equal
  contradiction

#print axioms mm2StackRows_append
#print axioms mm2StackRows_append_active
#print axioms mm2StackRows_append_assertion
#print axioms normalStackAtom_occurrence_injective
#print axioms admittedSourceAssertion_fires_start
#print axioms admittedSourceAssertion_scheduled_start
#print axioms admittedSourceAssertion_pop_edge
#print axioms admittedSourceAssertion_scheduled_pop_edge
#print axioms admittedSourceAssertion_fires_begin
#print axioms admittedSourceAssertion_scheduled_begin
#print axioms normalAssertionPopDirectiveTrace_exact
#print axioms admittedSourceAssertion_has_entry_trace
#print axioms HypothesisInstances.floating_fires_mm2
#print axioms HypothesisInstances.floating_inhabits_mm2_target_native_type
#print axioms HypothesisInstances.essential_starts_mm2_match
#print axioms HypothesisInstances.essential_inhabits_mm2_target_native_type
#print axioms admittedSourceAssertion_essential_fires_match
#print axioms normalAssertionSubstitutionAtom_mem_normalSubstitutionRows_iff
#print axioms normalBodyPrefixDirectiveTrace_append
#print axioms normalBodyMatchDirectiveTrace_of_bodySubstitution
#print axioms bodySubstitution_of_normalBodyMatchDirectiveTrace
#print axioms normalBodyMatchDirectiveTrace_iff_bodySubstitution
#print axioms normalBodyBuildPrefixDirectiveTrace_exact
#print axioms NormalBodyBuildPrefixDirectiveTrace.finalReversed_eq
#print axioms normalBodyReverseDirectiveTrace_exact
#print axioms NormalBodyReverseDirectiveTrace.finalBody_eq
#print axioms normalBodyBuildDirectiveTrace_of_bodySubstitution
#print axioms NormalBodyBuildDirectiveTrace.reflects_bodySubstitution
#print axioms normalBodyBuildDirectiveTrace_iff_bodySubstitution
#print axioms GeneratedAssertionNode.result_has_complete_mm2_directive_trace
#print axioms NormalHypothesisDirectiveTrace.reflects_semantics
#print axioms normalHypothesisDirectiveTrace_iff_semantics
#print axioms GeneratedAssertionNode.hypotheses_have_complete_mm2_directive_trace
#print axioms normalDVRightDirectiveTrace_iff_semantics
#print axioms normalDVLeftDirectiveTrace_iff_semantics
#print axioms normalDVListsDirectiveTrace_iff_semantics
#print axioms generatedAssertion_dvPairNamesDistinct
#print axioms GeneratedAssertionNode.dv_has_complete_mm2_directive_trace
#print axioms normalAssertionApplicationDirectiveTrace_nonempty_iff_semantics
#print axioms generatedAssertionNode_nonempty_iff_normalAssertionDirectiveTrace
#print axioms HypothesisInstances.essential_has_complete_mm2_directive_trace
#print axioms GeneratedProvesTree.terminal_inhabits_mm2_target_native_type

end Mettapedia.Languages.Metamath.MM2NormalStackCorrespondence
