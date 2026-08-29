import Mettapedia.Languages.Metamath.MM2NormalStackCorrespondence
import Mettapedia.Languages.Metamath.SourceInferenceExecution

open Mettapedia.GSLT.LanguageDef

/-!
# Whole normal-proof traces for the Metamath-to-MM2 transformation

This module indexes the already proved scheduled MM2 hypothesis and assertion
macro-steps by an arbitrary source-owned normal proof tree.  The recursion is
the source tree's authored postfix order.  Each leaf or assertion root is a
separately fireable scheduled event of the reflective MM2 GSLT, classified by
the native types synthesized by OSLF.

These are deliberately phase-local obligations.  They do not claim that the
freshly constructed phase spaces form one state-threaded execution.  The
assembled execution theorem belongs at the whole-program boundary.
-/

namespace Mettapedia.Languages.Metamath.MM2NormalProofCorrespondence

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2NormalStackCorrespondence
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK

/-! ## Source-indexed assertion entry -/

/-- The complete scheduled entry trace for one assertion occurrence selected
from the supplied source scope.  The selected assertion is read by position
from source-derived target data; it is not chosen by a compiler-side label
oracle. -/
structure NormalSourceAssertionEntryDirectiveTrace
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition assertionPosition stackBase : Nat) :
    Prop where
  assertionInBounds : assertionPosition < source.state.assertions.length
  header :
    assertionHeaderRow scopeOwner assertionPosition
        source.state.assertions[assertionPosition] ∈
      (transformNormalScope source mm2Target scopeOwner).executionRows
  start :
    let assertion := source.state.assertions[assertionPosition]
    let stackTop := stackBase + assertion.hypotheses.length
    let phase := normalAssertionStartPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition stackTop assertionPosition assertion
    let result := fireReflectiveSourceExecFact phase
      normalAssertionStartDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
        (reflectiveSourceExecExactTargetNativeType result).pred ∧
      normalAssertionPopAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertion stackTop ∈ result
  pop :
    let assertion := source.state.assertions[assertionPosition]
    NormalAssertionPopDirectiveTrace scopeOwner proofOwner proofPosition
      nextProofPosition assertion.label assertion.hypotheses.length
      (stackBase + assertion.hypotheses.length) stackBase
  begin :
    let assertion := source.state.assertions[assertionPosition]
    let phase := normalAssertionBeginPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition stackBase assertionPosition assertion
    let result := fireReflectiveSourceExecFact phase
      normalAssertionBeginDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
        (reflectiveSourceExecExactTargetNativeType result).pred ∧
      normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertion.label 0 assertion.hypotheses.length
        stackBase stackBase ∈ result

/-- An admitted source assertion occurrence supplies its exact scheduled MM2
entry trace. -/
theorem normalSourceAssertionEntryDirectiveTrace_of_admitted
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition assertionPosition stackBase : Nat)
    (inBounds : assertionPosition < source.state.assertions.length) :
    NormalSourceAssertionEntryDirectiveTrace source mm2Target scopeOwner
      proofOwner proofPosition nextProofPosition assertionPosition
      stackBase := by
  have trace := admittedSourceAssertion_has_entry_trace source mm2Target
    scopeOwner proofOwner proofPosition nextProofPosition assertionPosition
    stackBase inBounds
  exact
    { assertionInBounds := inBounds
      header := trace.1
      start := ⟨trace.2.1, trace.2.2.1⟩
      pop := trace.2.2.2.1
      begin := ⟨trace.2.2.2.2.1, trace.2.2.2.2.2⟩ }

/-! ## Recursive postfix macro-traces -/

mutual

/-- Scheduled MM2 macro-trace for one source-owned proof tree, starting at
the supplied stack and proof offsets. -/
def PhaseLocalNormalMM2TreeTrace
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (target : ValidatedCalculusLanguageDef) (scopeOwner proofOwner : Atom)
    {formula : ConstantHeadedFormula}
    (tree : SourceGeneratedProvesTree source.state.toSourcePrefix target
      formula)
    (stackBase proofOffset : Nat) : Prop :=
  match tree with
  | .active hypothesis _ =>
      hypothesisLookupRow scopeOwner hypothesis ∈
          (transformNormalScope source mm2Target scopeOwner).lookupRows ∧
        let phase := normalHypothesisPhaseSpace scopeOwner proofOwner
          proofOffset (proofOffset + 1) stackBase (stackBase + 1) hypothesis
        let result := fireReflectiveSourceExecFact phase
          normalHypothesisDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
            (reflectiveSourceExecExactTargetNativeType result).pred ∧
          normalHypothesisStackAtom proofOwner stackBase hypothesis
            proofOffset ∈ result
  | .assertion (assertion := assertion) (actuals := actuals)
      (substitution := substitution) _hmember _node children =>
      PhaseLocalNormalMM2ForestTrace source mm2Target target scopeOwner
          proofOwner children stackBase proofOffset ∧
        assertion.hypotheses.length = actuals.length ∧
        ∃ assertionPosition : Nat,
          ∃ _inBounds : assertionPosition < source.state.assertions.length,
          source.state.assertions[assertionPosition] = assertion ∧
          NormalSourceAssertionEntryDirectiveTrace source mm2Target scopeOwner
            proofOwner (proofOffset + children.labels.length)
            (proofOffset + children.labels.length + 1) assertionPosition
            stackBase ∧
          NormalAssertionApplicationDirectiveTrace
            source.state.toSourcePrefix.toProjection.callerFrame
            assertion.toProjectionView actuals formula children.toRuntime
            scopeOwner proofOwner (proofOffset + children.labels.length)
            (proofOffset + children.labels.length + 1) stackBase proofOffset
            substitution

/-- Scheduled MM2 macro-traces for an ordered source-owned proof forest.  The
stack advances by one root per tree while the proof offset advances by the
exact length of each tree's postfix label interval. -/
def PhaseLocalNormalMM2ForestTrace
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (target : ValidatedCalculusLanguageDef) (scopeOwner proofOwner : Atom)
    {formulas : List ConstantHeadedFormula}
    (forest : SourceGeneratedProvesForest source.state.toSourcePrefix target
      formulas)
    (stackBase proofOffset : Nat) : Prop :=
  match forest with
  | .nil => True
  | .cons head tail =>
      PhaseLocalNormalMM2TreeTrace source mm2Target target scopeOwner
          proofOwner head stackBase proofOffset ∧
        PhaseLocalNormalMM2ForestTrace source mm2Target target scopeOwner
          proofOwner tail (stackBase + 1)
          (proofOffset + head.labels.length)

end

/-! ## Construction from the authored Metamath proof -/

mutual

/-- Every source-owned normal proof tree has the recursively composed
scheduled MM2 macro-trace at arbitrary stack and proof offsets. -/
theorem sourceGeneratedProvesTree_has_phaseLocalNormalMM2Trace
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (target : ValidatedCalculusLanguageDef)
    (hsource :
      calculusLanguageDefOfSourcePrefix? source.state.toSourcePrefix = some target.1)
    (scopeOwner proofOwner : Atom)
    {formula : ConstantHeadedFormula}
    (tree : SourceGeneratedProvesTree source.state.toSourcePrefix target
      formula)
    (stackBase proofOffset : Nat) :
    PhaseLocalNormalMM2TreeTrace source mm2Target target scopeOwner proofOwner
      tree stackBase proofOffset := by
  have hprojection :
      calculusLanguageDefOfProjection?
          source.state.toSourcePrefix.toProjection = some target.1 := by
    rw [← calculusLanguageDefOfSourcePrefix?_eq_runtime]
    exact hsource
  cases tree with
  | active hypothesis hmember =>
      constructor
      · change hypothesisLookupRow scopeOwner hypothesis ∈
          hypothesisLookupRows scopeOwner source.state
        apply List.mem_map.mpr
        refine ⟨hypothesis, ?_, rfl⟩
        simpa [SourceState.toSourcePrefix] using hmember
      · exact normalHypothesisPhase_inhabits_target_native_type scopeOwner
          proofOwner proofOffset (proofOffset + 1) stackBase
          (stackBase + 1) hypothesis
  | @assertion assertion actuals result substitution hmember node children =>
      have runtimeMember :
          assertion.toProjectionView ∈
            source.state.toSourcePrefix.toProjection.assertions :=
        List.mem_map.mpr ⟨assertion, hmember, rfl⟩
      have instances :=
        (assertionRuleApplication_iff_instances
          source.state.toSourcePrefix.toProjection target hprojection
          runtimeMember).mp node.application
      obtain ⟨hypothesisInstances, _resultTypecode⟩ := instances
      have arity : assertion.hypotheses.length = actuals.length :=
        hypothesisInstances.lengths
      obtain ⟨assertionPosition, inBounds, atPosition⟩ :=
        List.mem_iff_getElem.mp
          (show assertion ∈ source.state.assertions by
            simpa [SourceState.toSourcePrefix] using hmember)
      refine ⟨sourceGeneratedProvesForest_has_phaseLocalNormalMM2Trace source
        mm2Target target hsource scopeOwner proofOwner children stackBase
        proofOffset, arity,
        assertionPosition, inBounds, atPosition, ?_, ?_⟩
      · exact normalSourceAssertionEntryDirectiveTrace_of_admitted source
          mm2Target scopeOwner proofOwner
          (proofOffset + children.labels.length)
          (proofOffset + children.labels.length + 1) assertionPosition
          stackBase inBounds
      · exact
          _root_.Mettapedia.Languages.Metamath.MM2NormalStackCorrespondence.GeneratedAssertionNode.has_complete_mm2_application_trace
          source.state.toSourcePrefix.toProjection target hprojection
          runtimeMember node children.toRuntime scopeOwner proofOwner
          (proofOffset + children.labels.length)
          (proofOffset + children.labels.length + 1) stackBase proofOffset

/-- Every ordered source-owned proof forest has the corresponding sequence of
scheduled MM2 macro-traces. -/
theorem sourceGeneratedProvesForest_has_phaseLocalNormalMM2Trace
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (target : ValidatedCalculusLanguageDef)
    (hsource :
      calculusLanguageDefOfSourcePrefix? source.state.toSourcePrefix = some target.1)
    (scopeOwner proofOwner : Atom)
    {formulas : List ConstantHeadedFormula}
    (forest : SourceGeneratedProvesForest source.state.toSourcePrefix target
      formulas)
    (stackBase proofOffset : Nat) :
    PhaseLocalNormalMM2ForestTrace source mm2Target target scopeOwner proofOwner
      forest stackBase proofOffset := by
  cases forest with
  | nil => trivial
  | cons head tail =>
      exact ⟨sourceGeneratedProvesTree_has_phaseLocalNormalMM2Trace source
          mm2Target target hsource scopeOwner proofOwner head stackBase
          proofOffset,
        sourceGeneratedProvesForest_has_phaseLocalNormalMM2Trace source
          mm2Target target hsource scopeOwner proofOwner tail (stackBase + 1)
          (proofOffset + head.labels.length)⟩

end

/-! ## Complete normal proof and terminal observation -/

/-- A complete source-owned normal proof supplies all recursively indexed
phase-local obligations and a separately fireable terminal phase. -/
structure PhaseLocalNormalProofMM2Trace
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (target : ValidatedCalculusLanguageDef) (scopeOwner proofOwner theoremLabel : Atom)
    {formula : ConstantHeadedFormula}
    (tree : SourceGeneratedProvesTree source.state.toSourcePrefix target
      formula) : Prop where
  proof : PhaseLocalNormalMM2TreeTrace source mm2Target target scopeOwner
    proofOwner tree 0 0
  terminal :
    let runtimeTree := tree.toRuntime
    let occurrence := generatedRootOccurrenceAtom 0 runtimeTree
    let phase := normalAcceptPhaseSpace scopeOwner proofOwner theoremLabel
      (formulaAtom formula) occurrence runtimeTree.labels.length
    let result := fireReflectiveSourceExecFact phase normalAcceptDirective
    normalStackAtomWithOccurrence proofOwner 0 formula occurrence ∈ phase ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveSourceExecGSLT .leaveInert)).satisfies phase
          (reflectiveSourceExecExactTargetNativeType result).pred ∧
        normalAcceptedAtom scopeOwner proofOwner theoremLabel
          (formulaAtom formula) occurrence ∈ result

/-- Arbitrary source-owned normal proofs determine every local MM2 phase and
the exact occurrence-sensitive terminal phase.  This theorem does not connect
those phases into one reachable target run. -/
theorem sourceGeneratedProvesTree_has_complete_phaseLocalNormalMM2Trace
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (target : ValidatedCalculusLanguageDef)
    (hsource :
      calculusLanguageDefOfSourcePrefix? source.state.toSourcePrefix = some target.1)
    (scopeOwner proofOwner theoremLabel : Atom)
    {formula : ConstantHeadedFormula}
    (tree : SourceGeneratedProvesTree source.state.toSourcePrefix target
      formula) :
    PhaseLocalNormalProofMM2Trace source mm2Target target scopeOwner proofOwner
      theoremLabel tree := by
  refine
    { proof := sourceGeneratedProvesTree_has_phaseLocalNormalMM2Trace source
        mm2Target target hsource scopeOwner proofOwner tree 0 0
      terminal := ?_ }
  exact
    _root_.Mettapedia.Languages.Metamath.MM2NormalStackCorrespondence.GeneratedProvesTree.terminal_inhabits_mm2_target_native_type
      tree.toRuntime scopeOwner proofOwner theoremLabel

/-! ## Independent verified-fold comparison -/

/-- One exact source proof tree, its submitted postfix labels, and the
phase-local MM2 obligations derived from that tree.  The verified runtime fold
is deliberately not stored in this witness. -/
structure PhaseLocalNormalProofMM2FoldWitness
    (source : AdmittedSourceScope) (mm2Target : MM2Target)
    (target : ValidatedCalculusLanguageDef) (scopeOwner proofOwner theoremLabel : Atom)
    (formula : ConstantHeadedFormula) (proofLabels : List String) : Type where
  tree : SourceGeneratedProvesTree source.state.toSourcePrefix target formula
  labels_eq : tree.labels = proofLabels
  trace : PhaseLocalNormalProofMM2Trace source mm2Target target scopeOwner
    proofOwner theoremLabel tree

/-- The independently verified normal-label fold accepts exactly when there
is a retained source proof occurrence with the same submitted postfix labels
and its phase-local MM2 obligations.  The reverse implication reads the stored
source tree, not an MM2 verdict; this is a comparison edge and is not the
assembled target-to-source reflection theorem. -/
theorem normalFold_accepts_iff_sourceTree_with_phaseLocalMM2Trace
    (db : RuntimeDB) (source : AdmittedSourceScope)
    (mm2Target : MM2Target) (target : ValidatedCalculusLanguageDef)
    (base : RuntimeProofState) (scopeOwner proofOwner theoremLabel : Atom)
    (formula : ConstantHeadedFormula) (proofLabels : List String)
    (hsource :
      calculusLanguageDefOfSourcePrefix? source.state.toSourcePrefix = some target.1)
    (hproject :
      projectPrefix? db = some source.state.toSourcePrefix.toProjection)
    (hbaseStack : base.stack = #[]) :
    proofLabels.foldlM (fun state label => db.stepNormal state label) base =
        .ok (base.push formula.toRuntime) ↔
      Nonempty
        (PhaseLocalNormalProofMM2FoldWitness source mm2Target target scopeOwner
          proofOwner theoremLabel formula proofLabels) := by
  rw [normalFold_accepts_iff_exactSourceTree db
    source.state.toSourcePrefix target base formula proofLabels hsource
    hproject hbaseStack]
  constructor
  · rintro ⟨⟨tree, labels_eq⟩⟩
    exact ⟨
      { tree := tree
        labels_eq := labels_eq
        trace :=
          sourceGeneratedProvesTree_has_complete_phaseLocalNormalMM2Trace
            source mm2Target target hsource scopeOwner proofOwner theoremLabel
            tree }⟩
  · rintro ⟨witness⟩
    exact ⟨⟨witness.tree, witness.labels_eq⟩⟩

#print axioms normalSourceAssertionEntryDirectiveTrace_of_admitted
#print axioms sourceGeneratedProvesTree_has_phaseLocalNormalMM2Trace
#print axioms sourceGeneratedProvesForest_has_phaseLocalNormalMM2Trace
#print axioms sourceGeneratedProvesTree_has_complete_phaseLocalNormalMM2Trace
#print axioms normalFold_accepts_iff_sourceTree_with_phaseLocalMM2Trace

end Mettapedia.Languages.Metamath.MM2NormalProofCorrespondence
