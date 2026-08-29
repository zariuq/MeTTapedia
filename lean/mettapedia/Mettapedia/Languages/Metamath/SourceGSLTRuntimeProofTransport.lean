import Mettapedia.Languages.Metamath.SourceGSLTRuntimeCoEvolution
import Mettapedia.Languages.Metamath.SourceInferenceExecution

open Mettapedia.GSLT.LanguageDef

/-!
# Proof-tree transport from the canonical runtime prefix

The runtime object map forgets declaration order, so `RuntimeDBAgrees` uses a
label-sorted `runtimePrefix`.  Source theorem occurrences remain indexed by
the authored `SourceState.toSourcePrefix`.  This module transports proof trees
between those representations by reflecting each generated assertion node to
its order-independent application semantics and rebuilding it in the authored
presentation.  No rule-table equality or unsafe cast is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceGSLTRuntimeProofTransport

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeStateAgreement
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceInferenceProjection

/-- Rebuild one local assertion-rule witness in the authored presentation.
The source and runtime projections have the same application semantics even
though their assertion lists use different orders.  Centralizing this choice
keeps proof-tree and compressed-DAG transport definitionally coherent. -/
noncomputable def runtimePrefixAssertionNodeToSource
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedCalculusLanguageDef}
    (runtimePresentation :
      calculusLanguageDefOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      calculusLanguageDefOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    {assertion : SourceAssertion}
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (member : assertion ∈ (runtimePrefix state).assertions)
    (node : GeneratedAssertionNode (runtimePrefix state).toProjection
      runtimeTarget assertion.toProjectionView actuals result substitution) :
    Σ sourceSubstitution : FiniteSubstitution,
      GeneratedAssertionNode state.toSourcePrefix.toProjection sourceTarget
        assertion.toProjectionView actuals result sourceSubstitution := by
  have runtimeProjection :
      calculusLanguageDefOfProjection? (runtimePrefix state).toProjection =
        some runtimeTarget.1 := by
    rw [← calculusLanguageDefOfSourcePrefix?_eq_runtime]
    exact runtimePresentation
  have sourceProjection :
      calculusLanguageDefOfProjection? state.toSourcePrefix.toProjection =
        some sourceTarget.1 := by
    rw [← calculusLanguageDefOfSourcePrefix?_eq_runtime]
    exact sourcePresentation
  have sourceMember : assertion ∈ state.assertions :=
    (runtimePrefix_assertion_mem_iff state assertion).mp member
  have runtimeProjectionMember :
      assertion.toProjectionView ∈
        (runtimePrefix state).toProjection.assertions :=
    List.mem_map_of_mem member
  have sourceProjectionMember :
      assertion.toProjectionView ∈
        state.toSourcePrefix.toProjection.assertions :=
    List.mem_map_of_mem sourceMember
  have semantics :=
    (generatedAssertionNode_nonempty_iff_semantics
      (runtimePrefix state).toProjection runtimeTarget runtimeProjection
      runtimeProjectionMember actuals result).mp
        ⟨⟨substitution, node⟩⟩
  exact Classical.choice
    ((generatedAssertionNode_nonempty_iff_semantics
      state.toSourcePrefix.toProjection sourceTarget sourceProjection
      sourceProjectionMember actuals result).mpr semantics)

mutual

/-- Rebuild a proof-occurrence tree over the authored prefix from the
canonical, label-sorted runtime view.  Local assertion applications are
transported through their independent semantics, not by equating rule lists. -/
noncomputable def runtimePrefixTreeToSource
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedCalculusLanguageDef}
    (runtimePresentation :
      calculusLanguageDefOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      calculusLanguageDefOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    {formula : ConstantHeadedFormula} :
    SourceGeneratedProvesTree (runtimePrefix state) runtimeTarget formula →
      SourceGeneratedProvesTree state.toSourcePrefix sourceTarget formula
  | .active hypothesis member =>
      .active hypothesis (by
        simpa [runtimePrefix, SourceState.toSourcePrefix] using member)
  | @SourceGeneratedProvesTree.assertion _ _ assertion actuals result
      substitution member node children => by
      have sourceMember : assertion ∈ state.assertions :=
        (runtimePrefix_assertion_mem_iff state assertion).mp member
      let sourceNode := runtimePrefixAssertionNodeToSource
        runtimePresentation sourcePresentation member node
      exact .assertion sourceMember sourceNode.2
        (runtimePrefixForestToSource runtimePresentation sourcePresentation
          children)

/-- Forest counterpart of `runtimePrefixTreeToSource`. -/
noncomputable def runtimePrefixForestToSource
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedCalculusLanguageDef}
    (runtimePresentation :
      calculusLanguageDefOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      calculusLanguageDefOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    {formulas : List ConstantHeadedFormula} :
    SourceGeneratedProvesForest (runtimePrefix state) runtimeTarget formulas →
      SourceGeneratedProvesForest state.toSourcePrefix sourceTarget formulas
  | .nil => .nil
  | .cons head tail =>
      .cons
        (runtimePrefixTreeToSource runtimePresentation sourcePresentation head)
        (runtimePrefixForestToSource runtimePresentation sourcePresentation
          tail)

end

mutual

/-- Canonicalization transport preserves the submitted postfix label list. -/
theorem runtimePrefixTreeToSource_labels
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedCalculusLanguageDef}
    (runtimePresentation :
      calculusLanguageDefOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      calculusLanguageDefOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    {formula : ConstantHeadedFormula}
    (tree : SourceGeneratedProvesTree
      (runtimePrefix state) runtimeTarget formula) :
    (runtimePrefixTreeToSource runtimePresentation sourcePresentation
      tree).labels = tree.labels := by
  cases tree with
  | active hypothesis member =>
      simp [runtimePrefixTreeToSource,
        SourceGeneratedProvesTree.labels]
  | assertion member node children =>
      simp [runtimePrefixTreeToSource,
        SourceGeneratedProvesTree.labels,
        runtimePrefixForestToSource_labels runtimePresentation
          sourcePresentation children]

/-- Forest label concatenation is likewise preserved. -/
theorem runtimePrefixForestToSource_labels
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedCalculusLanguageDef}
    (runtimePresentation :
      calculusLanguageDefOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      calculusLanguageDefOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    {formulas : List ConstantHeadedFormula}
    (forest : SourceGeneratedProvesForest
      (runtimePrefix state) runtimeTarget formulas) :
    (runtimePrefixForestToSource runtimePresentation sourcePresentation
      forest).labels = forest.labels := by
  cases forest with
  | nil => rfl
  | cons head tail =>
      simp [runtimePrefixForestToSource,
        SourceGeneratedProvesForest.labels,
        runtimePrefixTreeToSource_labels runtimePresentation
          sourcePresentation head,
        runtimePrefixForestToSource_labels runtimePresentation
          sourcePresentation tail]

end


/-- Negative calibration: canonicalization cannot turn a different label
sequence into the transported proof's labels. -/
theorem runtimePrefixTreeToSource_labels_ne
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedCalculusLanguageDef}
    (runtimePresentation :
      calculusLanguageDefOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      calculusLanguageDefOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    {formula : ConstantHeadedFormula}
    (tree : SourceGeneratedProvesTree
      (runtimePrefix state) runtimeTarget formula)
    (labels : List String) (different : tree.labels ≠ labels) :
    (runtimePrefixTreeToSource runtimePresentation sourcePresentation
      tree).labels ≠ labels := by
  rw [runtimePrefixTreeToSource_labels runtimePresentation
    sourcePresentation tree]
  exact different

end Mettapedia.Languages.Metamath.SourceGSLTRuntimeProofTransport
