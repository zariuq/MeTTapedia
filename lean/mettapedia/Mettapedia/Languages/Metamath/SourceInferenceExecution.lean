import Mettapedia.Languages.Metamath.SourceInferenceProjection
import Mettapedia.Languages.Metamath.InferenceNormalProvabilitySoundness

/-!
# Source-owned Metamath proof occurrences and verified execution

This file moves the exact normal-proof execution theorem from a runtime-owned
projection to the source-owned prefix carrier.  Source proof trees retain the
authored hypothesis and assertion occurrences.  Their translation into the
existing generated checker tree is total, and every generated checker tree
over the translated prefix reflects back to a source tree.

Consequently, `mm-lean4` normal-proof execution accepts exactly the postfix
labels of a source-owned proof-occurrence tree whenever the runtime database
is proved to represent that source prefix.  Constructing that prefix from the
raw source derivation remains a separate composition theorem.
-/

namespace Mettapedia.Languages.Metamath.SourceInferenceExecution

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
open Mettapedia.Languages.Metamath.InferenceNormalFoldReflection
open Mettapedia.Languages.Metamath.InferenceNormalProvabilitySoundness
open Mettapedia.Languages.Metamath.SourceInferenceProjection

/-! ## Source-owned proof-occurrence trees -/

mutual

/-- Proof-relevant occurrence tree indexed by one source-owned scoped prefix. -/
inductive SourceGeneratedProvesTree (source : SourcePrefix)
    (target : ValidatedPresentation) : ConstantHeadedFormula → Type where
  | active (hypothesis : HypothesisView)
      (hmember : hypothesis ∈ source.activeHypotheses) :
      SourceGeneratedProvesTree source target hypothesis.formula
  | assertion {assertion : SourceAssertion}
      {actuals : List ConstantHeadedFormula}
      {result : ConstantHeadedFormula}
      {substitution : FiniteSubstitution}
      (hmember : assertion ∈ source.assertions)
      (node :
        GeneratedAssertionNode source.toProjection target
          assertion.toProjectionView actuals result substitution)
      (children : SourceGeneratedProvesForest source target actuals) :
      SourceGeneratedProvesTree source target result

/-- Ordered source-owned trees for an assertion's mandatory hypotheses. -/
inductive SourceGeneratedProvesForest (source : SourcePrefix)
    (target : ValidatedPresentation) :
    List ConstantHeadedFormula → Type where
  | nil : SourceGeneratedProvesForest source target []
  | cons {formula : ConstantHeadedFormula}
      {formulas : List ConstantHeadedFormula}
      (head : SourceGeneratedProvesTree source target formula)
      (tail : SourceGeneratedProvesForest source target formulas) :
      SourceGeneratedProvesForest source target (formula :: formulas)

end

/-! ## Translation into the verified generated checker -/

mutual

def SourceGeneratedProvesTree.toRuntime
    {source : SourcePrefix} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula} :
    SourceGeneratedProvesTree source target formula →
      GeneratedProvesTree source.toProjection target formula
  | .active hypothesis hmember =>
      .active hypothesis hmember
  | .assertion (assertion := assertion) hmember node children =>
      .assertion
        (List.mem_map.mpr
          ⟨assertion, hmember, rfl⟩)
        node children.toRuntime

def SourceGeneratedProvesForest.toRuntime
    {source : SourcePrefix} {target : ValidatedPresentation}
    {formulas : List ConstantHeadedFormula} :
    SourceGeneratedProvesForest source target formulas →
      GeneratedProvesForest source.toProjection target formulas
  | .nil => .nil
  | .cons head tail => .cons head.toRuntime tail.toRuntime

end

/-! ## Exact authored labels -/

mutual

def SourceGeneratedProvesTree.labels
    {source : SourcePrefix} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula} :
    SourceGeneratedProvesTree source target formula → List String
  | .active hypothesis _ => [hypothesis.label]
  | .assertion (assertion := assertion) _ _ children =>
      children.labels ++ [assertion.label]

def SourceGeneratedProvesForest.labels
    {source : SourcePrefix} {target : ValidatedPresentation}
    {formulas : List ConstantHeadedFormula} :
    SourceGeneratedProvesForest source target formulas → List String
  | .nil => []
  | .cons head tail => head.labels ++ tail.labels

end

mutual

@[simp] theorem SourceGeneratedProvesTree.labels_toRuntime
    {source : SourcePrefix} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (tree : SourceGeneratedProvesTree source target formula) :
    tree.toRuntime.labels = tree.labels := by
  cases tree with
  | active => rfl
  | assertion hmember node children =>
      simp [SourceGeneratedProvesTree.toRuntime,
        SourceGeneratedProvesTree.labels,
        GeneratedProvesTree.labels,
        SourceAssertion.toProjectionView,
        children.labels_toRuntime]

@[simp] theorem SourceGeneratedProvesForest.labels_toRuntime
    {source : SourcePrefix} {target : ValidatedPresentation}
    {formulas : List ConstantHeadedFormula}
    (forest : SourceGeneratedProvesForest source target formulas) :
    forest.toRuntime.labels = forest.labels := by
  cases forest with
  | nil => rfl
  | cons head tail =>
      simp [SourceGeneratedProvesForest.toRuntime,
        SourceGeneratedProvesForest.labels,
        GeneratedProvesForest.labels,
        head.labels_toRuntime, tail.labels_toRuntime]

end

/-! ## Reflection back to source occurrences -/

mutual

theorem runtimeTree_exists_source
    {source : SourcePrefix} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree source.toProjection target formula) :
    ∃ sourceTree : SourceGeneratedProvesTree source target formula,
      sourceTree.toRuntime = tree := by
  cases tree with
  | active hypothesis hmember =>
      exact ⟨.active hypothesis hmember, rfl⟩
  | @assertion assertion actuals result substitution hmember node children =>
      rcases List.mem_map.mp hmember with
        ⟨sourceAssertion, hsourceMember, hsourceAssertion⟩
      subst assertion
      rcases runtimeForest_exists_source children with
        ⟨sourceChildren, hsourceChildren⟩
      refine
        ⟨.assertion hsourceMember node sourceChildren, ?_⟩
      simp [SourceGeneratedProvesTree.toRuntime, hsourceChildren]

theorem runtimeForest_exists_source
    {source : SourcePrefix} {target : ValidatedPresentation}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest source.toProjection target formulas) :
    ∃ sourceForest : SourceGeneratedProvesForest source target formulas,
      sourceForest.toRuntime = forest := by
  cases forest with
  | nil => exact ⟨.nil, rfl⟩
  | cons head tail =>
      rcases runtimeTree_exists_source head with ⟨sourceHead, hsourceHead⟩
      rcases runtimeForest_exists_source tail with ⟨sourceTail, hsourceTail⟩
      exact ⟨.cons sourceHead sourceTail, by
        simp [SourceGeneratedProvesForest.toRuntime,
          hsourceHead, hsourceTail]⟩

end

/-! ## Exact implementation/reflection theorem -/

/-- Normal-proof execution in the verified implementation accepts exactly the
labels of a source-owned proof-occurrence tree. -/
theorem normalFold_accepts_iff_exactSourceTree
    (db : RuntimeDB) (source : SourcePrefix)
    (target : ValidatedPresentation) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula) (labels : List String)
    (hsource :
      presentationOfSourcePrefix? source = some target.1)
    (hproject : projectPrefix? db = some source.toProjection)
    (hbaseStack : base.stack = #[]) :
    labels.foldlM (fun state label => db.stepNormal state label) base =
        .ok (base.push formula.toRuntime) ↔
      Nonempty
        { tree : SourceGeneratedProvesTree source target formula //
          tree.labels = labels } := by
  have hruntime :
      presentationOfProjection? source.toProjection = some target.1 := by
    rw [← presentationOfSourcePrefix?_eq_runtime]
    exact hsource
  rw [normalFold_accepts_iff_exactGeneratedTree
    db source.toProjection target base formula labels
    hruntime hproject hbaseStack]
  constructor
  · rintro ⟨⟨tree, hlabels⟩⟩
    rcases runtimeTree_exists_source tree with
      ⟨sourceTree, hsourceTree⟩
    refine ⟨⟨sourceTree, ?_⟩⟩
    calc
      sourceTree.labels = sourceTree.toRuntime.labels := by
        symm
        exact sourceTree.labels_toRuntime
      _ = tree.labels := congrArg GeneratedProvesTree.labels hsourceTree
      _ = labels := hlabels
  · rintro ⟨⟨sourceTree, hlabels⟩⟩
    exact ⟨⟨sourceTree.toRuntime, by
      rw [sourceTree.labels_toRuntime]
      exact hlabels⟩⟩

/-! ## Declarative/operational soundness -/

/-- Every source-owned proof-occurrence tree is provable in the operational
Metamath semantics represented by the same verified runtime database. -/
theorem sourceTree_to_operationalProvable
    (db : RuntimeDB) (source : SourcePrefix)
    (target : ValidatedPresentation) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (tree : SourceGeneratedProvesTree source target formula)
    (Γ : OperationalDatabase) (fr : OperationalFrame)
    (hsource :
      presentationOfSourcePrefix? source = some target.1)
    (hproject : projectPrefix? db = some source.toProjection)
    (hdatabase : Metamath.Kernel.toDatabase db = some Γ)
    (hframe : Metamath.Kernel.toFrame db db.frame = some fr)
    (hbaseStack : base.stack = #[]) :
    OperationalProvable Γ fr
      (Metamath.Kernel.toExpr formula.toRuntime) := by
  have hruntime :
      presentationOfProjection? source.toProjection = some target.1 := by
    rw [← presentationOfSourcePrefix?_eq_runtime]
    exact hsource
  exact generatedProvesTree_to_operationalProvable
    db source.toProjection target base formula tree.toRuntime Γ fr
    hruntime hproject hdatabase hframe hbaseStack

/-- A source-owned proof occurrence always contributes at least one authored
normal-proof label. -/
theorem SourceGeneratedProvesTree.labels_ne_nil
    {source : SourcePrefix} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (tree : SourceGeneratedProvesTree source target formula) :
    tree.labels ≠ [] := by
  cases tree <;> simp [SourceGeneratedProvesTree.labels]

end Mettapedia.Languages.Metamath.SourceInferenceExecution
