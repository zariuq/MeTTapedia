import Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
import Mettapedia.Languages.Metamath.InferencePreparedAssertionStepReceipt

/-!
# Proof-relevant operational receipts for complete generated proofs

The existing generated-proof executor proves the exact final verifier state.
This module retains the evidence occurrence by occurrence.  Its recursive
receipt shape is indexed by the existing `GeneratedProvesTree`; it is not a
second proof calculus or evaluator.

Active-hypothesis leaves retain their exact live step and frame invariants.
Assertion nodes retain the prepared assertion receipt after the recursively
ordered premise forest.  Repeated equal labels therefore remain distinct
receipt positions, while complete execution is still discharged by the
existing executor.
-/

namespace Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceHypothesisStepAgreement
open Mettapedia.Languages.Metamath.InferencePreparedAssertionStepReceipt

/-! ## Leaf receipts and exact intermediate states -/

/-- The exact live operational occurrence of one projected active hypothesis. -/
structure ActiveHypothesisStepReceipt
    (db : RuntimeDB) (projection : PrefixProjection)
    (hypothesis : HypothesisView) (pr : RuntimeProofState) : Type where
  projected : projectPrefix? db = some projection
  member : hypothesis ∈ projection.activeHypotheses
  inputStackRespects :
    Metamath.Kernel.StackRespectsFrame db db.frame pr.stack
  stepNormal :
    db.stepNormal pr hypothesis.label =
      .ok (pr.push hypothesis.formula.toRuntime)
  outputStackRespects :
    Metamath.Kernel.StackRespectsFrame db db.frame
      (pr.push hypothesis.formula.toRuntime).stack

/-- Construct an active-hypothesis receipt directly from projection membership
and the incoming stack invariant. -/
def activeHypothesisReceipt
    (db : RuntimeDB) (projection : PrefixProjection)
    (hypothesis : HypothesisView) (pr : RuntimeProofState)
    (projected : projectPrefix? db = some projection)
    (member : hypothesis ∈ projection.activeHypotheses)
    (inputStackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    ActiveHypothesisStepReceipt db projection hypothesis pr where
  projected := projected
  member := member
  inputStackRespects := inputStackRespects
  stepNormal := activeHypothesis_stepNormal db projection hypothesis pr
    projected member
  outputStackRespects := activeHypothesis_step_stackRespectsFrame db projection
    hypothesis pr projected member inputStackRespects

/-- The exact proof state after an ordered premise forest has pushed all of
its indexed formulas. -/
def forestResultState (pr : RuntimeProofState)
    (formulas : List ConstantHeadedFormula) : RuntimeProofState :=
  { pr with stack := pr.stack ++ runtimeFormulaArray formulas }

/-- Once the generated node fixes the premise count, consuming the complete
premise suffix is exactly the ordinary one-result push. -/
theorem assertionStepResult_forestResultState
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation)
    (presentation : presentationOfProjection? projection = some target.1)
    (projected : projectPrefix? db = some projection)
    (assertion : AssertionView)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (substitution : FiniteSubstitution)
    (member : assertion ∈ projection.assertions)
    (node : GeneratedAssertionNode projection target assertion actuals result
      substitution)
    (pr : RuntimeProofState) :
    assertionStepResult (forestResultState pr actuals) assertion result =
      pr.push result.toRuntime := by
  have actualLength : actuals.length = assertion.frame.hyps.size :=
    generatedAssertionNode_actuals_length_eq_frameHyps db projection target
      presentation assertion actuals result substitution node projected member
  have offset :
      (forestResultState pr actuals).stack.size -
          assertion.frame.hyps.size = pr.stack.size := by
    simp [forestResultState, Array.size_append, actualLength]
  have shrink :
      (forestResultState pr actuals).stack.shrink
          ((forestResultState pr actuals).stack.size -
            assertion.frame.hyps.size) = pr.stack := by
    rw [offset]
    exact shrink_append_prefix pr.stack (runtimeFormulaArray actuals)
  unfold assertionStepResult
  rw [shrink]
  rfl

/-! ## The tree-indexed receipt shape -/

mutual

/-- Exactly one operational receipt at every occurrence of a generated proof
tree, with assertion receipts placed after their ordered premise receipts. -/
def GeneratedProvesTree.receiptShape
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    (db : RuntimeDB) (pr : RuntimeProofState) : Type :=
  match tree with
  | .active hypothesis _ =>
      ActiveHypothesisStepReceipt db projection hypothesis pr
  | .assertion (assertion := assertion) (actuals := actuals)
      (result := result) (substitution := substitution) _ _ children =>
      children.receiptShape db pr ×
        PreparedAssertionStepReceipt db projection target assertion
          (forestResultState pr actuals) actuals result substitution

/-- Premise-order receipt shape.  The tail begins at the exact state produced
by the head, so an occurrence cannot be silently reordered or omitted. -/
def GeneratedProvesForest.receiptShape
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas)
    (db : RuntimeDB) (pr : RuntimeProofState) : Type :=
  match forest with
  | .nil => PUnit
  | .cons (formula := formula) head tail =>
      head.receiptShape db pr ×
        tail.receiptShape db (pr.push formula.toRuntime)

end

/-! ## Constructive receipt assembly -/

mutual

/-- Assemble the receipt shape for every tree occurrence.  The already-proved
recursive executor supplies only the next frame invariant; no second evaluator
or post-hoc checker is introduced. -/
def GeneratedProvesTree.buildReceipt
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    (db : RuntimeDB)
    (presentation : presentationOfProjection? projection = some target.1)
    (projected : projectPrefix? db = some projection)
    (pr : RuntimeProofState)
    (inputStackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    tree.receiptShape db pr :=
  match tree with
  | .active hypothesis member =>
      activeHypothesisReceipt db projection hypothesis pr projected member
        inputStackRespects
  | .assertion (assertion := assertion) (actuals := actuals)
      (result := result) (substitution := substitution)
      member node children => by
      let childrenReceipt := children.buildReceipt db presentation projected pr
        inputStackRespects
      have childrenExecution :=
        children.execute db presentation projected pr inputStackRespects
      have actualLength : actuals.length = assertion.frame.hyps.size :=
        generatedAssertionNode_actuals_length_eq_frameHyps db projection target
          presentation assertion actuals result substitution node projected
            member
      have stackEnough :
          assertion.frame.hyps.size ≤
            (forestResultState pr actuals).stack.size := by
        simp [forestResultState, Array.size_append, actualLength]
      have window :
          (forestResultState pr actuals).stack.extract
              ((forestResultState pr actuals).stack.size -
                assertion.frame.hyps.size)
              (forestResultState pr actuals).stack.size =
            runtimeFormulaArray actuals := by
        have offset :
            (forestResultState pr actuals).stack.size -
                assertion.frame.hyps.size = pr.stack.size := by
          simp [forestResultState, Array.size_append, actualLength]
        rw [offset]
        exact extract_append_suffix pr.stack (runtimeFormulaArray actuals)
      let parentReceipt := ofGeneratedNode db projection target assertion
        (forestResultState pr actuals) actuals result substitution projected
          presentation member node stackEnough window childrenExecution.2
      exact ⟨childrenReceipt, parentReceipt⟩

/-- Assemble ordered premise receipts, threading the exact intermediate state
and frame invariant from each head occurrence to its tail. -/
def GeneratedProvesForest.buildReceipt
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas)
    (db : RuntimeDB)
    (presentation : presentationOfProjection? projection = some target.1)
    (projected : projectPrefix? db = some projection)
    (pr : RuntimeProofState)
    (inputStackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    forest.receiptShape db pr :=
  match forest with
  | .nil => PUnit.unit
  | .cons (formula := formula) head tail =>
      let headReceipt := head.buildReceipt db presentation projected pr
        inputStackRespects
      let headExecution :=
        head.execute db presentation projected pr inputStackRespects
      let tailReceipt := tail.buildReceipt db presentation projected
        (pr.push formula.toRuntime) headExecution.2
      ⟨headReceipt, tailReceipt⟩

end

/-! ## Receipt observations and complete execution -/

mutual

/-- Read authored labels from the retained receipt occurrences themselves. -/
def GeneratedProvesTree.receiptLabels
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    {db : RuntimeDB} {pr : RuntimeProofState} :
    tree.receiptShape db pr → List String :=
  match tree with
  | .active hypothesis _ => fun _ => [hypothesis.label]
  | .assertion (assertion := assertion) _ _ children =>
      fun receipts => children.receiptLabels receipts.1 ++ [assertion.label]

/-- Read premise labels from the receipt forest in exact occurrence order. -/
def GeneratedProvesForest.receiptLabels
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas)
    {db : RuntimeDB} {pr : RuntimeProofState} :
    forest.receiptShape db pr → List String :=
  match forest with
  | .nil => fun _ => []
  | .cons head tail => fun receipts =>
      head.receiptLabels receipts.1 ++ tail.receiptLabels receipts.2

end

mutual

theorem GeneratedProvesTree.receiptLabels_eq_labels
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    {db : RuntimeDB} {pr : RuntimeProofState}
    (receipts : tree.receiptShape db pr) :
    tree.receiptLabels receipts = tree.labels := by
  cases tree with
  | active => rfl
  | assertion member node children =>
      simp only [GeneratedProvesTree.receiptLabels,
        GeneratedProvesTree.labels]
      rw [children.receiptLabels_eq_labels receipts.1]

theorem GeneratedProvesForest.receiptLabels_eq_labels
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas)
    {db : RuntimeDB} {pr : RuntimeProofState}
    (receipts : forest.receiptShape db pr) :
    forest.receiptLabels receipts = forest.labels := by
  cases forest with
  | nil => rfl
  | cons head tail =>
      simp only [GeneratedProvesForest.receiptLabels,
        GeneratedProvesForest.labels]
      rw [head.receiptLabels_eq_labels receipts.1,
        tail.receiptLabels_eq_labels receipts.2]

end

/-- Complete proof execution together with the receipt at every exact tree
occurrence.  `finalState_eq` prevents endpoint-only or wrong-state receipts. -/
structure GeneratedProvesExecutionReceipt
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    (db : RuntimeDB) (pr finalState : RuntimeProofState) : Type where
  occurrences : tree.receiptShape db pr
  inputStackRespects :
    Metamath.Kernel.StackRespectsFrame db db.frame pr.stack
  execution :
    tree.labels.foldlM (fun state label => db.stepNormal state label) pr =
      .ok finalState
  finalState_eq : finalState = pr.push formula.toRuntime
  outputStackRespects :
    Metamath.Kernel.StackRespectsFrame db db.frame finalState.stack

/-- Construct the complete receipt at the only possible final state. -/
def GeneratedProvesTree.executionReceipt
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    (db : RuntimeDB)
    (presentation : presentationOfProjection? projection = some target.1)
    (projected : projectPrefix? db = some projection)
    (pr : RuntimeProofState)
    (inputStackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    GeneratedProvesExecutionReceipt tree db pr
      (pr.push formula.toRuntime) := by
  have executed := tree.execute db presentation projected pr inputStackRespects
  exact
    { occurrences := tree.buildReceipt db presentation projected pr
        inputStackRespects
      inputStackRespects := inputStackRespects
      execution := executed.1
      finalState_eq := rfl
      outputStackRespects := executed.2 }

/-! ## Positive and negative controls -/

/-- A repeated active-hypothesis occurrence remains two receipt positions even
when both source labels and formulas are definitionally equal. -/
def duplicateActiveForest
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hypothesis : HypothesisView)
    (member : hypothesis ∈ projection.activeHypotheses) :
    GeneratedProvesForest projection target
      [hypothesis.formula, hypothesis.formula] :=
  .cons (.active hypothesis member)
    (.cons (.active hypothesis member) .nil)

theorem duplicateActiveForest_receiptLabels
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hypothesis : HypothesisView)
    (member : hypothesis ∈ projection.activeHypotheses)
    {db : RuntimeDB} {pr : RuntimeProofState}
    (receipts :
      (duplicateActiveForest (target := target) hypothesis member).receiptShape
        db pr) :
    (duplicateActiveForest (target := target) hypothesis member).receiptLabels
        receipts = [hypothesis.label, hypothesis.label] := by
  rfl

/-- A complete receipt cannot name a final proof state different from the
tree-indexed result. -/
theorem no_executionReceipt_at_wrong_finalState
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    (db : RuntimeDB) (pr wrong : RuntimeProofState)
    (wrong_ne : wrong ≠ pr.push formula.toRuntime) :
    ¬ Nonempty (GeneratedProvesExecutionReceipt tree db pr wrong) := by
  rintro ⟨receipt⟩
  exact wrong_ne receipt.finalState_eq

/-- A leaf receipt cannot be fabricated when its exact output violates the
caller-frame invariant. -/
theorem no_activeReceipt_of_bad_outputStack
    (db : RuntimeDB) (projection : PrefixProjection)
    (hypothesis : HypothesisView) (pr : RuntimeProofState)
    (bad : ¬ Metamath.Kernel.StackRespectsFrame db db.frame
      (pr.push hypothesis.formula.toRuntime).stack) :
    ¬ Nonempty (ActiveHypothesisStepReceipt db projection hypothesis pr) := by
  rintro ⟨receipt⟩
  exact bad receipt.outputStackRespects

#print axioms GeneratedProvesTree.executionReceipt
#print axioms GeneratedProvesTree.receiptLabels_eq_labels
#print axioms duplicateActiveForest_receiptLabels
#print axioms no_executionReceipt_at_wrong_finalState
#print axioms no_activeReceipt_of_bad_outputStack

end Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
