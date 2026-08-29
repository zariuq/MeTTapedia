import Mettapedia.Languages.Metamath.InferenceGeneratedProvesTree
import Mettapedia.Languages.Metamath.InferenceHypothesisStepAgreement
import Mettapedia.Languages.Metamath.InferenceAssertionStackInvariant
import Mettapedia.Languages.Metamath.InferenceAssertionStepAgreement

open Mettapedia.GSLT.LanguageDef

/-!
# Exact execution of source-pinned generated Metamath derivations

This runtime layer executes the authored postfix labels of the static
`GeneratedProvesTree`/`GeneratedProvesForest` views.  It proves equality of
complete `mm-lean4` proof states: a tree pushes exactly its indexed formula,
and a forest appends exactly its indexed runtime array.  Every recursive step
also derives `StackRespectsFrame`; neither successful execution nor output
frame validity is stored in the static view.

This is a forward theorem for the explicitly source-pinned fragment.  It does
not claim that every arbitrary generic `Derivation` has that shape; static
normalization remains a separate classification and decoding obligation.
-/

namespace Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceHypothesisStepAgreement
open Mettapedia.Languages.Metamath.InferenceAssertionStepAgreement
open Mettapedia.Languages.Metamath.InferenceAssertionStackInvariant

/-! ## Ordered runtime images -/

/-- Exact runtime array corresponding to an ordered formula list. -/
def runtimeFormulaArray (formulas : List ConstantHeadedFormula) :
    Array RuntimeFormula :=
  (formulas.map ConstantHeadedFormula.toRuntime).toArray

@[simp] theorem runtimeFormulaArray_size
    (formulas : List ConstantHeadedFormula) :
    (runtimeFormulaArray formulas).size = formulas.length := by
  simp [runtimeFormulaArray]

@[simp] theorem runtimeFormulaArray_nil :
    runtimeFormulaArray [] = #[] := by
  rfl

theorem runtimeFormulaArray_cons
    (formula : ConstantHeadedFormula)
    (formulas : List ConstantHeadedFormula) :
    runtimeFormulaArray (formula :: formulas) =
      #[formula.toRuntime] ++ runtimeFormulaArray formulas := by
  simp [runtimeFormulaArray]

/-- Pushing the head formula and then appending the tail array is the same
complete proof state as appending the runtime image of the whole list. -/
theorem push_append_runtimeFormulaArray_state
    (pr : RuntimeProofState) (formula : ConstantHeadedFormula)
    (formulas : List ConstantHeadedFormula) :
    ({pr.push formula.toRuntime with
      stack := (pr.push formula.toRuntime).stack ++
        runtimeFormulaArray formulas} : RuntimeProofState) =
      {pr with
        stack := pr.stack ++ runtimeFormulaArray (formula :: formulas)} := by
  rw [runtimeFormulaArray_cons]
  simp only [Metamath.Verify.ProofState.push]
  rw [Array.push_eq_append, Array.append_assoc]

/-! ## Exact array boundaries used by assertion execution -/

/-- Appending a premise array makes that array the exact extracted suffix. -/
theorem extract_append_suffix {alpha : Type} (left right : Array alpha) :
    (left ++ right).extract left.size (left ++ right).size = right := by
  rw [Array.size_append, Array.extract_append_right]
  simp

/-- Shrinking an appended premise array at the old size recovers the exact
pre-premise stack. -/
theorem shrink_append_prefix {alpha : Type} (left right : Array alpha) :
    (left ++ right).shrink left.size = left := by
  apply Array.ext
  · simp
  · intro index hleft hright
    rw [Array.getElem_shrink]
    exact Array.getElem_append_left hright

/-- A generated assertion node has exactly as many actual premises as the
live source frame has mandatory hypotheses.  This is derived jointly from
generated-node semantics and projection fidelity. -/
theorem generatedAssertionNode_actuals_length_eq_frameHyps
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (assertion : AssertionView)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (substitution : FiniteSubstitution)
    (node : GeneratedAssertionNode projection target assertion actuals result
      substitution)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    actuals.length = assertion.frame.hyps.size := by
  have hsemantics :
      AssertionApplicationSemantics projection.callerFrame assertion
        actuals result :=
    (generatedAssertionNode_nonempty_iff_semantics projection target
      hprojection hmember actuals result).mp
        ⟨⟨substitution, node⟩⟩
  rcases hsemantics with
    ⟨_semanticSubstitution, instances, _essential, _dv, _result⟩
  have hinstanceLengths := instances.lengths
  have hfidelity :=
    projectedAssertion_database_fidelity
      db projection assertion hproject hmember
  have hframeLengths := congrArg List.length hfidelity.2.2.1
  simp only [List.length_map, Array.length_toList] at hframeLengths
  exact hinstanceLengths.symm.trans hframeLengths

/-! ## One assertion after its recursively executed forest -/

/-- If the recursive children have produced the exact authored premise
suffix, the parent assertion consumes precisely that suffix and pushes its
generated result.  Complete proof-state equality and the frame invariant are
both conclusions. -/
theorem generatedAssertionNode_execute_after_children
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (assertion : AssertionView)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (substitution : FiniteSubstitution)
    (hmember : assertion ∈ projection.assertions)
    (node : GeneratedAssertionNode projection target assertion actuals result
      substitution)
    (childLabels : List String)
    (pr : RuntimeProofState)
    (hchildren :
      childLabels.foldlM
          (fun state label => db.stepNormal state label) pr =
        .ok {pr with
          stack := pr.stack ++ runtimeFormulaArray actuals})
    (hchildrenStack :
      Metamath.Kernel.StackRespectsFrame db db.frame
        ({pr with
          stack := pr.stack ++ runtimeFormulaArray actuals} :
          RuntimeProofState).stack) :
    (childLabels ++ [assertion.label]).foldlM
          (fun state label => db.stepNormal state label) pr =
        .ok (pr.push result.toRuntime) ∧
      Metamath.Kernel.StackRespectsFrame db db.frame
        (pr.push result.toRuntime).stack := by
  let actualState : RuntimeProofState :=
    {pr with stack := pr.stack ++ runtimeFormulaArray actuals}
  have hactualLength :
      actuals.length = assertion.frame.hyps.size :=
    generatedAssertionNode_actuals_length_eq_frameHyps
      db projection target hprojection assertion actuals result substitution
        node hproject hmember
  have hoffset :
      actualState.stack.size - assertion.frame.hyps.size = pr.stack.size := by
    simp [actualState, Array.size_append, runtimeFormulaArray_size,
      hactualLength]
  have hwindow :
      actualState.stack.extract
          (actualState.stack.size - assertion.frame.hyps.size)
          actualState.stack.size =
        runtimeFormulaArray actuals := by
    rw [hoffset]
    exact extract_append_suffix pr.stack (runtimeFormulaArray actuals)
  have hnode :
      Nonempty
        (Σ semanticSubstitution : FiniteSubstitution,
          GeneratedAssertionNode projection target assertion actuals result
            semanticSubstitution) :=
    ⟨⟨substitution, node⟩⟩
  have hstep :=
    (generatedAssertionNode_nonempty_iff_stepNormal
      db projection target hprojection assertion actualState actuals result
        hproject hmember hwindow hchildrenStack).mp hnode
  have hshrink :
      actualState.stack.shrink
          (actualState.stack.size - assertion.frame.hyps.size) =
        pr.stack := by
    rw [hoffset]
    exact shrink_append_prefix pr.stack (runtimeFormulaArray actuals)
  rw [hshrink] at hstep
  have hstep' :
      db.stepNormal actualState assertion.label =
        .ok (pr.push result.toRuntime) := by
    simpa [actualState, Metamath.Verify.ProofState.push] using hstep
  have hresultStack :=
    generatedAssertionNode_stackResult_respects_callerFrame
      db projection target hprojection assertion actualState.stack actuals
        result hproject hmember hnode hwindow hchildrenStack
  rw [hshrink] at hresultStack
  constructor
  · rw [List.foldlM_append, hchildren]
    simp only [List.foldlM_cons, List.foldlM_nil, bind, Except.bind]
    simp only [actualState] at hstep'
    rw [hstep']
    rfl
  · simpa [actualState, Metamath.Verify.ProofState.push] using hresultStack

/-! ## Exact mutual execution -/

mutual

/-- Every source-pinned tree executes as its exact authored normal proof,
preserves all non-stack proof-state fields, and pushes exactly its indexed
formula. -/
theorem GeneratedProvesTree.execute
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    (db : RuntimeDB)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (pr : RuntimeProofState)
    (hstack :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    tree.labels.foldlM
          (fun state label => db.stepNormal state label) pr =
        .ok (pr.push formula.toRuntime) ∧
      Metamath.Kernel.StackRespectsFrame db db.frame
        (pr.push formula.toRuntime).stack := by
  cases tree with
  | active hypothesis hmember =>
      constructor
      · simp only [GeneratedProvesTree.labels, List.foldlM_cons,
          List.foldlM_nil, bind, Except.bind]
        rw [activeHypothesis_stepNormal
          db projection hypothesis pr hproject hmember]
        rfl
      · exact activeHypothesis_step_stackRespectsFrame
          db projection hypothesis pr hproject hmember hstack
  | @assertion assertion actuals result substitution hmember node children =>
      have hchildren := children.execute
        db hprojection hproject pr hstack
      exact generatedAssertionNode_execute_after_children
        db projection target hprojection hproject assertion actuals formula
          substitution hmember node children.labels pr hchildren.1 hchildren.2

/-- Executing an ordered source-pinned forest appends exactly its indexed
runtime formula array to the original stack and preserves the complete
surrounding proof state and caller-frame invariant. -/
theorem GeneratedProvesForest.execute
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formulas : List ConstantHeadedFormula}
    (forest : GeneratedProvesForest projection target formulas)
    (db : RuntimeDB)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (pr : RuntimeProofState)
    (hstack :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    forest.labels.foldlM
          (fun state label => db.stepNormal state label) pr =
        .ok {pr with
          stack := pr.stack ++ runtimeFormulaArray formulas} ∧
      Metamath.Kernel.StackRespectsFrame db db.frame
        ({pr with
          stack := pr.stack ++ runtimeFormulaArray formulas} :
          RuntimeProofState).stack := by
  cases forest with
  | nil =>
      constructor
      · change (.ok pr : Except RuntimeError RuntimeProofState) = .ok pr
        rfl
      · simpa [runtimeFormulaArray] using hstack
  | @cons formula formulas head tail =>
      have hhead := head.execute db hprojection hproject pr hstack
      have htail := tail.execute db hprojection hproject
        (pr.push formula.toRuntime) hhead.2
      have hstate :=
        push_append_runtimeFormulaArray_state pr formula formulas
      rw [hstate] at htail
      constructor
      · rw [GeneratedProvesForest.labels, List.foldlM_append, hhead.1]
        simp only [bind, Except.bind]
        rw [htail.1]
      · exact htail.2

end

/-! ## Negative boundary -/

/-- Exact execution rules out every unequal complete proof state; the theorem
does not merely constrain the final stack. -/
theorem GeneratedProvesTree.execute_ne_wrong_state
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    (tree : GeneratedProvesTree projection target formula)
    (db : RuntimeDB)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (pr wrong : RuntimeProofState)
    (hstack :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack)
    (hne : wrong ≠ pr.push formula.toRuntime) :
    tree.labels.foldlM
        (fun state label => db.stepNormal state label) pr ≠ .ok wrong := by
  rw [(tree.execute db hprojection hproject pr hstack).1]
  intro heq
  exact hne (Except.ok.inj heq).symm

end Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
