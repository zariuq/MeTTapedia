import Mettapedia.GSLT.Examples.ScopedRhoBinding
import Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
import Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
import Mettapedia.OSLF.Syntax.RhoCombinedInterpretedStep
import Mettapedia.OSLF.Syntax.RhoQuoteSafeCommComparison
import Mettapedia.OSLF.Syntax.ScopedOperationalCertification
import Mettapedia.OSLF.MeTTaIL.OracleOccurrenceEmbedding

/-!
# The scoped and reflective rho operational profiles

The scoped executor needs explicit dependency declarations. Its COMM rule
keeps the immediate quoted-Drop contractum, whereas reflective COMM may
contract that round trip during substitution. Both must be compared at
their actual reducts, preserving the firing rather than identifying the two
raw output patterns.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedCombinedComparison

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.GSLT.Examples.ScopedRhoBinding
open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
open Mettapedia.OSLF.Binding.RhoSchema.Authored
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.Binding.RhoCombinedInterpretedStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ScopedOperationalCertification
open Mettapedia.OSLF.Binding.ScopedOperationalHistory
open Mettapedia.OSLF.MeTTaIL.OracleOccurrenceEmbedding

private def zeroPattern : Pattern := .apply "PZero" []

/-- Drop has no metavariable dependency on a binder. -/
def scopedDropBindingSpec : RuleBindingSpec :=
  { dependencies := [("P", [])] }

/-- The same source-level Drop pattern, admitted by the contextual executor. -/
def scopedDropRewrite : RewriteRule :=
  { rhoDropRewrite with «bindings» := some scopedDropBindingSpec }

/-- One authored rule list for scoped COMM, ParCong and Drop. -/
def rhoCalcScopedWithDrop : LanguageDef :=
  { rhoCalcWithScopedSchemas with «rewrites» :=
      [scopedCommRewrite, scopedParCongRewrite, scopedDropRewrite] }

theorem scoped_combined_rule_names :
    rhoCalcScopedWithDrop.rewrites.map (·.name) =
      ["Comm", "ParCong", "Drop"] := rfl

theorem scoped_combined_valid :
    rhoCalcScopedWithDrop.validate = [] := by
  have comparison : rhoCalcScopedWithDrop.validate = rhoCalcWithDrop.validate := by
    rfl
  exact comparison.trans rhoCalcWithDrop_valid

theorem scoped_combined_binding_admitted :
    bindingDeclarationsValid rhoCalcScopedWithDrop = true := by
  unfold bindingDeclarationsValid
  rw [scoped_combined_valid]
  decide +kernel

theorem scoped_combined_executable :
    Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution.scopedRewritesExecutable
      rhoCalcScopedWithDrop = true := by
  unfold Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution.scopedRewritesExecutable
  rw [scoped_combined_binding_admitted]
  decide +kernel

/-- The added process-sorted Drop declaration passes the same authored
rest-aware rewrite checker as COMM and ParCong. -/
theorem scoped_drop_typed :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType
      rhoCalcScopedWithDrop scopedDropRewrite = true := by
  decide +kernel

/-- Every rewrite of the complete scoped profile passes the rest-aware
authored checker, including the collection rest of COMM and ParCong. -/
theorem scoped_combined_rewrites_typed :
    ∀ rule ∈ rhoCalcScopedWithDrop.rewrites,
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType
        rhoCalcScopedWithDrop rule = true := by
  intro rule member
  change rule ∈
    [scopedCommRewrite, scopedParCongRewrite, scopedDropRewrite] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with comm | par | drop
  · subst rule
    decide +kernel
  · subst rule
    decide +kernel
  · subst rule
    exact scoped_drop_typed

/-- The old root congruence notation of this declared rule has one checked
sort and compiles to the canonical empty-binder step premise. -/
theorem par_congruence_elaborates :
    compileRulePremises? rhoCalcScopedWithDrop scopedParCongRewrite =
      some [.step (ScopedStepPremise.root (.base "Proc")
        (.fvar "S") (.fvar "T"))] := by
  decide +kernel

/-- The scoped matcher gives the same concrete source as the intrinsic COMM
encoding, with its input and output components ordered as authored. -/
theorem communication_source_agrees :
    communicationInput = authoredCommSource := by
  decide +kernel

/-! ### An open COMM target generated beyond the literal-source boundary -/

private def selectOpenComm : RuleHistory × Pattern → Option Pattern
  | (.fire 0 [], result) => some result
  | _ => none

/-- The scoped executor really fires the open intrinsic COMM example. Its
result is the authored hash-bag wrapper around the semantic rule's target. -/
theorem open_comm_executor_fires :
    (.fire 0 [],
      .collection .hashBag [encodeTerm openCommTarget] none) ∈
      rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 1 1
        (encodeTerm openCommSource) := by
  have tagged :
      some (.collection .hashBag [encodeTerm openCommTarget] none) ∈
        (rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 1 1
          (encodeTerm openCommSource)).map selectOpenComm := by
    decide +kernel
  obtain ⟨⟨history, result⟩, member, selected⟩ := List.mem_map.mp tagged
  cases history with
  | fire index premises =>
      cases index with
      | zero =>
          cases premises with
          | nil =>
              have equal : result =
                  .collection .hashBag [encodeTerm openCommTarget] none := by
                simpa [selectOpenComm] using selected
              subst result
              exact member
          | cons first rest => simp [selectOpenComm] at selected
      | succ index => simp [selectOpenComm] at selected

/-- The executor's open COMM contractum is exactly the general contextual
binder substitution after encoding. This compares the generated result, not
an independently chosen target with the same endpoints. -/
theorem open_comm_executor_fires_as_instantiate :
    (.fire 0 [],
      .collection .hashBag
        [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar
          (.apply "NQuote" [encodeTerm openCommPayload])
          (encodeTerm openCommContinuation)] none) ∈
      rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 1 1
        (encodeTerm openCommSource) := by
  simpa only
    [Mettapedia.OSLF.Binding.RhoQuoteSafeCommComparison.open_comm_target_eq_instantiate]
    using open_comm_executor_fires

/-- The source passes the authored quote-aware scope check, but the generated
target does not pass that *literal-source* check. Ordinary de Bruijn scope is
preserved; this is specifically a quotation boundary, not an escaping index. -/
theorem open_comm_executor_crosses_literal_boundary :
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" 1
      (encodeTerm openCommSource) = true ∧
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" 1
      (.collection .hashBag [encodeTerm openCommTarget] none) = false := by
  constructor
  · exact openCommSource_authored_admitted.2
  · decide +kernel

/-- The generated result remains ordinarily scoped at the same ambient
depth. The counterexample concerns the stronger literal-quotation contract. -/
theorem open_comm_executor_target_locally_scoped :
    (Pattern.collection .hashBag [encodeTerm openCommTarget] none).isWellScopedAt 1 =
      true :=
  rewriteAt_scoped RelationEnv.empty rhoCalcScopedWithDrop 1 1
    (encodeTerm openCommSource)
    (.collection .hashBag [encodeTerm openCommTarget] none)
    (.fire 0 []) open_comm_executor_fires

/-- The current scoped executor cannot use literal-source admission as a
preserved invariant for open rho COMM. A generated-term carrier is required
if this firing is to remain part of the operational semantics. -/
theorem scoped_executor_not_literal_quote_preserving :
    ¬ ∀ (source target : Pattern) (history : RuleHistory),
      Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" 1
        source = true →
      (history, target) ∈
        rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 1 1 source →
      Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" 1
        target = true := by
  intro preserves
  have safe := preserves (encodeTerm openCommSource)
    (.collection .hashBag [encodeTerm openCommTarget] none)
    (.fire 0 []) open_comm_executor_crosses_literal_boundary.1
    open_comm_executor_fires
  rw [open_comm_executor_crosses_literal_boundary.2] at safe
  cases safe

/-- The scoped COMM result retains the quoted Drop that the reflective
substitution profile can contract during the same communication. -/
theorem communication_output_is_intrinsic_representative :
    communicationOutput =
      .collection .hashBag [encodeTerm RhoSchema.commTarget] none := by
  decide +kernel

/-- A tag for the exact nullary COMM occurrence. It avoids imposing proof
irrelevance or a decidable equality on recursive firing histories. -/
private def selectComm : RuleHistory × Pattern → Option Pattern
  | (.fire 0 [], result) => some result
  | _ => none

/-- This three-rule scoped profile executes the declared COMM rule. -/
theorem scoped_comm_fires :
    (.fire 0 [], communicationOutput) ∈
      rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 1 0
        communicationInput := by
  have tagged : some communicationOutput ∈
      (rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 1 0
        communicationInput).map selectComm := by
    decide +kernel
  obtain ⟨⟨history, result⟩, member, selected⟩ := List.mem_map.mp tagged
  cases history with
  | fire index premises =>
      cases index with
      | zero =>
          cases premises with
          | nil =>
              have equal : result = communicationOutput := by
                simpa [selectComm] using selected
              subst result
              exact member
          | cons first rest => simp [selectComm] at selected
      | succ index => simp [selectComm] at selected

/-- The corresponding reflective COMM step occurs in the combined profile. -/
theorem reflective_comm_fires :
    RhoStepWithDrop communicationInput authoredCommReduct := by
  rw [communication_source_agrees]
  exact interpretedComm_in_withDrop

/-- The two actual COMM results agree under the process residual semantics,
not by raw pattern equality. -/
theorem comm_results_residually_equivalent :
    ProcResidualEquiv communicationOutput authoredCommReduct := by
  rw [communication_output_is_intrinsic_representative]
  exact ProcResidualEquiv.symm commWholeReducts_residualEquivalent

/-- Residual equivalence is needed: the two immediate reducts cannot be
identified by the authored structural equations alone. -/
theorem comm_results_not_structural :
    ¬ StructuralCongruence communicationOutput authoredCommReduct := by
  intro same
  rw [communication_output_is_intrinsic_representative] at same
  have unwrapped : StructuralCongruence
      (encodeTerm RhoSchema.commTarget) authoredCommReduct :=
    StructuralCongruence.trans _ _ _
      (StructuralCongruence.symm _ _
        (StructuralCongruence.par_singleton
          (encodeTerm RhoSchema.commTarget))) same
  exact notStructurallyCongruent unwrapped

private def selectDrop : RuleHistory × Pattern → Option Pattern
  | (.fire 2 [], result) => some result
  | _ => none

/-- The new authored Drop rule executes on the intrinsic COMM result. -/
theorem scoped_drop_fires :
    (.fire 2 [], zeroPattern) ∈
      rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 1 0
        (encodeTerm RhoSchema.commTarget) := by
  have tagged : some zeroPattern ∈
      (rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 1 0
        (encodeTerm RhoSchema.commTarget)).map selectDrop := by
    decide +kernel
  obtain ⟨⟨history, result⟩, member, selected⟩ := List.mem_map.mp tagged
  cases history with
  | fire index premises =>
      cases index with
      | zero => simp [selectDrop] at selected
      | succ index =>
          cases index with
          | zero => simp [selectDrop] at selected
          | succ index =>
              cases index with
              | zero =>
                  cases premises with
                  | nil =>
                      have equal : result = zeroPattern := by
                        simpa [selectDrop] using selected
                      subst result
                      exact member
                  | cons first rest => simp [selectDrop] at selected
              | succ index => simp [selectDrop] at selected

private def selectParDrop : RuleHistory × Pattern → Option Pattern
  | (.fire 1 [.step 0 0 (.fire 2 [])], result) => some result
  | _ => none

/-- The scoped ParCong rule consumes that Drop event as a recursive child,
keeping both authored rule positions in the history. -/
theorem scoped_par_drop_fires :
    (.fire 1 [.step 0 0 (.fire 2 [])],
      .collection .hashBag [zeroPattern] none) ∈
      rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 2 0
        communicationOutput := by
  have tagged : some (.collection .hashBag [zeroPattern] none) ∈
      (rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 2 0
        communicationOutput).map selectParDrop := by
    decide +kernel
  obtain ⟨⟨history, result⟩, member, selected⟩ := List.mem_map.mp tagged
  unfold selectParDrop at selected
  split at selected <;> simp_all

/-- The fixed free operational model receives the exact scoped ParCong over
Drop execution, with its selected child and ordinal certified. -/
theorem scoped_par_drop_has_certified_tree :
    ∃ tree : (presentation RelationEnv.empty rhoCalcScopedWithDrop).Derivation ()
        ⟨2, 0, communicationOutput,
          .collection .hashBag [zeroPattern] none⟩,
      CertifiedTree RelationEnv.empty rhoCalcScopedWithDrop _ tree ∧
        decodeHistory? RelationEnv.empty rhoCalcScopedWithDrop _ tree =
          some (.fire 1 [.step 0 0 (.fire 2 [])]) := by
  exact runtime_to_certified_tree RelationEnv.empty
    rhoCalcScopedWithDrop 2 0 communicationOutput
    (.collection .hashBag [zeroPattern] none)
    (.fire 1 [.step 0 0 (.fire 2 [])]) scoped_par_drop_fires

/-! ## An occurrence-ordinal obstruction to identity-on-history inclusion -/

/-- A mixed parallel child has a Drop redex before a COMM redex. -/
def mixedParallel : Pattern :=
  .collection .hashBag
    [.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]],
     communicationInput] none

def wrappedMixedParallel : Pattern :=
  .collection .hashBag [mixedParallel] none

/-- In the core, the outer ParCong selects the only inner result at ordinal
zero. The extension inserts a new inner Drop result before it. -/
def oldNestedCommHistory : RuleHistory :=
  .fire 1 [.step 0 0 (.fire 1 [.step 0 0 (.fire 0 [])])]

/-- The same nested COMM firing moves to child ordinal one when Drop is
admitted before it in the inner oracle result list. -/
def reindexedNestedCommHistory : RuleHistory :=
  .fire 1 [.step 0 1 (.fire 1 [.step 0 0 (.fire 0 [])])]

/-- The result retained by both firings; only the occurrence ordinal changes. -/
def nestedCommTarget : Pattern :=
  .collection .hashBag
    [.collection .hashBag
      [communicationOutput, encodeTerm RhoSchema.commTarget] none] none

private def innerCommTarget : Pattern :=
  .collection .hashBag
    [communicationOutput, encodeTerm RhoSchema.commTarget] none

private def innerCommHistory : RuleHistory :=
  .fire 1 [.step 0 0 (.fire 0 [])]

private def innerCommResult : RuleHistory × Pattern :=
  (innerCommHistory, innerCommTarget)

private def selectInnerCommAt (wanted : Nat) :
    ((RuleHistory × Pattern) × Nat) → Option Pattern
  | ((.fire 1 [.step 0 0 (.fire 0 [])], result), actual) =>
      if actual == wanted then some result else none
  | _ => none

private theorem selectedInnerCommAt (values : List (RuleHistory × Pattern))
    (wanted : Nat)
    (selected : some innerCommTarget ∈
      values.zipIdx.map (selectInnerCommAt wanted)) :
    (innerCommResult, wanted) ∈ values.zipIdx := by
  obtain ⟨⟨⟨history, result⟩, ordinal⟩, listed, tagged⟩ :=
    List.mem_map.mp selected
  unfold selectInnerCommAt at tagged
  split at tagged <;> simp_all [innerCommResult, innerCommHistory]

/-- The actual inner oracle result lists used by the outer ParCong premise. -/
def coreInnerResults : List (RuleHistory × Pattern) :=
  rewriteAt RelationEnv.empty rhoCalcWithScopedSchemas 2 0 mixedParallel

def extendedInnerResults : List (RuleHistory × Pattern) :=
  rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 2 0 mixedParallel

private theorem core_inner_results_length : coreInnerResults.length = 1 := by
  decide +kernel

private theorem extended_inner_results_length :
    extendedInnerResults.length = 2 := by
  decide +kernel

private theorem core_zero_bound : 0 < coreInnerResults.length := by
  rw [core_inner_results_length]
  omega

private theorem extended_one_bound : 1 < extendedInnerResults.length := by
  rw [extended_inner_results_length]
  omega

private theorem core_inner_at_zero :
    coreInnerResults.get ⟨0, core_zero_bound⟩ = innerCommResult := by
  have selected : some innerCommTarget ∈
      coreInnerResults.zipIdx.map (selectInnerCommAt 0) := by
    decide +kernel
  have listed := selectedInnerCommAt coreInnerResults 0 selected
  obtain ⟨bound, equality⟩ := List.mem_zipIdx' listed
  exact equality.symm

private theorem extended_inner_at_one :
    extendedInnerResults.get ⟨1, extended_one_bound⟩ =
      innerCommResult := by
  have selected : some innerCommTarget ∈
      extendedInnerResults.zipIdx.map (selectInnerCommAt 1) := by
    decide +kernel
  have listed := selectedInnerCommAt extendedInnerResults 1 selected
  obtain ⟨bound, equality⟩ := List.mem_zipIdx' listed
  exact equality.symm

private def innerPosition :
    Fin coreInnerResults.length ↪o Fin extendedInnerResults.length :=
  OrderEmbedding.ofMapLEIff
    (fun i => (⟨i.val + 1, by
      have oldBound : i.val < 1 := by
        simpa only [core_inner_results_length] using i.isLt
      have newLength := extended_inner_results_length
      omega⟩ : Fin extendedInnerResults.length)) (by
        intro i j
        change (i.val + 1 ≤ j.val + 1) ↔ (i.val ≤ j.val)
        omega)

/-- On the actual authored inner oracles, the old COMM result, including its
individual firing evidence, moves unchanged to position one. The outer
history must change its stored ordinal to select it. -/
def innerOccurrenceEmbedding :
    Embedding Eq coreInnerResults extendedInnerResults where
  position := innerPosition
  relates := by
    intro i
    have atZero : i.val = 0 := by
      have bound : i.val < 1 := by
        simpa only [core_inner_results_length] using i.isLt
      omega
    have indexEq : i = ⟨0, core_zero_bound⟩ :=
      Fin.ext atZero
    rw [indexEq]
    have targetIndex :
        innerPosition ⟨0, core_zero_bound⟩ =
          ⟨1, extended_one_bound⟩ := by
      apply Fin.ext
      rfl
    rw [targetIndex, core_inner_at_zero, extended_inner_at_one]

theorem innerOccurrenceEmbedding_reindexes :
    (innerOccurrenceEmbedding.position
      ⟨0, by rw [core_inner_results_length]; omega⟩).val = 1 := rfl

private def innerEvidenceEmbedding :
    Embedding
      (fun oldResult newResult =>
        oldResult.2 = newResult.2 ∧ oldResult.1 = newResult.1)
      coreInnerResults extendedInnerResults where
  position := innerOccurrenceEmbedding.position
  relates := by
    intro i
    have same := innerOccurrenceEmbedding.relates i
    exact ⟨congrArg Prod.snd same, congrArg Prod.fst same⟩

private def outerCapture : Assignment :=
  (matchRuleAt scopedParCongRewrite scopedParCongBindingSpec 0
    wrappedMixedParallel).head!

private def outerCompleted : Assignment :=
  ("T", (⟨[], 0, innerCommTarget⟩ : ContextualValue)) :: outerCapture

private def selectOldOuterPremise :
    (PremiseEvent RuleHistory × Assignment) → Option Assignment
  | (.step 0 0 (.fire 1 [.step 0 0 (.fire 0 [])]), completed) =>
      some completed
  | _ => none

private theorem old_outer_premise_selected :
    ((.step 0 0 innerCommHistory), outerCompleted) ∈
      stepResults
        (rewriteAt RelationEnv.empty rhoCalcWithScopedSchemas 2)
        scopedParCongRewrite scopedParCongBindingSpec 0 0 0
        (.fvar "S") (.fvar "T") outerCapture := by
  have selected : some outerCompleted ∈
      (stepResults
        (rewriteAt RelationEnv.empty rhoCalcWithScopedSchemas 2)
        scopedParCongRewrite scopedParCongBindingSpec 0 0 0
        (.fvar "S") (.fvar "T") outerCapture).map
          selectOldOuterPremise := by
    decide +kernel
  obtain ⟨⟨event, completed⟩, listed, tagged⟩ :=
    List.mem_map.mp selected
  unfold selectOldOuterPremise at tagged
  split at tagged <;> simp_all [innerCommHistory]

/-- The general scoped-premise transport theorem applies to the actual outer
ParCong premise: it preserves the completed contextual assignment and its
inner COMM evidence, while changing the selected inner ordinal from zero to
one. -/
theorem authored_outer_premise_reindexed :
    ((.step 0 1 innerCommHistory), outerCompleted) ∈
      stepResults
        (rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 2)
        scopedParCongRewrite scopedParCongBindingSpec 0 0 0
        (.fvar "S") (.fvar "T") outerCapture := by
  have instantiated :
      instantiateAt? scopedParCongRewrite scopedParCongBindingSpec 0
        (.premise 0 0 0) [] 0 outerCapture (.fvar "S") =
          some mixedParallel := by
    decide +kernel
  obtain ⟨bound, newEvidence, selected, sameEvidence⟩ :=
    stepResults_transport_at Eq
      (rewriteAt RelationEnv.empty rhoCalcWithScopedSchemas 2)
      (rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 2)
      scopedParCongRewrite scopedParCongBindingSpec 0 0 0
      (.fvar "S") (.fvar "T") mixedParallel
      outerCapture outerCompleted 0
      innerCommHistory
      instantiated innerEvidenceEmbedding old_outer_premise_selected
  cases sameEvidence
  have sameIndex :
      (innerEvidenceEmbedding.position ⟨0, bound⟩).val = 1 := by
    have boundEq : (⟨0, bound⟩ : Fin coreInnerResults.length) =
        ⟨0, core_zero_bound⟩ := Fin.ext rfl
    rw [boundEq]
    exact innerOccurrenceEmbedding_reindexes
  exact (congrArg
    (fun ordinal : Nat =>
      ((PremiseEvent.step 0 ordinal innerCommHistory, outerCompleted) ∈
        stepResults
          (rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 2)
          scopedParCongRewrite scopedParCongBindingSpec 0 0 0
          (.fvar "S") (.fvar "T") outerCapture)) sameIndex).mp selected

/-- The actual extended ParCong run consumes the reindexed COMM witness and
keeps its completed contextual assignment through the whole premise list. -/
theorem authored_outer_run_reindexed :
    (outerCompleted, [.step 0 1 innerCommHistory]) ∈
      runPremises
        (rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 2)
        RelationEnv.empty rhoCalcScopedWithDrop scopedParCongRewrite
        scopedParCongBindingSpec 0 0 scopedParCongRewrite.premises
        outerCapture := by
  change (outerCompleted, [.step 0 1 innerCommHistory]) ∈
    runPremises
      (rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 2)
      RelationEnv.empty rhoCalcScopedWithDrop scopedParCongRewrite
      scopedParCongBindingSpec 0 0
      [.congruence (.fvar "S") (.fvar "T")] outerCapture
  simp only [runPremises, List.mem_flatMap, List.mem_map]
  exact ⟨(.step 0 1 innerCommHistory, outerCompleted),
    authored_outer_premise_reindexed, (outerCompleted, []),
    by simp, rfl⟩

/-- The same actual rule matcher and reduct constructor consume that complete
run. This is a full authored firing, with the occurrence change visible in its
history rather than inferred from equal endpoints. -/
theorem authored_outer_firing_reindexed :
    ∃ firing ∈ applyRuleWithOracle
        (rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 2)
        RelationEnv.empty rhoCalcScopedWithDrop 0
        scopedParCongRewrite wrappedMixedParallel,
      firing.history = [.step 0 1 innerCommHistory] ∧
      firing.target = nestedCommTarget := by
  let firing : RuleFiring RuleHistory :=
    { captured := outerCapture, completed := outerCompleted,
      history := [.step 0 1 innerCommHistory],
      target := nestedCommTarget }
  have captured : outerCapture ∈
      matchRuleAt scopedParCongRewrite scopedParCongBindingSpec 0
        wrappedMixedParallel := by
    decide +kernel
  have finished : finish? scopedParCongRewrite scopedParCongBindingSpec
      0 outerCapture outerCompleted [.step 0 1 innerCommHistory] =
        some firing := by
    have reduct : reduct? scopedParCongRewrite scopedParCongBindingSpec
        0 outerCompleted = some nestedCommTarget := by
      decide +kernel
    have hscoped : nestedCommTarget.isWellScopedAt 0 = true := by
      decide +kernel
    simp [finish?, reduct, hscoped, firing]
  have listed : firing ∈ applyRuleWithOracle
      (rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 2)
      RelationEnv.empty rhoCalcScopedWithDrop 0 scopedParCongRewrite
      wrappedMixedParallel :=
    (mem_applyRuleWithOracle_iff _ _ _ _ _ _ _).mpr
      ⟨scopedParCongBindingSpec, outerCapture, outerCompleted,
        [.step 0 1 innerCommHistory], rfl, by decide +kernel,
        captured, authored_outer_run_reindexed, finished⟩
  exact ⟨firing, listed, rfl, rfl⟩

private def selectOldNestedCommOutput : RuleHistory × Pattern → Option Pattern
  | (.fire 1 [.step 0 0 (.fire 1 [.step 0 0 (.fire 0 [])])], result) =>
      some result
  | _ => none

theorem nested_comm_core_fires :
    (oldNestedCommHistory, nestedCommTarget) ∈
      rewriteAt RelationEnv.empty rhoCalcWithScopedSchemas 3 0
        wrappedMixedParallel := by
  have selected : some nestedCommTarget ∈
      (rewriteAt RelationEnv.empty rhoCalcWithScopedSchemas 3 0
        wrappedMixedParallel).map selectOldNestedCommOutput := by
    decide +kernel
  obtain ⟨⟨history, target⟩, member, accepted⟩ := List.mem_map.mp selected
  unfold selectOldNestedCommOutput at accepted
  split at accepted <;> simp_all [oldNestedCommHistory]

theorem nested_comm_reindexed_fires :
    (reindexedNestedCommHistory, nestedCommTarget) ∈
      rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 3 0
        wrappedMixedParallel := by
  obtain ⟨firing, selected, historyEq, targetEq⟩ :=
    authored_outer_firing_reindexed
  apply (mem_rewriteAt_succ_iff RelationEnv.empty rhoCalcScopedWithDrop
    2 0 wrappedMixedParallel nestedCommTarget
      reindexedNestedCommHistory).mpr
  refine ⟨scopedParCongRewrite, 1, ?_, firing, selected, ?_, ?_⟩
  · change (scopedParCongRewrite, 1) ∈
      [(scopedCommRewrite, 0), (scopedParCongRewrite, 1),
        (scopedDropRewrite, 2)]
    exact List.Mem.tail _ (List.Mem.head _)
  · rw [historyEq]
    rfl
  · exact targetEq.symm

private def selectsOldNestedComm : RuleHistory × Pattern → Bool
  | (.fire 1 [.step 0 0 (.fire 1 [.step 0 0 (.fire 0 [])])], _) => true
  | _ => false

/-- Adding Drop changes the result ordinal of the old COMM child; no result
of the extended evaluator retains this literal old history. The proved
reindexed firing has the same target, so a revision map must reindex
occurrences. -/
theorem old_nested_comm_history_not_literal_in_extension :
    ∀ target,
      (oldNestedCommHistory, target) ∉
        rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 3 0
          wrappedMixedParallel := by
  have selectedResults :
      (rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 3 0
        wrappedMixedParallel).map selectsOldNestedComm =
        [false, false] := by
    decide +kernel
  intro target member
  have selected : true ∈
      (rewriteAt RelationEnv.empty rhoCalcScopedWithDrop 3 0
        wrappedMixedParallel).map selectsOldNestedComm :=
    List.mem_map.mpr
      ⟨(oldNestedCommHistory, target), member,
        by simp [selectsOldNestedComm, oldNestedCommHistory]⟩
  rw [selectedResults] at selected
  simp at selected

/-- The unrestricted core cannot perform the newly admitted Drop firing. -/
theorem reflective_core_missing_drop :
    ¬ Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.RhoStep
      (encodeTerm RhoSchema.commTarget) zeroPattern := by
  exact interpretedDrop_is_properExtension.2

#print axioms scoped_combined_valid
#print axioms scoped_combined_binding_admitted
#print axioms scoped_combined_executable
#print axioms scoped_drop_typed
#print axioms scoped_combined_rewrites_typed
#print axioms par_congruence_elaborates
#print axioms scoped_comm_fires
#print axioms reflective_comm_fires
#print axioms comm_results_residually_equivalent
#print axioms comm_results_not_structural
#print axioms scoped_drop_fires
#print axioms scoped_par_drop_fires
#print axioms scoped_par_drop_has_certified_tree
#print axioms nested_comm_core_fires
#print axioms nested_comm_reindexed_fires
#print axioms innerOccurrenceEmbedding
#print axioms innerOccurrenceEmbedding_reindexes
#print axioms authored_outer_premise_reindexed
#print axioms authored_outer_run_reindexed
#print axioms authored_outer_firing_reindexed
#print axioms old_nested_comm_history_not_literal_in_extension
#print axioms reflective_core_missing_drop

end Mettapedia.OSLF.Binding.RhoScopedCombinedComparison
