import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelUniverseReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalModelControls

/-!
# Generated dependent certificates on enlarged external carriers

The source model has independently sized carriers and genuinely varying
function-indexed finite fibres. Common lifting retains the actual primitive
headers, complete sum-elimination witness and exchanged variable readings.
An incompatible annotation remains rejected after changing carrier sizes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.UniverseControls

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualSumComprehension
open ModelControls

def original : Contextual.Interpretation.QualifiedModel Controls.signature familyModel where
  data := model
  realization := realization
  products_substitution := Families.products_substitution
  products_beta := PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts
  products_eta := products_eta

abbrev raised := original.commonUniverseLift.{0, 1, 0, 1, 0, 2}
abbrev raisedComponents := liftContext.{1, 0, 1, 0, 2, 2, 2, 2} declarations.componentContext

abbrev branchType := familyModel.toCwf.tySub declarations.motive
  (pack sums (DeclaredModel.functionDomain (C := familyModel) products declarations.scalar) declarations.fibre)

noncomputable def extracted :=
  (Controls.fullBranchTyped Controls.emptyContext).termSection raised.data raised.realization
    raised.products_substitution raised.products_beta raised.products_eta raisedComponents (ULift.up branchType)
    (model.evaluateContext_universeLift _ _ declarations.component_header_read)
    (model.evaluateType_universeLift _ _ _ (declarations.branch_result_read Families.products_substitution))

theorem extracted_retains_supplied_branch : extracted.down = extractedBranch :=
  (Controls.fullBranchTyped Controls.emptyContext).termSection_universeLift original
    (Controls.fullBranchTyped Controls.emptyContext) declarations.componentContext branchType
    declarations.component_header_read (declarations.branch_result_read Families.products_substitution)

abbrev rawBranchType := (Controls.motive 0).substitute
  (packSubstitution (Controls.domain 0) (Controls.body 0))

def convertedBranch : Derivation Controls.signature
    (.term (Controls.componentContext 0 .nil) (Controls.fullBranch 0) rawBranchType) :=
  deriveList (.termConversion _ _ rawBranchType rawBranchType)
    (.cons (Controls.fullBranchTyped Controls.emptyContext)
      (.cons (deriveList (.typeReflexivity _ rawBranchType)
        (.cons Controls.branchResultFormed .nil)) .nil))

private def branchRootCode {judgment : Judgment Controls.symbols} :
    Derivation Controls.signature judgment → RuleCode Controls.signature
  | .node rule _ => rule.val

private theorem branchRootCode_cast {first second : Judgment Controls.symbols} (same : first = second)
    (tree : Derivation Controls.signature first) :
    branchRootCode (cast (congrArg (Derivation Controls.signature) same) tree) = branchRootCode tree := by
  cases same
  rfl

private theorem branchRootCode_direct : branchRootCode (Controls.fullBranchTyped Controls.emptyContext) =
    .primitive (Controls.componentContext 0 .nil) .fullBranch (Controls.componentArguments 0) := by
  unfold Controls.fullBranchTyped
  dsimp only
  exact branchRootCode_cast
    (congrArg (Judgment.term (Controls.componentContext 0 .nil) (Controls.fullBranch 0))
      (Controls.branchResult_substitute 0)) _

theorem distinct_certificate_trees : convertedBranch ≠ Controls.fullBranchTyped Controls.emptyContext := by
  intro same
  have roots := congrArg branchRootCode same
  rw [branchRootCode_direct] at roots
  cases roots

theorem different_certificate_recovers_same_section :
    (convertedBranch.termSection raised.data raised.realization raised.products_substitution
      raised.products_beta raised.products_eta raisedComponents (ULift.up branchType)
      (model.evaluateContext_universeLift _ _ declarations.component_header_read)
      (model.evaluateType_universeLift _ _ _
        (declarations.branch_result_read Families.products_substitution))).down = extractedBranch :=
  (Controls.fullBranchTyped Controls.emptyContext).termSection_universeLift original convertedBranch
    declarations.componentContext branchType declarations.component_header_read
    (declarations.branch_result_read Families.products_substitution)

theorem exact_varying_finite_witnesses :
    (extracted.down falsePoint).val = 0 ∧ (extracted.down trueZero).val = 0 ∧
      (extracted.down trueOne).val = 1 := by
  rw [extracted_retains_supplied_branch]
  exact supplied_witness_readouts

theorem full_motive_elimination_retains_witness :
    raised.data.evaluateTerm raisedComponents DeclaredModel.Declarations.pairElimination =
      some (liftValue.{1, 0, 1, 0, 2, 2, 2, 2}
        (⟨branchType, extractedBranch⟩ : Value familyModel.toCwf declarations.componentContext.1)) :=
  model.evaluateTerm_universeLift _ _ _ generated_elimination_recovers_branch

theorem primitive_value_is_exact :
    (raised.data.termValue .fullBranch).down = declarations.branch := rfl

theorem primitive_header_is_actual :
    raised.data.evaluateContext (Controls.signature.termParameters .fullBranch) =
      some (raised.data.termParameters .fullBranch) := raised.realization.termHeader .fullBranch

abbrev raisedBooleanContext := liftContext.{1, 0, 1, 0, 2, 2, 2, 2} booleanContext

theorem actual_exchange_read :
    raised.data.evaluateSubstitution raisedBooleanContext raisedBooleanContext exchangeRaw =
      some (ULift.up exchange) := model.evaluateSubstitution_universeLift _ _ _ _ exchange_evaluated

theorem exact_exchanged_component :
    (raisedBooleanContext.2.components (ULift.up exchange) (0 : Fin 2)).2.down
      ⟨⟨PUnit.unit, false⟩, true⟩ = false := rfl

theorem omission_of_exchange_changes_answer :
    (raisedBooleanContext.2.lookup (0 : Fin 2)).2.down ⟨⟨PUnit.unit, false⟩, true⟩ = true ∧
      (raisedBooleanContext.2.components (ULift.up exchange) (0 : Fin 2)).2.down
        ⟨⟨PUnit.unit, false⟩, true⟩ = false := ⟨rfl, rfl⟩

theorem incompatible_annotation_still_rejected :
    ModelData.check? (raised.data.evaluateTerm raisedComponents (Controls.fullBranch 0))
      (ULift.up wrongAnnotation) = none := by
  have read := model.evaluateTerm_universeLift.{0, 1, 0, 1, 0, 2, 2, 2, 2}
    (Controls.fullBranch 0) declarations.componentContext _ declarations.branch_read
  have rejected : Value.atType?
      (liftValue.{1, 0, 1, 0, 2, 2, 2, 2}
        (⟨branchType, declarations.branch⟩ : Value familyModel.toCwf declarations.componentContext.1))
      (ULift.up wrongAnnotation) = none :=
    (liftValue_atType _ _).trans
      (congrArg (Option.map ULift.up) (Value.atType?_none _ _ branch_annotation_differs))
  exact (congrArg (fun result => ModelData.check? (C := commonLiftWithTerminal.{1, 0, 1, 0, 2} familyModel)
    result (ULift.up wrongAnnotation)) read).trans rejected

theorem omission_of_second_witness_changes_answer :
    (extracted.down trueOne).val ≠ (extracted.down trueZero).val := by
  rw [extracted_retains_supplied_branch]
  exact omission_of_second_witness_detected

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.UniverseControls
