import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelMapComposition
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalModelMapControls

/-!
# Composed maps on supplied dependent certificates

Decoding a marked model and adding a different mark changes its actual type
presentations. The composite retains the full-motive branch and its exact
generated certificate. Three-stage comparisons and a nonidentity exchanged
substitution exercise both type and term actions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.ModelMapCompositionControls

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualTelescopeMorphism
open Mettapedia.TypeTheory.ContextualStrictMorphismComposition
open Mettapedia.TypeTheory.ContextualTypeOperations
open ModelMapControls

def remark : ModelMap (markedData true) (markedData false) := (forget true).comp (attach false)

theorem contexts {n : Nat} (Γ : Context original n) :
    ContextImage remark.morphism (markContext true Γ) (markContext false Γ) :=
  contextImage_comp (forget true).morphism (attach false).morphism
    (decoder_telescope true Γ.2) (embedding_telescope false Γ.2)

theorem changed_annotation : remark.morphism.toFamilyMorphism.mapType (branchType, true) =
    (branchType, false) := rfl

theorem composition_is_not_identity_on_types :
    remark.morphism.toFamilyMorphism.mapType (branchType, true) ≠ (branchType, true) := by
  rw [changed_annotation]
  exact supplied_marks_distinct.symm

theorem exact_full_motive_value :
    ValueImage remark.morphism
      (⟨(branchType, true), suppliedBranch⟩ : Value markedModel.toCwf branchContext.1)
      (⟨(branchType, false), suppliedBranch⟩ : Value markedModel.toCwf branchContext.1) :=
  remark.evaluateTerm_image_unique DeclaredModel.Declarations.pairElimination
    (markContext true branchContext) (markContext false branchContext) (contexts branchContext)
    _ _ (complete_sum_readout true) (complete_sum_readout false)

theorem exact_generated_section :
    HEq (remark.morphism.toFamilyMorphism.mapTerm (extractedMarkedBranch true))
      (extractedMarkedBranch false) :=
  Derivation.termSection_modelMap remark (marked_realization true)
    marked_product_substitution marked_product_beta marked_product_eta
    (marked_realization false) marked_product_substitution marked_product_beta marked_product_eta
    (Controls.fullBranchTyped Controls.emptyContext) (Controls.fullBranchTyped Controls.emptyContext)
    (markContext true branchContext) (markContext false branchContext) (contexts branchContext)
    (branchType, true) (branchType, false) ((marked_realization true).termHeader .fullBranch)
    ((marked_realization true).termResult .fullBranch) ((marked_realization false).termHeader .fullBranch)
    ((marked_realization false).termResult .fullBranch)

theorem exact_supplied_second_witness (point : branchContext.1) :
    (remark.morphism.toFamilyMorphism.mapTerm (extractedMarkedBranch true) point).val =
      (suppliedBranch point).val := by
  rw [eq_of_heq exact_generated_section, generated_section_readout false]

theorem varying_witness_readouts :
    (remark.morphism.toFamilyMorphism.mapTerm (extractedMarkedBranch true) ModelControls.trueZero).val = 0 ∧
    (remark.morphism.toFamilyMorphism.mapTerm (extractedMarkedBranch true) ModelControls.trueOne).val = 1 := by
  rw [eq_of_heq exact_generated_section, generated_section_readout false]
  exact full_motive_retains_second_witness

theorem round_trip : (attach true).comp (forget true) = ModelMap.identity ModelControls.model := by
  apply ModelMap.ext_of_morphism
  apply ext_of_family
  rfl

theorem three_stage_comparison :
    ((attach true).comp (forget true)).comp (attach false) = (attach true).comp remark :=
  ModelMap.assoc (attach true) (forget true) (attach false)

theorem three_stage_reduces_to_supplied_mark : (attach true).comp remark = attach false := by
  rw [← three_stage_comparison, round_trip, ModelMap.identity_comp]

theorem actual_exchanged_substitution :
    (markedData false).evaluateSubstitution (markContext false ModelControls.booleanContext)
      (markContext false ModelControls.booleanContext) ModelControls.exchangeRaw =
      some (imageArrow remark.morphism (contexts ModelControls.booleanContext).contexts
        (contexts ModelControls.booleanContext).contexts ModelControls.exchange) :=
  remark.evaluateSubstitution_image (markContext true ModelControls.booleanContext)
    (markContext true ModelControls.booleanContext) (markContext false ModelControls.booleanContext)
    (markContext false ModelControls.booleanContext) (contexts ModelControls.booleanContext)
    (contexts ModelControls.booleanContext) ModelControls.exchangeRaw ModelControls.exchange
    (actual_exchange_assembled true)

theorem exchanged_arrow_is_nonidentity :
    imageArrow remark.morphism (contexts ModelControls.booleanContext).contexts
      (contexts ModelControls.booleanContext).contexts ModelControls.exchange ≠
        markedModel.toCwf.idS ModelControls.booleanContext.1 := by
  have same : imageArrow remark.morphism (contexts ModelControls.booleanContext).contexts
      (contexts ModelControls.booleanContext).contexts ModelControls.exchange = ModelControls.exchange :=
    (eq_of_heq (imageArrow_heq _ _ _ _)).symm
  rw [same]
  intro identical
  have read := congrArg (fun function => (function ⟨⟨PUnit.unit, false⟩, true⟩).2) identical
  change false = true at read
  cases read

theorem omitting_second_type_action_changes_annotation :
    (attach true).morphism.toFamilyMorphism.mapType branchType ≠
      ((attach true).comp remark).morphism.toFamilyMorphism.mapType branchType := by
  change (branchType, true) ≠ (branchType, false)
  exact supplied_marks_distinct

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.ModelMapCompositionControls
