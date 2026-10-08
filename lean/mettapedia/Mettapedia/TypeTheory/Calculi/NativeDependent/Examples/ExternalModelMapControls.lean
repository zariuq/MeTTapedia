import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelMapReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalModelControls
import Mettapedia.TypeTheory.ContextualMarkedTypeEmbedding
import Mettapedia.TypeTheory.ContextualLogicalMorphismControls

/-!
# Logical model-map controls on actual dependent expressions

Constant supplied marks distinguish source type presentations. Forgetting
them preserves the actual function-indexed dependent families and sections.
The full-motive generated sum expression, its primitive branch, and a real
exchanged variable substitution exercise the independent source evaluators.
Incompatible source annotations can become compatible after decoding.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.ModelMapControls

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualTelescopeMorphism
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualLogicalMorphism
open Mettapedia.TypeTheory.ContextualMarkedTypes
open Mettapedia.TypeTheory.ContextualPiEta

abbrev original := ModelControls.familyModel
abbrev markedModel := withTerminal original
abbrev markedProducts := products ModelControls.products
abbrev markedSums := Mettapedia.TypeTheory.ContextualLogicalMorphismControls.markedSums

def markTelescope (mark : Bool) : {n : Nat} → {Γ : original.toCwf.Ctx} →
    Telescope original n Γ → Telescope markedModel n Γ
  | _, _, .nil => .nil
  | _, _, .snoc previous A => .snoc (markTelescope mark previous) (A, mark)

def markContext (mark : Bool) {n : Nat} (Γ : Context original n) : Context markedModel n :=
  ⟨Γ.1, markTelescope mark Γ.2⟩

theorem embedding_telescope (mark : Bool) : {n : Nat} → {Γ : original.toCwf.Ctx} →
    (telescope : Telescope original n Γ) →
    ContextImage (embedding original mark) ⟨Γ, telescope⟩ ⟨Γ, markTelescope mark telescope⟩
  | _, _, .nil => ContextImage.nil _
  | _, _, .snoc previous A =>
      (embedding_telescope mark previous).snoc _ (A' := (A, mark)) HEq.rfl

theorem decoder_telescope (mark : Bool) : {n : Nat} → {Γ : original.toCwf.Ctx} →
    (telescope : Telescope original n Γ) →
    ContextImage (decoder original) ⟨Γ, markTelescope mark telescope⟩ ⟨Γ, telescope⟩
  | _, _, .nil => ContextImage.nil _
  | _, _, .snoc previous A =>
      (decoder_telescope mark previous).snoc _ (A := (A, mark)) HEq.rfl

def markedData (mark : Bool) : ModelData Controls.symbols markedModel where
  products := markedProducts
  sums := markedSums
  typeParameters symbol := markContext mark (ModelControls.model.typeParameters symbol)
  typeFamily symbol := ⟨ModelControls.model.typeFamily symbol, mark⟩
  termParameters symbol := markContext mark (ModelControls.model.termParameters symbol)
  termType symbol := ⟨ModelControls.model.termType symbol, mark⟩
  termValue symbol := ModelControls.model.termValue symbol

def attach (mark : Bool) : ModelMap ModelControls.model (markedData mark) where
  morphism := embedding original mark
  logical := ⟨products_embedding_preserved original mark ModelControls.products,
    sums_embedding_preserved original mark ModelControls.sums.operations⟩
  typeParameters symbol := embedding_telescope mark (ModelControls.model.typeParameters symbol).2
  typeFamily _ := HEq.rfl
  termParameters symbol := embedding_telescope mark (ModelControls.model.termParameters symbol).2
  termType _ := HEq.rfl
  termValue _ := HEq.rfl

def forget (mark : Bool) : ModelMap (markedData mark) ModelControls.model where
  morphism := decoder original
  logical := ⟨products_preserved original ModelControls.products,
    sums_preserved original ModelControls.sums.operations⟩
  typeParameters symbol := decoder_telescope mark (ModelControls.model.typeParameters symbol).2
  typeFamily _ := HEq.rfl
  termParameters symbol := decoder_telescope mark (ModelControls.model.termParameters symbol).2
  termType _ := HEq.rfl
  termValue _ := HEq.rfl

theorem canonical_mark_image (mark : Bool) : {n : Nat} → {Γ : original.toCwf.Ctx} →
    (telescope : Telescope original n Γ) →
    imageContext (embedding original mark) ⟨Γ, telescope⟩ = ⟨Γ, markTelescope mark telescope⟩
  | _, _, .nil => rfl
  | _, _, .snoc previous A =>
      (imageContext_snoc (embedding original mark) ⟨_, previous⟩ A).trans
        (context_snoc_heq (canonical_mark_image mark previous)
          (imageType_heq (embedding original mark) _ A).symm)

/-- Primitive declaration realization in the marked model is earned from
the actual header parser and the independent source header equations. -/
theorem marked_realization (mark : Bool) : SignatureRealization (markedData mark) Controls.signature where
  typeHeader symbol := by
    have read := (attach mark).evaluateContext_image (Controls.signature.typeParameters symbol)
      (ModelControls.model.typeParameters symbol) (ModelControls.realization.typeHeader symbol)
    exact read.trans (congrArg some
      (canonical_mark_image mark (ModelControls.model.typeParameters symbol).2))
  termHeader symbol := by
    have read := (attach mark).evaluateContext_image (Controls.signature.termParameters symbol)
      (ModelControls.model.termParameters symbol) (ModelControls.realization.termHeader symbol)
    exact read.trans (congrArg some
      (canonical_mark_image mark (ModelControls.model.termParameters symbol).2))
  termResult symbol := by
    rcases (attach mark).evaluateType_image (Controls.signature.termResult symbol)
      (ModelControls.model.termParameters symbol) _
      (embedding_telescope mark (ModelControls.model.termParameters symbol).2)
      (ModelControls.model.termType symbol) (ModelControls.realization.termResult symbol) with
      ⟨actual, read, related⟩
    have types : actual = (ModelControls.model.termType symbol, mark) := (eq_of_heq related).symm
    exact read.trans (congrArg some types)

theorem marked_product_substitution : StrictPiSubstitution markedProducts := by
  refine ⟨?_, ?_, ?_⟩
  · intro Γ Δ σ A B
    rfl
  · intro Γ Δ σ A B body
    rfl
  · intro Γ Δ σ A B function argument function' functions
    cases eq_of_heq functions
    rfl

theorem marked_product_beta : PiBeta markedProducts := by
  intro Γ A B body argument
  rfl

theorem marked_product_eta : PiEta markedProducts marked_product_substitution.1 := by
  intro Γ A B function
  have read : genericSection markedProducts marked_product_substitution.1 function =
      (fun point : markedModel.toCwf.ext Γ A => function point.1 point.2) :=
    eq_of_heq (genericSection_heq markedProducts marked_product_substitution.1 function)
  rw [read]
  rfl

abbrev branchContext := ModelControls.declarations.componentContext
abbrev branchType := ModelControls.model.termType .fullBranch
abbrev suppliedBranch := ModelControls.declarations.branch

/-- The whole generated function transfers through the earned judgment
action, using the actual independent 68-rule certificate. -/
theorem generated_function_interpreted (mark : Bool) :
    Interprets (markedData mark) (.term .nil Controls.fullMotiveFunction
      (.pi (Controls.sum 0) (Controls.motive 0))) :=
  Controls.fullMotiveFunctionTyped.sound_modelMap (attach mark) ModelControls.realization
    Families.products_substitution
    (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts)
    ModelControls.products_eta

set_option backward.isDefEq.respectTransparency false in
theorem attached_readout (mark : Bool) {n : Nat} (Γ : Context original n)
    (term : TermExpr Controls.symbols n) (A : original.toCwf.Ty Γ.1)
    (value : original.toCwf.Tm Γ.1 A)
    (sourceRead : ModelControls.model.evaluateTerm Γ term = some ⟨A, value⟩) :
    (markedData mark).evaluateTerm (markContext mark Γ) term = some ⟨(A, mark), value⟩ := by
  have contexts := embedding_telescope mark Γ.2
  rcases (attach mark).evaluateTerm_image term Γ (markContext mark Γ) contexts _ sourceRead with
    ⟨actualValue, read, related⟩
  rcases ValueImage.at_type (embedding original mark) contexts.contexts
    (A' := (A, mark)) HEq.rfl value actualValue related with
    ⟨valueWitness, valueRead, sections⟩
  rw [valueRead] at read
  have exactSection : valueWitness = value := (eq_of_heq sections).symm
  simpa only [exactSection] using read

theorem complete_sum_readout (mark : Bool) :
    (markedData mark).evaluateTerm (markContext mark branchContext)
      DeclaredModel.Declarations.pairElimination =
      some ⟨(branchType, mark), suppliedBranch⟩ :=
  attached_readout mark branchContext DeclaredModel.Declarations.pairElimination branchType suppliedBranch
    (ModelControls.declarations.pair_elimination_read Families.products_substitution
      (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts)
      ModelControls.products_eta)

theorem primitive_branch_readout (mark : Bool) :
    (markedData mark).evaluateTerm (markContext mark branchContext) (Controls.fullBranch 0) =
      some ⟨(branchType, mark), suppliedBranch⟩ :=
  attached_readout mark branchContext (Controls.fullBranch 0) branchType suppliedBranch
    ModelControls.declarations.branch_read

noncomputable def extractedMarkedBranch (mark : Bool) :=
  (Controls.fullBranchTyped Controls.emptyContext).termSection (markedData mark)
    (marked_realization mark) marked_product_substitution marked_product_beta marked_product_eta
    (markContext mark branchContext) (branchType, mark)
    ((marked_realization mark).termHeader .fullBranch)
    ((marked_realization mark).termResult .fullBranch)

theorem generated_section_preserved (mark : Bool) :
    HEq ((attach mark).morphism.toFamilyMorphism.mapTerm ModelControls.extractedBranch)
      (extractedMarkedBranch mark) :=
  Derivation.termSection_modelMap (attach mark) ModelControls.realization
    Families.products_substitution
    (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts) ModelControls.products_eta
    (marked_realization mark) marked_product_substitution marked_product_beta marked_product_eta
    (Controls.fullBranchTyped Controls.emptyContext) (Controls.fullBranchTyped Controls.emptyContext)
    branchContext (markContext mark branchContext) (embedding_telescope mark branchContext.2)
    branchType (branchType, mark) (ModelControls.realization.termHeader .fullBranch)
    (ModelControls.realization.termResult .fullBranch)
    ((marked_realization mark).termHeader .fullBranch) ((marked_realization mark).termResult .fullBranch)

theorem generated_section_readout (mark : Bool) : extractedMarkedBranch mark = suppliedBranch := by
  have actual : ModelControls.extractedBranch = extractedMarkedBranch mark :=
    eq_of_heq (generated_section_preserved mark)
  exact actual.symm.trans ModelControls.extracted_branch_is_supplied

theorem decoding_complete_sum (mark : Bool) :
    ValueImage (decoder original)
      (⟨(branchType, mark), suppliedBranch⟩ : Value markedModel.toCwf branchContext.1)
      (⟨branchType, suppliedBranch⟩ : Value original.toCwf branchContext.1) :=
  (forget mark).evaluateTerm_image_unique DeclaredModel.Declarations.pairElimination
    (markContext mark branchContext) branchContext (decoder_telescope mark branchContext.2)
    _ _ (complete_sum_readout mark)
    (ModelControls.declarations.pair_elimination_read Families.products_substitution
      (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts)
      ModelControls.products_eta)

theorem full_motive_retains_second_witness :
    (suppliedBranch ModelControls.trueZero).val = 0 ∧
      (suppliedBranch ModelControls.trueOne).val = 1 := ⟨rfl, rfl⟩

theorem function_changes_fibre :
    Fintype.card (ModelControls.declarations.fibre ⟨PUnit.unit, ModelControls.falseFunction⟩) = 1 ∧
      Fintype.card (ModelControls.declarations.fibre ⟨PUnit.unit, ModelControls.trueFunction⟩) = 2 :=
  ModelControls.function_changes_domain

theorem supplied_marks_distinct : (branchType, true) ≠ (branchType, false) := by
  intro same
  have marks := congrArg Prod.snd same
  cases marks

theorem decoding_identifies_marks :
    (decoder original).toFamilyMorphism.mapType (branchType, true) =
      (decoder original).toFamilyMorphism.mapType (branchType, false) := rfl

theorem source_check_rejects_other_mark :
    ModelData.check? ((markedData true).evaluateTerm (markContext true branchContext)
      DeclaredModel.Declarations.pairElimination) (branchType, false) = none := by
  rw [complete_sum_readout]
  change Value.atType? (K := markedModel.toCwf) ⟨(branchType, true), suppliedBranch⟩
    (branchType, false) = none
  exact Value.atType?_none _ _ supplied_marks_distinct

theorem decoded_check_accepts :
    ModelData.check? (ModelControls.model.evaluateTerm branchContext
      DeclaredModel.Declarations.pairElimination)
      ((decoder original).toFamilyMorphism.mapType (branchType, false)) = some suppliedBranch := by
  rw [ModelControls.declarations.pair_elimination_read Families.products_substitution
    (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts)
    ModelControls.products_eta]
  exact ModelData.check?_supplied _ _

/-- The same actual nonidentity exchanged arrow is assembled in the
marked telescope; no component is silently replaced by an identity. -/
theorem actual_exchange_assembled (mark : Bool) :
    (markedData mark).evaluateSubstitution (markContext mark ModelControls.booleanContext)
      (markContext mark ModelControls.booleanContext) ModelControls.exchangeRaw =
      some ModelControls.exchange := by
  have contexts := embedding_telescope mark ModelControls.booleanContext.2
  have read := (attach mark).evaluateSubstitution_image ModelControls.booleanContext
    ModelControls.booleanContext _ _ contexts contexts ModelControls.exchangeRaw
    ModelControls.exchange ModelControls.exchange_evaluated
  have arrow : imageArrow (embedding original mark) contexts.contexts contexts.contexts
      ModelControls.exchange = ModelControls.exchange :=
    eq_of_heq (imageArrow_heq _ _ _ _).symm
  exact read.trans (congrArg some arrow)

theorem exchanged_variable_readouts (mark : Bool) :
    (markedData mark).evaluateTerm (markContext mark ModelControls.booleanContext) (.var 0) =
      some ⟨((fun _ => Bool), mark), (fun point => point.2)⟩ ∧
    (markedData mark).evaluateTerm (markContext mark ModelControls.booleanContext) (.var 1) =
      some ⟨((fun _ => Bool), mark), (fun point => point.1.2)⟩ := ⟨rfl, rfl⟩

theorem omitted_exchange_detected :
    (ModelControls.exchange ⟨⟨PUnit.unit, false⟩, true⟩).2 = false ∧
      (⟨⟨PUnit.unit, false⟩, true⟩ : ModelControls.booleanContext.1).2 = true := ⟨rfl, rfl⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.ModelMapControls
