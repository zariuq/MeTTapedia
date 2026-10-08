import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementModelCellIdentity
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementChosenCellReadout

/-!
# Declaration-admitted uniqueness of full refinement model cells

The local admission compares complete family displays, the distinguished
closed proposition display, and complete guarded primitive-predicate
displays against independently supplied target declarations. It never
refers to the canonical comparison. Actual logical constructor propagation
forces every generated mixed scope, and presentation naturality covers all
retained raw context objects.

Uniqueness concerns genuine corrected contextual cells satisfying these
local declaration squares. Unrestricted context transformations are not
claimed to be unique.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ClassifyingCells

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open Mettapedia.TypeTheory.ContextualPredicateModelScopeUniverseLift
open Mettapedia.TypeTheory.ContextualPredicateScopeMorphism
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open Refinement.Abstract
open SyntacticReification ModelMapComparison

universe u z p v w
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{max u z,max u z,max u z,max u z}}

noncomputable abbrev sourceModel (headers : HeaderFormation D) :=
  (SyntacticModel.qualified headers).commonCarrierLift.{u,u,u,u,u,u,z,0}

private theorem dependent_value_heq {Index : Sort v} {Family : Index → Sort w}
    (value : ∀ index, Family index) {first second : Index} (same : first = second) :
    HEq (value first) (value second) := by
  cases same
  rfl

variable (headers : HeaderFormation D)
  (target : Interpretation.QualifiedModel.{u,max u z,max u z,max u z,max u z,p} D C)
  (mapping : ModelMap (sourceModel.{u,z} headers).data target.data)
  (cell : mapping.morphism.toFamilyMorphism.base ⟶ mapping.morphism.toFamilyMorphism.base)

theorem scope_fixed (primitive : ModelCellIdentity.PrimitiveIdentity
    (sourceModel.{u,z} headers).data mapping.morphism cell)
    {n : Nat} (scope : SyntacticReification.Scope D n) :
    cell.app ⟨ULift.up ((quotientProjection D).obj scope.source)⟩ =
      𝟙 (mapping.morphism.toFamilyMorphism.base.obj
        ⟨ULift.up ((quotientProjection D).obj scope.source)⟩) :=
  ModelCellIdentity.context_success_fixed (sourceModel.{u,z} headers).data
    mapping.morphism cell (sourceModel.{u,z} headers).products_substitution
    target.products_substitution target.products_eta mapping.logical.products
    mapping.predicates primitive scope.raw (raisedScope.{u,z} scope)
    ((SyntacticModel.data headers).evaluateContext_carrierLift scope.raw scope.semantic
      (SyntacticModel.scope_context_read headers scope))

theorem mixed_fixed (primitive : ModelCellIdentity.PrimitiveIdentity
    (sourceModel.{u,z} headers).data mapping.morphism cell)
    {n : Nat} {Γ : QuotientCwf.QContext D}
    (mixed : ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n Γ) :
    cell.app ⟨ULift.up Γ⟩ = 𝟙 (mapping.morphism.toFamilyMorphism.base.obj ⟨ULift.up Γ⟩) := by
  have same := scope_fixed headers target mapping cell primitive
    (SyntacticReification.Scope.ofSemantic ⟨Γ,mixed⟩)
  have sourceSame := congrArg
    (fun scope : ModelScope (QuotientCwf.withTerminal D) (generatedModel D) n => scope.1)
    (SyntacticReification.Scope.ofSemantic_semantic ⟨Γ,mixed⟩)
  change (quotientProjection D).obj (SyntacticReification.Scope.ofSemantic ⟨Γ,mixed⟩).source = Γ
    at sourceSame
  rw [sourceSame] at same
  exact same

def rawCell (headers : HeaderFormation D)
    (target : Interpretation.QualifiedModel.{u,max u z,max u z,max u z,max u z,p} D C)
    (mapping : ModelMap (sourceModel.{u,z} headers).data target.data)
    (cell : mapping.morphism.toFamilyMorphism.base ⟶ mapping.morphism.toFamilyMorphism.base) :
    contextFunctor mapping ⟶ contextFunctor mapping where
  app Γ := cell.app ⟨ULift.up Γ⟩
  naturality {Γ Δ} arrow := by
    let raised : (⟨ULift.up Γ⟩ :
      (Interpretation.SourceModel.{u,z} D).toCwf.base.Context) ⟶ ⟨ULift.up Δ⟩ := ULift.up arrow
    exact cell.naturality raised

/-- Local readings force the whole transformation after genuine mixed
constructor propagation and actual raw-context presentation comparison. -/
theorem base_identity (primitive : ModelCellIdentity.PrimitiveIdentity
    (sourceModel.{u,z} headers).data mapping.morphism cell) :
    cell = 𝟙 mapping.morphism.toFamilyMorphism.base := by
  have lower : rawCell headers target mapping cell = 𝟙 (contextFunctor mapping) :=
    Presentation.natTrans_ext_chosen _ _ (fun Γ chosen => by
      rcases chosen.scope with ⟨mixed⟩
      exact mixed_fixed headers target mapping cell primitive mixed)
  apply NatTrans.ext
  funext Γ
  exact NatTrans.congr_app lower Γ.val.down

variable (first second : ModelMap (sourceModel.{u,z} headers).data target.data)

noncomputable def primitiveFamilyScope (symbol : S.TypeSymbol) :
    ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions (S.typeArity symbol + 1)
      ((QuotientCwf.cwf D).ext ((SyntacticModel.data headers).typeParameters symbol).1
        ((SyntacticModel.data headers).typeFamily symbol)) :=
  .snoc ((SyntacticModel.data headers).typeParameters symbol).2
    ((SyntacticModel.data headers).typeFamily symbol)

noncomputable def omegaScope :
    ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions 1
      ((QuotientCwf.cwf D).ext (QuotientCwf.withTerminal D).empty
        ((generatedModel D).propositions.omega (QuotientCwf.withTerminal D).empty)) :=
  .snoc .nil ((generatedModel D).propositions.omega (QuotientCwf.withTerminal D).empty)

noncomputable def primitivePredicateScope (symbol : S.PredicateSymbol) :
    ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions (S.predicateArity symbol)
      ((generatedModel D).assumptions.assumed ((SyntacticModel.data headers).predicateParameters symbol).1
        ((SyntacticModel.data headers).predicateValue symbol)) :=
  .assume ((SyntacticModel.data headers).predicateParameters symbol).2
    ((SyntacticModel.data headers).predicateValue symbol)

/-- Complete family-display readings follow only from actual header,
family and chosen comprehension preservation. -/
theorem primitiveFamilyImage (symbol : S.TypeSymbol) :
    mapping.morphism.toFamilyMorphism.base.obj
      ⟨(Interpretation.SourceModel.{u,z} D).toCwf.ext
        ((sourceModel.{u,z} headers).data.typeParameters symbol).1
        ((sourceModel.{u,z} headers).data.typeFamily symbol)⟩ =
      (⟨C.toCwf.ext (target.data.typeParameters symbol).1 (target.data.typeFamily symbol)⟩ :
        C.toCwf.base.Context) :=
  ContextualBase.Context.ext (extension_images mapping.morphism
    (mapping.typeParameters symbol).contexts (mapping.typeFamily symbol))

/-- The ordinary proposition generator is compared at its independently
specified closed target display. It is an ordinary type, not a universe. -/
theorem omegaImage :
    mapping.morphism.toFamilyMorphism.base.obj
      ⟨(Interpretation.SourceModel.{u,z} D).toCwf.ext
        (Interpretation.SourceModel.{u,z} D).empty
        ((sourceModel.{u,z} headers).localModel.propositions.omega
          (Interpretation.SourceModel.{u,z} D).empty)⟩ =
      (⟨C.toCwf.ext C.empty (target.localModel.propositions.omega C.empty)⟩ : C.toCwf.base.Context) := by
  have emptyContexts := congrArg ContextualBase.Context.val mapping.morphism.empty_preserved
  have types := (heq_of_eq (mapping.predicates.propositions.formation
    (Interpretation.SourceModel.{u,z} D).empty)).trans
      (dependent_value_heq target.localModel.propositions.omega emptyContexts)
  exact ContextualBase.Context.ext (extension_images mapping.morphism emptyContexts types)

/-- A primitive predicate retains its complete satisfying header object,
using only local parameter, predicate and assumption comparisons. -/
theorem primitivePredicateImage (symbol : S.PredicateSymbol) :
    mapping.morphism.toFamilyMorphism.base.obj
      ⟨(sourceModel.{u,z} headers).localModel.assumptions.assumed
        ((sourceModel.{u,z} headers).data.predicateParameters symbol).1
        ((sourceModel.{u,z} headers).data.predicateValue symbol)⟩ =
      (⟨target.localModel.assumptions.assumed (target.data.predicateParameters symbol).1
        (target.data.predicateValue symbol)⟩ : C.toCwf.base.Context) :=
  ContextualBase.Context.ext (assumption_images mapping.predicates.assumptions
    (mapping.predicateParameters symbol).contexts (mapping.predicateValue symbol))

/-- Intrinsic declaration admission: every square compares the candidate
with an independently supplied target declaration, never a canonical cell. -/
structure PrimitiveAdmission
    (candidate : CorrectedTransformationData first.morphism.toPseudo second.morphism.toPseudo) : Prop where
  families : ∀ symbol : S.TypeSymbol,
    candidate.base.app ⟨(Interpretation.SourceModel.{u,z} D).toCwf.ext
      ((sourceModel.{u,z} headers).data.typeParameters symbol).1
      ((sourceModel.{u,z} headers).data.typeFamily symbol)⟩ ≫
        eqToHom (primitiveFamilyImage headers target second symbol) =
      eqToHom (primitiveFamilyImage headers target first symbol)
  propositions : candidate.base.app ⟨(Interpretation.SourceModel.{u,z} D).toCwf.ext
    (Interpretation.SourceModel.{u,z} D).empty
    ((sourceModel.{u,z} headers).localModel.propositions.omega
      (Interpretation.SourceModel.{u,z} D).empty)⟩ ≫
      eqToHom (omegaImage headers target second) = eqToHom (omegaImage headers target first)
  predicates : ∀ symbol : S.PredicateSymbol,
    candidate.base.app ⟨(sourceModel.{u,z} headers).localModel.assumptions.assumed
      ((sourceModel.{u,z} headers).data.predicateParameters symbol).1
      ((sourceModel.{u,z} headers).data.predicateValue symbol)⟩ ≫
        eqToHom (primitivePredicateImage headers target second symbol) =
      eqToHom (primitivePredicateImage headers target first symbol)

theorem canonical_admitted : PrimitiveAdmission headers target first second
    (correctedIso headers first second).hom where
  families symbol := by
    erw [correctedIso_hom_mixed headers first second (primitiveFamilyScope headers symbol)]
    simp only [eqToHom_trans]
  propositions := by
    erw [correctedIso_hom_mixed headers first second (omegaScope (D := D))]
    simp only [eqToHom_trans]
  predicates symbol := by
    erw [correctedIso_hom_mixed headers first second (primitivePredicateScope headers symbol)]
    simp only [eqToHom_trans]

theorem family_calibration
    (candidate : CorrectedTransformationData first.morphism.toPseudo second.morphism.toPseudo)
    (admitted : PrimitiveAdmission headers target first second candidate) (symbol : S.TypeSymbol) :
    candidate.base.app ⟨(Interpretation.SourceModel.{u,z} D).toCwf.ext
      ((sourceModel.{u,z} headers).data.typeParameters symbol).1
      ((sourceModel.{u,z} headers).data.typeFamily symbol)⟩ =
      (correctedIso headers first second).hom.base.app
        ⟨(Interpretation.SourceModel.{u,z} D).toCwf.ext
          ((sourceModel.{u,z} headers).data.typeParameters symbol).1
          ((sourceModel.{u,z} headers).data.typeFamily symbol)⟩ := by
  apply (cancel_mono (eqToHom (primitiveFamilyImage headers target second symbol))).mp
  exact (admitted.families symbol).trans
    ((canonical_admitted headers target first second).families symbol).symm

theorem omega_calibration
    (candidate : CorrectedTransformationData first.morphism.toPseudo second.morphism.toPseudo)
    (admitted : PrimitiveAdmission headers target first second candidate) :
    candidate.base.app ⟨(Interpretation.SourceModel.{u,z} D).toCwf.ext
      (Interpretation.SourceModel.{u,z} D).empty
      ((sourceModel.{u,z} headers).localModel.propositions.omega
        (Interpretation.SourceModel.{u,z} D).empty)⟩ =
      (correctedIso headers first second).hom.base.app
        ⟨(Interpretation.SourceModel.{u,z} D).toCwf.ext
          (Interpretation.SourceModel.{u,z} D).empty
          ((sourceModel.{u,z} headers).localModel.propositions.omega
            (Interpretation.SourceModel.{u,z} D).empty)⟩ := by
  apply (cancel_mono (eqToHom (omegaImage headers target second))).mp
  exact admitted.propositions.trans (canonical_admitted headers target first second).propositions.symm

/-- Every admitted corrected cell equals the earned canonical comparison.
Complete displayed components follow from its comprehension coherence. -/
theorem cell_unique
    (candidate : CorrectedTransformationData first.morphism.toPseudo second.morphism.toPseudo)
    (admitted : PrimitiveAdmission headers target first second candidate) :
    candidate = (correctedIso headers first second).hom := by
  let comparison := correctedIso headers first second
  let endo := candidate.base ≫ comparison.inv.base
  have primitive : ModelCellIdentity.PrimitiveIdentity
      (sourceModel.{u,z} headers).data first.morphism endo := by
    constructor
    · intro symbol
      change candidate.base.app _ ≫ comparison.inv.base.app _ = _
      have readings := family_calibration headers target first second candidate admitted symbol
      erw [readings]
      exact congrArg (fun transformation => transformation.base.app
        ⟨(Interpretation.SourceModel.{u,z} D).toCwf.ext
          ((sourceModel.{u,z} headers).data.typeParameters symbol).1
          ((sourceModel.{u,z} headers).data.typeFamily symbol)⟩) comparison.hom_inv_id
    · change candidate.base.app _ ≫ comparison.inv.base.app _ = _
      have readings := omega_calibration headers target first second candidate admitted
      erw [readings]
      exact congrArg (fun transformation => transformation.base.app
        ⟨(Interpretation.SourceModel.{u,z} D).toCwf.ext
          (Interpretation.SourceModel.{u,z} D).empty
          ((sourceModel.{u,z} headers).localModel.propositions.omega
            (Interpretation.SourceModel.{u,z} D).empty)⟩) comparison.hom_inv_id
  have fixed := base_identity headers target first endo primitive
  apply CorrectedTransformationData.ext_of_base_eq
  have inverseThenHom := congrArg (fun transformation => transformation.base) comparison.inv_hom_id
  change comparison.inv.base ≫ comparison.hom.base = 𝟙 _ at inverseThenHom
  calc
    candidate.base = candidate.base ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = candidate.base ≫ (comparison.inv.base ≫ comparison.hom.base) := by
      exact congrArg (fun tail => candidate.base ≫ tail) inverseThenHom.symm
    _ = endo ≫ comparison.hom.base := (Category.assoc _ _ _).symm
    _ = 𝟙 _ ≫ comparison.hom.base := congrArg (fun tail => tail ≫ comparison.hom.base) fixed
    _ = comparison.hom.base := Category.id_comp _

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ClassifyingCells
