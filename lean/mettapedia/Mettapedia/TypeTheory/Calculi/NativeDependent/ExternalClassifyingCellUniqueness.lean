import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelCellIdentity
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalChosenCellReadout

/-!
# Declaration-admitted coherent cells of the generated model

The common-size source retains its authored context objects. Identity at the
complete display contexts of individual primitive declarations propagates
through every successful independent type and context evaluation. Actual
finite syntactic readbacks then cover every chosen context, and the earned
presentation isomorphisms cover every retained raw context.

Uniqueness concerns corrected cells retaining those local primitive readings.
It does not assert that unrestricted contextual transformations are unique.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ClassifyingCells

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open SyntacticReification
open LiftedModelMapComparison

universe u z
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{max u z,max u z,max u z,max u z}}

noncomputable abbrev sourceModel (headers : HeaderFormation D) :=
  (SyntacticModel.qualified headers).commonUniverseLift.{u,u,u,u,u,z}

variable (headers : HeaderFormation D) (target : Interpretation.QualifiedModel D C)
  (mapping : ModelMap (sourceModel.{u,z} headers).data target.data)
  (cell : mapping.morphism.toFamilyMorphism.base ⟶ mapping.morphism.toFamilyMorphism.base)

/-- Every actual finite source scope is fixed by constructor propagation
through its independently authored evaluator readback. -/
theorem scope_fixed (primitive : ModelCellIdentity.PrimitiveIdentity
    (sourceModel.{u,z} headers).data mapping.morphism cell)
    {n : Nat} (scope : Scope D n) :
    cell.app ⟨ULift.up ((quotientProjection D).obj scope.source)⟩ =
      𝟙 (mapping.morphism.toFamilyMorphism.base.obj
        ⟨ULift.up ((quotientProjection D).obj scope.source)⟩) :=
  ModelCellIdentity.context_success_fixed (sourceModel.{u,z} headers).data target.data
    mapping.morphism cell (sourceModel.{u,z} headers).products_substitution
    target.products_substitution target.products_eta mapping.logical.products primitive
    scope.raw (liftContext scope.semantic)
    ((SyntacticModel.data headers).evaluateContext_universeLift
      scope.raw scope.semantic (SyntacticModel.scope_context_read headers scope))

theorem telescope_fixed (primitive : ModelCellIdentity.PrimitiveIdentity
    (sourceModel.{u,z} headers).data mapping.morphism cell)
    {n : Nat} {Γ : quotientContext D}
    (telescope : Telescope (QuotientCwf.withTerminal D) n Γ) :
    cell.app ⟨ULift.up Γ⟩ =
      𝟙 (mapping.morphism.toFamilyMorphism.base.obj ⟨ULift.up Γ⟩) := by
  have same := scope_fixed headers target mapping cell primitive (Scope.ofSemantic ⟨Γ,telescope⟩)
  have sourceSame := congrArg
    (fun context : Mettapedia.TypeTheory.ContextualModelTelescopes.Context
      (QuotientCwf.withTerminal D) n => context.1)
    (Scope.ofSemantic_semantic ⟨Γ,telescope⟩)
  change (quotientProjection D).obj (Scope.ofSemantic ⟨Γ,telescope⟩).source = Γ at sourceSame
  rw [sourceSame] at same
  exact same

/-- Removing only the size and context wrappers preserves every original
ordered substitution and its actual cell naturality. -/
def rawCell (headers : HeaderFormation D) (target : Interpretation.QualifiedModel D C)
    (mapping : ModelMap (sourceModel.{u,z} headers).data target.data)
    (cell : mapping.morphism.toFamilyMorphism.base ⟶ mapping.morphism.toFamilyMorphism.base) :
    contextFunctor mapping ⟶ contextFunctor mapping where
  app Γ := cell.app ⟨ULift.up Γ⟩
  naturality {Γ Δ} arrow := by
    let raised : (⟨ULift.up Γ⟩ :
      (commonLiftWithTerminal.{u,u,u,u,z} (SyntacticModel.C D)).toCwf.base.Context) ⟶
        ⟨ULift.up Δ⟩ := ULift.up arrow
    exact cell.naturality raised

/-- Primitive admission, constructor propagation and presentation
naturality force the entire base transformation on all raw contexts. -/
theorem base_identity (primitive : ModelCellIdentity.PrimitiveIdentity
    (sourceModel.{u,z} headers).data mapping.morphism cell) :
    cell = 𝟙 mapping.morphism.toFamilyMorphism.base := by
  have lower : rawCell headers target mapping cell = 𝟙 (contextFunctor mapping) :=
    Presentation.natTrans_ext_chosen _ _ (fun Γ chosen => by
      rcases chosen.telescope with ⟨telescope⟩
      exact telescope_fixed headers target mapping cell primitive telescope)
  apply NatTrans.ext
  funext Γ
  exact NatTrans.congr_app lower Γ.val.down

variable (first second : ModelMap (sourceModel.{u,z} headers).data target.data)

/-- The actual complete finite comprehension telescope of one authored
primitive family, retaining the supplied parameter positions and family. -/
noncomputable def primitiveDisplayTelescope (symbol : S.TypeSymbol) :
    Telescope (QuotientCwf.withTerminal D) (S.typeArity symbol + 1)
      ((QuotientCwf.cwf D).ext ((SyntacticModel.data headers).typeParameters symbol).1
        ((SyntacticModel.data headers).typeFamily symbol)) :=
  .snoc ((SyntacticModel.data headers).typeParameters symbol).2
    ((SyntacticModel.data headers).typeFamily symbol)

/-- The image of one complete primitive display is compared directly
with the independently supplied target declaration. Only the local header,
family and strict comprehension fields of the model map are used. -/
theorem primitiveImage (symbol : S.TypeSymbol) :
    mapping.morphism.toFamilyMorphism.base.obj ⟨ULift.up ((QuotientCwf.cwf D).ext
      ((SyntacticModel.data headers).typeParameters symbol).1
      ((SyntacticModel.data headers).typeFamily symbol))⟩ =
      (⟨C.toCwf.ext (target.data.typeParameters symbol).1 (target.data.typeFamily symbol)⟩ :
        C.toCwf.base.Context) :=
  ContextualBase.Context.ext (extension_images mapping.morphism
    (mapping.typeParameters symbol).contexts (mapping.typeFamily symbol))

/-- Admission retains each individual primitive's complete displayed
reading. It requires no condition at all generated contexts or families. -/
def PrimitiveAdmission
    (candidate : CorrectedTransformationData first.morphism.toPseudo second.morphism.toPseudo) : Prop :=
  ∀ symbol : S.TypeSymbol,
    candidate.base.app ⟨ULift.up ((QuotientCwf.cwf D).ext
      ((SyntacticModel.data headers).typeParameters symbol).1
      ((SyntacticModel.data headers).typeFamily symbol))⟩ ≫
        eqToHom (primitiveImage headers target second symbol) =
      eqToHom (primitiveImage headers target first symbol)

/-- The actual canonical corrected comparison is admitted declaration by
declaration; its existence was earned from independent model evaluations. -/
theorem canonical_admitted : PrimitiveAdmission headers target first second
    (correctedIso headers first second).hom := by
  intro symbol
  erw [correctedIso_hom_telescope headers first second (primitiveDisplayTelescope headers symbol)]
  simp only [eqToHom_trans]

/-- The independently fixed target declaration square determines the
calibrated complete display reading. The calibration is a derived equality,
not the definition of primitive cell admission. -/
theorem primitive_calibration
    (candidate : CorrectedTransformationData first.morphism.toPseudo second.morphism.toPseudo)
    (admitted : PrimitiveAdmission headers target first second candidate)
    (symbol : S.TypeSymbol) :
    candidate.base.app ⟨ULift.up ((QuotientCwf.cwf D).ext
      ((SyntacticModel.data headers).typeParameters symbol).1
      ((SyntacticModel.data headers).typeFamily symbol))⟩ =
      (correctedIso headers first second).hom.base.app
        ⟨ULift.up ((QuotientCwf.cwf D).ext
          ((SyntacticModel.data headers).typeParameters symbol).1
          ((SyntacticModel.data headers).typeFamily symbol))⟩ := by
  apply (cancel_mono (eqToHom (primitiveImage headers target second symbol))).mp
  exact (admitted symbol).trans (canonical_admitted headers target first second symbol).symm

/-- Every admitted corrected cell equals the earned canonical comparison.
The full displayed data are forced by corrected comprehension coherence. -/
theorem cell_unique
    (candidate : CorrectedTransformationData first.morphism.toPseudo second.morphism.toPseudo)
    (admitted : PrimitiveAdmission headers target first second candidate) :
    candidate = (correctedIso headers first second).hom := by
  let comparison := correctedIso headers first second
  let endo := candidate.base ≫ comparison.inv.base
  have primitive : ModelCellIdentity.PrimitiveIdentity
      (sourceModel.{u,z} headers).data first.morphism endo := by
    intro symbol
    change candidate.base.app _ ≫ comparison.inv.base.app _ = _
    have readings := primitive_calibration headers target first second candidate admitted symbol
    erw [readings]
    exact congrArg (fun transformation => transformation.base.app
      ⟨(commonLiftWithTerminal.{u,u,u,u,z} (SyntacticModel.C D)).toCwf.ext
        ((sourceModel.{u,z} headers).data.typeParameters symbol).1
        ((sourceModel.{u,z} headers).data.typeFamily symbol)⟩) comparison.hom_inv_id
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

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ClassifyingCells
