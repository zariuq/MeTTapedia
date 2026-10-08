import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorCanonicalExtension
import Mettapedia.GSLT.Core.RelativeClosedFunctorReconstructionControls

/-!
# Generator admission distinguishes actual coherent closed extensions

The independently supplied Boolean identity and negation are retained by a
weak closed interpretation. Conjugating its fresh object by negation preserves
both declarations, but changes the actual complete natural comparison. Thus
the fixed-generator admission rejects a real alternative closed extension
cell; the admitted canonical cell remains uniquely determined.

Both cells are defined on the complete generated finite-limit closed category,
including its exponential and authored equalizer objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedFunctorExtensionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory Interpretation FunctorNormalization
open RelativeClosedInterpretationPreservationControls

abbrev weak := RelativeClosedFunctorReconstructionControls.weak
abbrev headers := RelativeClosedFunctorReconstructionControls.headers
abbrev meanings := assignment weak headers
abbrev realization := reconstruction_realization weak headers

def negationIso : ULift.{0} Bool ≅ ULift.{0} Bool where
  hom := TypeCat.ofHom (fun value => ULift.up (Bool.not value.down))
  inv := TypeCat.ofHom (fun value => ULift.up (Bool.not value.down))
  hom_inv_id := by
    ext value
    cases value with
    | up value => change Bool.not (Bool.not value) = value
                  rw [Bool.not_not]
  inv_hom_id := by
    ext value
    cases value with
    | up value => change Bool.not (Bool.not value) = value
                  rw [Bool.not_not]

def switchedImages : AtomicPresentation.PrimitiveImages weak meanings where
  base := Iso.refl _
  object _ := negationIso

abbrev switchedFunctor := AtomicPresentation.functor weak meanings switchedImages

theorem primitive_assignment_read (mapping : Object signature ⥤ Type)
    [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping] (origin : Bool) :
    (assignment mapping headers).arrow origin =
      ⟨mapping.obj dataObject, mapping.obj dataObject, mapping.map (declared origin)⟩ := by
  change (⟨(objectImage mapping dataObject).value, (objectImage mapping dataObject).value,
    (objectImage mapping dataObject).comparison.inv ≫ mapping.map (declared origin) ≫
      (objectImage mapping dataObject).comparison.hom⟩ : ArrowValue Type) = _
  have calibrated : objectImage mapping dataObject = ⟨mapping.obj dataObject, Iso.refl _⟩ :=
    objectImage_named mapping ()
  rw [calibrated]
  simp only [Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]

theorem wrapped_identity (value : ULift Bool) : weak.map (declared false) value = value := by
  change ULift.up (interpreted.map (declared false) value.down) = value
  rw [actual_identity]
  cases value
  rfl

theorem switched_declaration (origin : Bool) :
    switchedFunctor.map (declared origin) = weak.map (declared origin) := by
  ext value
  change ULift.up (Bool.not (weak.map (declared origin) (ULift.up (Bool.not value.down))).down) =
    weak.map (declared origin) value
  cases value with
  | up value =>
      cases origin with
      | false => rw [wrapped_identity, wrapped_identity, Bool.not_not]
      | true =>
          rw [RelativeClosedFunctorNormalizationControls.wrapped_negation,
            RelativeClosedFunctorNormalizationControls.wrapped_negation, Bool.not_not]

theorem switched_arrows : CoherentExtension.ArrowImages weak meanings switchedImages headers where
  arrow origin := by
    rw [primitive_assignment_read switchedFunctor origin, primitive_assignment_read weak origin]
    exact congrArg (fun arrow : ULift Bool ⟶ ULift Bool =>
      (⟨ULift Bool, ULift Bool, arrow⟩ : ArrowValue Type)) (switched_declaration origin)

def switchedComparison : weak ≅ reconstructedFunctor weak headers :=
  CoherentExtension.comparison weak meanings switchedImages headers switched_arrows realization

theorem switched_comparison_admitted : CoherentExtension.CellAdmission weak meanings switchedImages
    realization switchedComparison.hom :=
  CoherentExtension.comparison_admitted weak meanings switchedImages headers switched_arrows realization

def switchedReadout : ULift Bool ⟶ ULift Bool :=
  switchedComparison.hom.app dataObject ≫ eqToHom (reconstructed_named_object weak headers ())

theorem switchedReadout_complete : switchedReadout = negationIso.hom := by
  unfold switchedReadout
  have component := CoherentExtension.comparison_hom_name weak meanings switchedImages
    headers switched_arrows realization ()
  exact (congrArg (fun arrow : weak.obj dataObject ⟶ (reconstructedFunctor weak headers).obj dataObject =>
    arrow ≫ eqToHom (reconstructed_named_object weak headers ())) component).trans (by
      change (negationIso.hom ≫ eqToHom
        (CoherentExtension.target_named_object meanings realization ()).symm) ≫
          eqToHom (reconstructed_named_object weak headers ()) = _
      rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])

def canonicalReadout : ULift Bool ⟶ ULift Bool :=
  (parserComparison weak headers).hom.app dataObject ≫
    eqToHom (reconstructed_named_object weak headers ())

theorem canonicalReadout_complete : canonicalReadout = 𝟙 (ULift Bool) := by
  unfold canonicalReadout
  exact (congrArg (fun arrow : weak.obj dataObject ⟶ (reconstructedFunctor weak headers).obj dataObject =>
    arrow ≫ eqToHom (reconstructed_named_object weak headers ()))
      (parserComparison_hom_name weak headers ())).trans (by
        rw [eqToHom_trans, eqToHom_refl]
        rfl)

theorem switched_retains_supplied_values :
    (switchedReadout (ULift.up false)).down = true ∧
      (switchedReadout (ULift.up true)).down = false := by
  rw [switchedReadout_complete]
  exact ⟨rfl, rfl⟩

theorem complete_cells_differ : switchedComparison.hom ≠ (parserComparison weak headers).hom := by
  intro same
  have read := congrArg (fun cell : weak ⟶ reconstructedFunctor weak headers =>
    (cell.app dataObject ≫ eqToHom (reconstructed_named_object weak headers ())) (ULift.up false)) same
  change switchedReadout (ULift.up false) = canonicalReadout (ULift.up false) at read
  rw [switchedReadout_complete, canonicalReadout_complete] at read
  exact Bool.false_ne_true (congrArg ULift.down read).symm

theorem switched_fails_fixed_generator_admission :
    ¬ ParserCellAdmission weak headers switchedComparison.hom := by
  intro admitted
  exact complete_cells_differ (FunctorNormalization.admitted_cell_unique weak headers _ admitted)

@[instance_reducible] def canonical_fixed_generator_iso_unique :
    Unique (AdmittedParserIso weak headers) := inferInstance

theorem interpreted_canonical_comparison_is_identity :
    CanonicalExtension.comparison meanings realization headers =
      Iso.refl (Interpretation.functor meanings realization) :=
  CanonicalExtension.comparison_eq_refl meanings realization headers

end Mettapedia.GSLT.Core.RelativeClosedFunctorExtensionControls
