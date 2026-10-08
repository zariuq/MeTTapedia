import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationNormalization

/-!
# Canonical admission of the independently supplied interpretation

The interpreted base and fresh objects give the primitive comparison
isomorphisms. Their actual values calibrate the atomic presentation, while
the constructor calibration recovers every independently supplied primitive
arrow. Thus the interpretation itself satisfies the local extension contract.

The comparison and uniqueness concern these actual local declaration
readings. A free-extension action and its adjunction are further constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.CanonicalExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation FunctorNormalization

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]

private theorem calibrated_map {mapping : Object signature ⥤ D}
    {source target : Object signature} (input : ObjectImage mapping source)
    (output : ObjectImage mapping target)
    (inputSame : input = ⟨mapping.obj source, Iso.refl _⟩)
    (outputSame : output = ⟨mapping.obj target, Iso.refl _⟩) (arrow : source ⟶ target) :
    input.comparison.inv ≫ mapping.map arrow ≫ output.comparison.hom =
      eqToHom (congrArg ObjectImage.value inputSame) ≫ mapping.map arrow ≫
        eqToHom (congrArg ObjectImage.value outputSame).symm := by
  cases inputSame
  cases outputSame
  simp only [Iso.refl_inv, Iso.refl_hom, eqToHom_refl, Category.id_comp, Category.comp_id]

variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : Assignment C symbols D) (realization : Realization signature meanings)

abbrev interpreted := Interpretation.functor meanings realization

def images : AtomicPresentation.PrimitiveImages (interpreted meanings realization) meanings where
  base := eqToIso (functor_base meanings realization)
  object origin := eqToIso (CoherentExtension.target_named_object meanings realization origin)

theorem atomic_image (source : Object signature) :
    AtomicPresentation.image (interpreted meanings realization) meanings
      (images meanings realization) source =
        ⟨(interpreted meanings realization).obj source, Iso.refl _⟩ := by
  rcases source with ⟨code, formed⟩
  cases code with
  | base object =>
      apply InterpretationNormalization.image_eq_refl _
        (functor_base_object meanings realization object).symm
      change (eqToHom (functor_base meanings realization)).app object = _
      rw [eqToHom_app]
  | name origin =>
      apply InterpretationNormalization.image_eq_refl _
        (CoherentExtension.target_named_object meanings realization origin).symm
      rfl
  | terminal => rfl
  | product first second => rfl
  | exponential argument result => rfl
  | equalizer source target first second => rfl

theorem atomic_functor : AtomicPresentation.functor (interpreted meanings realization) meanings
    (images meanings realization) = interpreted meanings realization := by
  refine _root_.CategoryTheory.Functor.ext
    (fun source => congrArg ObjectImage.value (atomic_image meanings realization source)) ?_
  intro source target arrow
  exact calibrated_map _ _ (atomic_image meanings realization source)
    (atomic_image meanings realization target) arrow

theorem assignment_congr {first second : Object signature ⥤ D}
    [PreservesFiniteLimits first] [MonoidalClosedFunctor first]
    [PreservesFiniteLimits second] [MonoidalClosedFunctor second]
    (same : first = second) (headers : HeaderFormation signature) :
    assignment first headers = assignment second headers := by
  cases same
  rfl

theorem arrow_images (headers : HeaderFormation signature) :
    CoherentExtension.ArrowImages (interpreted meanings realization) meanings
      (images meanings realization) headers where
  arrow origin := congrArg (fun supplied : Assignment C symbols D => supplied.arrow origin)
    ((assignment_congr (atomic_functor meanings realization) headers).trans
      (InterpretationNormalization.normalized_assignment meanings realization headers))

def comparison (headers : HeaderFormation signature) :
    interpreted meanings realization ≅ Interpretation.functor meanings realization :=
  CoherentExtension.comparison (interpreted meanings realization) meanings
    (images meanings realization) headers (arrow_images meanings realization headers) realization

theorem comparison_admitted (headers : HeaderFormation signature) :
    CoherentExtension.CellAdmission (interpreted meanings realization) meanings
      (images meanings realization) realization (comparison meanings realization headers).hom :=
  CoherentExtension.comparison_admitted (interpreted meanings realization) meanings
    (images meanings realization) headers (arrow_images meanings realization headers) realization

theorem identity_admitted : CoherentExtension.CellAdmission (interpreted meanings realization) meanings
    (images meanings realization) realization (𝟙 (interpreted meanings realization)) where
  base object := by
    change 𝟙 _ = (eqToHom (functor_base meanings realization)).app object ≫
      eqToHom (functor_base_object meanings realization object).symm
    rw [eqToHom_app, eqToHom_trans, eqToHom_refl]
  object origin := by
    change 𝟙 _ = eqToHom (CoherentExtension.target_named_object meanings realization origin) ≫
      eqToHom (CoherentExtension.target_named_object meanings realization origin).symm
    rw [eqToHom_trans, eqToHom_refl]

theorem comparison_eq_refl (headers : HeaderFormation signature) :
    comparison meanings realization headers = Iso.refl (interpreted meanings realization) := by
  apply Iso.ext
  exact (CoherentExtension.admitted_cell_unique (interpreted meanings realization) meanings
    (images meanings realization) headers (arrow_images meanings realization headers) realization
    (𝟙 (interpreted meanings realization)) (identity_admitted meanings realization)).symm

@[instance_reducible] def admittedIsoUnique (headers : HeaderFormation signature) :
    Unique (CoherentExtension.AdmittedIso (interpreted meanings realization) meanings
      (images meanings realization) realization) :=
  CoherentExtension.admittedIsoUnique (interpreted meanings realization) meanings
    (images meanings realization) realization headers (arrow_images meanings realization headers)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.CanonicalExtension
