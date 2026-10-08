import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorAtomicPresentation

/-!
# Coherent extension to independently declared target meanings

Primitive object images are compared by an actual base natural isomorphism
and individual fresh-object isomorphisms. Each arrow declaration compares
the complete independently normalized image with the target's supplied
arrow, including its evaluated endpoints. These local readings reconstruct
the target assignment and give a natural isomorphism of the entire closed
functor with its independently evaluated interpretation.

The admitted cells use only the independently supplied primitive comparison
squares. Constructor propagation earns their complete uniqueness. Neither
strict equality of raw headers nor a whole-expression compatibility law is
assumed. A functorial free-extension construction and its biadjunction are
separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.CoherentExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation FunctorNormalization

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]

private theorem assignment_ext {first second : Assignment C symbols D}
    (base : first.base = second.base) (objects : first.object = second.object)
    (arrows : first.arrow = second.arrow) : first = second := by
  cases first
  cases second
  cases base
  cases objects
  cases arrows
  rfl

variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object signature ⥤ D) [PreservesFiniteLimits mapping]
variable [MonoidalClosedFunctor mapping] (meanings : Assignment C symbols D)
variable (images : AtomicPresentation.PrimitiveImages mapping meanings)
variable (headers : HeaderFormation signature)

abbrev presented := AtomicPresentation.functor mapping meanings images

structure ArrowImages : Prop where
  arrow (origin : symbols.ArrowName) :
    (assignment (presented mapping meanings images) headers).arrow origin = meanings.arrow origin

variable (admitted : ArrowImages mapping meanings images headers)

include admitted in
theorem assignment_equal : assignment (presented mapping meanings images) headers = meanings := by
  apply assignment_ext
  · exact AtomicPresentation.functor_base mapping meanings images
  · exact funext (AtomicPresentation.functor_named_object mapping meanings images)
  · exact funext admitted.arrow

private theorem interpretation_equal {first second : Assignment C symbols D}
    (same : first = second) (firstRealization : Realization signature first)
    (secondRealization : Realization signature second) :
    Interpretation.functor first firstRealization = Interpretation.functor second secondRealization := by
  cases same
  rfl

variable (realization : Realization signature meanings)

include admitted in
theorem reconstructed_equal : reconstructedFunctor (presented mapping meanings images) headers =
    Interpretation.functor meanings realization :=
  interpretation_equal (assignment_equal mapping meanings images headers admitted)
    (reconstruction_realization (presented mapping meanings images) headers) realization

def comparison : mapping ≅ Interpretation.functor meanings realization :=
  AtomicPresentation.comparison mapping meanings images ≪≫
    parserComparison (presented mapping meanings images) headers ≪≫
      eqToIso (reconstructed_equal mapping meanings images headers admitted realization)

theorem target_named_object (origin : symbols.ObjectName) :
    (Interpretation.functor meanings realization).obj (namedObject origin) = meanings.object origin :=
  objectValue_unique meanings realization (namedObject origin) _ rfl

structure CellAdmission (cell : mapping ⟶ Interpretation.functor meanings realization) : Prop where
  base (object : C) : cell.app (baseObject signature object) =
    images.base.hom.app object ≫ eqToHom (functor_base_object meanings realization object).symm
  object (origin : symbols.ObjectName) : cell.app (namedObject origin) =
    (images.object origin).hom ≫ eqToHom (target_named_object meanings realization origin).symm

theorem comparison_hom_base (object : C) :
    (comparison mapping meanings images headers admitted realization).hom.app (baseObject signature object) =
      images.base.hom.app object ≫ eqToHom (functor_base_object meanings realization object).symm := by
  change images.base.hom.app object ≫
    ((parserComparison (presented mapping meanings images) headers).hom.app (baseObject signature object) ≫
      (eqToHom (reconstructed_equal mapping meanings images headers admitted realization)).app
        (baseObject signature object)) = _
  rw [parserComparison_hom_base, eqToHom_app, eqToHom_trans]

theorem comparison_hom_name (origin : symbols.ObjectName) :
    (comparison mapping meanings images headers admitted realization).hom.app (namedObject origin) =
      (images.object origin).hom ≫ eqToHom (target_named_object meanings realization origin).symm := by
  change (images.object origin).hom ≫
    ((parserComparison (presented mapping meanings images) headers).hom.app (namedObject origin) ≫
      (eqToHom (reconstructed_equal mapping meanings images headers admitted realization)).app
        (namedObject origin)) = _
  rw [parserComparison_hom_name, eqToHom_app, eqToHom_trans]

theorem comparison_admitted : CellAdmission mapping meanings images realization
    (comparison mapping meanings images headers admitted realization).hom where
  base := comparison_hom_base mapping meanings images headers admitted realization
  object := comparison_hom_name mapping meanings images headers admitted realization

theorem admitted_cell_unique (candidate : mapping ⟶ Interpretation.functor meanings realization)
    (localReadings : CellAdmission mapping meanings images realization candidate) :
    candidate = (comparison mapping meanings images headers admitted realization).hom :=
  FunctorCellUniqueness.cells_equal_of_generators
    (comparison mapping meanings images headers admitted realization) candidate
    (fun object => (localReadings.base object).trans
      (comparison_hom_base mapping meanings images headers admitted realization object).symm)
    (fun origin => (localReadings.object origin).trans
      (comparison_hom_name mapping meanings images headers admitted realization origin).symm)

abbrev AdmittedCell := {cell : mapping ⟶ Interpretation.functor meanings realization //
  CellAdmission mapping meanings images realization cell}

@[instance_reducible] def admittedCellUnique (headers : HeaderFormation signature)
    (admitted : ArrowImages mapping meanings images headers) :
    Unique (AdmittedCell mapping meanings images realization) where
  default := ⟨(comparison mapping meanings images headers admitted realization).hom,
    comparison_admitted mapping meanings images headers admitted realization⟩
  uniq cell := Subtype.ext (admitted_cell_unique mapping meanings images headers admitted realization
    cell.val cell.property)

abbrev AdmittedIso := {iso : mapping ≅ Interpretation.functor meanings realization //
  CellAdmission mapping meanings images realization iso.hom}

@[instance_reducible] def admittedIsoUnique (headers : HeaderFormation signature)
    (admitted : ArrowImages mapping meanings images headers) :
    Unique (AdmittedIso mapping meanings images realization) where
  default := ⟨comparison mapping meanings images headers admitted realization,
    comparison_admitted mapping meanings images headers admitted realization⟩
  uniq iso := Subtype.ext (Iso.ext (admitted_cell_unique mapping meanings images headers admitted realization
    iso.val.hom iso.property))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.CoherentExtension
