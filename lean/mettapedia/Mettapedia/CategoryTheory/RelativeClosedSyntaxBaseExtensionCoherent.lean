import Mettapedia.CategoryTheory.RelativeClosedBaseRealizationUniqueness
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionWeakInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorExtension

/-!
# Coherent uniqueness of the weak native base extension

A candidate finite-limit closed diagram is compared with independently
supplied old meanings by a base isomorphism, individual old object
isomorphisms and complete old arrow readings. The two inverse equations
force every added native declaration. Constructor reconstruction then gives
the complete comparison and uniqueness of locally admitted cells.

The target meanings are independent. Neither an added-native-arrow square
nor a whole-expression comparison is part of admission. Raw presentations
and the supplied primitive isomorphisms are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseExtension.Coherent

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation FunctorNormalization

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : Assignment C symbols D)
variable [PreservesFiniteLimits meanings.base] [MonoidalClosedFunctor meanings.base]
variable (realized : Realization signature meanings) (headers : HeaderFormation signature)

abbrev extended := WeakExtension.assignment meanings
abbrev extendedRealization := WeakExtension.realization meanings realized

variable (mapping : Object (extend signature) ⥤ D)
variable [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]
variable (images : AtomicPresentation.PrimitiveImages mapping (extended meanings))

abbrev selected := CoherentExtension.presented mapping (extended meanings) images
abbrev extracted := assignment (selected meanings mapping images) (BaseExtension.headers signature headers)

structure OldArrowImages : Prop where
  arrow (origin : symbols.ArrowName) :
    (extracted meanings headers mapping images).arrow (originalArrows origin) = meanings.arrow origin

theorem native_arrow_image (choice : BaseComparisons.Choice C) :
    (extracted meanings headers mapping images).arrow (comparisonArrows choice) =
      (extended meanings).arrow (comparisonArrows choice) := by
  let current := extracted meanings headers mapping images
  have currentRealization : Realization (extend signature) current :=
    reconstruction_realization (selected meanings mapping images) (BaseExtension.headers signature headers)
  have base : ((comparisonMap signature).precompose current).base =
      (BaseComparisons.WeakDiagram.assignment meanings.base).base :=
    (Functor.id_comp current.base).trans
      (AtomicPresentation.functor_base mapping (extended meanings) images)
  have complete := BaseComparisons.RealizationUniqueness.assignment_equal
    ((comparisonMap signature).precompose current)
    ((comparisonMap signature).realization_precompose current currentRealization)
    (BaseComparisons.WeakDiagram.assignment meanings.base)
    (BaseComparisons.WeakDiagram.realization meanings.base) base
  exact congrArg (fun supplied : Assignment C (BaseComparisons.symbols C) D => supplied.arrow choice) complete

variable (admitted : OldArrowImages meanings headers mapping images)

include admitted in
theorem all_arrow_images : CoherentExtension.ArrowImages mapping (extended meanings) images
    (BaseExtension.headers signature headers) where
  arrow origin := by
    cases origin with
    | inl choice => exact native_arrow_image meanings headers mapping images choice
    | inr origin => exact admitted.arrow origin.down

def comparison : mapping ≅ Interpretation.functor (extended meanings) (extendedRealization meanings realized) :=
  CoherentExtension.comparison mapping (extended meanings) images (BaseExtension.headers signature headers)
    (all_arrow_images meanings headers mapping images admitted) (extendedRealization meanings realized)

abbrev CellAdmission := CoherentExtension.CellAdmission mapping (extended meanings) images
  (extendedRealization meanings realized)

theorem comparison_admitted : CellAdmission meanings realized mapping images
    (comparison meanings realized headers mapping images admitted).hom :=
  CoherentExtension.comparison_admitted mapping (extended meanings) images
    (BaseExtension.headers signature headers) (all_arrow_images meanings headers mapping images admitted)
      (extendedRealization meanings realized)

theorem admitted_cell_unique (candidate : mapping ⟶
    Interpretation.functor (extended meanings) (extendedRealization meanings realized))
    (localReadings : CellAdmission meanings realized mapping images candidate) :
    candidate = (comparison meanings realized headers mapping images admitted).hom :=
  CoherentExtension.admitted_cell_unique mapping (extended meanings) images
    (BaseExtension.headers signature headers) (all_arrow_images meanings headers mapping images admitted)
      (extendedRealization meanings realized) candidate localReadings

abbrev AdmittedCell := {candidate : mapping ⟶
  Interpretation.functor (extended meanings) (extendedRealization meanings realized) //
    CellAdmission meanings realized mapping images candidate}

@[instance_reducible] def admittedCellUnique :
    Unique (AdmittedCell meanings realized mapping images) :=
  CoherentExtension.admittedCellUnique mapping (extended meanings) images
    (extendedRealization meanings realized) (BaseExtension.headers signature headers)
      (all_arrow_images meanings headers mapping images admitted)

abbrev AdmittedIso := {candidate : mapping ≅
  Interpretation.functor (extended meanings) (extendedRealization meanings realized) //
    CellAdmission meanings realized mapping images candidate.hom}

@[instance_reducible] def admittedIsoUnique :
    Unique (AdmittedIso meanings realized mapping images) :=
  CoherentExtension.admittedIsoUnique mapping (extended meanings) images
    (extendedRealization meanings realized) (BaseExtension.headers signature headers)
      (all_arrow_images meanings headers mapping images admitted)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseExtension.Coherent
