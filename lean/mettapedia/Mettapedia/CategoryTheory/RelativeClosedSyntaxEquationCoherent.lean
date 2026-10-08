import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorExtension

/-!
# Coherent classification of the actual equation extension

An independently supplied closed finite-limit functor provides only
primitive base and object isomorphisms and complete primitive arrow images.
Those local images force satisfaction of every authored equation. They earn
the comparison on the entire equation-extended category and its uniqueness
among cells with the supplied primitive components.

The complete original diagram is recovered by restriction. No arbitrary
natural transformation is declared to preserve function structure, and no
model-category equivalence is inferred from object recovery.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.EquationExtension.Coherent

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {Index : Type k} (declarations : Index → Declaration signature)
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : Assignment C symbols D) (realized : Realization signature meanings)
variable (headers : HeaderFormation signature)
variable (candidate : Object (extend signature declarations) ⥤ D)
variable [PreservesFiniteLimits candidate] [MonoidalClosedFunctor candidate]
variable (images : AtomicPresentation.PrimitiveImages candidate (extendAssignment meanings))
variable (readings : CoherentExtension.ArrowImages candidate (extendAssignment meanings) images
  (EquationExtension.headers signature declarations headers))

include readings in
theorem locally_realized :
    Realization (extend signature declarations) (extendAssignment meanings) := by
  have recovered := FunctorNormalization.reconstruction_realization
    (CoherentExtension.presented candidate (extendAssignment meanings) images)
    (EquationExtension.headers signature declarations headers)
  exact (CoherentExtension.assignment_equal candidate (extendAssignment meanings) images
    (EquationExtension.headers signature declarations headers) readings) ▸ recovered

include readings in
theorem satisfies : Satisfies signature declarations meanings realized :=
  necessary_satisfaction signature declarations meanings realized
    (locally_realized declarations meanings headers candidate images readings)

def comparison : candidate ≅
    Interpretation.functor (extendAssignment meanings)
      (extended_realization signature declarations meanings realized
        (satisfies declarations meanings realized headers candidate images readings)) :=
  CoherentExtension.comparison candidate (extendAssignment meanings) images
    (EquationExtension.headers signature declarations headers) readings
    (extended_realization signature declarations meanings realized
      (satisfies declarations meanings realized headers candidate images readings))

abbrev CellAdmission
    (cell : candidate ⟶ Interpretation.functor (extendAssignment meanings)
      (extended_realization signature declarations meanings realized
        (satisfies declarations meanings realized headers candidate images readings))) : Prop :=
  CoherentExtension.CellAdmission candidate (extendAssignment meanings) images
    (extended_realization signature declarations meanings realized
      (satisfies declarations meanings realized headers candidate images readings)) cell

theorem comparison_admitted : CellAdmission declarations meanings realized headers candidate images readings
    (comparison declarations meanings realized headers candidate images readings).hom :=
  CoherentExtension.comparison_admitted candidate (extendAssignment meanings) images
    (EquationExtension.headers signature declarations headers) readings
    (extended_realization signature declarations meanings realized
      (satisfies declarations meanings realized headers candidate images readings))

theorem admitted_cell_unique
    (cell : candidate ⟶ Interpretation.functor (extendAssignment meanings)
      (extended_realization signature declarations meanings realized
        (satisfies declarations meanings realized headers candidate images readings)))
    (localComponents : CellAdmission declarations meanings realized headers candidate images readings cell) :
    cell = (comparison declarations meanings realized headers candidate images readings).hom :=
  CoherentExtension.admitted_cell_unique candidate (extendAssignment meanings) images
    (EquationExtension.headers signature declarations headers) readings
    (extended_realization signature declarations meanings realized
      (satisfies declarations meanings realized headers candidate images readings)) cell localComponents

@[instance_reducible] def admittedIsoUnique :
    Unique {iso : candidate ≅ Interpretation.functor (extendAssignment meanings)
      (extended_realization signature declarations meanings realized
        (satisfies declarations meanings realized headers candidate images readings)) //
      CellAdmission declarations meanings realized headers candidate images readings iso.hom} :=
  CoherentExtension.admittedIsoUnique candidate (extendAssignment meanings) images
    (extended_realization signature declarations meanings realized
      (satisfies declarations meanings realized headers candidate images readings))
    (EquationExtension.headers signature declarations headers) readings

def originalComparison : (inclusion signature declarations).functor ⋙ candidate ≅
    Interpretation.functor meanings realized :=
  Functor.isoWhiskerLeft (inclusion signature declarations).functor
    (comparison declarations meanings realized headers candidate images readings) ≪≫
      eqToIso (complete_restriction signature declarations meanings realized
        (satisfies declarations meanings realized headers candidate images readings))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.EquationExtension.Coherent
