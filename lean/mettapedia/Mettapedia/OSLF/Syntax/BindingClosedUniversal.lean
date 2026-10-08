import Mettapedia.OSLF.Syntax.BindingClosedInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorExtension

/-!
# Coherent classification of arbitrary binding constructor presentations

Only primitive sort isomorphisms and complete primitive operator readings
are supplied for a candidate closed finite-limit interpretation. The local
data earns a natural isomorphism on the whole generated category. Every
admitted comparison is uniquely determined by its primitive components.

The theorem concerns the independently generated constructor presentation.
Authored equations and operational edge objects require their own generators
and realization proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.Universal

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory.RelativeClosedSyntax

universe u v

variable {binding : Mettapedia.OSLF.Binding.Signature}
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable (operations : Operations binding C)
variable (candidate : GeneratedCategory.Object (signature.{v} binding) ⥤ C)
variable [PreservesFiniteLimits candidate] [MonoidalClosedFunctor candidate]

structure ObjectImages where
  sort (origin : binding.Srt) : candidate.obj (sortObject binding origin) ≅ operations.sort origin

private def emptyBaseComparison : GeneratedCategory.baseFunctor (signature.{v} binding) ⋙ candidate ≅
    operations.assignment.base :=
  NatIso.ofComponents (fun object => isEmptyElim object) (by
    intro source target arrow
    exact False.elim (isEmptyElim source : False))

def primitiveImages (images : ObjectImages operations candidate) :
    AtomicPresentation.PrimitiveImages candidate operations.assignment where
  base := emptyBaseComparison operations candidate
  object origin := images.sort origin.down

def normalizedOperator (images : ObjectImages operations candidate) (origin : Sigma binding.Op) :
    Interpretation.ArrowValue C :=
  (FunctorNormalization.assignment
    (AtomicPresentation.functor candidate operations.assignment (primitiveImages operations candidate images))
      (headers binding)).arrow ⟨origin⟩

structure OperatorImages (images : ObjectImages operations candidate) : Prop where
  operator (origin : Sigma binding.Op) :
    normalizedOperator operations candidate images origin = operations.primitiveValue origin

theorem arrowImages (images : ObjectImages operations candidate)
    (readings : OperatorImages operations candidate images) :
    CoherentExtension.ArrowImages candidate operations.assignment
      (primitiveImages operations candidate images) (headers binding) where
  arrow origin := readings.operator origin.down

def comparison (images : ObjectImages operations candidate)
    (readings : OperatorImages operations candidate images) : candidate ≅ operations.interpretation.functor :=
  CoherentExtension.comparison candidate operations.assignment
    (primitiveImages operations candidate images) (headers binding)
    (arrowImages operations candidate images readings) operations.realization

abbrev CellAdmission (images : ObjectImages operations candidate)
    (cell : candidate ⟶ operations.interpretation.functor) : Prop :=
  CoherentExtension.CellAdmission candidate operations.assignment
    (primitiveImages operations candidate images) operations.realization cell

theorem comparison_admitted (images : ObjectImages operations candidate)
    (readings : OperatorImages operations candidate images) :
    CellAdmission operations candidate images (comparison operations candidate images readings).hom :=
  CoherentExtension.comparison_admitted candidate operations.assignment
    (primitiveImages operations candidate images) (headers binding)
    (arrowImages operations candidate images readings) operations.realization

theorem admitted_cell_unique (images : ObjectImages operations candidate)
    (readings : OperatorImages operations candidate images)
    (cell : candidate ⟶ operations.interpretation.functor)
    (localComponents : CellAdmission operations candidate images cell) :
    cell = (comparison operations candidate images readings).hom :=
  CoherentExtension.admitted_cell_unique candidate operations.assignment
    (primitiveImages operations candidate images) (headers binding)
    (arrowImages operations candidate images readings) operations.realization cell localComponents

@[instance_reducible] def admittedIsoUnique (images : ObjectImages operations candidate)
    (readings : OperatorImages operations candidate images) :
    Unique {iso : candidate ≅ operations.interpretation.functor //
      CellAdmission operations candidate images iso.hom} :=
  CoherentExtension.admittedIsoUnique candidate operations.assignment
    (primitiveImages operations candidate images) operations.realization (headers binding)
    (arrowImages operations candidate images readings)

end Mettapedia.OSLF.Binding.ClosedPresentation.Universal
