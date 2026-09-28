import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelModal
import Mettapedia.OSLF.Syntax.VaryingEventObservations

/-!
# Chosen reduction observations over substitution-operational models

At a selected substitution context, model events and their endpoint pairs
form a diagram varying with the lawful model. The existing image doctrine
then constructs the least justified reduction mono and its universal map.
This uses images in the selected target category; it does not claim that
finite limits alone produce them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelObservation

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf
open Mettapedia.OSLF.Binding.VaryingEventObservations

universe u
variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))

/-- The actual individual-evidence object and endpoint-pair object vary
functorially with an operational interpretation at each context. -/
noncomputable def modelEventDiagramAt
    (A : BindingCloneAlgebra.Algebra.{u} S) (X : Base A) :
    EventDiagram (SubstitutionModel R A) (Type u) where
  events := {
    obj := fun Y => (modelEvents R Y).obj X
    map := fun h => (mapModelEvents R h).app X
    map_id := by
      intro Y
      apply ConcreteCategory.hom_ext
      intro event
      rfl
    map_comp := by
      intro Y Z W f g
      apply ConcreteCategory.hom_ext
      intro event
      rfl
  }
  pairs := {
    obj := fun _ => (states A).obj X × (states A).obj X
    map := fun _ => 𝟙 _
    map_id := by intro Y; rfl
    map_comp := by intro Y Z W f g; rfl
  }
  endpoints := {
    app := fun Y => TypeCat.ofHom (fun event =>
      ((modelSource R Y).app X event, (modelTarget R Y).app X event))
    naturality := by
      intro Y Z h
      apply ConcreteCategory.hom_ext
      intro event
      rfl
  }

/-- In the selected Set-valued target, taking the endpoint image is left
adjoint to forgetting the chosen predicate. The adjunction retains the
event object and has ordinary model maps as its underlying morphisms. -/
noncomputable def modelImageAdjunctionAt
    (A : BindingCloneAlgebra.Algebra.{u} S) (X : Base A) :
    imageFunctor (modelEventDiagramAt R A X) ⊣
      forget (modelEventDiagramAt R A X) :=
  VaryingEventObservations.imageAdjunction (modelEventDiagramAt R A X)

#print axioms modelEventDiagramAt
#print axioms modelImageAdjunctionAt

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelObservation
