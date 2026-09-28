import Mettapedia.OSLF.Syntax.FreePresheafEventExtension
import Mettapedia.OSLF.Syntax.RhoFreePresheafEvents
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# Endpoint images of freely adjoined event graphs

A graph of operational events carries more information than its reduction
predicate. In a presheaf target, the predicate is the image of the paired
endpoint map. Taking the free disjoint union of event graphs takes the join
of their endpoint images, without identifying the events themselves.

This is the image comparison needed by the Chapter 7 graph layer. It does
not assert that finite limits alone provide images, or that the resulting
presheaf model is the free cartesian-closed classifying theory.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FreePresheafEventImage

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.FreePresheafEventExtension

universe u v w

variable {C : Type u} [Category.{v} C]
variable {vertex : C ⥤ Type w}

/-- The source and target maps of a graph, paired into one natural map. -/
def endpointMap (G : Graph vertex) :
    G.edge ⟶ FunctorToTypes.prod vertex vertex :=
  FunctorToTypes.prod.lift G.source G.target

/-- The proposition-valued reduction predicate represented by the image of
the paired endpoint map. This keeps the image assumption visible: it uses
the pointwise image structure of the presheaf target. -/
def endpointImage (G : Graph vertex) :
    Subfunctor (FunctorToTypes.prod vertex vertex) :=
  Subfunctor.range (endpointMap G)

/-- A pair belongs to the endpoint image precisely when an event has that
source and target at the given stage. -/
theorem mem_endpointImage_iff (G : Graph vertex) (X : C)
    (pair : vertex.obj X × vertex.obj X) :
    pair ∈ (endpointImage G).obj X ↔
      ∃ event : G.edge.obj X,
        G.source.app X event = pair.1 ∧
        G.target.app X event = pair.2 := by
  change (∃ event : G.edge.obj X,
    (G.source.app X event, G.target.app X event) = pair) ↔ _
  constructor
  · rintro ⟨event, equal⟩
    exact ⟨event, congrArg Prod.fst equal, congrArg Prod.snd equal⟩
  · rintro ⟨event, sourceEq, targetEq⟩
    exact ⟨event, Prod.ext sourceEq targetEq⟩

/-- The paired endpoint map of a free disjoint union is the copair of the
original endpoint maps. -/
  theorem endpointMap_graphSum (G H : Graph vertex) :
    endpointMap (graphSum G H) =
      copair (endpointMap G) (endpointMap H) := by
  ext X event <;> cases event <;> rfl

/-- The image of a map out of a pointwise disjoint sum is the join of the
images of its two restrictions. -/
theorem range_copair {A B Z : C ⥤ Type w}
    (f : A ⟶ Z) (g : B ⟶ Z) :
    Subfunctor.range (copair f g) =
      Subfunctor.range f ⊔ Subfunctor.range g := by
  ext X point
  constructor
  · rintro ⟨event, rfl⟩
    cases event with
    | inl left => exact Or.inl ⟨left, rfl⟩
    | inr right => exact Or.inr ⟨right, rfl⟩
  · rintro (⟨left, rfl⟩ | ⟨right, rfl⟩)
    · exact ⟨Sum.inl left, rfl⟩
    · exact ⟨Sum.inr right, rfl⟩

/-- Free adjoining is a join at the level of endpoint predicates, while
the graph itself remains the disjoint sum of firing events. -/
theorem endpointImage_graphSum (G H : Graph vertex) :
    endpointImage (graphSum G H) =
      endpointImage G ⊔ endpointImage H := by
  rw [endpointImage, endpointMap_graphSum]
  exact range_copair (endpointMap G) (endpointMap H)

end Mettapedia.OSLF.Binding.FreePresheafEventImage

namespace Mettapedia.OSLF.Binding.FreePresheafEventImage.RhoExample

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.RhoFreePresheafEvents
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents
open Mettapedia.OSLF.Binding.ContextualReductionSubobject

/-- For the actual authored rho COMM/Drop presentation, the image of the
freely adjoined event graph is exactly the previously constructed
contextual reduction subobject, at every substitution context. -/
theorem free_source_image_eq_reduction :
    endpointImage
      (freeObject sourceEvents (emptyGraph states)).graph =
        sourceReduction := by
  ext X pair
  exact (mem_endpointImage_iff _ X pair).trans
    (free_endpoint_image_iff_reduction X pair)

/-- The authored generator graph itself already has the complete source
one-step predicate as its endpoint image. -/
theorem source_image_eq_reduction :
    endpointImage sourceEvents = sourceReduction := by
  ext X pair
  exact mem_endpointImage_iff sourceEvents X pair

/-- A second authored COMM occurrence gives a second event in the same
operational graph, even though its pair of endpoints is unchanged. -/
def duplicatedGraph : Graph (termQPresheaf duplicatedCommunication.eqs Srt.pr) where
  edge := presentationEventPresheaf duplicatedCommunication Srt.pr
  source := presentationSourceNatural duplicatedCommunication Srt.pr
  target := presentationTargetNatural duplicatedCommunication Srt.pr

/-- The endpoint-image operation loses rule-occurrence identity in the
actual rho presentation. It therefore cannot replace the event graph for
history or cost consumers. -/
theorem duplicated_endpoint_map_not_injective :
    ¬ Function.Injective
      ((endpointMap duplicatedGraph).app closedContext) := by
  intro endpointInjective
  apply ContextualReductionSubobject.RhoExample.duplicated_communication_incidence_not_injective
  intro first second sameIncidence
  apply endpointInjective
  exact congrArg Subtype.val sameIncidence

end Mettapedia.OSLF.Binding.FreePresheafEventImage.RhoExample
