import Mettapedia.GSLT.Topos.ConstructivePresheafOperations

/-!
# Internal modalities of a presheaf event graph

Existential quantification along the source after reindexing along the target
gives the may-step modality on subfunctors. Its right adjoint quantifies along
the target and observes the source. This is the step-past box. The universal
forward-step modality is stated separately to make the orientation explicit.

Universal quantification includes every further restriction of a section.
Pointwise quantification over the events currently present is insufficient
when a substitution creates a new redex.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PresheafEventModalities

open CategoryTheory
open ConstructivePresheaf
open scoped ConstructivePresheaf

universe u v w
variable {C : Type u} [Category.{v} C] (G : EventGraph.{u, v, w} C)

/-- The source states of events whose targets satisfy the predicate. -/
def diamond (P : Subfunctor G.vertex) : Subfunctor G.vertex :=
  image G.source (preimage G.target P)

/-- The internal right adjoint observes all incoming events after every
restriction. It is the step-past box, not the universal forward-step modality. -/
def box (P : Subfunctor G.vertex) : Subfunctor G.vertex :=
  ConstructivePresheaf.forallAlong G.target (preimage G.source P)

def forwardBox (P : Subfunctor G.vertex) : Subfunctor G.vertex :=
  ConstructivePresheaf.forallAlong G.source (preimage G.target P)

theorem diamond_le_iff (P Q : Subfunctor G.vertex) :
    diamond G P ≤ Q ↔ P ≤ box G Q := by
  exact (image_le_iff G.source (preimage G.target P) Q).trans
    (preimage_le_iff G.target P (preimage G.source Q))

theorem galois : GaloisConnection (diamond G) (box G) := diamond_le_iff G

theorem diamond_spec (P : Subfunctor G.vertex) (X : C) (x : G.vertex.obj X) :
    x ∈ (diamond G P).obj X ↔
      ∃ event : G.edge.obj X, G.target.app X event ∈ P.obj X ∧
        G.source.app X event = x := Iff.rfl

theorem box_spec (P : Subfunctor G.vertex) (X : C) (x : G.vertex.obj X) :
    x ∈ (box G P).obj X ↔
      ∀ (Y : C) (restriction : X ⟶ Y) (event : G.edge.obj Y),
        G.target.app Y event = G.vertex.map restriction x →
          G.source.app Y event ∈ P.obj Y := Iff.rfl

theorem forwardBox_spec (P : Subfunctor G.vertex) (X : C) (x : G.vertex.obj X) :
    x ∈ (forwardBox G P).obj X ↔
      ∀ (Y : C) (restriction : X ⟶ Y) (event : G.edge.obj Y),
        G.source.app Y event = G.vertex.map restriction x →
          G.target.app Y event ∈ P.obj Y := Iff.rfl

theorem diamond_restrict (P : Subfunctor G.vertex) {X Y : C}
    (restriction : X ⟶ Y) {x : G.vertex.obj X}
    (holds : x ∈ (diamond G P).obj X) :
    G.vertex.map restriction x ∈ (diamond G P).obj Y :=
  (diamond G P).map restriction holds

theorem box_restrict (P : Subfunctor G.vertex) {X Y : C}
    (restriction : X ⟶ Y) {x : G.vertex.obj X}
    (holds : x ∈ (box G P).obj X) :
    G.vertex.map restriction x ∈ (box G P).obj Y :=
  (box G P).map restriction holds

end Mettapedia.GSLT.Topos.PresheafEventModalities
