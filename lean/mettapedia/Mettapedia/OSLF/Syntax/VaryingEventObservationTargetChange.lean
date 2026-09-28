import Mettapedia.OSLF.Syntax.VaryingEventObservations
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Change of semantic target for event observations

A finite-limit-preserving target functor preserves monomorphisms. This
module first uses the weaker monomorphism-preservation contract to map a
varying event diagram and its chosen reduction predicates to a new target.
Preservation of *image* observations is a further condition; mapping a
chosen mono does not by itself identify it with the image of mapped events.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.VaryingEventObservations

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

universe uB vB uD vD uE vE

variable {B : Type uB} [Category.{vB} B]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]
variable (G : EventDiagram B D) (H : D ⥤ E)

/-- Apply a semantic target functor to event objects, paired program
objects, and their natural endpoint map. -/
def EventDiagram.mapTarget : EventDiagram B E where
  events := G.events ⋙ H
  pairs := G.pairs ⋙ H
  endpoints := Functor.whiskerRight G.endpoints H

variable [H.PreservesMonomorphisms]

private noncomputable def mappedReduction (X : Observation G) :
    Subobject (H.obj (G.pairs.obj X.base)) := by
  letI : Mono (H.map X.reduction.arrow) :=
    Functor.PreservesMonomorphisms.preserves X.reduction.arrow
  exact Subobject.mk (H.map X.reduction.arrow)

/-- Map an observed interpretation to a new semantic target, retaining
the event object and mapping its chosen reduction mono. -/
noncomputable def Observation.mapTarget (X : Observation G) :
    Observation (G.mapTarget H) where
  base := X.base
  reduction := mappedReduction G H X
  contains := by
    have monoMap : Mono (H.map X.reduction.arrow) :=
      Functor.PreservesMonomorphisms.preserves X.reduction.arrow
    change (Subobject.mk (H.map X.reduction.arrow)).Factors
      (H.map (G.endpoints.app X.base))
    apply (Subobject.mk_factors_iff _ _).2
    refine ⟨H.map (X.reduction.factorThru
      (G.endpoints.app X.base) X.contains), ?_⟩
    simp [← H.map_comp,
      X.reduction.factorThru_arrow]

/-- A map of interpreted models transports its reduction-factorization
through a target functor that preserves monomorphisms. -/
theorem Observation.mapTarget_preserves {X Y : Observation G}
    (f : X ⟶ Y) :
    ((Y.mapTarget G H).reduction).Factors
      ((X.mapTarget G H).reduction.arrow ≫
        (G.mapTarget H).pairs.map f.base) := by
  have monoX : Mono (H.map X.reduction.arrow) :=
    Functor.PreservesMonomorphisms.preserves X.reduction.arrow
  have monoY : Mono (H.map Y.reduction.arrow) :=
    Functor.PreservesMonomorphisms.preserves Y.reduction.arrow
  change (Subobject.mk (H.map Y.reduction.arrow)).Factors
    ((Subobject.mk (H.map X.reduction.arrow)).arrow ≫
      H.map (G.pairs.map f.base))
  apply (Subobject.mk_factors_iff _ _).2
  change ∃ g : (Subobject.mk (H.map X.reduction.arrow) : E) ⟶
      H.obj (Y.reduction : D),
    g ≫ H.map Y.reduction.arrow =
      (Subobject.mk (H.map X.reduction.arrow)).arrow ≫
        H.map (G.pairs.map f.base)
  refine ⟨(Subobject.underlyingIso (H.map X.reduction.arrow)).hom ≫
    H.map (Y.reduction.factorThru
      (X.reduction.arrow ≫ G.pairs.map f.base) f.preserves), ?_⟩
  rw [Category.assoc, ← H.map_comp,
    Y.reduction.factorThru_arrow, H.map_comp]
  rw [← Category.assoc,
    Subobject.underlyingIso_hom_comp_eq_mk]

/-- Change the semantic target without forgetting firing objects or
the chosen reduction predicate. -/
noncomputable def mapTargetFunctor :
    Observation G ⥤ Observation (G.mapTarget H) where
  obj X := X.mapTarget G H
  map f := { base := f.base
             preserves := Observation.mapTarget_preserves G H f }
  map_id := by
    intro X
    apply Hom.ext
    rfl
  map_comp := by
    intro X Y Z f g
    apply Hom.ext
    rfl

/-- Changing the semantic target leaves the independently defined base
interpretation and its maps unchanged. -/
theorem mapTargetFunctor_forget :
    mapTargetFunctor G H ⋙ forget (G.mapTarget H) = forget G := by
  rfl

/-- In the new target, the endpoint image is contained in every mapped
chosen observation. Equality requires an image-preservation hypothesis. -/
theorem mapped_image_le (X : Observation G)
    [HasImage ((G.mapTarget H).endpoints.app X.base)] :
    (imageObservation (G.mapTarget H) X.base).reduction ≤
      (X.mapTarget G H).reduction := by
  have imageAtMapped : HasImage
      ((G.mapTarget H).endpoints.app (X.mapTarget G H).base) := by
    change HasImage ((G.mapTarget H).endpoints.app X.base)
    infer_instance
  exact image_le (G.mapTarget H) (X.mapTarget G H)

end Mettapedia.OSLF.Binding.VaryingEventObservations
