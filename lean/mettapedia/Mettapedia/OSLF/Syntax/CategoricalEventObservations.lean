import Mettapedia.OSLF.Syntax.EventGraphSlice
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Event evidence and its least reduction observation

For a fixed program object, an event graph is an object of the slice over
paired endpoints. An observation additionally chooses a reduction subobject
containing every event endpoint. This retains individual firings even when
several have the same endpoints.

When images exist, the image of the event arrow is the least such reduction
predicate. The construction is left adjoint to forgetting the predicate.
Only image existence is assumed here; preservation under substitution or
base change requires further hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalEventObservations

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.EventGraphSlice.Categorical

universe u v

noncomputable section

variable {D : Type u} [Category.{v} D]
variable (programs : D) [HasBinaryProduct programs programs]

private abbrev Pairs := programs ⨯ programs

/-- A reduction predicate justified by a retained graph of firing events. -/
structure Observation where
  graph : EventGraph programs
  reduction : Subobject (Pairs programs)
  contains : reduction.Factors graph.hom

/-- Maps preserve firing evidence and may enlarge the observed reduction
predicate. They need not cover every target firing or reflect target steps. -/
structure Hom (X Y : Observation programs) where
  event : X.graph ⟶ Y.graph
  reduction_le : X.reduction ≤ Y.reduction

namespace Hom

@[ext] theorem ext {X Y : Observation programs} {f g : Hom programs X Y}
    (h : f.event = g.event) : f = g := by
  cases f
  cases g
  cases h
  rfl

end Hom

instance : Category (Observation programs) where
  Hom := Hom programs
  id X := ⟨𝟙 X.graph, le_refl X.reduction⟩
  comp f g := ⟨f.event ≫ g.event, le_trans f.reduction_le g.reduction_le⟩
  id_comp := by intro X Y f; apply Hom.ext; simp
  comp_id := by intro X Y f; apply Hom.ext; simp
  assoc := by intro W X Y Z f g h; apply Hom.ext; simp [Category.assoc]

/-- Forget a chosen endpoint predicate, keeping every firing event. -/
def forget : Observation programs ⥤ EventGraph programs where
  obj X := X.graph
  map f := f.event
  map_id _ := rfl
  map_comp _ _ := rfl

variable [HasImages D]

/-- The image predicate is the least observation justified by a graph. -/
noncomputable def imageObservation (G : EventGraph programs) :
    Observation programs where
  graph := G
  reduction := reductionImage programs G
  contains := firingFactorsReduction programs G

/-- Every event map preserves the least endpoint observation. -/
theorem image_mono (G H : EventGraph programs) (f : G ⟶ H) :
    (imageObservation programs G).reduction ≤
      (imageObservation programs H).reduction := by
  change imageSubobject G.hom ≤ imageSubobject H.hom
  rw [← Over.w f]
  exact imageSubobject_comp_le f.left H.hom

/-- Freely observe a graph by its endpoint image. -/
noncomputable def imageFunctor :
    EventGraph programs ⥤ Observation programs where
  obj := imageObservation programs
  map f := ⟨f, image_mono programs _ _ f⟩
  map_id := by intro G; apply Hom.ext; rfl
  map_comp := by intro G H K f g; apply Hom.ext; rfl

/-- Any event map into an observed graph carries the source image into the
target reduction predicate. This is the universal property of the image,
without a coverage or state-injectivity condition on the map. -/
theorem image_le_of_event_map (G : EventGraph programs)
    (Y : Observation programs) (f : G ⟶ Y.graph) :
    (imageObservation programs G).reduction ≤ Y.reduction := by
  change imageSubobject G.hom ≤ Y.reduction
  have factors : Y.reduction.Factors G.hom := by
    rw [← Over.w f]
    exact Subobject.factors_of_factors_right f.left Y.contains
  exact imageSubobject_le G.hom
    (Y.reduction.factorThru G.hom factors)
    (Y.reduction.factorThru_arrow G.hom factors)

/-- A map from the image observation is uniquely determined by its map of
individual firing events. -/
noncomputable def imageHomEquiv (G : EventGraph programs)
    (Y : Observation programs) :
    ((imageFunctor programs).obj G ⟶ Y) ≃ (G ⟶ Y.graph) where
  toFun f := f.event
  invFun f := ⟨f, image_le_of_event_map programs G Y f⟩
  left_inv := by intro f; apply Hom.ext; rfl
  right_inv := by intro f; rfl

/-- Taking the least reduction observation is left adjoint to forgetting
it, with the actual event map as the hom-set comparison. -/
noncomputable def imageAdjunction :
    imageFunctor programs ⊣ forget programs :=
  Adjunction.mkOfHomEquiv
    { homEquiv := imageHomEquiv programs
      homEquiv_naturality_left_symm := by
        intro G' G Y first second
        apply Hom.ext
        rfl
      homEquiv_naturality_right := by
        intro G X Y first second
        rfl }

end

end Mettapedia.OSLF.Binding.CategoricalEventObservations
