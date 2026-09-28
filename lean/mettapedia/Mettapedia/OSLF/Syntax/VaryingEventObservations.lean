import Mettapedia.OSLF.Syntax.CategoricalEventObservations

/-!
# Chosen reduction observations over varying event interpretations

An interpreted program object and its firing events both vary with the
underlying language interpretation. The diagram below records their endpoint
map as a natural transformation. An observation chooses a reduction mono
containing every event endpoint; maps preserve events through the base model
map and preserve the chosen reduction predicate by factorization.

This is the target-side interface available even without images. Requiring
the reduction mono to be the image is a separate extension of this doctrine.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.VaryingEventObservations

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

universe uB vB uD vD

variable {B : Type uB} [Category.{vB} B]
variable {D : Type uD} [Category.{vD} D]

/-- A functorial family of retained event objects and endpoint-pair objects
over independently defined semantic base interpretations. -/
structure EventDiagram (B : Type uB) [Category.{vB} B]
    (D : Type uD) [Category.{vD} D] where
  events : B ⥤ D
  pairs : B ⥤ D
  endpoints : events ⟶ pairs

namespace EventDiagram

@[ext] theorem ext {G H : EventDiagram B D}
    (events : G.events = H.events) (pairs : G.pairs = H.pairs)
    (endpoints : HEq G.endpoints H.endpoints) : G = H := by
  cases G
  cases H
  cases events
  cases pairs
  cases endpoints
  rfl

end EventDiagram

variable (G : EventDiagram B D)

/-- A chosen reduction subobject for one interpretation. The event object
and its endpoint map remain part of the independent base interpretation. -/
structure Observation where
  base : B
  reduction : Subobject (G.pairs.obj base)
  contains : reduction.Factors (G.endpoints.app base)

/-- Where the endpoint image exists, it gives the least reduction predicate
justified by the events of a model. No stable-image assumption is needed to
construct the observation at this one model. -/
noncomputable def imageObservation (b : B)
    [HasImage (G.endpoints.app b)] : Observation G where
  base := b
  reduction := imageSubobject (G.endpoints.app b)
  contains := by
    simpa using imageSubobject_factors_comp_self
      (G.endpoints.app b) (𝟙 (G.events.obj b))

/-- An interpretation map preserves the chosen predicate in the direction
of its program-pair map. It need not cover target events or reflect steps. -/
structure Hom (X Y : Observation G) where
  base : X.base ⟶ Y.base
  preserves : Y.reduction.Factors
    (X.reduction.arrow ≫ G.pairs.map base)

namespace Hom

@[ext] theorem ext {X Y : Observation G} {f g : Hom G X Y}
    (h : f.base = g.base) : f = g := by
  cases f
  cases g
  cases h
  rfl

end Hom

instance : Category (Observation G) where
  Hom := Hom G
  id X := ⟨𝟙 X.base, by
    simpa using Subobject.factors_self X.reduction⟩
  comp := by
    intro X Y Z f g
    refine ⟨f.base ≫ g.base, ?_⟩
    have factors := Subobject.factors_of_factors_right
      (Y.reduction.factorThru _ f.preserves) g.preserves
    have composed : Z.reduction.Factors
        ((X.reduction.arrow ≫ G.pairs.map f.base) ≫
          G.pairs.map g.base) := by
      convert factors using 1
      exact (congrArg
        (fun arrow : (X.reduction : D) ⟶ G.pairs.obj Y.base =>
          arrow ≫ G.pairs.map g.base)
        (Y.reduction.factorThru_arrow _ f.preserves).symm).trans
          (Category.assoc _ _ _)
    simpa only [Functor.map_comp, Category.assoc] using composed
  id_comp := by intro X Y f; apply Hom.ext; simp
  comp_id := by intro X Y f; apply Hom.ext; simp
  assoc := by intro W X Y Z f g h; apply Hom.ext; simp [Category.assoc]

/-- Retain the underlying model with all of its firing events. -/
def forget : Observation G ⥤ B where
  obj X := X.base
  map f := f.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- In a target with images, taking the endpoint image is functorial in
the entire base interpretation. The event diagram's naturality supplies
the commuting square; no reflection or event coverage is imposed on maps. -/
noncomputable def imageFunctor [HasImages D] [HasImageMaps D] :
    B ⥤ Observation G where
  obj b := imageObservation G b
  map {a b} f :=
    { base := f
      preserves := by
        let sq : Arrow.mk (G.endpoints.app a) ⟶
            Arrow.mk (G.endpoints.app b) :=
          Arrow.homMk (G.events.map f) (G.pairs.map f)
            (G.endpoints.naturality f)
        apply (Subobject.factors_iff _ _).2
        refine ⟨imageSubobjectMap (f := G.endpoints.app a)
          (g := G.endpoints.app b) sq, ?_⟩
        exact imageSubobjectMap_arrow sq }
  map_id := by
    intro X
    apply Hom.ext
    rfl
  map_comp := by
    intro X Y Z f g
    apply Hom.ext
    rfl

/-- The image of an event graph is the least reduction predicate justified
by its actual firing evidence. -/
theorem image_le (X : Observation G) [HasImage (G.endpoints.app X.base)] :
    (imageObservation G X.base).reduction ≤ X.reduction := by
  exact imageSubobject_le (G.endpoints.app X.base)
    (X.reduction.factorThru (G.endpoints.app X.base) X.contains)
    (X.reduction.factorThru_arrow (G.endpoints.app X.base) X.contains)

/-- The image observation is free over a base interpretation: an observed
map out of it is exactly a map of the underlying interpretations. -/
noncomputable def imageHomEquiv [HasImages D] [HasImageMaps D]
    (b : B) (X : Observation G) :
    ((imageFunctor G).obj b ⟶ X) ≃ (b ⟶ X.base) where
  toFun f := f.base
  invFun f :=
    { base := f
      preserves :=
        Subobject.factors_of_le _ (image_le G X)
          ((imageFunctor G).map f).preserves }
  left_inv := by intro f; apply Hom.ext; rfl
  right_inv := by intro f; rfl

/-- Endpoint-image observation is left adjoint to forgetting the chosen
predicate, now for models whose program and event objects vary. -/
noncomputable def imageAdjunction [HasImages D] [HasImageMaps D] :
    imageFunctor G ⊣ forget G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := imageHomEquiv G
      homEquiv_naturality_left_symm := by
        intro b' b X first second
        apply Hom.ext
        rfl
      homEquiv_naturality_right := by
        intro b X Y first second
        rfl }
/-- Event endpoints of a source model remain in the target reduction
predicate after an observation map. This follows from naturality of the
event diagram and the chosen predicate-preservation factorization. -/
theorem mapped_event_factors {X Y : Observation G} (f : X ⟶ Y) :
    Y.reduction.Factors
      (G.events.map f.base ≫ G.endpoints.app Y.base) := by
  have sourceFactors : X.reduction.Factors (G.endpoints.app X.base) := X.contains
  have targetFactors : Y.reduction.Factors
      (G.endpoints.app X.base ≫ G.pairs.map f.base) := by
    rw [← X.reduction.factorThru_arrow _ sourceFactors]
    simpa only [Category.assoc] using
      (Subobject.factors_of_factors_right
        (X.reduction.factorThru _ sourceFactors) f.preserves)
  simpa only [G.endpoints.naturality] using targetFactors

/-! ## Change of the base interpretation category -/

variable {A : Type*} [Category A]

/-- Pull an event-and-endpoint diagram back along a functor on underlying
semantic interpretations. No event or predicate quotient is introduced. -/
def EventDiagram.reindex (F : A ⥤ B) : EventDiagram A D where
  events := F ⋙ G.events
  pairs := F ⋙ G.pairs
  endpoints :=
    { app := fun a => G.endpoints.app (F.obj a)
      naturality := by
        intro a b f
        simpa only [Functor.comp_map] using
          G.endpoints.naturality (F.map f) }

/-- Change the base interpretation while retaining exactly the same
reduction subobject and individual event object in the semantic target. -/
def reindexFunctor (F : A ⥤ B) :
    Observation (G.reindex F) ⥤ Observation G where
  obj X :=
    { base := F.obj X.base
      reduction := X.reduction
      contains := X.contains }
  map f :=
    { base := F.map f.base
      preserves := f.preserves }
  map_id := by
    intro X
    apply Hom.ext
    change F.map (𝟙 X.base) = 𝟙 (F.obj X.base)
    simp
  map_comp := by
    intro X Y Z f g
    apply Hom.ext
    change F.map (f.base ≫ g.base) = F.map f.base ≫ F.map g.base
    simp

/-- Faithfulness of the base comparison lifts to interpretations with chosen
reduction predicates and retained firing events. -/
instance reindexFunctor_faithful (F : A ⥤ B) [F.Faithful] :
    (reindexFunctor G F).Faithful where
  map_injective := by
    intro X Y f g h
    apply Hom.ext
    apply F.map_injective
    exact congrArg (fun k :
      (reindexFunctor G F).obj X ⟶ (reindexFunctor G F).obj Y =>
        k.base) h

/-- Fullness also lifts: every target observation map between interpreted
source models comes from a unique source base map, because the predicate
factorization is unchanged. This does not assert essential surjectivity. -/
noncomputable instance reindexFunctor_full (F : A ⥤ B)
    [F.Full] [F.Faithful] : (reindexFunctor G F).Full where
  map_surjective := by
    intro X Y h
    obtain ⟨f, mapped⟩ := F.map_surjective h.base
    have preserves : Y.reduction.Factors
        (X.reduction.arrow ≫ (G.reindex F).pairs.map f) := by
      change Y.reduction.Factors
        (X.reduction.arrow ≫ G.pairs.map (F.map f))
      rw [mapped]
      exact h.preserves
    refine ⟨⟨f, preserves⟩, ?_⟩
    apply Hom.ext
    exact mapped

/-! ## Transport of observations along an isomorphism of base models -/

/-- Transport a chosen reduction predicate back along an isomorphism of
base interpretations. Event evidence is not quotiented: its endpoint map
factors through the transported predicate by naturality. -/
noncomputable def Observation.transportAlongIso
    (Y : Observation G) {a : B} (e : a ≅ Y.base) : Observation G := by
  let p : G.pairs.obj a ≅ G.pairs.obj Y.base := G.pairs.mapIso e
  let r : Subobject (G.pairs.obj a) :=
    Subobject.mk (Y.reduction.arrow ≫ p.inv)
  have contains : r.Factors (G.endpoints.app a) := by
    change (Subobject.mk (Y.reduction.arrow ≫ p.inv)).Factors
      (G.endpoints.app a)
    apply (Subobject.factors_iff _ _).2
    refine ⟨G.events.map e.hom ≫
      Y.reduction.factorThru (G.endpoints.app Y.base) Y.contains ≫
        (Subobject.underlyingIso (Y.reduction.arrow ≫ p.inv)).inv, ?_⟩
    simp [Category.assoc, p, ← Functor.map_comp]
  exact ⟨a, r, contains⟩

/-- Transporting an observation along a base isomorphism gives an
isomorphism of observations, preserving the chosen reduction predicate
in both directions. -/
noncomputable def Observation.transportAlongIsoIso
    (Y : Observation G) {a : B} (e : a ≅ Y.base) :
    Y.transportAlongIso G e ≅ Y := by
  let p : G.pairs.obj a ≅ G.pairs.obj Y.base := G.pairs.mapIso e
  let r : Subobject (G.pairs.obj a) :=
    Subobject.mk (Y.reduction.arrow ≫ p.inv)
  have forward : Y.reduction.Factors
      (r.arrow ≫ G.pairs.map e.hom) := by
    apply (Subobject.factors_iff _ _).2
    refine ⟨(Subobject.underlyingIso (Y.reduction.arrow ≫ p.inv)).hom, ?_⟩
    change (Subobject.underlyingIso (Y.reduction.arrow ≫ p.inv)).hom ≫
      Y.reduction.arrow =
      (Subobject.mk (Y.reduction.arrow ≫ p.inv)).arrow ≫ p.hom
    calc
      _ = ((Subobject.underlyingIso (Y.reduction.arrow ≫ p.inv)).hom ≫
          Y.reduction.arrow) ≫ (p.inv ≫ p.hom) := by simp
      _ = ((Subobject.underlyingIso (Y.reduction.arrow ≫ p.inv)).hom ≫
          (Y.reduction.arrow ≫ p.inv)) ≫ p.hom := by
            simp only [Category.assoc]
      _ = (Subobject.mk (Y.reduction.arrow ≫ p.inv)).arrow ≫ p.hom := by
        rw [Subobject.underlyingIso_hom_comp_eq_mk]
  have backward : r.Factors
      (Y.reduction.arrow ≫ G.pairs.map e.inv) := by
    exact Subobject.mk_factors_self _
  refine ⟨⟨e.hom, forward⟩, ⟨e.inv, backward⟩, ?_, ?_⟩
  · apply Hom.ext
    exact e.hom_inv_id
  · apply Hom.ext
    exact e.inv_hom_id

/-- Essential surjectivity lifts as well: transport the chosen predicate
along an isomorphism from a base-model preimage. -/
noncomputable instance reindexFunctor_essSurj (F : A ⥤ B) [F.EssSurj] :
    (reindexFunctor G F).EssSurj where
  mem_essImage Y := by
    let a : A := F.objPreimage Y.base
    let e : F.obj a ≅ Y.base := F.objObjPreimageIso Y.base
    let X : Observation G := Y.transportAlongIso G e
    let Z : Observation (G.reindex F) :=
      { base := a
        reduction := X.reduction
        contains := X.contains }
    refine ⟨Z, ⟨?_⟩⟩
    exact Y.transportAlongIsoIso G e

/-- An equivalence of base interpretations induces an equivalence on
interpretations carrying events and a chosen reduction predicate. -/
noncomputable instance reindexFunctor_isEquivalence
    (F : A ⥤ B) [F.IsEquivalence] :
    (reindexFunctor G F).IsEquivalence where

end Mettapedia.OSLF.Binding.VaryingEventObservations
