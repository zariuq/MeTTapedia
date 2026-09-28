import Mettapedia.OSLF.Syntax.CategoricalBindingGroupoid

/-!
# Interpretation maps for the second-order binding classifier

Commuting with evaluation on the image of a sort map does not by itself
preserve abstraction. A classifying interpretation map must commute with
every authored contextual assignment, including those built by currying.

The first example separates these conditions. The category below keeps the
existing independently specified binding models, but uses maps that preserve
their interpreted contextual assignments. Its classifying-functor map is
constructed from the function-object components and their proven assignment
law.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingInterpretationMaps

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v

/-- A single inhabited source sort included in a two-element target sort. -/
def includeUnit (_ : PUnit) : Bool := false

/-- An evaluation-compatible map that discards behavior outside the image
of the source sort. -/
def eraseOutsideImage (_ : PUnit → PUnit) : Bool → Bool :=
  fun _ => false

/-- Evaluation commutes on every mapped source input. -/
theorem eraseOutsideImage_eval (q : PUnit → PUnit) (x : PUnit) :
    eraseOutsideImage q (includeUnit x) = includeUnit (q x) := by
  rfl

/-- Yet the same map sends the source identity abstraction to a constant
function, not to the target identity abstraction. -/
theorem eraseOutsideImage_not_identity :
    eraseOutsideImage (id : PUnit → PUnit) ≠ (id : Bool → Bool) := by
  intro h
  have atTrue := congrFun h true
  simp [eraseOutsideImage] at atTrue

/-- A positive control: choosing the target identity also satisfies the
evaluation square and preserves this abstraction. -/
def retainIdentity (_ : PUnit → PUnit) : Bool → Bool := id

theorem retainIdentity_eval (q : PUnit → PUnit) (x : PUnit) :
    retainIdentity q (includeUnit x) = includeUnit (q x) := by
  rfl

theorem retainIdentity_preserves_identity :
    retainIdentity (id : PUnit → PUnit) = (id : Bool → Bool) := by
  rfl

variable {S : Signature}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-- A map of independently specified binding models that preserves the
interpretation of every authored contextual assignment. The underlying
evaluation/operator map remains available, but its laws alone are weaker. -/
structure Hom (M N : Model S D) where
  underlying : M ⟶ N
  assignment_comm : ∀ {X Y : SecondOrderContext.Object S} (σ : X ⟶ Y),
    M.assignHom σ ≫ Model.familyMap underlying.power Y.arities =
      Model.familyMap underlying.power X.arities ≫ N.assignHom σ

@[ext] theorem Hom.ext {M N : Model S D} {first second : Hom M N}
    (same : first.underlying = second.underlying) : first = second := by
  cases first with
  | mk firstUnderlying firstLaw =>
    cases second with
    | mk secondUnderlying secondLaw =>
      cases same
      rfl

def Hom.id (M : Model S D) : Hom M M where
  underlying := 𝟙 M
  assignment_comm := by
    intro X Y σ
    change M.assignHom σ ≫
        Model.familyMap (fun _ _ => 𝟙 _) Y.arities =
      Model.familyMap (fun _ _ => 𝟙 _) X.arities ≫ M.assignHom σ
    rw [Model.familyMap_id, Model.familyMap_id]
    simp

def Hom.comp {M N P : Model S D} (first : Hom M N) (second : Hom N P) :
    Hom M P where
  underlying := first.underlying ≫ second.underlying
  assignment_comm := by
    intro X Y σ
    change M.assignHom σ ≫
        Model.familyMap (fun Γ s => first.underlying.power Γ s ≫
          second.underlying.power Γ s) Y.arities =
      Model.familyMap (fun Γ s => first.underlying.power Γ s ≫
        second.underlying.power Γ s) X.arities ≫ P.assignHom σ
    rw [Model.familyMap_comp, Model.familyMap_comp]
    calc
      M.assignHom σ ≫
          (Model.familyMap first.underlying.power Y.arities ≫
            Model.familyMap second.underlying.power Y.arities) =
        (M.assignHom σ ≫ Model.familyMap first.underlying.power Y.arities) ≫
          Model.familyMap second.underlying.power Y.arities :=
            (Category.assoc _ _ _).symm
      _ = (Model.familyMap first.underlying.power X.arities ≫
          N.assignHom σ) ≫ Model.familyMap second.underlying.power Y.arities := by
            rw [first.assignment_comm σ]
      _ = Model.familyMap first.underlying.power X.arities ≫
          (N.assignHom σ ≫ Model.familyMap second.underlying.power Y.arities) :=
            Category.assoc _ _ _
      _ = Model.familyMap first.underlying.power X.arities ≫
          (Model.familyMap second.underlying.power X.arities ≫ P.assignHom σ) := by
            rw [second.assignment_comm σ]
      _ = (Model.familyMap first.underlying.power X.arities ≫
          Model.familyMap second.underlying.power X.arities) ≫ P.assignHom σ :=
            (Category.assoc _ _ _).symm

/-- Objects are authored binding models; morphisms preserve their full
contextual interpretation. -/
structure Interpretation (S : Signature) (D : Type u)
    [Category.{v} D] [CartesianMonoidalCategory D] where
  model : Model S D

instance : Category (Interpretation S D) where
  Hom M N := Hom M.model N.model
  id M := Hom.id M.model
  comp f g := Hom.comp f g
  id_comp := by
    intro M N f
    apply Hom.ext
    exact Category.id_comp f.underlying
  comp_id := by
    intro M N f
    apply Hom.ext
    exact Category.comp_id f.underlying
  assoc := by
    intro M N P Q f g h
    apply Hom.ext
    exact Category.assoc f.underlying g.underlying h.underlying

/-- Each full interpretation map induces a natural transformation between
the independently constructed classifying functors. -/
def classifyingMap {M N : Model S D} (h : Hom M N) :
    M.classifyingFunctor ⟶ N.classifyingFunctor where
  app X := Model.familyMap h.underlying.power X.arities
  naturality _ _ σ := h.assignment_comm σ

/-- The map-level classifying construction is functorial. This is the
binding-only component required by a later operational equivalence. -/
def classifyingFunctor :
    Interpretation S D ⥤ (SecondOrderContext.Object S ⥤ D) where
  obj M := M.model.classifyingFunctor
  map h := classifyingMap h
  map_id M := by
    ext X
    exact Model.familyMap_id M.model X.arities
  map_comp f g := by
    ext X
    exact Model.familyMap_comp f.underlying.power g.underlying.power X.arities

/-- A natural transformation between classifying functors preserves each
interpreted contextual assignment and hence determines a full interpretation
map. The underlying model map is the independently proved reconstruction. -/
def Hom.ofNat {M N : Model S D}
    (τ : M.classifyingFunctor ⟶ N.classifyingFunctor) : Hom M N where
  underlying := Model.homOfNat τ
  assignment_comm := by
    intro X Y σ
    have natural := τ.naturality σ
    change M.assignHom σ ≫ τ.app Y = τ.app X ≫ N.assignHom σ at natural
    rw [Model.app_eq_familyMap τ X, Model.app_eq_familyMap τ Y] at natural
    exact natural

theorem Hom.natPower_classifyingMap {M N : Model S D} (h : Hom M N)
    (Γ : Ctx S) (s : S.Srt) :
    Model.natPower (classifyingMap h) Γ s = h.underlying.power Γ s := by
  change (M.powerIso Γ s).inv ≫
      Model.familyMap h.underlying.power [(Γ, s)] ≫
      (N.powerIso Γ s).hom = h.underlying.power Γ s
  change (M.powerIso Γ s).inv ≫
    (Model.familyMap h.underlying.power [(Γ, s)] ≫
      N.familyProj [(Γ, s)] ⟨0, by simp⟩) = h.underlying.power Γ s
  rw [Model.familyMap_proj]
  change (M.powerIso Γ s).inv ≫ (M.powerIso Γ s).hom ≫
    h.underlying.power Γ s = h.underlying.power Γ s
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem Hom.ofNat_classifyingMap {M N : Model S D} (h : Hom M N) :
    Hom.ofNat (classifyingMap h) = h := by
  apply Hom.ext
  apply Model.Hom.ext
  · funext s
    change Model.natSort (classifyingMap h) s = h.underlying.sort s
    rw [← cancel_epi (M.emptyPowerIso s).hom,
      ← Model.natPower_emptyPower,
      Hom.natPower_classifyingMap,
      Model.power_nil_comp_emptyPower]
  · funext Γ s
    exact Hom.natPower_classifyingMap h Γ s

theorem Hom.classifyingMap_ofNat {M N : Model S D}
    (τ : M.classifyingFunctor ⟶ N.classifyingFunctor) :
    classifyingMap (Hom.ofNat τ) = τ := by
  apply NatTrans.ext
  funext X
  exact (Model.app_eq_familyMap τ X).symm

/-- Full faithfulness at the level of hom-sets: contextual interpretation
maps are exactly the natural transformations between the corresponding
classifying functors. -/
def interpretationHomEquiv (M N : Model S D) :
    Hom M N ≃ (M.classifyingFunctor ⟶ N.classifyingFunctor) where
  toFun := classifyingMap
  invFun := Hom.ofNat
  left_inv := Hom.ofNat_classifyingMap
  right_inv := Hom.classifyingMap_ofNat

end Mettapedia.OSLF.Binding.CategoricalBindingInterpretationMaps

#print axioms Mettapedia.OSLF.Binding.CategoricalBindingInterpretationMaps.eraseOutsideImage_not_identity
#print axioms Mettapedia.OSLF.Binding.CategoricalBindingInterpretationMaps.classifyingFunctor
