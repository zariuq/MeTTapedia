import Mettapedia.OSLF.Syntax.CategoricalBindingTargetPreservation
import Mettapedia.OSLF.Syntax.CategoricalBindingQuotientEquivalence

/-!
# Categorical target change for full binding interpretations and equations

The target-change functor sends actual sorts and function objects to their
images. Contextual assignment laws follow from the generic interpretation
comparison, and equation satisfaction follows at every target stage from
naturality of generalized elements.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v u' v'

variable {S : Signature}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable (H : D ⥤ D') [PreservesFiniteProducts H] [ExponentialPreservation H]

/-- Contextual assignment commutes with the actual family-product comparison. -/
theorem mapModel_assignHom (M : Model S D) {X Y : Object S} (σ : X ⟶ Y) :
    (mapModel H M).assignHom σ ≫ (familyComparison H M.power Y.arities).hom =
      (familyComparison H M.power X.arities).hom ≫ H.map (M.assignHom σ) := by
  apply (cancel_mono (familyComparison H M.power Y.arities).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  symm
  apply (mapModel H M).familyLift_unique
  intro j
  rw [← familyComparison_proj H M]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← H.map_comp, M.assignHom_proj]
  exact (mapModel_curry_generic H M X.arities (σ j)).symm

/-- The mapped binding model classifies the postcomposition of the original
classifying functor, with its actual family-product comparison. -/
def mapModel_classifyingIso (M : Model S D) :
    (mapModel H M).classifyingFunctor ≅ M.classifyingFunctor ⋙ H :=
  NatIso.ofComponents (fun X => familyComparison H M.power X.arities)
    (fun {_X _Y} σ => mapModel_assignHom H M σ)

/-- Equation satisfaction transports at every stage of the new target. -/
theorem mapModel_equations (M : Model S D) {schema : List (MetaArity S)}
    (P : EquationPresentation S schema) (satisfies : M.Satisfies P) :
    (mapModel H M).Satisfies P := by
  intro X i Θ Δ body ambient ordinary
  apply Preserving.elem_eq_of_generic
  change (mapModel H M).generic X.arities (ContextualAssignment.instantiate body ambient ordinary ((P.axioms X).get i).lhs) =
    (mapModel H M).generic X.arities (ContextualAssignment.instantiate body ambient ordinary ((P.axioms X).get i).rhs)
  rw [mapModel_generic H M, mapModel_generic H M]
  have equal : M.generic X.arities (ContextualAssignment.instantiate body ambient ordinary ((P.axioms X).get i).lhs) =
      M.generic X.arities (ContextualAssignment.instantiate body ambient ordinary ((P.axioms X).get i).rhs) :=
    congrArg (fun x => x.value _ (snd _ _) (M.genericEnv _ _)) (satisfies X i body ambient ordinary)
  rw [equal]

/-- A full interpretation map transports by mapping its actual components.
Its contextual assignment law is derived, including for noninvertible maps. -/
def mapInterpretationHom {M N : Model S D}
    (f : CategoricalBindingInterpretationMaps.Hom M N) :
    CategoricalBindingInterpretationMaps.Hom (mapModel H M) (mapModel H N) where
  underlying := mapModelHom H f.underlying
  assignment_comm := by
    intro X Y σ
    apply (cancel_mono (familyComparison H N.power Y.arities).hom).mp
    change ((mapModel H M).assignHom σ ≫
        Model.familyMap (M := mapModel H M) (N := mapModel H N)
          (fun Γ s => H.map (f.underlying.power Γ s)) Y.arities) ≫
          (familyComparison H N.power Y.arities).hom =
      (Model.familyMap (M := mapModel H M) (N := mapModel H N)
          (fun Γ s => H.map (f.underlying.power Γ s)) X.arities ≫
        (mapModel H N).assignHom σ) ≫ (familyComparison H N.power Y.arities).hom
    rw [Category.assoc, ← familyComparison_natural H, ← Category.assoc,
      mapModel_assignHom H M, Category.assoc, ← H.map_comp, f.assignment_comm,
      H.map_comp, ← Category.assoc, familyComparison_natural H,
      Category.assoc, ← mapModel_assignHom H N, Category.assoc]

/-- Target change on the entire category of full binding interpretations. -/
def mapInterpretations :
    CategoricalBindingInterpretationMaps.Interpretation S D ⥤
      CategoricalBindingInterpretationMaps.Interpretation S D' where
  obj M := ⟨mapModel H M.model⟩
  map f := mapInterpretationHom H f
  map_id M := by
    apply CategoricalBindingInterpretationMaps.Hom.ext
    exact (mapModels H).map_id M.model
  map_comp f g := by
    apply CategoricalBindingInterpretationMaps.Hom.ext
    exact (mapModels H).map_comp f.underlying g.underlying

/-- The image-model classifying comparison is natural in every full model
map, including noninvertible maps. -/
def mapInterpretationsClassifyingIso :
    mapInterpretations (S := S) H ⋙
        CategoricalBindingInterpretationMaps.classifyingFunctor ≅
      CategoricalBindingInterpretationMaps.classifyingFunctor ⋙
        (Functor.whiskeringRight (Object S) D D').obj H :=
  NatIso.ofComponents (fun M => mapModel_classifyingIso H M.model) (fun {M N} f => by
    apply NatTrans.ext
    funext X
    exact (familyComparison_natural H f.underlying.power X.arities).symm)

/-- Target change on models satisfying the existing equation presentation. -/
def mapSatisfyingInterpretations {schema : List (MetaArity S)} (P : EquationPresentation S schema) :
    CategoricalBindingEquationEquivalence.SatisfyingInterpretation (D := D) P ⥤
      CategoricalBindingEquationEquivalence.SatisfyingInterpretation (D := D') P where
  obj M := ⟨(mapInterpretations H).obj M.interpretation,
    mapModel_equations H M.interpretation.model P M.satisfies⟩
  map f := (mapInterpretations H).map f
  map_id M := (mapInterpretations H).map_id M.interpretation
  map_comp f g := (mapInterpretations H).map_comp f g

end Mettapedia.OSLF.Binding.CategoricalBindingModel
