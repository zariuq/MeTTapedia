import Mettapedia.OSLF.Syntax.CategoricalBindingEquivalence

/-!
# Relative categorical classification with authored equations

An equation presentation restricts binding models to those satisfying every
instance of its axioms, and structured functors to those identifying the
generated equation relation. The binding equivalence restricts to an
equivalence between these categories, including noninvertible interpretation
maps. The separately proved quotient universal property then identifies the
target functors with interpretations of equation-class contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingEquationEquivalence

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalBindingInterpretationMaps
open Mettapedia.OSLF.Binding.CategoricalBindingEquivalence
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v

variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-- Binding models satisfying every authored equation instance. -/
structure SatisfyingInterpretation (P : EquationPresentation S schema) where
  interpretation : Interpretation S D
  satisfies : interpretation.model.Satisfies P

instance (P : EquationPresentation S schema) : Category (SatisfyingInterpretation (D := D) P) where
  Hom M N := M.interpretation ⟶ N.interpretation
  id M := 𝟙 M.interpretation
  comp f g := f ≫ g
  id_comp := by intros; simp
  comp_id := by intros; simp
  assoc := by intros; exact Category.assoc _ _ _

/-- Structured functors that identify all generated equations. -/
structure RespectingStructuredFunctor (P : EquationPresentation S schema) where
  structured : StructuredFunctor S D
  respects : ∀ {X Y : SecondOrderContext.Object S} {σ τ : X ⟶ Y},
    P.homRel σ τ → structured.carrier.map σ = structured.carrier.map τ

instance (P : EquationPresentation S schema) :
    Category (RespectingStructuredFunctor (D := D) P) where
  Hom F G := F.structured ⟶ G.structured
  id F := 𝟙 F.structured
  comp f g := f ≫ g
  id_comp := by intros; simp
  comp_id := by intros; simp
  assoc := by intros; exact Category.assoc _ _ _

/-- The classifying interpretation of equations, on models and all lawful
contextual interpretation maps. -/
def equationClassifier (P : EquationPresentation S schema) :
    SatisfyingInterpretation (D := D) P ⥤ RespectingStructuredFunctor (D := D) P where
  obj M := {
    structured := (bindingClassifier (S := S) (D := D)).obj M.interpretation
    respects := by
      intro X Y σ τ related
      exact M.interpretation.model.assignHom_congr P M.satisfies related }
  map h := (bindingClassifier (S := S) (D := D)).map h
  map_id M := (bindingClassifier (S := S) (D := D)).map_id M.interpretation
  map_comp f g := (bindingClassifier (S := S) (D := D)).map_comp f g

instance (P : EquationPresentation S schema) : (equationClassifier (D := D) P).Full where
  map_surjective := by
    intro M N τ
    refine ⟨Hom.ofNat τ, ?_⟩
    exact Hom.classifyingMap_ofNat τ

instance (P : EquationPresentation S schema) : (equationClassifier (D := D) P).Faithful where
  map_injective := by
    intro M N f g same
    change classifyingMap f = classifyingMap g at same
    have recovered := congrArg Hom.ofNat same
    simpa only [Hom.ofNat_classifyingMap] using recovered

instance (P : EquationPresentation S schema) : (equationClassifier (D := D) P).EssSurj where
  mem_essImage F := by
    let M := F.structured.preserving.toModel
    have sat : M.Satisfies P :=
      F.structured.preserving.satisfies_of_respects P F.respects
    refine ⟨⟨⟨M⟩, sat⟩, ⟨?_⟩⟩
    exact {
      hom := F.structured.preserving.isoClassifying.inv
      inv := F.structured.preserving.isoClassifying.hom
      hom_inv_id := F.structured.preserving.isoClassifying.inv_hom_id
      inv_hom_id := F.structured.preserving.isoClassifying.hom_inv_id }

instance (P : EquationPresentation S schema) :
    (equationClassifier (D := D) P).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-- Lawful binding models of an equation presentation, with all contextual
model maps, are equivalent to structured functors respecting its equations. -/
noncomputable def equationEquivalence (P : EquationPresentation S schema) :
    SatisfyingInterpretation (D := D) P ≌ RespectingStructuredFunctor (D := D) P :=
  (equationClassifier (D := D) P).asEquivalence

end Mettapedia.OSLF.Binding.CategoricalBindingEquationEquivalence

#print axioms Mettapedia.OSLF.Binding.CategoricalBindingEquationEquivalence.equationEquivalence
