import Mettapedia.OSLF.Syntax.IndexedRulePresentationCategory
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraCategory
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraPullback
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Rule presentations equipped with proof-relevant operational models

An equipped presentation consists of a context-indexed polynomial of rules
and an algebra interpreting those rules. A map carries both a cartesian
presentation translation and an algebra map into the pullback target model.
The context base remains fixed. Authored binding clones and equations must
still be connected to this generic category by a separate construction.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory

open Mettapedia.TypeTheory
open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
open Mettapedia.OSLF.Binding.IndexedRuleAlgebraPullback

universe uBase uIndex uShape uPosition

variable {Base : Type uBase}

/-- A rule presentation together with an interpretation of each of its
constructors and recursively addressed premises. -/
structure Equipped (Base : Type uBase) where
  presentation : Presentation.{uBase, uIndex, uShape, uPosition} Base
  model : OperationalRuleModels.Model presentation.rules

namespace Equipped

variable {X Y Z : Equipped.{uBase, uIndex, uShape, uPosition} Base}

/-- An operational interpretation preserves both authored rule shapes and
the target algebra's action on every recursively supplied premise. -/
structure Map (X Y : Equipped.{uBase, uIndex, uShape, uPosition} Base) where
  presentation : Presentation.Map X.presentation Y.presentation
  toFun : ∀ b i, X.model.carrier b i →
    Y.model.carrier b (presentation.judgment b i)
  preserves : ∀ b i
    (layer : X.presentation.rules.Extension X.model.carrier b i),
    toFun b i (X.model.rules.act b i layer) =
      (pullback presentation.rules Y.model.rules).act b i
        (IndexedPolynomial.Extension.map X.presentation.rules toFun layer)

namespace Map

/-- The evidence action of an equipped-presentation map is an actual
homomorphism into the reindexed target rule algebra. -/
noncomputable def toAlgebraHom (mapping : Map X Y) :
    IndexedPolynomial.Algebra.Hom X.model.rules
      (pullback mapping.presentation.rules Y.model.rules) where
  toFun := mapping.toFun
  commutes := mapping.preserves

def id (X : Equipped.{uBase, uIndex, uShape, uPosition} Base) :
    Map X X where
  presentation := Presentation.Map.id X.presentation
  toFun := fun _ _ value => value
  preserves := by
    intro b i layer
    cases layer
    rfl

noncomputable def comp (first : Map X Y) (second : Map Y Z) :
    Map X Z where
  presentation := Presentation.Map.comp first.presentation second.presentation
  toFun := fun b i value =>
    second.toFun b (first.presentation.judgment b i)
      (first.toFun b i value)
  preserves := by
    intro b i layer
    let composite : IndexedPolynomial.Algebra.Hom X.model.rules
        (pullback first.presentation.rules
          (pullback second.presentation.rules Z.model.rules)) :=
      IndexedPolynomial.Algebra.Hom.comp first.toAlgebraHom
        (pullbackHom first.presentation.rules second.toAlgebraHom)
    have h := composite.commutes b i layer
    change composite.toFun b i (X.model.rules.act b i layer) =
      (pullback first.presentation.rules
        (pullback second.presentation.rules Z.model.rules)).act b i
          (IndexedPolynomial.Extension.map X.presentation.rules
            composite.toFun layer) at h
    change composite.toFun b i (X.model.rules.act b i layer) =
      (pullback
        (IndexedRulePolynomialMorphisms.Hom.comp first.presentation.rules
          second.presentation.rules) Z.model.rules).act b i
          (IndexedPolynomial.Extension.map X.presentation.rules
            composite.toFun layer)
    rw [pullback_comp]
    exact h

/-- Two maps coincide when their presentation maps and evidence functions
coincide. Preservation proofs then coincide by proof irrelevance. -/
theorem ext {first second : Map X Y}
    (presentationEq : first.presentation = second.presentation)
    (evidenceEq : HEq first.toFun second.toFun) :
    first = second := by
  cases first with
  | mk firstPresentation firstEvidence firstPreserves =>
      cases second with
      | mk secondPresentation secondEvidence secondPreserves =>
          cases presentationEq
          cases evidenceEq
          rfl

/-- A pointwise heterogeneous equality of evidence maps suffices once the
presentation maps agree. This avoids identifying evidence functions whose
codomain families are indexed through differently written presentation maps. -/
theorem ext_of_pointwise {first second : Map X Y}
    (presentationEq : first.presentation = second.presentation)
    (points : ∀ b i value,
      first.toFun b i value ≍ second.toFun b i value) :
    first = second := by
  cases first with
  | mk firstPresentation firstEvidence firstPreserves =>
      cases second with
      | mk secondPresentation secondEvidence secondPreserves =>
          dsimp at presentationEq points
          cases presentationEq
          have same : firstEvidence = secondEvidence := by
            funext b i value
            exact eq_of_heq (points b i value)
          cases same
          rfl

theorem id_comp (mapping : Map X Y) :
    comp (id X) mapping = mapping := by
  apply ext (Presentation.Map.id_comp mapping.presentation)
  rfl

theorem comp_id (mapping : Map X Y) :
    comp mapping (id Y) = mapping := by
  apply ext (Presentation.Map.comp_id mapping.presentation)
  rfl

theorem comp_assoc {W : Equipped.{uBase, uIndex, uShape, uPosition} Base}
    (first : Map X Y) (second : Map Y Z) (third : Map Z W) :
    comp (comp first second) third =
      comp first (comp second third) := by
  apply ext (Presentation.Map.comp_assoc
    first.presentation second.presentation third.presentation)
  rfl

end Map

end Equipped

/-- Equipped rule presentations and proof-relevant algebra-preserving maps
form a category. -/
noncomputable instance : _root_.CategoryTheory.Category
    (Equipped.{uBase, uIndex, uShape, uPosition} Base) where
  Hom X Y := Equipped.Map X Y
  id X := Equipped.Map.id X
  comp first second := Equipped.Map.comp first second
  id_comp := by
    intro X Y mapping
    exact Equipped.Map.id_comp mapping
  comp_id := by
    intro X Y mapping
    exact Equipped.Map.comp_id mapping
  assoc := by
    intro X Y Z W first second third
    exact Equipped.Map.comp_assoc first second third

/-- Forgetting the chosen rule-algebra interpretation retains the exact
presentation morphism, including its recursive premise addresses. -/
noncomputable def forget :
    Equipped.{uBase, uIndex, uShape, uPosition} Base ⥤
      Presentation.{uBase, uIndex, uShape, uPosition} Base where
  obj X := X.presentation
  map mapping := mapping.presentation
  map_id := by intro X; rfl
  map_comp := by intro X Y Z first second; rfl

/-- Equip a rule presentation with its free proof-relevant constructor-tree
algebra. -/
def free (P : Presentation.{uBase, uIndex, uShape, uPosition} Base) :
    Equipped.{uBase, uIndex, uShape, uPosition} Base where
  presentation := P
  model := OperationalRuleModels.free P.rules

/-- A cartesian presentation map acts on every free firing history and
preserves the constructor algebra. -/
noncomputable def freeMap
    {P Q : Presentation.{uBase, uIndex, uShape, uPosition} Base}
    (mapping : Presentation.Map P Q) :
    Equipped.Map (free P) (free Q) where
  presentation := mapping
  toFun := mapping.rules.mapFix
  preserves := by
    intro b i layer
    cases layer with
    | mk shape children =>
        rfl

/-- Free constructor-tree models vary functorially with their rule
presentations. -/
noncomputable def freeFunctor :
    Presentation.{uBase, uIndex, uShape, uPosition} Base ⥤
      Equipped.{uBase, uIndex, uShape, uPosition} Base where
  obj := free
  map := fun mapping => freeMap mapping
  map_id := by
    intro P
    change freeMap (Presentation.Map.id P) = Equipped.Map.id (free P)
    apply Equipped.Map.ext
      (first := freeMap (Presentation.Map.id P))
      (second := Equipped.Map.id (free P)) rfl
    apply heq_of_eq
    funext b i tree
    exact IndexedRulePolynomialMorphisms.Hom.mapFix_id P.rules b i tree
  map_comp := by
    intro P Q R first second
    change freeMap (Presentation.Map.comp first second) =
      Equipped.Map.comp (freeMap first) (freeMap second)
    apply Equipped.Map.ext
      (first := freeMap (Presentation.Map.comp first second))
      (second := Equipped.Map.comp (freeMap first) (freeMap second)) rfl
    apply heq_of_eq
    funext b i tree
    exact IndexedRulePolynomialMorphisms.Hom.mapFix_comp
      first.rules second.rules b i tree

/-- Interpret the free rule histories of a presentation in any equipped
target along a cartesian presentation map. -/
noncomputable def lift
    {P : Presentation.{uBase, uIndex, uShape, uPosition} Base}
    (X : Equipped.{uBase, uIndex, uShape, uPosition} Base)
    (mapping : Presentation.Map P X.presentation) :
    Equipped.Map (free P) X where
  presentation := mapping
  toFun := relativeFold mapping.rules X.model.rules
  preserves := by
    intro b i layer
    cases layer with
    | mk shape children =>
        rfl

/-- Any interpretation from a free equipped presentation is determined
uniquely by its underlying presentation map. -/
theorem lift_unique
    {P : Presentation.{uBase, uIndex, uShape, uPosition} Base}
    {X : Equipped.{uBase, uIndex, uShape, uPosition} Base}
    (mapping : Equipped.Map (free P) X) :
    lift X mapping.presentation = mapping := by
  apply Equipped.Map.ext
    (first := lift X mapping.presentation) (second := mapping) rfl
  apply heq_of_eq
  funext b i tree
  symm
  apply relativeFold_unique mapping.presentation.rules X.model.rules
    mapping.toFun
  · intro b i shape children
    exact mapping.preserves b i ⟨shape, children⟩

/-- The free equipped presentation has the expected hom-set universal
property, including interpretation maps and their proof-relevant actions. -/
noncomputable def freeHomEquiv
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (X : Equipped.{uBase, uIndex, uShape, uPosition} Base) :
    (free P ⟶ X) ≃ (P ⟶ X.presentation) where
  toFun mapping := mapping.presentation
  invFun := lift X
  left_inv := lift_unique
  right_inv := by intro mapping; rfl

/-- Freely adjoining a proof-relevant algebra of rule firings is left
adjoint to forgetting the chosen algebra. The adjunction ranges over actual
presentation and algebra morphisms, and its hom equivalence is the relative
fold's uniqueness theorem. -/
noncomputable def freeAdjunction :
    (freeFunctor (Base := Base) :
      Presentation.{uBase, uIndex, uShape, uPosition} Base ⥤
        Equipped.{uBase, uIndex, uShape, uPosition} Base) ⊣
    (forget (Base := Base) :
      Equipped.{uBase, uIndex, uShape, uPosition} Base ⥤
        Presentation.{uBase, uIndex, uShape, uPosition} Base) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := freeHomEquiv
      homEquiv_naturality_left_symm := by
        intro P' P X first second
        apply (freeHomEquiv P' X).injective
        rfl
      homEquiv_naturality_right := by
        intro P X Y first second
        rfl }

/-- The unit leaves an authored rule presentation unchanged. -/
theorem freeAdjunction_unit_app
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base) :
    (freeAdjunction (Base := Base)).unit.app P = 𝟙 P := by
  rfl

/-- The counit interprets each freely generated firing history in the
chosen target rule algebra. -/
theorem freeAdjunction_counit_app
    (X : Equipped.{uBase, uIndex, uShape, uPosition} Base) :
    (freeAdjunction (Base := Base)).counit.app X =
      lift X (𝟙 X.presentation) := by
  rfl

#print axioms freeAdjunction
#print axioms freeAdjunction_unit_app
#print axioms freeAdjunction_counit_app

end Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory
