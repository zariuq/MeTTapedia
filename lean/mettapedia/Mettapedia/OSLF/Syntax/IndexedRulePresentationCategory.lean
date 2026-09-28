import Mettapedia.OSLF.Syntax.IndexedRulePolynomialMorphisms
import Mathlib.CategoryTheory.Category.Basic

/-!
# Category of indexed rule presentations over a context base

An object has judgment indices and a polynomial of rule constructors at
each context and judgment. A morphism maps judgments and constructors while
bijectively transporting each constructor's recursive premises. Thus this
category describes cartesian rule translations; a translation that erases or
duplicates premise evidence requires a different morphism class.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IndexedRulePresentationCategory

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms

universe uBase uIndex uShape uPosition

/- The index and polynomial universe parameters meet in the dependent
polynomial field; all three are retained for maps between rich fibres. -/
set_option linter.checkUnivs false in
/-- A context-indexed rule presentation with individually addressed
recursive premises. -/
structure Presentation (Base : Type uBase) where
  Judgment : Base → Type uIndex
  rules : IndexedPolynomial.{uBase, uIndex, uShape, uPosition}
    Base Judgment

namespace Presentation

variable {Base : Type uBase}

/-- A cartesian translation of rule presentations. -/
structure Map (source target : Presentation.{uBase, uIndex, uShape, uPosition}
    Base) where
  judgment : ∀ b, source.Judgment b → target.Judgment b
  rules : IndexedRulePolynomialMorphisms.Hom source.rules target.rules judgment

namespace Map

variable {source middle target fourth :
  Presentation.{uBase, uIndex, uShape, uPosition} Base}

/-- A presentation map is determined by its judgment and rule actions. -/
theorem ext {first second : Map source target}
    (judgmentEq : first.judgment = second.judgment)
    (rulesEq : HEq first.rules second.rules) : first = second := by
  cases first with
  | mk firstJudgment firstRules =>
      cases second with
      | mk secondJudgment secondRules =>
          cases judgmentEq
          cases rulesEq
          rfl

def id (source : Presentation.{uBase, uIndex, uShape, uPosition} Base) :
    Map source source where
  judgment := fun _ i => i
  rules := IndexedRulePolynomialMorphisms.Hom.id source.rules

def comp (earlier : Map source middle) (later : Map middle target) :
    Map source target where
  judgment := fun b i => later.judgment b (earlier.judgment b i)
  rules := IndexedRulePolynomialMorphisms.Hom.comp earlier.rules later.rules

theorem id_comp (f : Map source target) : comp (id source) f = f := by
  cases f with
  | mk judgment rules =>
      exact congrArg (Map.mk judgment)
        (IndexedRulePolynomialMorphisms.Hom.id_comp rules)

theorem comp_id (f : Map source target) : comp f (id target) = f := by
  cases f with
  | mk judgment rules =>
      exact congrArg (Map.mk judgment)
        (IndexedRulePolynomialMorphisms.Hom.comp_id rules)

theorem comp_assoc (f : Map source middle) (g : Map middle target)
    (h : Map target fourth) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f with
  | mk fIndex fRules =>
      cases g with
      | mk gIndex gRules =>
          cases h with
          | mk hIndex hRules =>
              exact congrArg
                (Map.mk (fun b i => hIndex b (gIndex b (fIndex b i))))
                (IndexedRulePolynomialMorphisms.Hom.comp_assoc
                  fRules gRules hRules)

end Map

instance : CategoryTheory.Category
    (Presentation.{uBase, uIndex, uShape, uPosition} Base) where
  Hom source target := Map source target
  id := Map.id
  comp := Map.comp
  id_comp := by
    intro source target f
    exact Map.id_comp f
  comp_id := by
    intro source target f
    exact Map.comp_id f
  assoc := by
    intro source middle target fourth f g h
    exact Map.comp_assoc f g h

end Presentation

end Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
