import Mettapedia.GSLT.LanguageDef.BagNormalFormSection
import Mathlib.Logic.Relation

/-!
# Deciding the declared equations of a bag presentation

For admissible open terms, equality of the computed normal forms is equivalent
to the generated equation relation. Both implications use the actual declared
bag laws: generator invariance and the normalization path. This characterization
does not include additional equations of another presentation.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

variable {language : LanguageDef} {bag : GrammarRule} {unit : Option String}

/-- Two or more surviving components retain their bag wrapper. -/
theorem collapse_eq_bag_of_length (unit : String) (elements : List Pattern)
    (many : 2 ≤ elements.length) :
    collapse unit elements = .collection .hashBag elements none := by
  cases elements with
  | nil => simp at many
  | cons first rest =>
      cases rest with
      | nil => simp at many
      | cons second tail => rfl

/-- Bag shape depends on multiplicity, without evaluating the sorting order. -/
theorem normalizeBag_isBagNode_of_length (unit : String) (elements : List Pattern)
    (many : 2 ≤ (bagContents unit elements).length) :
    IsBagNode (normalizeBag (some unit) elements) := by
  refine ⟨Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns (bagContents unit elements), ?_⟩
  exact collapse_eq_bag_of_length unit _ (by simpa using many)

/-- The constructive normalization path is an equation derivation. -/
theorem equationEquiv_normalForm (laws : BagTheory language bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {pattern : Pattern}
    (admissible : Admissible language free bound type pattern)
    (collectionless : collectionFree type = true) :
    EquationEquiv base language pattern (normalForm unit pattern) := by
  exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
    (path_normalForm laws base pattern admissible collectionless)

/-- Exact equation adequacy of normalization, including open binding contexts. -/
theorem equationEquiv_iff_normalForm_eq (laws : BagTheory language bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (leftAdmissible : Admissible language free bound type left)
    (rightAdmissible : Admissible language free bound type right)
    (collectionless : collectionFree type = true) :
    EquationEquiv base language left right ↔ normalForm unit left = normalForm unit right := by
  constructor
  · exact normalForm_eq_of_equationEquiv laws
  · intro equal
    exact .trans _ _ _ (equationEquiv_normalForm laws base leftAdmissible collectionless)
      (equal ▸ (equationEquiv_normalForm laws base rightAdmissible collectionless).symm)

/-- A decision procedure for the authored equation theory on its admissible terms. -/
def decideEquationEquiv (laws : BagTheory language bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (leftAdmissible : Admissible language free bound type left)
    (rightAdmissible : Admissible language free bound type right)
    (collectionless : collectionFree type = true) : Decidable (EquationEquiv base language left right) :=
  decidable_of_iff (normalForm unit left = normalForm unit right)
    (equationEquiv_iff_normalForm_eq laws base leftAdmissible rightAdmissible collectionless).symm

end Mettapedia.GSLT.LanguageDef.BagNormalForm
