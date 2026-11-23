import Mettapedia.GSLT.LanguageDef.BagNormalFormSection
import Mathlib.Data.Multiset.Defs

/-! The extensional mathematical interface of the declared bag laws. -/

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
theorem equationEquiv_normalForm (laws : BareBagTheory language bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {pattern : Pattern}
    (admissible : Admissible language free bound type pattern)
    (collectionless : collectionFree type = true) :
    EquationEquiv base language pattern (normalForm unit pattern) := by
  exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
    (path_normalForm laws base pattern admissible collectionless)

/-- Exact equation adequacy of normalization, including open binding contexts. -/
theorem equationEquiv_iff_normalForm_eq (laws : BareBagTheory language bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (leftAdmissible : Admissible language free bound type left)
    (rightAdmissible : Admissible language free bound type right)
    (collectionless : collectionFree type = true) :
    EquationEquiv base language left right ↔ normalForm unit left = normalForm unit right := by
  constructor
  · exact normalForm_eq_of_equationEquiv laws.toBagTheory
  · intro equal
    exact .trans _ _ _ (equationEquiv_normalForm laws base leftAdmissible collectionless)
      (equal ▸ (equationEquiv_normalForm laws base rightAdmissible collectionless).symm)

/-- A decision procedure for the authored equation theory on its admissible terms. -/
def decideEquationEquiv (laws : BareBagTheory language bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (leftAdmissible : Admissible language free bound type left)
    (rightAdmissible : Admissible language free bound type right)
    (collectionless : collectionFree type = true) : Decidable (EquationEquiv base language left right) :=
  decidable_of_iff (normalForm unit left = normalForm unit right)
    (equationEquiv_iff_normalForm_eq laws base leftAdmissible rightAdmissible collectionless).symm

end Mettapedia.GSLT.LanguageDef.BagNormalForm

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode

theorem bagContents_of_rootNormal_bag {unitLabel : String} {elements : List Pattern}
    (normal : RootNormal unitLabel (.collection .hashBag elements none)) :
    bagContents unitLabel [.collection .hashBag elements none] = elements := by
  simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, splice_bag]
  apply List.filter_eq_self.mpr
  intro element member
  simpa using ((normal elements rfl).2.2 element member).1

/-- Reading a root-normal algebra value into components and rebuilding by the
existing algebra collapse returns that value, including the declared unit. -/
theorem collapse_contents {unitLabel : String} {focus : Pattern}
    (normal : RootNormal unitLabel focus) :
    collapse unitLabel (bagContents unitLabel [focus]) = focus := by
  by_cases bagNode : IsBagNode focus
  · obtain ⟨elements, rfl⟩ := bagNode
    rw [bagContents_of_rootNormal_bag normal,
      collapse_eq_bag_of_length unitLabel elements (normal elements rfl).2.1]
  · by_cases isUnit : focus = .apply unitLabel []
    · subst focus
      simp [bagContents, splice, collapse]
    · simp [bagContents, splice_of_not_bag bagNode, isUnit, collapse]

theorem rootContents_sorted {unitLabel : String} {focus : Pattern}
    (normal : RootNormal unitLabel focus) :
    sortPatterns (bagContents unitLabel [focus]) = bagContents unitLabel [focus] := by
  by_cases isBag : IsBagNode focus
  · obtain ⟨elements, rfl⟩ := isBag
    rw [bagContents_of_rootNormal_bag normal, (normal elements rfl).1]
  · by_cases isUnit : focus = .apply unitLabel []
    · subst focus
      simp [bagContents, splice]
    · simp [bagContents, splice_of_not_bag isBag, isUnit]

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

/-- The extensional value of an algebra focus. The multiset retains
multiplicity and the normalized components, independent of source addresses. -/
def componentMultiset (unit : String) (source : Pattern) : Multiset Pattern :=
  bagContents unit [normalForm (some unit) source]

theorem componentMultiset_eq_iff_normalForm_eq (unit : String) (left right : Pattern) :
    componentMultiset unit left = componentMultiset unit right ↔
      normalForm (some unit) left = normalForm (some unit) right := by
  constructor
  · intro equal
    have perm := Multiset.coe_eq_coe.mp equal
    have sorted := Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns_eq_of_perm perm
    rw [WithAuthoredEquations.AlgebraFocus.rootContents_sorted (rootNormal_normalForm unit left),
      WithAuthoredEquations.AlgebraFocus.rootContents_sorted (rootNormal_normalForm unit right)] at sorted
    rw [← WithAuthoredEquations.AlgebraFocus.collapse_contents (rootNormal_normalForm unit left),
      ← WithAuthoredEquations.AlgebraFocus.collapse_contents (rootNormal_normalForm unit right), sorted]
  · intro equal
    simp only [componentMultiset, equal]

/-- Extensional bag values decide the scoped source-equation relation. -/
theorem equationEquiv_iff_componentMultiset_eq {language : LanguageDef}
    {bag : GrammarRule} {unit : String}
    (laws : BareBagTheory language bag (some unit))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (leftAdmissible : Admissible language free bound type left)
    (rightAdmissible : Admissible language free bound type right)
    (collectionless : collectionFree type = true) :
    EquationEquiv base language left right ↔ componentMultiset unit left = componentMultiset unit right :=
  (equationEquiv_iff_normalForm_eq laws base leftAdmissible rightAdmissible collectionless).trans
    (componentMultiset_eq_iff_normalForm_eq unit left right).symm

#print axioms equationEquiv_iff_componentMultiset_eq

end Mettapedia.GSLT.LanguageDef.BagNormalForm

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A singleton wrapper has the same bag value as its component. -/
theorem normalForm_singleton (unit : String) (pattern : Pattern) :
    normalForm (some unit) (.collection .hashBag [pattern] none) =
      normalForm (some unit) pattern := by
  simp only [normalForm_bag, List.map_singleton, normalizeBag]
  rw [AlgebraFocus.rootContents_sorted (rootNormal_normalForm unit pattern)]
  exact AlgebraFocus.collapse_contents (rootNormal_normalForm unit pattern)

/-- The two actual retained wrapper-unit rows are invariant under every
binding substitution, including substitutions containing arbitrary terms. -/
theorem normalForm_insert_unit (unit : String) (before after : List Pattern) :
    normalForm (some unit) (.collection .hashBag (before ++ .apply unit [] :: after) none) =
      normalForm (some unit) (.collection .hashBag (before ++ after) none) := by
  rw [normalForm_bag,normalForm_bag]
  apply normalizeBag_contents_perm
  simp only [List.map_append,List.map_cons,bagContents_append]
  rw [bagContents_cons unit (normalForm (some unit) (.apply unit []))]
  have noUnit : bagContents unit [normalForm (some unit) (.apply unit [])] = [] := by
    simp [normalForm,normalFormList,bagContents,splice]
  rw [noUnit,List.nil_append]

#print axioms normalForm_singleton
#print axioms normalForm_insert_unit

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations
