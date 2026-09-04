import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.StructuralCategory
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Binding naturality of structural language translations

`StructuralCategory.mapPattern` is the action of an authored language-symbol
map on the shared locally nameless pattern carrier.  This file proves that the
action is compatible with the operations that give that carrier its binding
meaning: opening, closing, lifting, and binder-eliminating substitution.

Object-language constructors and outer judgment heads are distinct
namespaces.  A replacement inserted into a judgment is therefore translated
as an object-language pattern, while the retained outer judgment head is
translated through `CalculusLanguageSymbols.judgment`.  Naturality for
opening and instantiation is consequently stated for judgment-shaped claims;
an explicit counterexample shows why it is false for arbitrary raw patterns.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## Structural patterns commute with locally nameless operations -/

/-- Structural symbol transport commutes with opening a bound variable. -/
theorem mapPattern_openBVar (symbols : LanguageDefSymbolMap) (index : Nat)
    (replacement body : Pattern) :
    mapPattern symbols (openBVar index replacement body) =
      openBVar index (mapPattern symbols replacement)
        (mapPattern symbols body) := by
  induction body using Pattern.inductionOn generalizing index with
  | hbvar variableIndex =>
      by_cases equal : variableIndex = index <;>
        simp [openBVar, mapPattern, equal]
  | hfvar name => simp [openBVar, mapPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [openBVar, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (Pattern.apply (symbols.constructor constructor))
      apply List.map_congr_left
      intro argument membership
      simpa only [Function.comp_apply] using
        inductionHypothesis argument membership index
  | hlambda binder body inductionHypothesis =>
      simp [openBVar, mapPattern, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [openBVar, mapPattern, inductionHypothesis]
  | hsubst body replacement bodyIH replacementIH =>
      simp [openBVar, mapPattern, bodyIH, replacementIH]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [openBVar, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (fun mappedElements =>
        Pattern.collection collectionType mappedElements rest)
      apply List.map_congr_left
      intro element membership
      simpa only [Function.comp_apply] using
        inductionHypothesis element membership index

/-- Structural symbol transport commutes with abstraction of a free
metavariable. -/
theorem mapPattern_closeFVar (symbols : LanguageDefSymbolMap) (index : Nat)
    (name : String) (body : Pattern) :
    mapPattern symbols (closeFVar index name body) =
      closeFVar index name (mapPattern symbols body) := by
  induction body using Pattern.inductionOn generalizing index with
  | hbvar variableIndex => simp [closeFVar, mapPattern]
  | hfvar variableName =>
      by_cases equal : variableName = name <;>
        simp [closeFVar, mapPattern, equal]
  | happly constructor arguments inductionHypothesis =>
      simp only [closeFVar, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (Pattern.apply (symbols.constructor constructor))
      apply List.map_congr_left
      intro argument membership
      simpa only [Function.comp_apply] using
        inductionHypothesis argument membership index
  | hlambda binder body inductionHypothesis =>
      simp [closeFVar, mapPattern, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [closeFVar, mapPattern, inductionHypothesis]
  | hsubst body replacement bodyIH replacementIH =>
      simp [closeFVar, mapPattern, bodyIH, replacementIH]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [closeFVar, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (fun mappedElements =>
        Pattern.collection collectionType mappedElements rest)
      apply List.map_congr_left
      intro element membership
      simpa only [Function.comp_apply] using
        inductionHypothesis element membership index

/-- Structural symbol transport commutes with de Bruijn lifting. -/
theorem mapPattern_liftBVars (symbols : LanguageDefSymbolMap)
    (cutoff shift : Nat) (body : Pattern) :
    mapPattern symbols (liftBVars cutoff shift body) =
      liftBVars cutoff shift (mapPattern symbols body) := by
  induction body using Pattern.inductionOn generalizing cutoff with
  | hbvar variableIndex =>
      by_cases shifted : cutoff ≤ variableIndex <;>
        simp [liftBVars, mapPattern, shifted]
  | hfvar name => simp [liftBVars, mapPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [liftBVars, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (Pattern.apply (symbols.constructor constructor))
      apply List.map_congr_left
      intro argument membership
      simpa only [Function.comp_apply] using
        inductionHypothesis argument membership cutoff
  | hlambda binder body inductionHypothesis =>
      simp [liftBVars, mapPattern, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [liftBVars, mapPattern, inductionHypothesis]
  | hsubst body replacement bodyIH replacementIH =>
      simp [liftBVars, mapPattern, bodyIH, replacementIH]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [liftBVars, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (fun mappedElements =>
        Pattern.collection collectionType mappedElements rest)
      apply List.map_congr_left
      intro element membership
      simpa only [Function.comp_apply] using
        inductionHypothesis element membership cutoff

/-- Structural symbol transport commutes with binder-eliminating
substitution at every depth. -/
theorem mapPattern_instantiateBVarAt (symbols : LanguageDefSymbolMap)
    (depth : Nat) (replacement body : Pattern) :
    mapPattern symbols (instantiateBVarAt depth replacement body) =
      instantiateBVarAt depth (mapPattern symbols replacement)
        (mapPattern symbols body) := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar variableIndex =>
      simp only [instantiateBVarAt, mapPattern]
      split <;> try rfl
      split <;> try rfl
      exact mapPattern_liftBVars symbols 0 depth replacement
  | hfvar name => simp [instantiateBVarAt, mapPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [instantiateBVarAt, mapPattern, mapPatternList_eq_map,
        List.map_map]
      apply congrArg (Pattern.apply (symbols.constructor constructor))
      apply List.map_congr_left
      intro argument membership
      simpa only [Function.comp_apply] using
        inductionHypothesis argument membership depth
  | hlambda binder body inductionHypothesis =>
      simp [instantiateBVarAt, mapPattern, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [instantiateBVarAt, mapPattern, inductionHypothesis]
  | hsubst body nestedReplacement bodyIH replacementIH =>
      simp [instantiateBVarAt, mapPattern, bodyIH, replacementIH]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [instantiateBVarAt, mapPattern, mapPatternList_eq_map,
        List.map_map]
      apply congrArg (fun mappedElements =>
        Pattern.collection collectionType mappedElements rest)
      apply List.map_congr_left
      intro element membership
      simpa only [Function.comp_apply] using
        inductionHypothesis element membership depth

/-- Structural symbol transport commutes with elimination of the innermost
binder. -/
theorem mapPattern_instantiateBVar (symbols : LanguageDefSymbolMap)
    (replacement body : Pattern) :
    mapPattern symbols (instantiateBVar replacement body) =
      instantiateBVar (mapPattern symbols replacement)
        (mapPattern symbols body) :=
  mapPattern_instantiateBVarAt symbols 0 replacement body

/-! ## Faithfulness under injective constructor maps -/

/-- Applying a constructor map and then a pointwise left inverse recovers the
entire locally nameless pattern, including binder metadata and occurrences. -/
theorem mapPattern_leftInverse
    (forward backward : LanguageDefSymbolMap)
    (constructorLeftInverse :
      Function.LeftInverse backward.constructor forward.constructor)
    (pattern : Pattern) :
    mapPattern backward (mapPattern forward pattern) = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, List.map_map]
      rw [constructorLeftInverse constructor]
      congr 1
      calc
        List.map (mapPattern backward ∘ mapPattern forward) arguments =
            List.map _root_.id arguments := by
          apply List.map_congr_left
          intro argument membership
          simpa only [Function.comp_apply, id_eq] using
            inductionHypothesis argument membership
        _ = arguments := List.map_id arguments
  | hlambda binder body inductionHypothesis =>
      simp [mapPattern, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [mapPattern, inductionHypothesis]
  | hsubst body replacement bodyIH replacementIH =>
      simp [mapPattern, bodyIH, replacementIH]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, List.map_map]
      congr 1
      calc
        List.map (mapPattern backward ∘ mapPattern forward) elements =
            List.map _root_.id elements := by
          apply List.map_congr_left
          intro element membership
          simpa only [Function.comp_apply, id_eq] using
            inductionHypothesis element membership
        _ = elements := List.map_id elements

/-- An injective constructor action induces an injective action on complete
patterns. -/
theorem mapPattern_injective_of_constructor_injective
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor) :
    Function.Injective (mapPattern symbols) := by
  classical
  let inverse : LanguageDefSymbolMap :=
    { LanguageDefSymbolMap.id with
      constructor := Function.invFun symbols.constructor }
  have leftInverse :
      Function.LeftInverse inverse.constructor symbols.constructor := by
    exact Function.leftInverse_invFun constructorInjective
  intro first second equality
  have mappedEquality := congrArg (mapPattern inverse) equality
  simpa only [mapPattern_leftInverse symbols inverse leftInverse] using
    mappedEquality

/-! ## The distinct outer-judgment namespace -/

/-- A raw pattern has the outer shape required of a calculus judgment. -/
def JudgmentShaped : Pattern → Prop
  | .apply _ _ => True
  | _ => False

/-- A left inverse on both relevant namespaces recovers a complete judgment
pattern. -/
theorem mapJudgmentPattern_leftInverse
    (forward backward : CalculusLanguageSymbols)
    (constructorLeftInverse : Function.LeftInverse
      backward.constructor forward.constructor)
    (judgmentLeftInverse : Function.LeftInverse
      backward.judgment forward.judgment)
    (claim : Pattern) :
    mapJudgmentPattern backward (mapJudgmentPattern forward claim) = claim := by
  cases claim with
  | apply head arguments =>
      simp only [mapJudgmentPattern, List.map_map]
      rw [judgmentLeftInverse head]
      congr 1
      calc
        List.map
              (mapPattern backward.toLanguageDefSymbolMap ∘
                mapPattern forward.toLanguageDefSymbolMap) arguments =
            List.map _root_.id arguments := by
          apply List.map_congr_left
          intro argument _
          simpa only [Function.comp_apply, id_eq] using
            mapPattern_leftInverse forward.toLanguageDefSymbolMap
              backward.toLanguageDefSymbolMap constructorLeftInverse argument
        _ = arguments := List.map_id arguments
  | bvar index => rfl
  | fvar name => rfl
  | lambda binder body =>
      exact mapPattern_leftInverse forward.toLanguageDefSymbolMap
        backward.toLanguageDefSymbolMap constructorLeftInverse _
  | multiLambda arity binders body =>
      exact mapPattern_leftInverse forward.toLanguageDefSymbolMap
        backward.toLanguageDefSymbolMap constructorLeftInverse _
  | subst body replacement =>
      exact mapPattern_leftInverse forward.toLanguageDefSymbolMap
        backward.toLanguageDefSymbolMap constructorLeftInverse _
  | collection collectionType elements rest =>
      exact mapPattern_leftInverse forward.toLanguageDefSymbolMap
        backward.toLanguageDefSymbolMap constructorLeftInverse _

/-- Injective constructor and judgment-head actions induce an injective map
on complete judgment patterns. -/
theorem mapJudgmentPattern_injective
    (symbols : CalculusLanguageSymbols)
    (constructorInjective : Function.Injective symbols.constructor)
    (judgmentInjective : Function.Injective symbols.judgment) :
    Function.Injective (mapJudgmentPattern symbols) := by
  classical
  let inversePresentation : LanguageDefSymbolMap :=
    { LanguageDefSymbolMap.id with
      constructor := Function.invFun symbols.constructor }
  let inverse : CalculusLanguageSymbols :=
    { toLanguageDefSymbolMap := inversePresentation
      judgment := Function.invFun symbols.judgment
      rule := _root_.id }
  have constructorLeftInverse :
      Function.LeftInverse inverse.constructor symbols.constructor := by
    exact Function.leftInverse_invFun constructorInjective
  have judgmentLeftInverse :
      Function.LeftInverse inverse.judgment symbols.judgment := by
    exact Function.leftInverse_invFun judgmentInjective
  intro first second equality
  have mappedEquality := congrArg (mapJudgmentPattern inverse) equality
  simpa only [mapJudgmentPattern_leftInverse symbols inverse
    constructorLeftInverse judgmentLeftInverse] using mappedEquality

/-- Opening inside a judgment-shaped claim maps the replacement through the
object-language constructor namespace and retains the outer judgment
namespace. -/
theorem mapJudgmentPattern_openBVar
    (symbols : CalculusLanguageSymbols) (index : Nat)
    (replacement : Pattern) (head : String) (arguments : List Pattern) :
    mapJudgmentPattern symbols
        (openBVar index replacement (.apply head arguments)) =
      openBVar index (mapPattern symbols.toLanguageDefSymbolMap replacement)
        (mapJudgmentPattern symbols (.apply head arguments)) := by
  simp only [openBVar, mapJudgmentPattern, List.map_map]
  congr 1
  apply List.map_congr_left
  intro argument _
  exact mapPattern_openBVar symbols.toLanguageDefSymbolMap index replacement
    argument

/-- Binder-eliminating substitution inside a judgment-shaped claim has the
same mixed-namespace naturality law. -/
theorem mapJudgmentPattern_instantiateBVarAt
    (symbols : CalculusLanguageSymbols) (depth : Nat)
    (replacement : Pattern) (head : String) (arguments : List Pattern) :
    mapJudgmentPattern symbols
        (instantiateBVarAt depth replacement (.apply head arguments)) =
      instantiateBVarAt depth
        (mapPattern symbols.toLanguageDefSymbolMap replacement)
        (mapJudgmentPattern symbols (.apply head arguments)) := by
  simp only [instantiateBVarAt, mapJudgmentPattern, List.map_map]
  congr 1
  apply List.map_congr_left
  intro argument _
  exact mapPattern_instantiateBVarAt symbols.toLanguageDefSymbolMap depth
    replacement argument

/-! ## Discriminating examples -/

namespace StructuralPatternBindingNaturalityCanary

def distinctNamespaces : CalculusLanguageSymbols where
  toLanguageDefSymbolMap :=
    { LanguageDefSymbolMap.id with
      constructor := fun head => "constructor:" ++ head }
  judgment := fun head => "judgment:" ++ head
  rule := _root_.id

/-- Positive example: a nontrivial structural translation carries a term
under a binder and commutes with opening. -/
theorem constructor_opening_commutes :
    mapPattern distinctNamespaces.toLanguageDefSymbolMap
        (openBVar 0 (.apply "datum" [])
          (.lambda none (.apply "body" [.bvar 1]))) =
      openBVar 0
        (mapPattern distinctNamespaces.toLanguageDefSymbolMap
          (.apply "datum" []))
        (mapPattern distinctNamespaces.toLanguageDefSymbolMap
          (.lambda none (.apply "body" [.bvar 1]))) :=
  mapPattern_openBVar _ _ _ _

/-- Positive example: opening an argument maps its constructor, while the
outer judgment head uses the independent judgment namespace. -/
theorem judgment_opening_uses_both_namespaces :
    mapJudgmentPattern distinctNamespaces
        (openBVar 0 (.apply "datum" [])
          (.apply "holds" [.bvar 0])) =
      .apply "judgment:holds" [.apply "constructor:datum" []] := by
  simp [distinctNamespaces, mapJudgmentPattern, openBVar, mapPattern]

/-- Negative example: without the judgment-shape boundary, opening can change
which namespace owns the newly exposed outer application.  Thus the tempting
unrestricted interchange equation is false. -/
theorem unrestricted_judgment_opening_fails :
    mapJudgmentPattern distinctNamespaces
        (openBVar 0 (.apply "datum" []) (.bvar 0)) ≠
      openBVar 0
        (mapPattern distinctNamespaces.toLanguageDefSymbolMap
          (.apply "datum" []))
        (mapJudgmentPattern distinctNamespaces (.bvar 0)) := by
  simp [distinctNamespaces, mapJudgmentPattern, openBVar, mapPattern]

/-- Negative example: a collapsing constructor action really does collapse
distinct patterns and therefore cannot support exact checker replay. -/
theorem constant_constructor_map_not_injective :
    ¬ Function.Injective
      (mapPattern
        { LanguageDefSymbolMap.id with constructor := fun _ => "constant" }) := by
  intro injective
  have collision :
      mapPattern
          { LanguageDefSymbolMap.id with constructor := fun _ => "constant" }
          (.apply "left" []) =
        mapPattern
          { LanguageDefSymbolMap.id with constructor := fun _ => "constant" }
          (.apply "right" []) := rfl
  have equal := injective collision
  have different :
      (.apply "left" [] : Pattern) ≠ .apply "right" [] := by
    intro impossible
    injection impossible with headEquality
    simp at headEquality
  exact different equal

end StructuralPatternBindingNaturalityCanary

#print axioms mapPattern_openBVar
#print axioms mapPattern_closeFVar
#print axioms mapPattern_liftBVars
#print axioms mapPattern_instantiateBVarAt
#print axioms mapPattern_leftInverse
#print axioms mapPattern_injective_of_constructor_injective
#print axioms mapJudgmentPattern_injective
#print axioms mapJudgmentPattern_openBVar
#print axioms mapJudgmentPattern_instantiateBVarAt
#print axioms StructuralPatternBindingNaturalityCanary.unrestricted_judgment_opening_fails

end Mettapedia.GSLT.LanguageDef
