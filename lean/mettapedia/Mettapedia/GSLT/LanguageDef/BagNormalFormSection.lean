import Mettapedia.GSLT.LanguageDef.BagNormalFormTyping
import Mettapedia.GSLT.LanguageDef.CanonicalSection
import Mettapedia.GSLT.LanguageDef.Interaction.Freeness

/-!
# The canonical section of a bag theory

The normal form of `BagNormalForm` is a section of the static equivalence on
the closed interacting fibre of any iGSLT whose presentation is a bag theory.

Completeness is the raw statement already proved: equivalent patterns have
one normal form.  This module supplies the other half.  A sorted pattern is
joined to its normal form by a chain of the presentation's own bag laws, each
applied in a context (`path_normalForm`): the components of every bag are
normalized first, then nested bags are spliced, units dropped, the components
sorted, and an empty or singleton wrapper removed.  The typing of each bag on
the way justifies the law applied to it, and every pattern on the chain is
again sorted, so the chain lies inside the fibre (`presented_of_path`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {language : LanguageDef} {bag : GrammarRule} {unit : Option String}

/-! ## Chains of steps -/

/-- A chain of steps of the static equivalence. -/
abbrev Path (base : BasePremiseEvaluator) (language : LanguageDef) :
    Pattern → Pattern → Prop :=
  Relation.ReflTransGen (EquationContextStep base language)

/-- A chain can be run inside any context. -/
theorem path_fill {base : BasePremiseEvaluator} (context : OneHoleContext)
    {source target : Pattern} (path : Path base language source target) :
    Path base language (context.fill source) (context.fill target) := by
  induction path with
  | refl => exact .refl
  | tail _ step recurse => exact recurse.tail (equationContextStep_fill context step)

/-- A chain from an admissible pattern ends at an admissible pattern. -/
theorem path_admissible (laws : BagTheory language bag unit)
    {base : BasePremiseEvaluator} {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern}
    (path : Path base language source target)
    (admissible : Admissible language free bound type source)
    (collectionless : collectionFree type = true) :
    Admissible language free bound type target := by
  induction path with
  | refl => exact admissible
  | tail _ step recurse => exact step_admissible laws step recurse collectionless

/-- Chains on the members of a list, run one after another inside a node
built from the list. -/
theorem path_map {base : BasePremiseEvaluator} (node : List Pattern → Pattern)
    (frame : List Pattern → List Pattern → OneHoleContext)
    (fills : ∀ before pattern after,
      (frame before after).fill pattern = node (before ++ pattern :: after))
    (image : Pattern → Pattern) :
    ∀ (done todo : List Pattern),
      (∀ pattern ∈ todo, Path base language pattern (image pattern)) →
        Path base language (node (done ++ todo)) (node (done ++ todo.map image))
  | _, [], _ => by simpa using Relation.ReflTransGen.refl
  | done, pattern :: rest, paths => by
      have first : Path base language (node (done ++ pattern :: rest))
          (node (done ++ image pattern :: rest)) := by
        have lifted := path_fill (frame done rest) (paths pattern (by simp))
        simpa only [fills] using lifted
      have later := path_map node frame fills image (done ++ [image pattern]) rest
        (fun other membership => paths other (by simp [membership]))
      simp only [List.append_assoc, List.cons_append, List.nil_append] at later
      simpa using first.trans later

/-- One bag law at the root is a chain of length one. -/
theorem path_of_derived {base : BasePremiseEvaluator} {source target : Pattern}
    (derived : DerivedInstance language source target) :
    Path base language source target :=
  Relation.ReflTransGen.single (EquationContextStep.inContext .hole (Or.inr derived))

/-! ## The chain to the normal form -/

/-- An admissible bag is sorted at the bag's sort. -/
theorem sortedAt_of_admissible (laws : BagTheory language bag unit)
    {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr}
    {elements : List Pattern}
    (admissible : Admissible language free bound type
      (.collection .hashBag elements none))
    (collectionless : collectionFree type = true) :
    SortedAt language (.collection .hashBag elements none) bag.category := by
  obtain ⟨-, rfl, -⟩ := bag_typing laws admissible.typed collectionless
  exact ⟨free, bound, admissible.typed⟩

section Flattening

variable {unitName : String}

/-- Splice every nested bag of an admissible bag. -/
theorem path_splice (laws : BagTheory language bag (some unitName))
    {base : BasePremiseEvaluator} {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} (collectionless : collectionFree type = true) :
    ∀ (todo done : List Pattern),
      Admissible language free bound type (.collection .hashBag (done ++ todo) none) →
        Path base language (.collection .hashBag (done ++ todo) none)
          (.collection .hashBag (done ++ todo.flatMap splice) none)
  | [], _, _ => by simpa using Relation.ReflTransGen.refl
  | pattern :: rest, done, admissible => by
      by_cases nested : IsBagNode pattern
      · obtain ⟨inner, rfl⟩ := nested
        have law : DerivedInstance language
            (.collection .hashBag (done ++ .collection .hashBag inner none :: rest) none)
            (.collection .hashBag (done ++ inner ++ rest) none) :=
          DerivedInstance.flatten laws.bagAlgebraRule rfl
            (sortedAt_of_admissible laws admissible collectionless)
        have first : Path base language _ _ := path_of_derived (base := base) law
        have next := path_admissible laws first admissible collectionless
        have later := path_splice (base := base) laws collectionless rest (done ++ inner) next
        simpa [List.append_assoc] using first.trans later
      · have regrouped :
            done ++ pattern :: rest = (done ++ [pattern]) ++ rest := by simp
        have later := path_splice (base := base) laws collectionless rest (done ++ [pattern])
          (regrouped ▸ admissible)
        simpa [splice_of_not_bag nested, List.append_assoc] using later

/-- Drop every unit of an admissible bag. -/
theorem path_dropUnits (laws : BagTheory language bag (some unitName))
    {base : BasePremiseEvaluator} {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} (collectionless : collectionFree type = true) :
    ∀ (todo done : List Pattern),
      Admissible language free bound type (.collection .hashBag (done ++ todo) none) →
        Path base language (.collection .hashBag (done ++ todo) none)
          (.collection .hashBag
            (done ++ todo.filter fun pattern => decide (pattern ≠ .apply unitName [])) none)
  | [], _, _ => by simpa using Relation.ReflTransGen.refl
  | pattern :: rest, done, admissible => by
      by_cases isUnit : pattern = .apply unitName []
      · subst isUnit
        have law : DerivedInstance language
            (.collection .hashBag (done ++ .apply unitName [] :: rest) none)
            (.collection .hashBag (done ++ rest) none) :=
          DerivedInstance.unitElim laws.bagAlgebraRule rfl
            (sortedAt_of_admissible laws admissible collectionless)
        have first : Path base language _ _ := path_of_derived (base := base) law
        have next := path_admissible laws first admissible collectionless
        have later := path_dropUnits (base := base) laws collectionless rest done next
        simpa using first.trans later
      · have regrouped :
            done ++ pattern :: rest = (done ++ [pattern]) ++ rest := by simp
        have later := path_dropUnits (base := base) laws collectionless rest (done ++ [pattern])
          (regrouped ▸ admissible)
        simpa [isUnit, List.append_assoc] using later

/-- Remove an empty or singleton wrapper from an admissible bag. -/
theorem path_collapse (laws : BagTheory language bag (some unitName))
    {base : BasePremiseEvaluator} {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} (collectionless : collectionFree type = true)
    {components : List Pattern}
    (admissible : Admissible language free bound type
      (.collection .hashBag components none)) :
    Path base language (.collection .hashBag components none)
      (collapse unitName components) := by
  have sorted := sortedAt_of_admissible laws admissible collectionless
  match components, sorted with
  | [], sorted =>
      exact path_of_derived (DerivedInstance.emptyUnit laws.bagAlgebraRule rfl sorted)
  | [component], sorted =>
      exact path_of_derived (DerivedInstance.singleton laws.bagAlgebraRule rfl sorted)
  | first :: second :: rest, _ => exact .refl

end Flattening

/-- **An admissible bag of normal components reaches its normal form.** -/
theorem path_normalizeBag (laws : BagTheory language bag unit)
    {base : BasePremiseEvaluator} {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} (collectionless : collectionFree type = true)
    {components : List Pattern}
    (admissible : Admissible language free bound type
      (.collection .hashBag components none)) :
    Path base language (.collection .hashBag components none)
      (normalizeBag unit components) := by
  have sort : ∀ {elements : List Pattern},
      Admissible language free bound type (.collection .hashBag elements none) →
        Path base language (.collection .hashBag elements none)
          (.collection .hashBag (sortPatterns elements) none) := by
    intro elements good
    exact path_of_derived (DerivedInstance.bagPerm laws.bagCarrier
      (sortedAt_of_admissible laws good collectionless) (sortPatterns_perm elements).symm)
  cases unit with
  | none => exact sort admissible
  | some unitName =>
      have spliced := path_splice (base := base) laws collectionless components []
        (by simpa using admissible)
      simp only [List.nil_append] at spliced
      have afterSplice := path_admissible laws spliced admissible collectionless
      have dropped := path_dropUnits (base := base) laws collectionless
        (components.flatMap splice) [] (by simpa using afterSplice)
      simp only [List.nil_append] at dropped
      have afterDrop := path_admissible laws dropped afterSplice collectionless
      have sorted := sort afterDrop
      have afterSort := path_admissible laws sorted afterDrop collectionless
      have collapsed := path_collapse (base := base) laws collectionless afterSort
      exact ((spliced.trans dropped).trans sorted).trans collapsed

/-- **Soundness.**  An admissible pattern at a collection-free type reaches
its normal form by a chain of steps of the static equivalence. -/
theorem path_normalForm (laws : BagTheory language bag unit)
    (base : BasePremiseEvaluator) (pattern : Pattern) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr},
      Admissible language free bound type pattern → collectionFree type = true →
        Path base language pattern (normalForm unit pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro free bound type _ _
      simpa [normalForm] using Relation.ReflTransGen.refl
  | hfvar name =>
      intro free bound type _ _
      simpa [normalForm] using Relation.ReflTransGen.refl
  | happly label arguments recurse =>
      intro free bound type admissible collectionless
      rw [normalForm_apply]
      obtain ⟨rule, membership, -, notBare, -, argumentsTyped⟩ :=
        hasType_apply_inversion admissible.typed
      have ruleNotBag : rule ≠ bag := by
        rintro rfl
        obtain ⟨parameterName, shape⟩ := laws.bagShape
        exact notBare ⟨parameterName, .hashBag, .base _, shape⟩
      have paths : ∀ argument ∈ arguments,
          Path base language argument (normalForm unit argument) := by
        intro argument argumentMember
        obtain ⟨before, after, rfl⟩ := List.append_of_mem argumentMember
        obtain ⟨beforeParameters, parameter, afterParameters, expected, parametersEq, -, -,
            -, parameterType, argumentTyped, -⟩ :=
          ArgumentsHaveTypes.append_cons_split argumentsTyped
        have expectedFree : collectionFree expected = true :=
          collectionFree_parameterType
            (laws.otherParameters rule membership ruleNotBag parameter
              (by rw [parametersEq]; simp))
            parameterType
        have canonical := admissible.canonical
        have object := admissible.object
        simp only [Pattern.hasCanonicalBinderMetadata,
          hasCanonicalBinderMetadataList_iff] at canonical
        simp only [isObjectPattern, isObjectPatternList_iff] at object
        exact recurse argument argumentMember
          ⟨argumentTyped, canonical argument argumentMember, object argument argumentMember⟩
          expectedFree
      have chain := path_map (base := base) (language := language) (.apply label)
        (fun before after => .apply label before .hole after) (fun _ _ _ => rfl)
        (normalForm unit) [] arguments paths
      simpa using chain
  | hlambda binder body recurse =>
      intro free bound type admissible collectionless
      have typed := admissible.typed
      cases typed with
      | @lambda _ _ _ domain codomain bodyTyped =>
          simp only [collectionFree, Bool.and_eq_true] at collectionless
          have canonical := admissible.canonical
          have object := admissible.object
          simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
          simp only [isObjectPattern] at object
          have inner := recurse ⟨bodyTyped, canonical.2, object⟩ collectionless.2
          simpa [normalForm, OneHoleContext.fill] using
            path_fill (.lambda binder .hole) inner
  | hmultiLambda arity binders body recurse =>
      intro free bound type admissible collectionless
      have typed := admissible.typed
      cases typed with
      | @multiLambda _ _ _ _ domain codomain bodyTyped =>
          simp only [collectionFree, Bool.and_eq_true] at collectionless
          have canonical := admissible.canonical
          have object := admissible.object
          simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
          simp only [isObjectPattern] at object
          have inner := recurse ⟨bodyTyped, canonical.2, object⟩ collectionless.2
          simpa [normalForm, OneHoleContext.fill] using
            path_fill (.multiLambda arity binders .hole) inner
  | hsubst body replacement _ _ =>
      intro free bound type admissible _
      have object := admissible.object
      simp [isObjectPattern] at object
  | hcollection kind elements rest recurse =>
      intro free bound type admissible collectionless
      obtain ⟨rfl, rfl, elementsTyped⟩ := bag_typing laws admissible.typed collectionless
      have object := admissible.object
      simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
      obtain ⟨rfl, objectElements⟩ := object
      have canonical := admissible.canonical
      simp only [Pattern.hasCanonicalBinderMetadata,
        hasCanonicalBinderMetadataList_iff] at canonical
      rw [normalForm_bag]
      have paths : ∀ element ∈ elements,
          Path base language element (normalForm unit element) := by
        intro element elementMember
        exact recurse element elementMember
          ⟨elementsHaveType_iff.mp elementsTyped element elementMember,
            canonical element elementMember,
            isObjectPatternList_iff.mp objectElements element elementMember⟩
          rfl
      have inside := path_map (base := base) (language := language)
        (fun components => .collection .hashBag components none)
        (fun before after => .collection .hashBag before .hole after none)
        (fun _ _ _ => rfl) (normalForm unit) [] elements paths
      simp only [List.nil_append] at inside
      have afterInside := path_admissible laws inside admissible rfl
      exact inside.trans (path_normalizeBag laws rfl afterInside)

/-! ## The section -/

/-- A closed term of a sort is admissible at that sort in the empty
contexts. -/
theorem admissible_of_closed {sort : LangSort language} {pattern : Pattern}
    (closed : ClosedTermWellSorted language sort pattern) :
    Admissible language FreeTypeContext.empty [] (.base sort.1) pattern :=
  ⟨closed.1, closed.2.2.1, closed.2.2.2.1⟩

/-- A pattern admissible at a sort in the empty contexts is a closed term of
that sort: scope and groundness follow from the sorting. -/
theorem closed_of_admissible {sort : LangSort language} {pattern : Pattern}
    (admissible : Admissible language FreeTypeContext.empty [] (.base sort.1) pattern) :
    ClosedTermWellSorted language sort pattern := by
  have wellScoped : pattern.isWellScopedAt 0 = true := by
    simpa using admissible.typed.isWellScopedAt
  exact ⟨admissible.typed,
    ground_of_closed_sorting admissible.typed admissible.object wellScoped,
    admissible.canonical, admissible.object, wellScoped⟩

/-- A chain from a closed term of the interacting fibre stays in the fibre,
and relates its two ends in the fibre's static equivalence. -/
theorem presented_of_path {presentation : InteractivePresentation}
    (laws : BagTheory presentation.presentation.language bag unit)
    {source target : Pattern}
    (path : Path defaultBasePremises presentation.presentation.language source target)
    (sourceClosed : ClosedTermWellSorted presentation.presentation.language
      presentation.interactingLangSort source) :
    ∃ targetClosed : ClosedTermWellSorted presentation.presentation.language
        presentation.interactingLangSort target,
      (presentedEquationSetoid defaultBasePremises presentation).r
        ⟨source, sourceClosed⟩ ⟨target, targetClosed⟩ := by
  induction path with
  | refl => exact ⟨sourceClosed, Relation.EqvGen.refl _⟩
  | @tail middle target _ step recurse =>
      obtain ⟨middleClosed, related⟩ := recurse
      have targetClosed := closed_of_admissible
        (step_admissible laws step (admissible_of_closed middleClosed) rfl)
      exact ⟨targetClosed, Relation.EqvGen.trans _ _ _ related
        (Relation.EqvGen.rel
          (⟨middle, middleClosed⟩ : presentation.Term) ⟨target, targetClosed⟩ step)⟩

/-- **The canonical section of a bag theory.**  On the closed interacting
fibre of an iGSLT whose presentation is a bag theory, the normal form is a
computable section of the static equivalence: every term is equivalent to its
normal form, and equivalent terms have the same normal form. -/
def bagCanonicalSection (theory : IGSLT) {bag : GrammarRule} {unit : Option String}
    (laws : BagTheory theory.presentation.presentation.language bag unit) :
    ComputableCanonicalSection theory where
  normalize term :=
    ⟨normalForm unit term.1,
      (presented_of_path laws
        (path_normalForm laws defaultBasePremises term.1 (admissible_of_closed term.2) rfl)
        term.2).fst⟩
  equivalent term :=
    Relation.EqvGen.symm _ _
      (presented_of_path laws
        (path_normalForm laws defaultBasePremises term.1 (admissible_of_closed term.2) rfl)
        term.2).snd
  complete := by
    intro left right equivalent
    apply Subtype.ext
    exact normalForm_eq_of_equationEquiv laws
      (equationEquiv_of_presentedEquationSetoid equivalent)

/-- The section normalizes the underlying pattern by the raw normalizer. -/
@[simp] theorem bagCanonicalSection_normalize_val (theory : IGSLT) {bag : GrammarRule}
    {unit : Option String}
    (laws : BagTheory theory.presentation.presentation.language bag unit)
    (term : theory.toGSLT.Term) :
    ((bagCanonicalSection theory laws).normalize term).1 = normalForm unit term.1 :=
  rfl

end Mettapedia.GSLT.LanguageDef.BagNormalForm
