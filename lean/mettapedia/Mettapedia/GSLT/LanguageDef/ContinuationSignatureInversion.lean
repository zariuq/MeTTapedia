import Mettapedia.GSLT.LanguageDef.ContinuationRetyping
import Mettapedia.GSLT.LanguageDef.TypingInversion

/-!
# Reading a typing in the continuation signature back

The continuation signature of a cut has a base copy of every constructor and
a wrapped copy of every constructor other than the two introductions, and it
types exactly two schema variables at the wrapped sort: the two continuation
variables of the cut.  This module inverts typings in that signature.

* A schema variable typed at the wrapped sort is one of the two continuation
  variables.
* A constructor whose result is the wrapped sort is the wrapped copy of a
  constructor of the continuation closure whose result is the interacting
  sort.
* An application of a wrapped copy is typed by that copy's parameters.

Together they bound what a wrappable contractum can use: every variable it
needs at the wrapped sort must be one of two.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A bare collection typed at a base sort is typed by a declared collection
constructor of that sort, whose element type types its elements. -/
theorem HasType.collection_base_inv {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {collectionType : CollType} {elements : List Pattern}
    {rest : Option String} {sort : String}
    (typed : HasType language free bound (.collection collectionType elements rest)
      (.base sort)) :
    ∃ rule, rule ∈ language.terms ∧ rule.category = sort ∧
      ∃ parameterName elementType,
        rule.params = [.simple parameterName (.collection collectionType elementType)] ∧
          ElementsHaveType language free bound elements elementType := by
  generalize source : Pattern.collection collectionType elements rest = pattern at typed
  generalize target : TypeExpr.base sort = type at typed
  cases typed with
  | collectionConstructor membership parameters elementsTyped =>
      simp only [Pattern.collection.injEq] at source
      obtain ⟨rfl, rfl, rfl⟩ := source
      simp only [TypeExpr.base.injEq] at target
      exact ⟨_, membership, target.symm, _, _, parameters, elementsTyped⟩
  | collection _ => cases target
  | bvar _ => cases source
  | fvar _ => cases source
  | constructor _ _ _ => cases source
  | lambda _ => cases source
  | multiLambda _ => cases source
  | subst _ _ => cases source

/-- A substitution node is typed by typing its body under one more bound
variable and its replacement at that variable's type. -/
theorem HasType.subst_inv {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {body replacement : Pattern} {type : TypeExpr}
    (typed : HasType language free bound (.subst body replacement) type) :
    ∃ domain, HasType language free (domain :: bound) body type ∧
      HasType language free bound replacement domain := by
  generalize source : Pattern.subst body replacement = pattern at typed
  cases typed with
  | subst bodyTyped replacementTyped =>
      simp only [Pattern.subst.injEq] at source
      obtain ⟨rfl, rfl⟩ := source
      exact ⟨_, bodyTyped, replacementTyped⟩
  | bvar _ => cases source
  | fvar _ => cases source
  | constructor _ _ _ => cases source
  | lambda _ => cases source
  | multiLambda _ => cases source
  | collection _ => cases source
  | collectionConstructor _ _ _ => cases source

/-- A schema variable is typed by the free context. -/
theorem HasType.fvar_inv {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {name : String} {type : TypeExpr}
    (typed : HasType language free bound (.fvar name) type) :
    free name = some type := by
  generalize source : Pattern.fvar name = pattern at typed
  cases typed with
  | fvar lookup =>
      simp only [Pattern.fvar.injEq] at source
      subst source
      exact lookup
  | bvar _ => cases source
  | constructor _ _ _ => cases source
  | lambda _ => cases source
  | multiLambda _ => cases source
  | subst _ _ => cases source
  | collection _ => cases source
  | collectionConstructor _ _ _ => cases source

end Mettapedia.GSLT.LanguageDef.WellSorted

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open StructuralMorphism
open WellSorted

/-- The base retyping of a type is never the wrapped sort. -/
theorem costBaseTypeExpr_ne_wrapped (type : TypeExpr) :
    costBaseTypeExpr type ≠ .base costWrappedSortName := by
  cases type with
  | base sort =>
      intro same
      simp only [costBaseTypeExpr, TypeExpr.base.injEq] at same
      exact costBaseSortName_ne_wrapped sort same
  | arrow _ _ => simp [costBaseTypeExpr]
  | multiBinder _ => simp [costBaseTypeExpr]
  | collection _ _ => simp [costBaseTypeExpr]

namespace ContinuationRetypingPlan

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- **Only the two continuation variables are wrapped.**  A schema variable
typed at the wrapped sort by the continuation signature is the program
continuation variable or the environment continuation variable. -/
theorem wrapped_variable (plan : ContinuationRetypingPlan cut) {name : String}
    (typed : plan.generatedFreeContext name = some (.base costWrappedSortName)) :
    name = cut.program.continuationVariable.name ∨
      name = cut.environment.continuationVariable.name := by
  by_contra neither
  rw [generatedFreeContext_apply] at typed
  cases lookup :
      lookupTypeContext theory.presentation.interactionRewrite.1.typeContext name with
  | none =>
      rw [lookup] at typed
      cases typed
  | some type =>
      rw [lookup] at typed
      simp only [Option.map_some, if_neg neither, Option.some.injEq] at typed
      exact costBaseTypeExpr_ne_wrapped type typed

/-- **What returns the wrapped sort.**  A constructor of the continuation
signature whose result is the wrapped sort is the wrapped copy of a
constructor of the continuation closure whose result is the interacting
sort. -/
theorem wrapped_category_inv (plan : ContinuationRetypingPlan cut) {rule : GrammarRule}
    (membership : rule ∈ plan.generatedLanguage.terms)
    (category : rule.category = costWrappedSortName) :
    ∃ constructor ∈ plan.wrappedConstructors,
      rule = costWrappedConstructor (theory := theory) constructor.1 ∧
        constructor.1.category = theory.presentation.interactingSort.1.name := by
  have split : rule ∈
      theory.presentation.presentation.language.terms.map (costBaseConstructor cut) ∨
        rule ∈ plan.wrappedConstructors.map
          (fun constructor => costWrappedConstructor (theory := theory) constructor.1) :=
    List.mem_append.mp membership
  rcases split with baseCopy | wrappedCopy
  · obtain ⟨source, -, rfl⟩ := List.mem_map.mp baseCopy
    exact absurd category (costBaseSortName_ne_wrapped source.category)
  · obtain ⟨constructor, wrapped, rfl⟩ := List.mem_map.mp wrappedCopy
    refine ⟨constructor, wrapped, rfl, ?_⟩
    by_contra other
    have result : (costWrappedConstructor (theory := theory) constructor.1).category =
        costBaseSortName constructor.1.category := by
      simp [costWrappedConstructor, other]
    rw [result] at category
    exact costBaseSortName_ne_wrapped _ category

/-- **An application of a wrapped copy is typed by that copy.**  Its type is
the copy's result sort and its arguments are typed by the copy's
parameters. -/
theorem hasType_wrapped_apply_inv (plan : ContinuationRetypingPlan cut)
    (constructor : DeclaredConstructor theory.presentation.presentation)
    (wrapped : constructor ∈ plan.wrappedConstructors)
    {free : FreeTypeContext} {bound : List TypeExpr} {arguments : List Pattern}
    {type : TypeExpr}
    (typed : HasType plan.generatedLanguage free bound
      (.apply (costWrappedConstructorName constructor.1.label) arguments) type) :
    type = .base (costWrappedConstructor (theory := theory) constructor.1).category ∧
      ArgumentsHaveTypes plan.generatedLanguage free bound arguments
        (costWrappedConstructor (theory := theory) constructor.1).params := by
  obtain ⟨rule, membership, label, typeEq, -, argumentsTyped⟩ := typed.apply_inv
  have same : rule = costWrappedConstructor (theory := theory) constructor.1 :=
    List.inj_on_of_nodup_map (generatedConstructorLabels_nodup plan) membership
      (plan.costWrappedConstructor_mem_generated constructor wrapped) label
  subst same
  exact ⟨typeEq, argumentsTyped⟩

end ContinuationRetypingPlan

end Mettapedia.GSLT.LanguageDef
