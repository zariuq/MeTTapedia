import Mettapedia.GSLT.LanguageDef.BagNormalForm
import Mettapedia.GSLT.LanguageDef.BagNormalFormTyping
import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# A parallel bag beside named multisets

A calculus with restriction composes its processes in one bare bag with a unit. It may also have **named multiset
operators**: constructors whose one parameter is a bag of terms of another sort, kept as a named application, with
no algebra. CCS's sum is one: a process `Σ {α₁.P₁, …, αₙ.Pₙ}` whose guards are reordered and never flattened into
the parallel bag.

`ParallelBag` asks for the parallel bag as `BagPresentation` does, except that the other constructors may be named
multiset operators of other sorts, listed by label. With no named multisets it is a bare bag presentation
(`ParallelBag.ofBare`, `ParallelBag.toBare`).

- A bare collection typed at a sort is the parallel bag, at its sort (`bag_typing`).
- The only collection algebra is the parallel bag's (`algebra_rule`).
- A collection typed through a constructor's parameter is the parallel bag or a named multiset
  (`collectionTyped`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.BagNormalForm (BagPresentation BareBagPresentation collectionFree)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (AlgebraRule DerivedInstance)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff)

/-- **A named multiset operator** of a language: a constructor kept as a named application, whose one parameter is
a bag of terms of a sort other than `proc`, with no algebra. -/
structure NamedMultiset (rule : GrammarRule) (proc : String) : Prop where
  wrapped : rule.collectionRepresentation = .wrapped
  noAlgebra : rule.algebra? = none
  shape : ∃ parameterName sort, rule.params = [.simple parameterName (.collection .hashBag (.base sort))] ∧
    sort ≠ proc

/-- **A parallel bag beside named multisets**: the bare bag over the process sort with its unit, and every other
constructor either free of collections or a named multiset operator whose label is listed. -/
structure ParallelBag (language : LanguageDef) (bag : GrammarRule) (unit : String) (multisets : List String) :
    Prop where
  bagAuthored : bag ∈ language.terms
  bagShape : ∃ parameterName, bag.params = [.simple parameterName (.collection .hashBag (.base bag.category))]
  bagAlgebra : bag.algebra? = some { flatten := true, unit := some unit }
  representedBare : bag.collectionRepresentation = .bare
  unitAuthored : ∃ unitRule ∈ language.terms,
    unitRule.label = unit ∧ unitRule.category = bag.category ∧ unitRule.params = []
  otherParameters : ∀ rule ∈ language.terms, rule ≠ bag →
    (∀ parameter ∈ rule.params, collectionFree (TermParam.typeExpr parameter) = true) ∨
      (rule.label ∈ multisets ∧ NamedMultiset rule bag.category)

namespace ParallelBag

variable {language : LanguageDef} {bag : GrammarRule} {unit : String} {multisets : List String}

/-- A bare bag presentation is a parallel bag with no named multisets. -/
theorem ofBare (laws : BareBagPresentation language bag (some unit)) : ParallelBag language bag unit [] where
  bagAuthored := laws.bagAuthored
  bagShape := laws.bagShape
  bagAlgebra := laws.bagAlgebra
  representedBare := laws.representedBare
  unitAuthored := laws.unitAuthored unit rfl
  otherParameters := fun rule member different => .inl (laws.otherParameters rule member different)

/-- A parallel bag with no named multisets is a bare bag presentation. -/
theorem toBare (laws : ParallelBag language bag unit []) : BareBagPresentation language bag (some unit) where
  bagAuthored := laws.bagAuthored
  bagShape := laws.bagShape
  bagAlgebra := laws.bagAlgebra
  otherParameters := by
    intro rule member different
    rcases laws.otherParameters rule member different with free | ⟨listed, -⟩
    · exact free
    · simp at listed
  unitAuthored := by
    intro name same
    cases Option.some.inj same
    exact laws.unitAuthored
  representedBare := laws.representedBare

/-- **A bare collection parameter is the parallel bag's**: a constructor whose bare parameters are one collection is
the bag, over its own sort. -/
theorem eq_bag_of_bareShape (laws : ParallelBag language bag unit multisets) {rule : GrammarRule}
    (authored : rule ∈ language.terms) {parameterName : String} {kind : CollType} {elementType : TypeExpr}
    (shape : rule.bareParams = [.simple parameterName (.collection kind elementType)]) :
    rule = bag ∧ kind = .hashBag ∧ elementType = .base bag.category := by
  obtain ⟨bare, params⟩ := (GrammarRule.bareParams_cons_iff _ _ _).mp shape
  have same : rule = bag := by
    by_contra different
    rcases laws.otherParameters rule authored different with free | ⟨-, named⟩
    · have collectionless := free (.simple parameterName (.collection kind elementType)) (by rw [params]; simp)
      simp [TermParam.typeExpr, collectionFree] at collectionless
    · rw [named.wrapped] at bare
      cases bare
  subst same
  obtain ⟨bagName, bagShape⟩ := laws.bagShape
  rw [bagShape] at params
  simp only [List.cons.injEq, TermParam.simple.injEq, TypeExpr.collection.injEq, and_true] at params
  exact ⟨rfl, params.2.1.symm, params.2.2.symm⟩

/-- **A bare collection sorted at a collection-free type is the parallel bag**: its type is the bag's sort and its
components have that sort. -/
theorem bag_typing (laws : ParallelBag language bag unit multisets) {free : FreeTypeContext}
    {bound : List TypeExpr} {kind : CollType} {elements : List Pattern} {rest : Option String} {type : TypeExpr}
    (typed : HasType language free bound (.collection kind elements rest) type)
    (collectionless : collectionFree type = true) :
    kind = .hashBag ∧ type = .base bag.category ∧
      ElementsHaveType language free bound elements (.base bag.category) := by
  rcases hasType_collection_inversion typed with
    ⟨elementType, typeEq, -⟩ | ⟨rule, parameterName, elementType, membership, shape, typeEq, elementsTyped⟩
  · subst typeEq
    simp [collectionFree] at collectionless
  · obtain ⟨rfl, kindEq, elementEq⟩ := laws.eq_bag_of_bareShape membership shape
    subst elementEq
    exact ⟨kindEq, typeEq, elementsTyped⟩

/-- A list of components of the bag's sort is a bag of the bag's sort. -/
theorem bag_hasType (laws : ParallelBag language bag unit multisets) {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern} {rest : Option String}
    (elementsTyped : ElementsHaveType language free bound elements (.base bag.category)) :
    HasType language free bound (.collection .hashBag elements rest) (.base bag.category) := by
  obtain ⟨parameterName, shape⟩ := laws.bagShape
  have bareShape : bag.bareParams = [.simple parameterName (.collection .hashBag (.base bag.category))] := by
    rw [GrammarRule.bareParams_of_bare _ laws.representedBare, shape]
  exact HasType.collectionConstructor laws.bagAuthored bareShape elementsTyped

/-- **The only collection algebra is the parallel bag's**, with its unit. -/
theorem algebra_rule (laws : ParallelBag language bag unit multisets) {rule : GrammarRule} {kind : CollType}
    {algebra : CollectionAlgebra} (algebraRule : AlgebraRule language rule kind algebra) :
    rule = bag ∧ kind = .hashBag ∧ algebra = { flatten := true, unit := some unit } := by
  have same : rule = bag := by
    by_contra different
    obtain ⟨parameterName, selfShape⟩ := algebraRule.selfSorted
    rcases laws.otherParameters rule algebraRule.authored different with free | ⟨-, named⟩
    · have collectionless := free (.simple parameterName (.collection kind (.base rule.category)))
        (by rw [selfShape]; simp)
      simp [TermParam.typeExpr, collectionFree] at collectionless
    · have declared := algebraRule.declared
      rw [named.noAlgebra] at declared
      cases declared
  subst same
  obtain ⟨parameterName, selfShape⟩ := algebraRule.selfSorted
  obtain ⟨bagName, bagShape⟩ := laws.bagShape
  rw [bagShape] at selfShape
  simp only [List.cons.injEq, TermParam.simple.injEq, TypeExpr.collection.injEq, and_true] at selfShape
  have declared := algebraRule.declared
  rw [laws.bagAlgebra, Option.some.injEq] at declared
  exact ⟨rfl, selfShape.2.symm, declared.symm⟩

/-- The parallel bag's algebra, as an algebra rule. -/
theorem bagAlgebraRule (laws : ParallelBag language bag unit multisets) :
    AlgebraRule language bag .hashBag { flatten := true, unit := some unit } where
  authored := laws.bagAuthored
  declared := laws.bagAlgebra
  selfSorted := laws.bagShape
  unitAuthored := by
    intro name same
    cases Option.some.inj same
    exact laws.unitAuthored

private theorem collectionTypeOccurs_not_collectionFree {kind : CollType} {elementType type : TypeExpr}
    (occurs : CollectionTypeOccurs kind elementType type) : collectionFree type = false := by
  induction occurs with
  | here => rfl
  | domain occurs ih => simp [collectionFree, ih]
  | codomain occurs ih => simp [collectionFree, ih]
  | binder occurs ih => exact ih
  | element occurs ih => rfl

private theorem not_set_in_bag {elementType : TypeExpr} {sort : String}
    (occurs : CollectionTypeOccurs .hashSet elementType (.collection .hashBag (.base sort))) : False := by
  cases occurs with
  | element inner => cases inner

/-- **No collection is typed as a set.** -/
theorem no_set (laws : ParallelBag language bag unit multisets) {rule : GrammarRule} {elements : List Pattern}
    (authored : rule ∈ language.terms) : ¬ CollectionTypedAt language rule .hashSet elements := by
  rintro ⟨parameter, member, elementType, occurs, -⟩
  by_cases same : rule = bag
  · subst same
    obtain ⟨bagName, bagShape⟩ := laws.bagShape
    rw [bagShape] at member
    obtain rfl := List.mem_singleton.mp member
    exact not_set_in_bag occurs
  · rcases laws.otherParameters rule authored same with free | ⟨-, named⟩
    · have collectionless := free parameter member
      rw [collectionTypeOccurs_not_collectionFree occurs] at collectionless
      cases collectionless
    · obtain ⟨parameterName, sort, shape, -⟩ := named.shape
      rw [shape] at member
      obtain rfl := List.mem_singleton.mp member
      exact not_set_in_bag occurs

/-- **A bag law keeps a term of a collection-free type typed.** -/
theorem derived_hasType (laws : ParallelBag language bag unit multisets)
    {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} (derived : DerivedInstance language source target)
    (typed : HasType language free bound source type)
    (collectionless : collectionFree type = true) :
    HasType language free bound target type := by
  cases derived with
  | bagPerm _ _ permutation =>
      obtain ⟨-, rfl, elementsTyped⟩ := laws.bag_typing typed collectionless
      apply laws.bag_hasType
      apply elementsHaveType_iff.mpr
      intro element membership
      exact elementsHaveType_iff.mp elementsTyped element (permutation.mem_iff.mpr membership)
  | setPerm declaration kindTyped _ => exact (laws.no_set declaration kindTyped).elim
  | setDedup declaration kindTyped => exact (laws.no_set declaration kindTyped).elim
  | @flatten rule kind algebra before inner after algebraRule _ _ =>
      obtain ⟨rfl, rfl, elementsTyped⟩ := laws.bag_typing typed collectionless
      obtain ⟨beforeTyped, nestedTyped, afterTyped⟩ := ElementsHaveType.append_cons_split elementsTyped
      obtain ⟨-, -, innerTyped⟩ := laws.bag_typing nestedTyped rfl
      apply laws.bag_hasType
      apply elementsHaveType_iff.mpr
      intro element membership
      simp only [List.mem_append] at membership
      rcases membership with (inBefore | inInner) | inAfter
      · exact elementsHaveType_iff.mp beforeTyped element inBefore
      · exact elementsHaveType_iff.mp innerTyped element inInner
      · exact elementsHaveType_iff.mp afterTyped element inAfter
  | @singleton rule kind algebra _ algebraRule _ _ =>
      obtain ⟨rfl, rfl, elementsTyped⟩ := laws.bag_typing typed collectionless
      exact elementsHaveType_iff.mp elementsTyped target (by simp)
  | @unitElim rule kind algebra unitName before after algebraRule _ _ =>
      obtain ⟨rfl, rfl, elementsTyped⟩ := laws.bag_typing typed collectionless
      apply laws.bag_hasType
      apply elementsHaveType_iff.mpr
      intro element membership
      apply elementsHaveType_iff.mp elementsTyped element
      simp only [List.mem_append, List.mem_cons] at membership ⊢
      tauto
  | @emptyUnit rule kind algebra unitName algebraRule declaredUnit _ =>
      obtain ⟨-, rfl, -⟩ := laws.bag_typing typed collectionless
      obtain ⟨rfl, -, -⟩ := laws.algebra_rule algebraRule
      obtain ⟨unitRule, unitMember, rfl, categoryEq, parametersEq⟩ := algebraRule.unitAuthored unitName declaredUnit
      rw [← categoryEq]
      apply HasType.constructor unitMember
      · rintro ⟨parameterName, collectionKind, elementType, shape⟩
        have ordinaryShape := (GrammarRule.bareParams_cons_iff _ _ _).mp shape |>.2
        rw [parametersEq] at ordinaryShape
        cases ordinaryShape
      · rw [parametersEq]
        exact .nil

end ParallelBag

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
