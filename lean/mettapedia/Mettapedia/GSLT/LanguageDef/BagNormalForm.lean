import Mettapedia.GSLT.LanguageDef.EquationInvariant
import Mettapedia.OSLF.MeTTaIL.PatternCode

/-!
# Normal forms for a bag contact

A presentation whose only static laws are the laws of one bag has a normal
form for its static equivalence, computed on raw patterns.

The presentations covered are described by `BagTheory`.  They author no
equation, and exactly one of their constructors carries a collection: a bag
over its own sort.  The bag either declares no algebra, so that its only law
is permutation of components, or declares the flattening algebra with a unit,
so that nested bags are spliced, a singleton bag is its component, the unit is
dropped, and the empty bag is the unit.

The normalizer rewrites every bag from the inside out.  With no algebra it
sorts the normalized components.  With the algebra it splices nested bags,
drops units, sorts, and rebuilds without an empty or singleton wrapper.
Sorting uses the collision-free structural code of patterns, so it depends
only on the multiset of components.

This module proves the raw half: equivalent patterns have the same normal
form.  The other half, that a sorted pattern is equivalent to its normal form
through sorted patterns only, needs typing along contexts; it is the subject
of `BagNormalFormTyping` and `BagNormalFormSection`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef.EquationSemantics

/-! ## The presentations covered -/

/-- A type expression that mentions no collection. -/
def collectionFree : TypeExpr → Bool
  | .base _ => true
  | .arrow domain codomain => collectionFree domain && collectionFree codomain
  | .multiBinder body => collectionFree body
  | .collection _ _ => false

/-- A presentation whose static laws are those of one bag.

`bag` is the bag constructor and `unit` records its algebra: `none` for a bag
with no declared algebra, `some name` for the flattening algebra whose unit is
the nullary constructor `name`. -/
structure BagTheory (language : LanguageDef) (bag : GrammarRule)
    (unit : Option String) : Prop where
  /-- No equation is authored. -/
  equationsEmpty : language.equations = []
  /-- The bag constructor is declared. -/
  bagAuthored : bag ∈ language.terms
  /-- Its single parameter is a bag over its own sort. -/
  bagShape : ∃ parameterName,
    bag.params = [.simple parameterName (.collection .hashBag (.base bag.category))]
  /-- It declares no algebra, or the flattening algebra with the given unit. -/
  bagAlgebra : bag.algebra? =
    unit.map fun name => ({ flatten := true, unit := some name } : CollectionAlgebra)
  /-- No other constructor has a parameter whose type mentions a collection. -/
  otherParameters : ∀ rule ∈ language.terms, rule ≠ bag →
    ∀ parameter ∈ rule.params, collectionFree (TermParam.typeExpr parameter) = true
  /-- A declared unit is a nullary constructor of the bag's sort. -/
  unitAuthored : ∀ name, unit = some name →
    ∃ unitRule ∈ language.terms,
      unitRule.label = name ∧ unitRule.category = bag.category ∧ unitRule.params = []

namespace BagTheory

variable {language : LanguageDef} {bag : GrammarRule} {unit : Option String}

/-- A declared constructor whose single parameter is a collection is the bag,
and the collection is a bag over the bag's sort. -/
theorem eq_bag_of_collectionParameter (laws : BagTheory language bag unit)
    {rule : GrammarRule} (authored : rule ∈ language.terms)
    {parameterName : String} {kind : CollType} {elementType : TypeExpr}
    (shape : rule.params = [.simple parameterName (.collection kind elementType)]) :
    rule = bag ∧ kind = .hashBag ∧ elementType = .base bag.category := by
  have same : rule = bag := by
    by_contra different
    have free := laws.otherParameters rule authored different
      (.simple parameterName (.collection kind elementType)) (by rw [shape]; simp)
    simp [TermParam.typeExpr, collectionFree] at free
  subst same
  obtain ⟨bagName, bagShape⟩ := laws.bagShape
  rw [bagShape] at shape
  simp only [List.cons.injEq, TermParam.simple.injEq, TypeExpr.collection.injEq,
    and_true] at shape
  exact ⟨rfl, shape.2.1.symm, shape.2.2.symm⟩

/-- Every collection carrier of the presentation is the bag. -/
theorem carrier (laws : BagTheory language bag unit) {rule : GrammarRule}
    {kind : CollType} (declared : CollectionCarrierRule language rule kind) :
    rule = bag ∧ kind = .hashBag := by
  obtain ⟨parameterName, elementType, shape⟩ := declared.selfSorted
  obtain ⟨same, kindEq, -⟩ := laws.eq_bag_of_collectionParameter declared.authored shape
  exact ⟨same, kindEq⟩

/-- Every declared collection algebra is the bag's flattening algebra with its
unit. -/
theorem algebraRule (laws : BagTheory language bag unit) {rule : GrammarRule}
    {kind : CollType} {algebra : CollectionAlgebra}
    (declared : AlgebraRule language rule kind algebra) :
    rule = bag ∧ kind = .hashBag ∧
      ∃ name, unit = some name ∧ algebra = { flatten := true, unit := some name } := by
  obtain ⟨parameterName, shape⟩ := declared.selfSorted
  obtain ⟨same, kindEq, -⟩ := laws.eq_bag_of_collectionParameter declared.authored shape
  subst same
  refine ⟨rfl, kindEq, ?_⟩
  have algebraEq := declared.declared
  rw [laws.bagAlgebra] at algebraEq
  cases unit with
  | none => simp at algebraEq
  | some name =>
      simp only [Option.map_some, Option.some.injEq] at algebraEq
      exact ⟨name, rfl, algebraEq.symm⟩

/-- The collection-carrier evidence of the bag itself. -/
theorem bagCarrier (laws : BagTheory language bag unit) :
    CollectionCarrierRule language bag .hashBag := by
  obtain ⟨parameterName, shape⟩ := laws.bagShape
  exact ⟨laws.bagAuthored, parameterName, .base bag.category, shape⟩

/-- The algebra evidence of the bag when it declares its unit. -/
theorem bagAlgebraRule {unitName : String}
    (laws : BagTheory language bag (some unitName)) :
    AlgebraRule language bag .hashBag { flatten := true, unit := some unitName } := by
  refine ⟨laws.bagAuthored, by simpa using laws.bagAlgebra, laws.bagShape, ?_⟩
  intro name declaredUnit
  simp only [Option.some.injEq] at declaredUnit
  subst declaredUnit
  exact laws.unitAuthored unitName rfl

end BagTheory

/-- The executable test for `BagTheory`. -/
def bagTheoryCheck (language : LanguageDef) (bag : GrammarRule) (unit : Option String) :
    Bool :=
  language.equations.isEmpty &&
    language.terms.contains bag &&
    (match bag.params with
      | [.simple _ (.collection .hashBag (.base sort))] => sort == bag.category
      | _ => false) &&
    (bag.algebra? ==
      unit.map fun name => ({ flatten := true, unit := some name } : CollectionAlgebra)) &&
    (language.terms.all fun rule =>
      rule == bag ||
        rule.params.all fun parameter => collectionFree (TermParam.typeExpr parameter)) &&
    (match unit with
      | none => true
      | some name =>
          language.terms.any fun rule =>
            rule.label == name && rule.category == bag.category && rule.params.isEmpty)

/-- A presentation passing the test is a bag theory. -/
theorem bagTheory_of_check {language : LanguageDef} {bag : GrammarRule}
    {unit : Option String} (checked : bagTheoryCheck language bag unit = true) :
    BagTheory language bag unit := by
  simp only [bagTheoryCheck, Bool.and_eq_true] at checked
  obtain ⟨⟨⟨⟨⟨equations, member⟩, shape⟩, algebra⟩, others⟩, unitDeclared⟩ := checked
  refine
    { equationsEmpty := List.isEmpty_iff.mp equations
      bagAuthored := by simpa using member
      bagShape := ?_
      bagAlgebra := by simpa using algebra
      otherParameters := ?_
      unitAuthored := ?_ }
  · split at shape
    · next parameterName sort parameters =>
        exact ⟨parameterName, by rw [parameters, show sort = bag.category by simpa using shape]⟩
    · cases shape
  · intro rule membership different parameter parameterMember
    have entry := List.all_eq_true.mp others rule membership
    simp only [Bool.or_eq_true, beq_iff_eq, different, false_or] at entry
    exact List.all_eq_true.mp entry parameter parameterMember
  · intro name declared
    subst declared
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff]
      at unitDeclared
    obtain ⟨unitRule, membership, ⟨label, category⟩, parameters⟩ := unitDeclared
    exact ⟨unitRule, membership, label, category, parameters⟩

/-! ## Sorting -/

/-- Sorting permutes. -/
theorem sortPatterns_perm (patterns : List Pattern) :
    (sortPatterns patterns).Perm patterns :=
  List.mergeSort_perm _ _

@[simp] theorem mem_sortPatterns {pattern : Pattern} {patterns : List Pattern} :
    pattern ∈ sortPatterns patterns ↔ pattern ∈ patterns :=
  (sortPatterns_perm patterns).mem_iff

@[simp] theorem sortPatterns_nil : sortPatterns [] = [] := by
  simp [sortPatterns]

@[simp] theorem sortPatterns_singleton (pattern : Pattern) :
    sortPatterns [pattern] = [pattern] := by
  simp [sortPatterns]

@[simp] theorem sortPatterns_length (patterns : List Pattern) :
    (sortPatterns patterns).length = patterns.length :=
  (sortPatterns_perm patterns).length_eq

/-- Sorting a sorted list changes nothing. -/
@[simp] theorem sortPatterns_idempotent (patterns : List Pattern) :
    sortPatterns (sortPatterns patterns) = sortPatterns patterns :=
  sortPatterns_eq_of_perm (sortPatterns_perm patterns)

/-- A list already in code order is its own sorting. -/
theorem sortPatterns_of_sorted {patterns : List Pattern}
    (sorted : patterns.Pairwise fun left right => patternCode left ≤ patternCode right) :
    sortPatterns patterns = patterns :=
  List.mergeSort_of_pairwise (sorted.imp fun ordered => by simpa using ordered)

/-! ## The normalizer -/

/-- A closed bag node. -/
def IsBagNode (pattern : Pattern) : Prop :=
  ∃ elements, pattern = .collection .hashBag elements none

/-- What a component contributes when nested bags are flattened: the
components of a bag node, or the component itself. -/
def splice : Pattern → List Pattern
  | .collection .hashBag elements none => elements
  | pattern => [pattern]

@[simp] theorem splice_bag (elements : List Pattern) :
    splice (.collection .hashBag elements none) = elements := rfl

/-- A component that is not a bag node contributes itself. -/
theorem splice_of_not_bag {pattern : Pattern} (notBag : ¬ IsBagNode pattern) :
    splice pattern = [pattern] := by
  cases pattern with
  | collection kind elements rest =>
      cases kind <;> cases rest <;> first
        | rfl
        | exact absurd ⟨elements, rfl⟩ notBag
  | _ => rfl

/-- The components of a bag after splicing nested bags and dropping units. -/
def bagContents (unit : String) (elements : List Pattern) : List Pattern :=
  (elements.flatMap splice).filter fun pattern => decide (pattern ≠ .apply unit [])

@[simp] theorem bagContents_nil (unit : String) : bagContents unit [] = [] := rfl

@[simp] theorem bagContents_append (unit : String) (first second : List Pattern) :
    bagContents unit (first ++ second) = bagContents unit first ++ bagContents unit second := by
  simp [bagContents]

theorem bagContents_cons (unit : String) (head : Pattern) (tail : List Pattern) :
    bagContents unit (head :: tail) = bagContents unit [head] ++ bagContents unit tail := by
  rw [← bagContents_append]
  rfl

/-- Rebuild a bag without an empty or singleton wrapper. -/
def collapse (unit : String) : List Pattern → Pattern
  | [] => .apply unit []
  | [pattern] => pattern
  | patterns => .collection .hashBag patterns none

/-- Normalize a bag whose components are already normal. -/
def normalizeBag : Option String → List Pattern → Pattern
  | none, elements => .collection .hashBag (sortPatterns elements) none
  | some unit, elements => collapse unit (sortPatterns (bagContents unit elements))

mutual
  /-- The normal form of a pattern for the laws of one bag. -/
  def normalForm (unit : Option String) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply label arguments => .apply label (normalFormList unit arguments)
    | .lambda binder body => .lambda binder (normalForm unit body)
    | .multiLambda arity binders body =>
        .multiLambda arity binders (normalForm unit body)
    | .subst body replacement =>
        .subst (normalForm unit body) (normalForm unit replacement)
    | .collection kind elements rest =>
        if kind = .hashBag ∧ rest = none then
          normalizeBag unit (normalFormList unit elements)
        else
          .collection kind (normalFormList unit elements) rest

  /-- The normal forms of a list of patterns. -/
  def normalFormList (unit : Option String) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => normalForm unit pattern :: normalFormList unit patterns
end

@[simp] theorem normalFormList_eq_map (unit : Option String) (patterns : List Pattern) :
    normalFormList unit patterns = patterns.map (normalForm unit) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp [normalFormList, recurse]

/-- The normal form of a closed bag node. -/
theorem normalForm_bag (unit : Option String) (elements : List Pattern) :
    normalForm unit (.collection .hashBag elements none) =
      normalizeBag unit (elements.map (normalForm unit)) := by
  simp [normalForm]

/-- The normal form of a constructor application. -/
theorem normalForm_apply (unit : Option String) (label : String)
    (arguments : List Pattern) :
    normalForm unit (.apply label arguments) =
      .apply label (arguments.map (normalForm unit)) := by
  simp [normalForm]

/-- The normal form sees a context only through the normal form of what fills
its hole. -/
theorem normalForm_fill_congr (unit : Option String) :
    ∀ (context : OneHoleContext) {first second : Pattern},
      normalForm unit first = normalForm unit second →
        normalForm unit (context.fill first) = normalForm unit (context.fill second)
  | .hole, _, _, same => same
  | .apply label before inner after, _, _, same => by
      simp [OneHoleContext.fill, normalForm, normalForm_fill_congr unit inner same]
  | .lambda _ inner, _, _, same => by
      simp [OneHoleContext.fill, normalForm, normalForm_fill_congr unit inner same]
  | .multiLambda _ _ inner, _, _, same => by
      simp [OneHoleContext.fill, normalForm, normalForm_fill_congr unit inner same]
  | .substBody inner replacement, _, _, same => by
      simp [OneHoleContext.fill, normalForm, normalForm_fill_congr unit inner same]
  | .substReplacement body inner, _, _, same => by
      simp [OneHoleContext.fill, normalForm, normalForm_fill_congr unit inner same]
  | .collection kind before inner after rest, _, _, same => by
      simp [OneHoleContext.fill, normalForm, normalForm_fill_congr unit inner same]

/-! ## The shape of a normal form -/

/-- At its root a normal form in the flattening mode is not a bag, or is a
sorted bag of at least two components none of which is a bag or the unit. -/
def RootNormal (unit : String) (pattern : Pattern) : Prop :=
  ∀ elements, pattern = .collection .hashBag elements none →
    sortPatterns elements = elements ∧ 2 ≤ elements.length ∧
      ∀ element ∈ elements, element ≠ .apply unit [] ∧ ¬ IsBagNode element

/-- Components that are root-normal contribute neither a bag nor the unit. -/
theorem bagContents_spec {unit : String} {elements : List Pattern}
    (normal : ∀ element ∈ elements, RootNormal unit element)
    {component : Pattern} (membership : component ∈ bagContents unit elements) :
    component ≠ .apply unit [] ∧ ¬ IsBagNode component := by
  simp only [bagContents, List.mem_filter, List.mem_flatMap, decide_eq_true_eq] at membership
  obtain ⟨⟨element, elementMember, spliced⟩, notUnit⟩ := membership
  refine ⟨notUnit, ?_⟩
  by_cases elementBag : IsBagNode element
  · obtain ⟨inner, rfl⟩ := elementBag
    exact ((normal _ elementMember inner rfl).2.2 component (by simpa using spliced)).2
  · rw [splice_of_not_bag elementBag] at spliced
    obtain rfl := List.mem_singleton.mp spliced
    exact elementBag

/-- Rebuilding a list of components that are neither bags nor the unit and
then reading its components back returns the list. -/
theorem bagContents_collapse {unit : String} {components : List Pattern}
    (plain : ∀ component ∈ components,
      component ≠ .apply unit [] ∧ ¬ IsBagNode component) :
    bagContents unit [collapse unit components] = components := by
  match components, plain with
  | [], _ => simp [collapse, bagContents, splice]
  | [component], plain =>
      have facts := plain component (by simp)
      simp [collapse, bagContents, splice_of_not_bag facts.2, facts.1]
  | first :: second :: rest, plain =>
      simp only [collapse, bagContents, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, splice_bag]
      apply List.filter_eq_self.mpr
      intro component membership
      simpa using (plain component membership).1

/-- A rebuilt list of plain, sorted components is root-normal. -/
theorem rootNormal_collapse {unit : String} {components : List Pattern}
    (sorted : sortPatterns components = components)
    (plain : ∀ component ∈ components,
      component ≠ .apply unit [] ∧ ¬ IsBagNode component) :
    RootNormal unit (collapse unit components) := by
  match components, sorted, plain with
  | [], _, _ =>
      intro elements same
      simp [collapse] at same
  | [component], _, plain =>
      intro elements same
      exact absurd ⟨elements, same⟩ (plain component (by simp)).2
  | first :: second :: rest, sorted, plain =>
      intro elements same
      simp only [collapse, Pattern.collection.injEq, true_and, and_true] at same
      subst same
      exact ⟨sorted, by simp, plain⟩

/-- Every normal form in the flattening mode is root-normal. -/
theorem rootNormal_normalForm (unit : String) (pattern : Pattern) :
    RootNormal unit (normalForm (some unit) pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro elements same; simp [normalForm] at same
  | hfvar name => intro elements same; simp [normalForm] at same
  | happly label arguments _ => intro elements same; simp [normalForm] at same
  | hlambda binder body _ => intro elements same; simp [normalForm] at same
  | hmultiLambda arity binders body _ => intro elements same; simp [normalForm] at same
  | hsubst body replacement _ _ => intro elements same; simp [normalForm] at same
  | hcollection kind elements rest recurse =>
      by_cases closedBag : kind = .hashBag ∧ rest = none
      · obtain ⟨rfl, rfl⟩ := closedBag
        rw [normalForm_bag]
        apply rootNormal_collapse (sortPatterns_idempotent _)
        intro component membership
        apply bagContents_spec (elements := elements.map (normalForm (some unit)))
        · intro element elementMember
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp elementMember
          exact recurse original originalMember
        · exact mem_sortPatterns.mp membership
      · intro components same
        simp only [normalForm, closedBag, if_false, Pattern.collection.injEq] at same
        exact absurd ⟨same.1, same.2.2⟩ closedBag

/-! ## Equivalent patterns have one normal form -/

/-- Normalizing a bag depends only on the multiset of its components. -/
theorem normalizeBag_perm (unit : Option String) {first second : List Pattern}
    (permutation : List.Perm first second) :
    normalizeBag unit first = normalizeBag unit second := by
  cases unit with
  | none => simp [normalizeBag, sortPatterns_eq_of_perm permutation]
  | some name =>
      simp only [normalizeBag]
      rw [sortPatterns_eq_of_perm]
      exact (permutation.flatMap_right splice).filter _

/-- In the flattening mode, normalizing a bag depends only on the multiset of
contents of its components. -/
theorem normalizeBag_contents_perm (unit : String) {first second : List Pattern}
    (permutation : List.Perm (bagContents unit first) (bagContents unit second)) :
    normalizeBag (some unit) first = normalizeBag (some unit) second := by
  simp only [normalizeBag]
  rw [sortPatterns_eq_of_perm permutation]

/-- Every law the presentation derives from its bag preserves the normal
form. -/
theorem normalForm_derived {language : LanguageDef} {bag : GrammarRule}
    {unit : Option String} (laws : BagTheory language bag unit)
    {source target : Pattern} (derived : DerivedInstance language source target) :
    normalForm unit source = normalForm unit target := by
  cases derived with
  | bagPerm _ _ permutation =>
      rw [normalForm_bag, normalForm_bag]
      exact normalizeBag_perm unit (permutation.map _)
  | setPerm declaration _ _ =>
      exact absurd (laws.carrier declaration).2 (by decide)
  | setDedup declaration _ =>
      exact absurd (laws.carrier declaration).2 (by decide)
  | @flatten rule kind algebra before inner after algebraRule _ _ =>
      obtain ⟨-, rfl, name, rfl, -⟩ := laws.algebraRule algebraRule
      rw [normalForm_bag, normalForm_bag]
      apply normalizeBag_contents_perm
      simp only [List.map_append, List.map_cons, bagContents_append, List.append_assoc]
      rw [bagContents_cons name (normalForm (some name) (.collection .hashBag inner none))]
      refine List.Perm.append_left _ (List.Perm.append_right _ ?_)
      rw [normalForm_bag]
      simp only [normalizeBag]
      rw [bagContents_collapse]
      · exact sortPatterns_perm _
      · intro component membership
        apply bagContents_spec (elements := inner.map (normalForm (some name)))
        · intro element elementMember
          obtain ⟨original, -, rfl⟩ := List.mem_map.mp elementMember
          exact rootNormal_normalForm name original
        · exact mem_sortPatterns.mp membership
  | @singleton rule kind algebra _ algebraRule _ _ =>
      obtain ⟨-, rfl, name, rfl, -⟩ := laws.algebraRule algebraRule
      rw [normalForm_bag]
      simp only [List.map_cons, List.map_nil, normalizeBag]
      have normal := rootNormal_normalForm name target
      generalize normalForm (some name) target = image at normal ⊢
      by_cases isUnit : image = .apply name []
      · subst isUnit
        simp [bagContents, splice, collapse]
      · by_cases isBag : IsBagNode image
        · obtain ⟨components, rfl⟩ := isBag
          obtain ⟨sorted, long, plain⟩ := normal components rfl
          have contents : bagContents name [.collection .hashBag components none] =
              components := by
            simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil,
              splice_bag]
            apply List.filter_eq_self.mpr
            intro component membership
            simpa using (plain component membership).1
          rw [contents, sorted]
          match components, long with
          | first :: second :: rest, _ => rfl
        · have contents : bagContents name [image] = [image] := by
            simp [bagContents, splice_of_not_bag isBag, isUnit]
          rw [contents, sortPatterns_singleton]
          rfl
  | @unitElim rule kind algebra unitName before after algebraRule declaredUnit _ =>
      obtain ⟨-, rfl, name, rfl, rfl⟩ := laws.algebraRule algebraRule
      simp only [Option.some.injEq] at declaredUnit
      subst declaredUnit
      rw [normalForm_bag, normalForm_bag]
      apply normalizeBag_contents_perm
      simp only [List.map_append, List.map_cons, bagContents_append]
      rw [bagContents_cons name (normalForm (some name) (.apply name []))]
      have unitContents :
          bagContents name [normalForm (some name) (.apply name [])] = [] := by
        simp [normalForm, normalFormList, bagContents, splice]
      rw [unitContents, List.nil_append]
  | @emptyUnit rule kind algebra unitName algebraRule declaredUnit _ =>
      obtain ⟨-, rfl, name, rfl, rfl⟩ := laws.algebraRule algebraRule
      simp only [Option.some.injEq] at declaredUnit
      subst declaredUnit
      rw [normalForm_bag]
      simp [normalizeBag, collapse, normalForm, normalFormList]

/-- **Completeness.**  Patterns identified by the static equivalence of a bag
theory have the same normal form. -/
theorem normalForm_eq_of_equationEquiv {language : LanguageDef} {bag : GrammarRule}
    {unit : Option String} (laws : BagTheory language bag unit)
    {base : BasePremiseEvaluator} {left right : Pattern}
    (equivalent : EquationEquiv base language left right) :
    normalForm unit left = normalForm unit right := by
  apply equationEquiv_invariant (normalForm unit)
    (fun context _ _ same => normalForm_fill_congr unit context same) _ equivalent
  rintro source target (authored | derived)
  · exact absurd authored
      (no_equationInstance_of_equations_eq_nil laws.equationsEmpty source target)
  · exact normalForm_derived laws derived

end Mettapedia.GSLT.LanguageDef.BagNormalForm
