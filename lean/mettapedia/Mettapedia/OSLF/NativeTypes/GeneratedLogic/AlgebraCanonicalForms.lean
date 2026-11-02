import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateEquations
import Mettapedia.GSLT.LanguageDef.BagNormalFormSection

/-!
# Canonical forms for a bag algebra

A language with one bag constructor, which declares the flattening algebra and a unit, has one normal form for
its laws (`BagNormalForm.normalForm`): nested bags spliced, units dropped, components sorted, and no empty or
singleton bag. The parallel composition of the π-calculus is such a bag. Equivalent terms have one normal form
(`normalForm_eq_of_equationEquiv`), and a sorted term reaches its normal form through sorted terms
(`path_normalForm`).

The canonical forms here are that normal form on closed terms of the bag's sort (`domain`), and the term itself
elsewhere (`canon`).

- **One sort** (`singleSorted`): every constructor has the bag's sort, and every parameter of another
  constructor has that sort or binds a variable of it.
- **The laws relate sorted terms only to sorted terms** (`admissible_iff_of_equivalent`), in one sort. Read
  from right to left, the singleton law wraps a term in a bag. The law requires that bag to be sorted, so the
  term is not a binder, and in one sort a term that is not a binder has the sort of every position it can
  stand at (`hasType_base_of_sorted`).
- **The contract holds** (`canonical`), in every relation environment.

Outside the domain the normal form can meet a term it is not equivalent to. A bag holding a binder, `{λx. P}`,
has the normal form `λx. P`, but no law applies to it, since that bag is not sorted. So the canonical form
leaves terms outside the domain as they are.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AlgebraForms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVarAt instantiateBVar liftBVars)
open Mettapedia.OSLF.MeTTaIL.PatternCode (sortPatterns)
open Mettapedia.GSLT.LanguageDef (defaultBasePremises)
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm

/-! ## One sort -/

/-- A position type of one sort: the sort, or a binder over the sort into the sort. -/
def sortedType (sort : String) : TypeExpr → Bool
  | .base value => value == sort
  | .arrow (.base domain) (.base codomain) => domain == sort && codomain == sort
  | .arrow (.multiBinder (.base domain)) (.base codomain) => domain == sort && codomain == sort
  | _ => false

/-- A parameter of one sort. -/
def sortedParameter (sort : String) (parameter : TermParam) : Bool :=
  match parameterType? parameter with
  | some type => sortedType sort type
  | none => false

/-- **One sort**: every constructor has the bag's sort, and every parameter of another constructor has that
sort or binds a variable of it. -/
def singleSorted (language : LanguageDef) (bag : GrammarRule) : Bool :=
  language.terms.all fun rule =>
    rule.category == bag.category && (rule == bag || rule.params.all (sortedParameter bag.category))

/-- A bound variable of one sort: of the sort, or a list of them. -/
def SortedEntry (sort : String) (entry : TypeExpr) : Prop :=
  entry = .base sort ∨ entry = .multiBinder (.base sort)

theorem sortedType_collectionFree {sort : String} {type : TypeExpr} (sorted : sortedType sort type = true) :
    collectionFree type = true := by
  unfold sortedType at sorted
  split at sorted <;> first | rfl | cases sorted

theorem sortedType_base (sort : String) : sortedType sort (.base sort) = true := by
  simp [sortedType]

theorem sortedType_arrow {sort : String} {domain codomain : TypeExpr}
    (sorted : sortedType sort (.arrow domain codomain) = true) :
    SortedEntry sort domain ∧ codomain = .base sort := by
  rcases domain with first | _ | inner | _ <;> rcases codomain with second | _ | _ | _ <;>
    simp [sortedType] at sorted
  · exact ⟨Or.inl (by rw [sorted.1]), by rw [sorted.2]⟩
  · rcases inner with first | _ | _ | _ <;> simp at sorted
    exact ⟨Or.inr (by rw [sorted.1]), by rw [sorted.2]⟩

theorem sortedType_multiBinder {sort : String} {domain codomain : TypeExpr}
    (sorted : sortedType sort (.arrow (.multiBinder domain) codomain) = true) :
    domain = .base sort ∧ codomain = .base sort := by
  rcases domain with first | _ | _ | _ <;> rcases codomain with second | _ | _ | _ <;>
    simp [sortedType] at sorted
  exact ⟨by rw [sorted.1], by rw [sorted.2]⟩

variable {language : LanguageDef} {bag : GrammarRule} {unit : Option String}

theorem category_of_singleSorted (sorted : singleSorted language bag = true) {rule : GrammarRule}
    (member : rule ∈ language.terms) : rule.category = bag.category := by
  have ruleSorted := List.all_eq_true.mp sorted rule member
  simp only [Bool.and_eq_true, beq_iff_eq] at ruleSorted
  exact ruleSorted.1

/-- **In one sort, a term that is not a binder has the sort** at every position of one sort it stands at. -/
theorem hasType_base_of_sorted (sorted : singleSorted language bag = true) {bound : List TypeExpr}
    (entries : ∀ entry ∈ bound, SortedEntry bag.category entry) {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language FreeTypeContext.empty bound pattern type)
    (position : sortedType bag.category type = true) (object : isObjectPattern pattern = true)
    (notLambda : ∀ binder body, pattern ≠ .lambda binder body)
    (notMulti : ∀ arity binders body, pattern ≠ .multiLambda arity binders body) :
    type = .base bag.category := by
  cases typed with
  | bvar lookup =>
    rcases entries _ (List.mem_of_getElem? lookup) with same | same
    · exact same
    · subst same
      simp [sortedType] at position
  | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | constructor member _ _ => rw [category_of_singleSorted sorted member]
  | lambda _ => exact absurd rfl (notLambda _ _)
  | multiLambda _ => exact absurd rfl (notMulti _ _ _)
  | subst _ _ => simp [isObjectPattern] at object
  | collection _ => simp [sortedType] at position
  | collectionConstructor member _ _ => rw [category_of_singleSorted sorted member]

/-! ## Typing along a context, in one sort -/

/-- **Typing at the hole of a context, in one sort.** The hole's bound variables and its type are of one sort,
and a replacement of that type that meets the same parameter representations can be put back. -/
theorem hasType_fill_sorted (laws : BareBagTheory language bag unit) (sorted : singleSorted language bag = true) :
    ∀ (context : OneHoleContext) {bound : List TypeExpr} {original : Pattern} {type : TypeExpr},
      (∀ entry ∈ bound, SortedEntry bag.category entry) → sortedType bag.category type = true →
      HasType language FreeTypeContext.empty bound (context.fill original) type →
      isObjectPattern (context.fill original) = true →
      ∃ holeBound holeType, (∀ entry ∈ holeBound, SortedEntry bag.category entry) ∧
        sortedType bag.category holeType = true ∧
        HasType language FreeTypeContext.empty holeBound original holeType ∧
        ∀ replacement, Represents original replacement →
          HasType language FreeTypeContext.empty holeBound replacement holeType →
          HasType language FreeTypeContext.empty bound (context.fill replacement) type := by
  intro context
  induction context with
  | hole =>
    intro bound original type entries position typed _
    exact ⟨bound, type, entries, position, typed, fun _ _ replaced => replaced⟩
  | apply label before inner after recurse =>
    intro bound original type entries position typed object
    simp only [OneHoleContext.fill] at typed object
    obtain ⟨rule, membership, labelEq, notBare, typeEq, arguments⟩ := hasType_apply_inversion typed
    obtain ⟨beforeParameters, parameter, afterParameters, expected, parametersEq, -,
        beforeTyped, representation, parameterType, middleTyped, afterTyped⟩ :=
      ArgumentsHaveTypes.append_cons_split arguments
    have ruleNotBag : rule ≠ bag := by
      rintro rfl
      obtain ⟨parameterName, shape⟩ := laws.bareShape
      exact notBare ⟨parameterName, .hashBag, .base _, shape⟩
    have expectedSorted : sortedType bag.category expected = true := by
      have ruleSorted := List.all_eq_true.mp sorted rule membership
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, ruleNotBag, false_or] at ruleSorted
      have parameterSorted := List.all_eq_true.mp ruleSorted.2 parameter (by rw [parametersEq]; simp)
      simpa [sortedParameter, parameterType] using parameterSorted
    have objectMiddle : isObjectPattern (inner.fill original) = true := by
      simp only [isObjectPattern] at object
      exact isObjectPatternList_append_cons object
    obtain ⟨holeBound, holeType, holeEntries, holePosition, originalTyped, rebuild⟩ :=
      recurse entries expectedSorted middleTyped objectMiddle
    refine ⟨holeBound, holeType, holeEntries, holePosition, originalTyped, ?_⟩
    intro replacement transfer replacementTyped
    subst typeEq labelEq
    simp only [OneHoleContext.fill]
    apply HasType.constructor membership notBare
    rw [parametersEq]
    exact argumentsHaveTypes_join
      (represents_fill inner transfer parameter representation) parameterType
      (rebuild replacement transfer replacementTyped) afterTyped beforeTyped
  | lambda binder inner recurse =>
    intro bound original type entries position typed object
    simp only [OneHoleContext.fill] at typed object
    cases typed with
    | @lambda _ _ _ domain codomain bodyTyped =>
      simp only [isObjectPattern] at object
      obtain ⟨domainEntry, rfl⟩ := sortedType_arrow position
      have bodyEntries : ∀ entry ∈ domain :: bound, SortedEntry bag.category entry := by
        intro entry member
        rcases List.mem_cons.mp member with rfl | inBound
        · exact domainEntry
        · exact entries entry inBound
      obtain ⟨holeBound, holeType, holeEntries, holePosition, originalTyped, rebuild⟩ :=
        recurse bodyEntries (sortedType_base _) bodyTyped object
      exact ⟨holeBound, holeType, holeEntries, holePosition, originalTyped,
        fun replacement transfer replacementTyped => HasType.lambda (rebuild replacement transfer replacementTyped)⟩
  | multiLambda arity binders inner recurse =>
    intro bound original type entries position typed object
    simp only [OneHoleContext.fill] at typed object
    cases typed with
    | @multiLambda _ _ _ _ domain codomain bodyTyped =>
      simp only [isObjectPattern] at object
      obtain ⟨rfl, rfl⟩ := sortedType_multiBinder position
      have bodyEntries : ∀ entry ∈ List.replicate arity (TypeExpr.base bag.category) ++ bound,
          SortedEntry bag.category entry := by
        intro entry member
        rcases List.mem_append.mp member with inReplicate | inBound
        · exact Or.inl (List.eq_of_mem_replicate inReplicate)
        · exact entries entry inBound
      obtain ⟨holeBound, holeType, holeEntries, holePosition, originalTyped, rebuild⟩ :=
        recurse bodyEntries (sortedType_base _) bodyTyped object
      exact ⟨holeBound, holeType, holeEntries, holePosition, originalTyped,
        fun replacement transfer replacementTyped =>
          HasType.multiLambda (rebuild replacement transfer replacementTyped)⟩
  | substBody inner replacement _ =>
    intro bound original type _ _ _ object
    simp [OneHoleContext.fill, isObjectPattern] at object
  | substReplacement body inner _ =>
    intro bound original type _ _ _ object
    simp [OneHoleContext.fill, isObjectPattern] at object
  | collection kind before inner after rest recurse =>
    intro bound original type entries position typed object
    simp only [OneHoleContext.fill] at typed object
    obtain ⟨rfl, rfl, elementsTyped⟩ := bag_typing laws.toBareBagPresentation typed (sortedType_collectionFree position)
    obtain ⟨beforeTyped, middleTyped, afterTyped⟩ := ElementsHaveType.append_cons_split elementsTyped
    have objectMiddle : isObjectPattern (inner.fill original) = true := by
      simp only [isObjectPattern, Bool.and_eq_true] at object
      exact isObjectPatternList_append_cons object.2
    obtain ⟨holeBound, holeType, holeEntries, holePosition, originalTyped, rebuild⟩ :=
      recurse entries (sortedType_base _) middleTyped objectMiddle
    refine ⟨holeBound, holeType, holeEntries, holePosition, originalTyped, ?_⟩
    intro replacement transfer replacementTyped
    simp only [OneHoleContext.fill]
    apply bag_hasType laws.toBareBagPresentation
    apply elementsHaveType_iff.mpr
    intro element membership
    simp only [List.mem_append, List.mem_cons] at membership
    rcases membership with inBefore | rfl | inAfter
    · exact elementsHaveType_iff.mp beforeTyped element inBefore
    · exact rebuild replacement transfer replacementTyped
    · exact elementsHaveType_iff.mp afterTyped element inAfter

/-! ## The laws read from right to left -/

/-- **Each bag law, read from right to left, keeps the type**, at a position of one sort. -/
theorem derived_hasType_back (laws : BareBagTheory language bag unit) (sorted : singleSorted language bag = true)
    {bound : List TypeExpr} (entries : ∀ entry ∈ bound, SortedEntry bag.category entry) {type : TypeExpr}
    (position : sortedType bag.category type = true) {source target : Pattern}
    (derived : DerivedInstance language source target)
    (typed : HasType language FreeTypeContext.empty bound target type) (object : isObjectPattern target = true) :
    HasType language FreeTypeContext.empty bound source type ∧ Represents target source := by
  have collectionless := sortedType_collectionFree position
  cases derived with
  | bagPerm _ _ permutation =>
    obtain ⟨-, rfl, elementsTyped⟩ := bag_typing laws.toBareBagPresentation typed collectionless
    exact ⟨bag_hasType laws.toBareBagPresentation (elementsHaveType_iff.mpr fun element member =>
      elementsHaveType_iff.mp elementsTyped element (permutation.mem_iff.mp member)), represents_collection _ _ _ _⟩
  | setPerm member kindTyped _ => exact absurd (laws.toBagTheory.collectionTyped member kindTyped).2 (by decide)
  | setDedup member kindTyped => exact absurd (laws.toBagTheory.collectionTyped member kindTyped).2 (by decide)
  | flatten algebraRule _ _ =>
    obtain ⟨-, rfl, -⟩ := laws.toBagTheory.algebraRule algebraRule
    obtain ⟨-, rfl, elementsTyped⟩ := bag_typing laws.toBareBagPresentation typed collectionless
    refine ⟨bag_hasType laws.toBareBagPresentation (elementsHaveType_iff.mpr ?_), represents_collection _ _ _ _⟩
    intro element member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with inBefore | rfl | inAfter
    · exact elementsHaveType_iff.mp elementsTyped element (by simp [inBefore])
    · exact bag_hasType laws.toBareBagPresentation (elementsHaveType_iff.mpr fun inner member =>
        elementsHaveType_iff.mp elementsTyped inner (by simp [member]))
    · exact elementsHaveType_iff.mp elementsTyped element (by simp [inAfter])
  | singleton algebraRule _ sortedAt =>
    obtain ⟨rfl, rfl, -⟩ := laws.toBagTheory.algebraRule algebraRule
    obtain ⟨free', bound', sortedTyped⟩ := sortedAt
    obtain ⟨-, -, elementTyped⟩ := bag_typing laws.toBareBagPresentation sortedTyped rfl
    have elementBase := elementsHaveType_iff.mp elementTyped target (by simp)
    have notLambda : ∀ binder body, target ≠ .lambda binder body := by
      rintro binder body rfl
      cases elementBase
    have notMulti : ∀ arity binders body, target ≠ .multiLambda arity binders body := by
      rintro arity binders body rfl
      cases elementBase
    obtain rfl := hasType_base_of_sorted sorted entries typed position object notLambda notMulti
    refine ⟨bag_hasType laws.toBareBagPresentation (elementsHaveType_iff.mpr fun element member => by
      rw [List.mem_singleton.mp member]
      exact typed), ?_⟩
    intro parameter matched
    cases parameter with
    | simple => trivial
    | abstractionNamed binder bodyName parameterType =>
      obtain ⟨body, rfl⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp matched
      exact absurd rfl (notLambda none body)
    | multiAbstractionNamed binders bodyName parameterType =>
      cases target <;> simp [MatchesParameterRepresentation] at matched
      exact absurd rfl (notMulti _ _ _)
  | unitElim algebraRule unitIs _ =>
    obtain ⟨rfl, rfl, -⟩ := laws.toBagTheory.algebraRule algebraRule
    obtain ⟨-, rfl, elementsTyped⟩ := bag_typing laws.toBareBagPresentation typed collectionless
    obtain ⟨unitRule, unitMember, labelIs, categoryIs, parametersAre⟩ := algebraRule.unitAuthored _ unitIs
    have unitTyped : HasType language FreeTypeContext.empty bound (.apply unitRule.label [])
        (.base unitRule.category) := by
      refine HasType.constructor unitMember ?_ (by rw [parametersAre]; exact .nil)
      rintro ⟨_, _, _, shape⟩
      cases representation : unitRule.collectionRepresentation <;>
        simp [GrammarRule.bareParams, representation, parametersAre] at shape
    rw [labelIs, categoryIs] at unitTyped
    refine ⟨bag_hasType laws.toBareBagPresentation (elementsHaveType_iff.mpr ?_), represents_collection _ _ _ _⟩
    intro element member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with inBefore | rfl | inAfter
    · exact elementsHaveType_iff.mp elementsTyped element (by simp [inBefore])
    · exact unitTyped
    · exact elementsHaveType_iff.mp elementsTyped element (by simp [inAfter])
  | emptyUnit algebraRule _ _ =>
    obtain ⟨rfl, rfl, -⟩ := laws.toBagTheory.algebraRule algebraRule
    obtain rfl := hasType_base_of_sorted sorted entries typed position object
      (by intro _ _ same; cases same) (by intro _ _ _ same; cases same)
    refine ⟨bag_hasType laws.toBareBagPresentation (.nil _ _), ?_⟩
    intro parameter matched
    cases parameter <;> simp_all [MatchesParameterRepresentation]

/-- Each bag law, read from right to left, relates object patterns to object patterns. -/
theorem derived_isObjectPattern_back {source target : Pattern} (derived : DerivedInstance language source target)
    (object : isObjectPattern target = true) : isObjectPattern source = true := by
  cases derived with
  | bagPerm _ _ permutation =>
    simp only [isObjectPattern, Option.isNone_none, Bool.true_and, isObjectPatternList_iff] at object ⊢
    exact fun pattern membership => object pattern (permutation.mem_iff.mp membership)
  | setPerm _ _ permutation =>
    simp only [isObjectPattern, Option.isNone_none, Bool.true_and, isObjectPatternList_iff] at object ⊢
    exact fun pattern membership => object pattern (permutation.mem_iff.mp membership)
  | setDedup _ _ =>
    simp only [isObjectPattern, Option.isNone_none, Bool.true_and, isObjectPatternList_iff] at object ⊢
    intro pattern membership
    rcases List.mem_cons.mp membership with rfl | inTail
    · exact object _ (by simp)
    · exact object pattern inTail
  | flatten _ _ _ =>
    simp only [isObjectPattern, Option.isNone_none, Bool.true_and, isObjectPatternList_iff, List.mem_append,
      List.mem_cons] at object ⊢
    rintro pattern (inBefore | rfl | inAfter)
    · exact object pattern (Or.inl (Or.inl inBefore))
    · simp only [isObjectPattern, Option.isNone_none, Bool.true_and, isObjectPatternList_iff]
      exact fun element member => object element (Or.inl (Or.inr member))
    · exact object pattern (Or.inr inAfter)
  | singleton _ _ _ =>
    simp only [isObjectPattern, Option.isNone_none, Bool.true_and, isObjectPatternList_iff, List.mem_singleton]
    rintro pattern rfl
    exact object
  | unitElim _ _ _ =>
    simp only [isObjectPattern, Option.isNone_none, Bool.true_and, isObjectPatternList_iff, List.mem_append,
      List.mem_cons] at object ⊢
    rintro pattern (inBefore | rfl | inAfter)
    · exact object pattern (Or.inl inBefore)
    · simp [isObjectPattern, isObjectPatternList]
    · exact object pattern (Or.inr inAfter)
  | emptyUnit _ _ _ => simp [isObjectPattern, isObjectPatternList]

/-- Each bag law, read from right to left, relates canonically bound patterns to canonically bound patterns. -/
theorem derived_hasCanonicalBinderMetadata_back {source target : Pattern}
    (derived : DerivedInstance language source target) (canonical : target.hasCanonicalBinderMetadata = true) :
    source.hasCanonicalBinderMetadata = true := by
  cases derived with
  | bagPerm _ _ permutation =>
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff] at canonical ⊢
    exact fun pattern membership => canonical pattern (permutation.mem_iff.mp membership)
  | setPerm _ _ permutation =>
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff] at canonical ⊢
    exact fun pattern membership => canonical pattern (permutation.mem_iff.mp membership)
  | setDedup _ _ =>
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff] at canonical ⊢
    intro pattern membership
    rcases List.mem_cons.mp membership with rfl | inTail
    · exact canonical _ (by simp)
    · exact canonical pattern inTail
  | flatten _ _ _ =>
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff, List.mem_append,
      List.mem_cons] at canonical ⊢
    rintro pattern (inBefore | rfl | inAfter)
    · exact canonical pattern (Or.inl (Or.inl inBefore))
    · simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff]
      exact fun element member => canonical element (Or.inl (Or.inr member))
    · exact canonical pattern (Or.inr inAfter)
  | singleton _ _ _ =>
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff, List.mem_singleton]
    rintro pattern rfl
    exact canonical
  | unitElim _ _ _ =>
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff, List.mem_append,
      List.mem_cons] at canonical ⊢
    rintro pattern (inBefore | rfl | inAfter)
    · exact canonical pattern (Or.inl inBefore)
    · simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
    · exact canonical pattern (Or.inr inAfter)
  | emptyUnit _ _ _ => simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]

/-- **A step of the laws, read from right to left, keeps a closed term of the sort one**, in one sort. -/
theorem step_admissible_back (laws : BareBagTheory language bag unit) (sorted : singleSorted language bag = true)
    {base : BasePremiseEvaluator} {source target : Pattern} (step : EquationContextStep base language source target)
    (admissible : Admissible language FreeTypeContext.empty [] (.base bag.category) target) :
    Admissible language FreeTypeContext.empty [] (.base bag.category) source := by
  generalize targetEq : target = finish at step
  cases step with
  | @inContext context redex contractum generator =>
    subst targetEq
    rcases generator with authored | derived
    · exact absurd authored (no_equationInstance_of_equations_eq_nil laws.equationsEmpty redex contractum)
    · obtain ⟨holeBound, holeType, holeEntries, holePosition, contractumTyped, rebuild⟩ :=
        hasType_fill_sorted laws sorted context (by simp) (sortedType_base _) admissible.typed admissible.object
      obtain ⟨redexTyped, represents⟩ := derived_hasType_back laws sorted holeEntries holePosition derived
        contractumTyped (object_of_fill context admissible.object)
      exact
        { typed := rebuild redex represents redexTyped
          canonical := hasCanonicalBinderMetadata_fill_replace context admissible.canonical
            (derived_hasCanonicalBinderMetadata_back derived)
          object := isObjectPattern_fill_replace context admissible.object (derived_isObjectPattern_back derived) }

theorem admissible_iff_of_step (laws : BareBagTheory language bag unit) (sorted : singleSorted language bag = true)
    {base : BasePremiseEvaluator} {source target : Pattern} (step : EquationContextStep base language source target) :
    Admissible language FreeTypeContext.empty [] (.base bag.category) source ↔
      Admissible language FreeTypeContext.empty [] (.base bag.category) target :=
  ⟨fun admissible => step_admissible laws step admissible rfl, step_admissible_back laws sorted step⟩

/-! ## The reference relation's equations are the laws -/

variable {relEnv : RelationEnv}

theorem equationContextStep_of_step (noEquations : language.equations = []) (base : BasePremiseEvaluator)
    {source target : Pattern} (step : EquationStep relEnv language source target) :
    EquationContextStep base language source target := by
  cases step with
  | inContext context generator =>
    rcases generator with authored | derived
    · cases authored with
      | forward member _ _ _ => rw [noEquations] at member; cases member
      | reverse member _ _ _ => rw [noEquations] at member; cases member
      | declared member _ _ => rw [noEquations] at member; cases member
      | premised member _ _ _ => rw [noEquations] at member; cases member
    · exact .inContext context (Or.inr derived)

theorem step_of_equationContextStep (noEquations : language.equations = []) {base : BasePremiseEvaluator}
    {source target : Pattern} (step : EquationContextStep base language source target) :
    EquationStep relEnv language source target := by
  cases step with
  | inContext context generator =>
    rcases generator with authored | derived
    · exact absurd authored (no_equationInstance_of_equations_eq_nil noEquations _ _)
    · exact .inContext context (Or.inr derived)

theorem equationEquiv_of_objectEquivalent (noEquations : language.equations = []) (base : BasePremiseEvaluator)
    {first second : Pattern} (equivalent : ObjectEquivalent relEnv language .syntax first second) :
    EquationEquiv base language first second :=
  Relation.EqvGen.mono (fun _ _ step => equationContextStep_of_step noEquations base step.2.2) _ _ equivalent

/-- **The laws relate closed terms of the sort only to closed terms of the sort**, in one sort. -/
theorem admissible_iff_of_equivalent (laws : BareBagTheory language bag unit)
    (sorted : singleSorted language bag = true) {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv language .syntax first second) :
    Admissible language FreeTypeContext.empty [] (.base bag.category) first ↔
      Admissible language FreeTypeContext.empty [] (.base bag.category) second := by
  induction equivalent with
  | rel _ _ step =>
    exact admissible_iff_of_step laws sorted (equationContextStep_of_step laws.equationsEmpty defaultBasePremises step.2.2)
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- A chain of laws from a closed term of the sort is an equivalence of object terms. -/
theorem objectEquivalent_of_path (laws : BareBagTheory language bag unit) {base : BasePremiseEvaluator}
    {source target : Pattern} (path : Path base language source target)
    (admissible : Admissible language FreeTypeContext.empty [] (.base bag.category) source) :
    ObjectEquivalent relEnv language .syntax source target := by
  induction path with
  | refl => exact Relation.EqvGen.refl _
  | tail before step previous =>
    have middle := path_admissible laws before admissible rfl
    have last := step_admissible laws step middle rfl
    exact Relation.EqvGen.trans _ _ _ previous
      (Relation.EqvGen.rel _ _ ⟨middle.object, last.object, step_of_equationContextStep laws.equationsEmpty step⟩)

/-! ## Canonical forms -/

variable (language bag unit)

/-- **The domain**: closed terms of the bag's sort. -/
def domain (term : Pattern) : Bool :=
  checkOpenPatternWellSorted language FreeTypeContext.empty [] (.base bag.category) term

/-- **The canonical form**: the bag normal form on the domain, the term itself elsewhere. -/
def canon (term : Pattern) : Pattern :=
  if domain language bag term then normalForm unit term else term

variable {language bag unit}

theorem domain_iff {term : Pattern} :
    domain language bag term = true ↔ Admissible language FreeTypeContext.empty [] (.base bag.category) term := by
  unfold domain
  rw [checkOpenPatternWellSorted_eq_true_iff]
  constructor
  · rintro ⟨typed, canonical, object, -⟩
    exact ⟨typed, canonical, object⟩
  · intro admissible
    exact ⟨admissible.typed, admissible.canonical, admissible.object,
      by simpa [ScopeSafeAt] using admissible.typed.isWellScopedAt⟩

theorem normalForm_admissible (laws : BareBagTheory language bag unit) {term : Pattern}
    (admissible : Admissible language FreeTypeContext.empty [] (.base bag.category) term) :
    Admissible language FreeTypeContext.empty [] (.base bag.category) (normalForm unit term) :=
  path_admissible laws (path_normalForm laws defaultBasePremises term admissible rfl) admissible rfl

/-- **The bag normal form gives canonical forms** on closed terms of the bag's sort, in one sort, whose domain is
read off them. -/
theorem canonicalDetermined (laws : BareBagTheory language bag unit) (sorted : singleSorted language bag = true) :
    CanonicalDetermined relEnv language (canon language bag unit) (domain language bag) where
  object admitted := (domain_iff.mp admitted).object
  determined term := by
    unfold canon
    by_cases admitted : domain language bag term = true
    · rw [if_pos admitted, admitted]
      exact domain_iff.mpr (normalForm_admissible laws (domain_iff.mp admitted))
    · rw [if_neg admitted]
  equivalent {term} admitted := by
    unfold canon
    rw [if_pos admitted]
    exact objectEquivalent_of_path laws
      (path_normalForm laws defaultBasePremises term (domain_iff.mp admitted) rfl) (domain_iff.mp admitted)
  same {first second} admitted equivalent := by
    have secondAdmitted := (admissible_iff_of_equivalent laws sorted equivalent).mp (domain_iff.mp admitted)
    unfold canon
    rw [if_pos admitted, if_pos (domain_iff.mpr secondAdmitted)]
    exact normalForm_eq_of_equationEquiv laws.toBagTheory
      (equationEquiv_of_objectEquivalent laws.equationsEmpty defaultBasePremises equivalent)
  closed {term} admitted := by
    unfold canon
    rw [if_pos admitted]
    have before := (domain_iff.mp admitted).typed.isWellScopedAt
    have after := (normalForm_admissible laws (domain_iff.mp admitted)).typed.isWellScopedAt
    simp only [List.length_nil] at before after
    rw [before, after]

/-- **The bag normal form gives canonical forms** on closed terms of the bag's sort, in one sort. -/
theorem canonical (laws : BareBagTheory language bag unit) (sorted : singleSorted language bag = true) :
    Canonical relEnv language (canon language bag unit) (domain language bag) :=
  (canonicalDetermined laws sorted).canonical

/-! ## The normal form respects substitution -/

/-- **A structural map**: a map on patterns, indexed by binder depth, that commutes with every constructor.
Substitution for a bound variable and lifting are structural; they differ only at variables. -/
structure Structural where
  map : ℕ → Pattern → Pattern
  apply : ∀ depth label arguments, map depth (.apply label arguments) = .apply label (arguments.map (map depth))
  lambda : ∀ depth binder body, map depth (.lambda binder body) = .lambda binder (map (depth + 1) body)
  multiLambda : ∀ depth arity binders body,
    map depth (.multiLambda arity binders body) = .multiLambda arity binders (map (depth + arity) body)
  subst : ∀ depth body replacement,
    map depth (.subst body replacement) = .subst (map (depth + 1) body) (map depth replacement)
  collection : ∀ depth kind elements rest,
    map depth (.collection kind elements rest) = .collection kind (elements.map (map depth)) rest

/-- The identity. -/
def Structural.identity : Structural where
  map _ pattern := pattern
  apply _ _ arguments := by simp
  lambda _ _ _ := rfl
  multiLambda _ _ _ _ := rfl
  subst _ _ _ := rfl
  collection _ _ elements _ := by simp

/-- Substitution for the bound variable at a depth. -/
def Structural.instantiate (replacement : Pattern) : Structural where
  map depth := instantiateBVarAt depth replacement
  apply depth label arguments := by simp [instantiateBVarAt]
  lambda depth binder body := by simp [instantiateBVarAt]
  multiLambda depth arity binders body := by simp [instantiateBVarAt]
  subst depth body nested := by simp [instantiateBVarAt]
  collection depth kind elements rest := by simp [instantiateBVarAt]

/-- Lifting the bound variables at or above a cutoff. -/
def Structural.lift (shift : ℕ) : Structural where
  map cutoff := liftBVars cutoff shift
  apply cutoff label arguments := by simp [liftBVars]
  lambda cutoff binder body := by simp [liftBVars]
  multiLambda cutoff arity binders body := by simp [liftBVars]
  subst cutoff body replacement := by simp [liftBVars]
  collection cutoff kind elements rest := by simp [liftBVars]

variable (unitName : String)

/-- Normalizing one root-normal component returns it. -/
theorem normalizeBag_single {pattern : Pattern} (normal : RootNormal unitName pattern) :
    normalizeBag (some unitName) [pattern] = pattern := by
  by_cases bag : IsBagNode pattern
  · obtain ⟨elements, rfl⟩ := bag
    obtain ⟨sorted, long, plain⟩ := normal elements rfl
    have contents : bagContents unitName [.collection .hashBag elements none] = elements := by
      simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, splice_bag]
      exact List.filter_eq_self.mpr fun element member => by simpa using (plain element member).1
    simp only [normalizeBag, contents, sorted]
    match elements, long with
    | _ :: _ :: _, _ => rfl
  · by_cases unit : pattern = .apply unitName []
    · subst unit
      simp [normalizeBag, bagContents, splice, collapse]
    · have contents : bagContents unitName [pattern] = [pattern] := by
        simp [bagContents, splice_of_not_bag bag, unit]
      simp [normalizeBag, contents, collapse]

/-- The components of a normalized bag are the components of what it normalizes, sorted. -/
theorem contents_normalizeBag {elements : List Pattern} (normal : ∀ element ∈ elements, RootNormal unitName element) :
    (bagContents unitName [normalizeBag (some unitName) elements]).Perm (bagContents unitName elements) := by
  simp only [normalizeBag]
  rw [bagContents_collapse fun component member => bagContents_spec normal (mem_sortPatterns.mp member)]
  exact sortPatterns_perm _

theorem contents_map_structural (g : Structural) (depth : ℕ) {elements : List Pattern}
    (each : ∀ element ∈ elements, normalForm (some unitName) (g.map depth element) =
      normalForm (some unitName) (g.map depth (normalForm (some unitName) element))) :
    (bagContents unitName (elements.map fun element => normalForm (some unitName) (g.map depth element))).Perm
      (bagContents unitName ((bagContents unitName (elements.map (normalForm (some unitName)))).map
        fun component => normalForm (some unitName) (g.map depth component))) := by
  induction elements with
  | nil => simp
  | cons element rest ih =>
    simp only [List.map_cons]
    rw [bagContents_cons, bagContents_cons unitName (normalForm (some unitName) element), List.map_append,
      bagContents_append]
    refine List.Perm.append ?_ (ih fun other member => each other (by simp [member]))
    rw [each element (by simp)]
    have normal := rootNormal_normalForm unitName element
    generalize normalForm (some unitName) element = shape at normal ⊢
    by_cases bag : IsBagNode shape
    · obtain ⟨components, rfl⟩ := bag
      obtain ⟨-, -, plain⟩ := normal components rfl
      have spliced : bagContents unitName [.collection .hashBag components none] = components := by
        simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, splice_bag]
        exact List.filter_eq_self.mpr fun component member => by simpa using (plain component member).1
      rw [spliced, g.collection, normalForm_bag, List.map_map]
      exact contents_normalizeBag unitName fun component member => by
        obtain ⟨original, -, rfl⟩ := List.mem_map.mp member
        exact rootNormal_normalForm unitName _
    · by_cases unit : shape = .apply unitName []
      · subst unit
        simp [bagContents, splice, g.apply, normalForm_apply]
      · have single : bagContents unitName [shape] = [shape] := by
          simp [bagContents, splice_of_not_bag bag, unit]
        rw [single]
        simp

theorem normalForm_structural_collapse (g : Structural) (depth : ℕ) {components : List Pattern}
    (plain : ∀ component ∈ components, component ≠ .apply unitName [] ∧ ¬ IsBagNode component) :
    normalForm (some unitName) (g.map depth (collapse unitName (sortPatterns components))) =
      normalizeBag (some unitName)
        (components.map fun component => normalForm (some unitName) (g.map depth component)) := by
  have reorder := normalizeBag_perm (some unitName)
    ((sortPatterns_perm components).map fun component => normalForm (some unitName) (g.map depth component))
  rw [← reorder]
  have sortedPlain : ∀ component ∈ sortPatterns components,
      component ≠ .apply unitName [] ∧ ¬ IsBagNode component :=
    fun component member => plain component (mem_sortPatterns.mp member)
  generalize sortPatterns components = sorted at sortedPlain ⊢
  match sorted, sortedPlain with
  | [], _ => simp [collapse, g.apply, normalForm_apply, normalizeBag, bagContents]
  | [component], _ =>
    simp only [collapse, List.map_cons, List.map_nil]
    exact (normalizeBag_single unitName (rootNormal_normalForm unitName _)).symm
  | first :: second :: rest, _ =>
    simp only [collapse, g.collection, normalForm_bag, List.map_map]
    rfl

/-- **The normal form sees through a structural map**: mapping a pattern or its normal form gives one normal
form. -/
theorem normalForm_structural (g : Structural) (pattern : Pattern) :
    ∀ depth, normalForm (some unitName) (g.map depth pattern) =
      normalForm (some unitName) (g.map depth (normalForm (some unitName) pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth; simp [normalForm]
  | hfvar name => intro depth; simp [normalForm]
  | happly label arguments recurse =>
    intro depth
    rw [g.apply, normalForm_apply, normalForm_apply, g.apply, normalForm_apply, List.map_map, List.map_map,
      List.map_map]
    congr 1
    exact List.map_congr_left fun argument member => recurse argument member depth
  | hlambda binder body recurse =>
    intro depth
    simp only [g.lambda, normalForm]
    rw [recurse (depth + 1)]
  | hmultiLambda arity binders body recurse =>
    intro depth
    simp only [g.multiLambda, normalForm]
    rw [recurse (depth + arity)]
  | hsubst body replacement bodyRecurse replacementRecurse =>
    intro depth
    simp only [g.subst, normalForm]
    rw [bodyRecurse (depth + 1), replacementRecurse depth]
  | hcollection kind elements rest recurse =>
    intro depth
    by_cases closed : kind = .hashBag ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := closed
      rw [g.collection, normalForm_bag, normalForm_bag, List.map_map]
      show normalizeBag (some unitName)
          (elements.map fun element => normalForm (some unitName) (g.map depth element)) =
        normalForm (some unitName) (g.map depth (collapse unitName
          (sortPatterns (bagContents unitName (elements.map (normalForm (some unitName)))))))
      rw [normalForm_structural_collapse unitName g depth fun component member =>
        bagContents_spec (fun element member => by
          obtain ⟨original, -, rfl⟩ := List.mem_map.mp member
          exact rootNormal_normalForm unitName original) member]
      exact normalizeBag_contents_perm unitName
        (contents_map_structural unitName g depth fun element member => recurse element member depth)
    · have keep : ∀ items : List Pattern, normalForm (some unitName) (.collection kind items rest) =
          .collection kind (items.map (normalForm (some unitName))) rest := fun items => by
        simp [normalForm, closed]
      rw [g.collection, keep, keep, g.collection, keep, List.map_map, List.map_map, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => recurse element member depth

/-- The normal form is a normal form. -/
theorem normalForm_idempotent (pattern : Pattern) :
    normalForm (some unitName) (normalForm (some unitName) pattern) = normalForm (some unitName) pattern :=
  (normalForm_structural unitName Structural.identity pattern 0).symm

/-- Substitution sees a replacement only through its normal form. -/
theorem normalForm_instantiate_replacement {replacement replacement' : Pattern}
    (same : normalForm (some unitName) replacement = normalForm (some unitName) replacement') (body : Pattern) :
    ∀ depth, normalForm (some unitName) (instantiateBVarAt depth replacement body) =
      normalForm (some unitName) (instantiateBVarAt depth replacement' body) := by
  induction body using Pattern.inductionOn with
  | hbvar index =>
    intro depth
    simp only [instantiateBVarAt]
    split
    · rfl
    · split
      · have first := normalForm_structural unitName (Structural.lift depth) replacement 0
        have second := normalForm_structural unitName (Structural.lift depth) replacement' 0
        simp only [Structural.lift] at first second
        rw [first, second, same]
      · rfl
  | hfvar name => intro depth; simp [instantiateBVarAt]
  | happly label arguments recurse =>
    intro depth
    simp only [instantiateBVarAt, normalForm_apply, List.map_map]
    congr 1
    exact List.map_congr_left fun argument member => recurse argument member depth
  | hlambda binder body recurse =>
    intro depth
    simp only [instantiateBVarAt, normalForm]
    rw [recurse (depth + 1)]
  | hmultiLambda arity binders body recurse =>
    intro depth
    simp only [instantiateBVarAt, normalForm]
    rw [recurse (depth + arity)]
  | hsubst body nested bodyRecurse nestedRecurse =>
    intro depth
    simp only [instantiateBVarAt, normalForm]
    rw [bodyRecurse (depth + 1), nestedRecurse depth]
  | hcollection kind elements rest recurse =>
    intro depth
    simp only [instantiateBVarAt]
    by_cases closed : kind = .hashBag ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := closed
      rw [normalForm_bag, normalForm_bag, List.map_map, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => recurse element member depth
    · have keep : ∀ items : List Pattern, normalForm (some unitName) (.collection kind items rest) =
          .collection kind (items.map (normalForm (some unitName))) rest := fun items => by
        simp [normalForm, closed]
      rw [keep, keep, List.map_map, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => recurse element member depth

/-- **The normal form respects substitution**: substituting a replacement for a bound variable, or its normal
form into the body's normal form, gives one normal form. -/
theorem normalForm_instantiateBVar (replacement body : Pattern) :
    normalForm (some unitName) (instantiateBVar replacement body) =
      normalForm (some unitName)
        (instantiateBVar (normalForm (some unitName) replacement) (normalForm (some unitName) body)) := by
  unfold instantiateBVar
  have mapped := normalForm_structural unitName (Structural.instantiate replacement) body 0
  simp only [Structural.instantiate] at mapped
  rw [mapped]
  exact normalForm_instantiate_replacement unitName (normalForm_idempotent unitName replacement).symm _ 0

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AlgebraForms
