import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Coherence

/-!
# Typing facts of restriction blocks

Over any calculus with restriction (`BlockLanguage`), in a context whose free and bound variables have base sorts
(`BaseContext`):

- a filled context of a base sort, of the type of abstractions between base sorts, or of a bag over a base sort,
  types a filling that is no abstraction at a base sort or a bag over one, under some context of base sorts, and
  every term of that type can be put back (`fill_typed`);
- a typed object term carries no binder names (`metadata_of_typed`);
- a map acting on bags member by member and fixing the unit carries a bag law to a bag law (`derived_map`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff argumentsHaveTypes_join isObjectPatternList_iff
  hasCanonicalBinderMetadataList_iff)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance SortedAt)

variable {language : LanguageDef} {block : Block}

/-- An abstraction has an arrow type, so it has no base sort. -/
theorem lambda_untyped {free : FreeTypeContext} {bound : List TypeExpr} {binder : Option String} {body : Pattern}
    {sort : String} (typed : HasType language free bound (.lambda binder body) (.base sort)) : False := by
  cases typed

theorem notLambda_of_typed {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {sort : String}
    (typed : HasType language free bound pattern (.base sort)) : ∀ binder body, pattern ≠ .lambda binder body := by
  rintro binder body rfl
  exact lambda_untyped typed

/-- In a context of base sorts, an object of the type of abstractions is an abstraction. -/
theorem lambda_of_arrow {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {domain sort : String}
    (context : BaseContext free bound)
    (typed : HasType language free bound pattern (.arrow (.base domain) (.base sort)))
    (object : isObjectPattern pattern = true) : ∃ binder body, pattern = .lambda binder body := by
  cases typed with
  | bvar lookup =>
      obtain ⟨_, isBase⟩ := context.bound _ (List.mem_of_getElem? lookup)
      cases isBase
  | fvar lookup =>
      obtain ⟨_, isBase⟩ := context.free _ _ lookup
      cases isBase
  | lambda => exact ⟨_, _, rfl⟩
  | subst => simp [isObjectPattern] at object

variable [laws : BlockSignature language block]

/-- **The type of a named multiset's argument**: a bag over another sort than processes, declared by some
constructor's parameter. -/
def MultisetType (language : LanguageDef) (block : Block) (type : TypeExpr) : Prop :=
  ∃ sort, sort ≠ block.proc ∧ type = .collection .hashBag (.base sort) ∧
    ∃ rule ∈ language.terms, ∃ parameter ∈ rule.params, CollectionTypeOccurs .hashBag (.base sort) parameter.typeExpr

/-- The types a hole may have: a base sort, or the type of a named multiset's argument. -/
def HoleType (language : LanguageDef) (block : Block) (type : TypeExpr) : Prop :=
  (∃ sort, type = .base sort) ∨ MultisetType language block type

omit laws in
theorem representation_of_collection {parameter : TermParam} {argument : Pattern} {elementType : TypeExpr}
    (typeIs : parameterType? parameter = some (.collection .hashBag elementType)) :
    MatchesParameterRepresentation parameter argument := by
  cases parameter with
  | simple => trivial
  | abstractionNamed binder name type =>
      cases type <;> simp [parameterType?] at typeIs
  | multiAbstractionNamed binders name type =>
      cases type with
      | arrow domain codomain => cases domain <;> simp [parameterType?] at typeIs
      | _ => simp [parameterType?] at typeIs

omit laws in
theorem append_cons_parameters {before before' after after' : List TermParam} {parameter parameter' : TermParam}
    (equal : before ++ parameter :: after = before' ++ parameter' :: after') (lengths : before.length = before'.length) :
    parameter = parameter' := by
  have := List.append_inj equal lengths
  simp only [List.cons.injEq] at this
  exact this.2.1

include laws in
/-- **Typing at a hole, for two fillings at once**: two fillings of one context, both typed at a base sort, at the
type of abstractions between base sorts, or at a bag over another sort, are typed at one hole type, under one context
of base sorts, and every term of that type can be put back. -/
theorem fill_typed_pair {free : FreeTypeContext} :
    ∀ (context : OneHoleContext) {bound : List TypeExpr} {first second : Pattern} {type : TypeExpr},
      BaseContext free bound → HasType language free bound (context.fill first) type →
      HasType language free bound (context.fill second) type →
      ((∃ sort, type = .base sort) ∨ (∃ domain sort, type = .arrow (.base domain) (.base sort)) ∨
        MultisetType language block type) →
      isObjectPattern (context.fill first) = true → isObjectPattern (context.fill second) = true →
      (∀ binder body, first ≠ .lambda binder body) →
      ∃ holeBound holeType, BaseContext free holeBound ∧ HoleType language block holeType ∧
        HasType language free holeBound first holeType ∧ HasType language free holeBound second holeType ∧
        ∀ replacement, HasType language free holeBound replacement holeType →
          HasType language free bound (context.fill replacement) type
  | .hole, bound, first, second, type, baseContext, firstTyped, secondTyped, typeIs, firstObject, _,
      firstNotLambda => by
      rcases typeIs with ⟨sort, rfl⟩ | ⟨domain, sort, rfl⟩ | multiset
      · exact ⟨bound, _, baseContext, .inl ⟨sort, rfl⟩, firstTyped, secondTyped, fun _ replaced => replaced⟩
      · obtain ⟨binder, body, rfl⟩ := lambda_of_arrow baseContext firstTyped firstObject
        exact absurd rfl (firstNotLambda binder body)
      · exact ⟨bound, _, baseContext, .inr multiset, firstTyped, secondTyped, fun _ replaced => replaced⟩
  | .apply label before inner after, bound, first, second, type, baseContext, firstTyped, secondTyped, typeIs,
      firstObject, secondObject, firstNotLambda => by
      simp only [OneHoleContext.fill] at firstTyped secondTyped firstObject secondObject
      obtain ⟨rule, member, labelEq, notBare, typeEq, arguments⟩ := hasType_apply_inversion firstTyped
      obtain ⟨rule', member', labelEq', -, -, arguments'⟩ := hasType_apply_inversion secondTyped
      obtain rfl := laws.rule_eq_of_label member member' (labelEq.symm.trans labelEq')
      obtain ⟨beforeParameters, parameter, afterParameters, expected, parametersEq, lengthIs,
          beforeTyped, representation, parameterType, middleTyped, afterTyped⟩ :=
        ArgumentsHaveTypes.append_cons_split arguments
      obtain ⟨beforeParameters', parameter', afterParameters', expected', parametersEq', lengthIs', -, -,
          parameterType', middleTyped', -⟩ := ArgumentsHaveTypes.append_cons_split arguments'
      obtain rfl := append_cons_parameters (parametersEq.symm.trans parametersEq') (lengthIs.trans lengthIs'.symm)
      rw [parameterType, Option.some.injEq] at parameterType'
      subst parameterType'
      have expectedIs : (∃ sort, expected = .base sort) ∨
          (∃ domain sort, expected = .arrow (.base domain) (.base sort)) ∨ MultisetType language block expected := by
        by_cases isMultiset : rule.label ∈ block.multisets
        · obtain ⟨-, -, parameterName, sort, params, other⟩ := laws.multisetShape rule member isMultiset
          have present : parameter ∈ rule.params := by rw [parametersEq]; simp
          have carrier : ∃ rule ∈ language.terms, ∃ parameter ∈ rule.params,
              CollectionTypeOccurs .hashBag (.base sort) parameter.typeExpr :=
            ⟨rule, member, parameter, present, by
              rw [params, List.mem_singleton] at present
              subst present
              exact .here⟩
          rw [params, List.mem_singleton] at present
          subst present
          simp only [parameterType?, Option.some.injEq] at parameterType
          exact .inr (.inr ⟨sort, other, parameterType.symm, carrier⟩)
        rcases laws.params rule member notBare isMultiset parameter (by rw [parametersEq]; simp) with
          ⟨sort, shape⟩ | ⟨domain, sort, shape⟩
        · rw [parameterType, Option.some.injEq] at shape
          exact .inl ⟨sort, shape⟩
        · rw [parameterType, Option.some.injEq] at shape
          exact .inr (.inl ⟨domain, sort, shape⟩)
      have firstMiddleObject : isObjectPattern (inner.fill first) = true := isObject_apply_member firstObject
      have secondMiddleObject : isObjectPattern (inner.fill second) = true := isObject_apply_member secondObject
      obtain ⟨holeBound, holeType, holeContext, holeKind, firstHole, secondHole, rebuild⟩ :=
        fill_typed_pair inner baseContext middleTyped middleTyped' expectedIs firstMiddleObject secondMiddleObject
          firstNotLambda
      refine ⟨holeBound, holeType, holeContext, holeKind, firstHole, secondHole, fun replacement replaced => ?_⟩
      subst typeEq labelEq
      simp only [OneHoleContext.fill]
      apply HasType.constructor member notBare
      rw [parametersEq]
      have kept : MatchesParameterRepresentation parameter (inner.fill replacement) := by
        rcases expectedIs with ⟨sort, rfl⟩ | ⟨domain, sort, rfl⟩ | ⟨sort, -, rfl, -⟩
        · exact representation_of_base parameterType
        · obtain ⟨binder, body, isLambda⟩ := lambda_of_arrow baseContext middleTyped firstMiddleObject
          rcases fill_eq_lambda isLambda with ⟨rfl, rfl⟩ | ⟨inner', rfl⟩
          · exact absurd rfl (firstNotLambda binder body)
          · exact representation_lambda (first := inner'.fill first) (by simpa [OneHoleContext.fill] using
              (show MatchesParameterRepresentation parameter (OneHoleContext.fill (.lambda binder inner') first)
                from representation))
        · exact representation_of_collection parameterType
      exact argumentsHaveTypes_join kept parameterType (rebuild replacement replaced) afterTyped beforeTyped
  | .lambda binder inner, bound, first, second, type, baseContext, firstTyped, secondTyped, typeIs, firstObject,
      secondObject, firstNotLambda => by
      simp only [OneHoleContext.fill] at firstTyped secondTyped firstObject secondObject
      rcases typeIs with ⟨sort, rfl⟩ | ⟨domain, sort, rfl⟩ | ⟨sort, -, rfl, -⟩
      · exact (lambda_untyped firstTyped).elim
      · cases firstTyped with
        | lambda firstBody =>
            cases secondTyped with
            | lambda secondBody =>
                simp only [isObjectPattern] at firstObject secondObject
                obtain ⟨holeBound, holeType, holeContext, holeKind, firstHole, secondHole, rebuild⟩ :=
                  fill_typed_pair inner (baseContext.cons domain) firstBody secondBody (.inl ⟨sort, rfl⟩) firstObject
                    secondObject firstNotLambda
                exact ⟨holeBound, holeType, holeContext, holeKind, firstHole, secondHole, fun replacement replaced =>
                  HasType.lambda (rebuild replacement replaced)⟩
      · cases firstTyped
  | .multiLambda arity binders inner, bound, first, second, type, baseContext, firstTyped, secondTyped, typeIs,
      firstObject, secondObject, firstNotLambda => by
      simp only [OneHoleContext.fill] at firstTyped
      rcases typeIs with ⟨sort, rfl⟩ | ⟨domain, sort, rfl⟩ | ⟨sort, -, rfl, -⟩ <;> cases firstTyped
  | .substBody inner replacement, bound, first, second, type, baseContext, firstTyped, secondTyped, typeIs,
      firstObject, secondObject, firstNotLambda => by
      simp [OneHoleContext.fill, isObjectPattern] at firstObject
  | .substReplacement body inner, bound, first, second, type, baseContext, firstTyped, secondTyped, typeIs,
      firstObject, secondObject, firstNotLambda => by
      simp [OneHoleContext.fill, isObjectPattern] at firstObject
  | .collection kind before inner after rest, bound, first, second, type, baseContext, firstTyped, secondTyped,
      typeIs, firstObject, secondObject, firstNotLambda => by
      simp only [OneHoleContext.fill] at firstTyped secondTyped firstObject secondObject
      rcases typeIs with ⟨sort, rfl⟩ | ⟨domain, sort, rfl⟩ | ⟨sort, other, rfl, -⟩
      · obtain ⟨rfl, rfl, elementsTyped⟩ := laws.bag_members firstTyped
        obtain ⟨-, -, elementsTyped'⟩ := laws.bag_members secondTyped
        obtain ⟨beforeTyped, middleTyped, afterTyped⟩ := ElementsHaveType.append_cons_split elementsTyped
        obtain ⟨-, middleTyped', -⟩ := ElementsHaveType.append_cons_split elementsTyped'
        obtain ⟨holeBound, holeType, holeContext, holeKind, firstHole, secondHole, rebuild⟩ :=
          fill_typed_pair inner baseContext middleTyped middleTyped' (.inl ⟨block.proc, rfl⟩)
            (isObject_collection_member firstObject) (isObject_collection_member secondObject) firstNotLambda
        refine ⟨holeBound, holeType, holeContext, holeKind, firstHole, secondHole, fun replacement replaced => ?_⟩
        simp only [OneHoleContext.fill]
        apply laws.bag_typed
        apply elementsHaveType_iff.mpr
        intro element membership
        simp only [List.mem_append, List.mem_cons] at membership
        rcases membership with inBefore | rfl | inAfter
        · exact elementsHaveType_iff.mp beforeTyped element inBefore
        · exact rebuild replacement replaced
        · exact elementsHaveType_iff.mp afterTyped element inAfter
      · rcases hasType_collection_inversion firstTyped with ⟨_, typeIs', _⟩ | ⟨_, _, _, _, _, typeIs', _⟩ <;>
          cases typeIs'
      · rcases hasType_collection_inversion firstTyped with ⟨elementType, typeIs', elementsTyped⟩ |
          ⟨_, _, _, _, _, typeIs', _⟩
        swap
        · cases typeIs'
        rcases hasType_collection_inversion secondTyped with ⟨elementType', typeIs'', elementsTyped'⟩ |
          ⟨_, _, _, _, _, typeIs'', _⟩
        swap
        · cases typeIs''
        simp only [TypeExpr.collection.injEq] at typeIs' typeIs''
        obtain ⟨rfl, rfl⟩ := typeIs'
        obtain ⟨-, rfl⟩ := typeIs''
        obtain ⟨beforeTyped, middleTyped, afterTyped⟩ := ElementsHaveType.append_cons_split elementsTyped
        obtain ⟨-, middleTyped', -⟩ := ElementsHaveType.append_cons_split elementsTyped'
        obtain ⟨holeBound, holeType, holeContext, holeKind, firstHole, secondHole, rebuild⟩ :=
          fill_typed_pair inner baseContext middleTyped middleTyped' (.inl ⟨sort, rfl⟩)
            (isObject_collection_member firstObject) (isObject_collection_member secondObject) firstNotLambda
        refine ⟨holeBound, holeType, holeContext, holeKind, firstHole, secondHole, fun replacement replaced => ?_⟩
        simp only [OneHoleContext.fill]
        apply HasType.collection
        apply elementsHaveType_iff.mpr
        intro element membership
        simp only [List.mem_append, List.mem_cons] at membership
        rcases membership with inBefore | rfl | inAfter
        · exact elementsHaveType_iff.mp beforeTyped element inBefore
        · exact rebuild replacement replaced
        · exact elementsHaveType_iff.mp afterTyped element inAfter

include laws in
/-- **Typing at a hole**: a filled context of a base sort, of the type of abstractions between base sorts, or of a
bag over another sort, types a filling that is no abstraction at a hole type, under some context of base sorts, and
every term of that type can be put back. -/
theorem fill_typed {free : FreeTypeContext} (context : OneHoleContext) {bound : List TypeExpr} {original : Pattern}
    {type : TypeExpr} (baseContext : BaseContext free bound) (typed : HasType language free bound (context.fill original) type)
    (typeIs : (∃ sort, type = .base sort) ∨ (∃ domain sort, type = .arrow (.base domain) (.base sort)) ∨
      MultisetType language block type)
    (object : isObjectPattern (context.fill original) = true) (notLambda : ∀ binder body, original ≠ .lambda binder body) :
    ∃ holeBound holeType, BaseContext free holeBound ∧ HoleType language block holeType ∧
      HasType language free holeBound original holeType ∧
      ∀ replacement, HasType language free holeBound replacement holeType →
        HasType language free bound (context.fill replacement) type := by
  obtain ⟨holeBound, holeType, holeContext, holeKind, originalTyped, -, rebuild⟩ :=
    fill_typed_pair context baseContext typed typed typeIs object object notLambda
  exact ⟨holeBound, holeType, holeContext, holeKind, originalTyped, rebuild⟩

/-! ## Typed terms carry no binder names -/

omit laws in
/-- Each argument of a typed application meets its parameter's representation and has its parameter's type. -/
theorem argument_typed {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ {arguments : List Pattern} {params : List TermParam},
      ArgumentsHaveTypes language free bound arguments params →
      ∀ argument ∈ arguments, ∃ param ∈ params, ∃ type, MatchesParameterRepresentation param argument ∧
        parameterType? param = some type ∧ HasType language free bound argument type
  | [], _, _, _, inside => by simp at inside
  | first :: rest, _, typed, argument, inside => by
    cases typed with
    | cons representation found firstTyped restTyped =>
      rcases List.mem_cons.mp inside with rfl | later
      · exact ⟨_, List.mem_cons_self, _, representation, found, firstTyped⟩
      · obtain ⟨param, member, type, represented, found', typed'⟩ := argument_typed restTyped argument later
        exact ⟨param, List.mem_cons_of_mem _ member, type, represented, found', typed'⟩

include laws in
/-- An abstraction argument has no display name. -/
theorem abstraction_binder {rule : GrammarRule} (member : rule ∈ language.terms) (notBare : ¬ UsesBareCollection rule)
    (notMultiset : rule.label ∉ block.multisets)
    {param : TermParam} (paramMember : param ∈ rule.params) {domain sort : String}
    (found : parameterType? param = some (.arrow (.base domain) (.base sort)))
    {binder : Option String} {body : Pattern} (representation : MatchesParameterRepresentation param (.lambda binder body)) :
    binder = none := by
  obtain ⟨declared, bodyName, rfl⟩ :=
    laws.arrowsAbstract rule member notBare notMultiset param paramMember domain sort found
  cases binder <;> simp_all [MatchesParameterRepresentation]

include laws in
/-- **A typed object term carries no binder names**, nor does the body of a typed abstraction, nor a bag over a
base sort. -/
theorem metadata_of_typed (term : Pattern) : ∀ {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr},
    HasType language free bound term type → isObjectPattern term = true →
      ((∃ sort, type = .base sort) → term.hasCanonicalBinderMetadata = true) ∧
      ((∃ domain sort, type = .arrow (.base domain) (.base sort)) → ∀ binder body, term = .lambda binder body →
        body.hasCanonicalBinderMetadata = true) ∧
      ((∃ sort, type = .collection .hashBag (.base sort)) → term.hasCanonicalBinderMetadata = true) := by
  induction term using Pattern.inductionOn with
  | hbvar => intros; exact ⟨fun _ => rfl, ⟨fun _ _ _ equal => (by cases equal), fun _ => rfl⟩⟩
  | hfvar => intros; exact ⟨fun _ => rfl, ⟨fun _ _ _ equal => (by cases equal), fun _ => rfl⟩⟩
  | happly label arguments recurse =>
    intro free bound type typed object
    obtain ⟨rule, member, labelIs, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
    refine ⟨fun _ => ?_, ⟨fun _ _ _ equal => (by cases equal), fun ⟨sort, collectionIs⟩ => ?_⟩⟩
    swap
    · rw [typeIs] at collectionIs
      cases collectionIs
    simp only [isObjectPattern, isObjectPatternList_iff] at object
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff]
    intro argument inside
    obtain ⟨param, paramMember, argumentType, representation, found, argumentTyped⟩ :=
      argument_typed argumentsTyped argument inside
    by_cases isMultiset : rule.label ∈ block.multisets
    · obtain ⟨-, -, parameterName, sort, params, -⟩ := laws.multisetShape rule member isMultiset
      rw [params, List.mem_singleton] at paramMember
      subst paramMember
      simp only [parameterType?, Option.some.injEq] at found
      subst found
      exact (recurse argument inside argumentTyped (object argument inside)).2.2 ⟨sort, rfl⟩
    rcases laws.params rule member notBare isMultiset param paramMember with ⟨sort, shape⟩ | ⟨domain, sort, shape⟩ <;>
      rw [found, Option.some.injEq] at shape <;> subst shape
    · exact (recurse argument inside argumentTyped (object argument inside)).1 ⟨sort, rfl⟩
    · cases argument with
      | bvar => rfl
      | fvar => rfl
      | lambda binder body =>
          cases abstraction_binder (block := block) member notBare isMultiset paramMember found representation
          simpa [Pattern.hasCanonicalBinderMetadata] using
            (recurse _ inside argumentTyped (object _ inside)).2.1 ⟨domain, sort, rfl⟩ none body rfl
      | apply => cases argumentTyped
      | multiLambda => cases argumentTyped
      | subst => exact absurd (object _ inside) (by simp [isObjectPattern])
      | collection => cases argumentTyped
  | hlambda binder body recurse =>
    intro free bound type typed object
    refine ⟨fun ⟨sort, typeIs⟩ => (by subst typeIs; exact (lambda_untyped typed).elim),
      ⟨fun ⟨domain, sort, typeIs⟩ _ _ equal => ?_, fun ⟨sort, typeIs⟩ => (by subst typeIs; cases typed)⟩⟩
    cases equal
    subst typeIs
    cases typed with
    | lambda bodyTyped => exact (recurse bodyTyped (by simpa [isObjectPattern] using object)).1 ⟨sort, rfl⟩
  | hmultiLambda arity binders body _ =>
    intro free bound type typed _
    refine ⟨fun ⟨sort, typeIs⟩ => (by subst typeIs; cases typed), ⟨fun _ _ _ equal => (by cases equal),
      fun ⟨sort, typeIs⟩ => (by subst typeIs; cases typed)⟩⟩
  | hsubst => intro _ _ _ _ object; simp [isObjectPattern] at object
  | hcollection kind elements rest recurse =>
    intro free bound type typed object
    simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_iff] at object
    refine ⟨fun ⟨sort, typeIs⟩ => ?_, ⟨fun _ _ _ equal => (by cases equal), fun ⟨sort, typeIs⟩ => ?_⟩⟩
    · subst typeIs
      simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff]
      obtain ⟨-, -, elementsTyped⟩ := laws.bag_members typed
      intro element inside
      exact (recurse element inside (elementsHaveType_iff.mp elementsTyped element inside) (object.2 element inside)).1
        ⟨block.proc, rfl⟩
    · subst typeIs
      simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff]
      rcases hasType_collection_inversion typed with ⟨elementType, typeIs', elementsTyped⟩ |
        ⟨_, _, _, _, _, typeIs', _⟩
      swap
      · cases typeIs'
      simp only [TypeExpr.collection.injEq] at typeIs'
      obtain ⟨-, rfl⟩ := typeIs'
      intro element inside
      exact (recurse element inside (elementsHaveType_iff.mp elementsTyped element inside) (object.2 element inside)).1
        ⟨sort, rfl⟩

/-! ## Bag laws under structural maps -/

/-- A map acting on bags member by member and fixing the unit. -/
structure Structural (block : Block) (map : Pattern → Pattern) : Prop where
  collection : ∀ kind elements rest, map (.collection kind elements rest) = .collection kind (elements.map map) rest
  unit : map (.apply block.unit []) = .apply block.unit []

theorem members_of_bag {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    {rest : Option String} (typed : HasType language free bound (.collection .hashBag elements rest) (.base block.proc)) :
    Members language block free bound elements :=
  fun element member => elementsHaveType_iff.mp (laws.bag_members typed).2.2 element member

/-- **A structural map carries a bag law to a bag law**, once either side of the image is a process; the other side
is one too. -/
theorem derived_map {map : Pattern → Pattern} (structural : Structural block map) {free : FreeTypeContext}
    {bound : List TypeExpr} {source target : Pattern} (derived : DerivedInstance language source target)
    (typed : HasType language free bound (map source) (.base block.proc) ∨
      HasType language free bound (map target) (.base block.proc)) :
    DerivedInstance language (map source) (map target) ∧
      HasType language free bound (map source) (.base block.proc) := by
  cases derived with
  | @bagPerm _ elements elements' _ _ permutation =>
      rw [structural.collection, structural.collection] at typed ⊢
      have sourceTyped : HasType language free bound (.collection .hashBag (elements.map map) none)
          (.base block.proc) := by
        rcases typed with typed | typed
        · exact typed
        · exact bag_typed fun element member =>
            members_of_bag typed element ((permutation.map map).mem_iff.mp member)
      exact ⟨DerivedInstance.bagPerm_of_sorted ⟨free, bound, sourceTyped⟩ (permutation.map map), sourceTyped⟩
  | setPerm declaration kindTyped _ => exact absurd kindTyped (laws.no_set_rule declaration)
  | setDedup declaration kindTyped => exact absurd kindTyped (laws.no_set_rule declaration)
  | @flatten rule _ _ pre inner post declaration flat _ =>
      obtain ⟨rfl, -⟩ := laws.algebra_shape declaration
      obtain ⟨bag, algebraRule, category⟩ := laws.algebra
      simp only [structural.collection, List.map_append, List.map_cons] at typed ⊢
      have sourceTyped : HasType language free bound (.collection .hashBag (List.map map pre ++
          .collection .hashBag (List.map map inner) none :: List.map map post) none) (.base block.proc) := by
        rcases typed with typed | typed
        · exact typed
        · have members := members_of_bag typed
          apply bag_typed
          intro element member
          simp only [List.mem_append, List.mem_cons] at member
          rcases member with inBefore | rfl | inAfter
          · exact members element (by simp [inBefore])
          · exact bag_typed fun inner member => members inner (by simp [member])
          · exact members element (by simp [inAfter])
      exact ⟨laws.flatten sourceTyped, sourceTyped⟩
  | singleton declaration flat _ =>
      obtain ⟨rfl, -⟩ := laws.algebra_shape declaration
      simp only [structural.collection, List.map_cons, List.map_nil] at typed ⊢
      have sourceTyped : HasType language free bound (.collection .hashBag [map target] none) (.base block.proc) := by
        rcases typed with typed | typed
        · exact typed
        · exact bag_typed fun element member => by
            rw [List.mem_singleton.mp member]
            exact typed
      exact ⟨laws.singleton (members_of_bag sourceTyped _ List.mem_cons_self), sourceTyped⟩
  | @unitElim _ _ _ unit pre post declaration unitIs _ =>
      obtain ⟨rfl, named⟩ := laws.algebra_shape declaration
      rw [unitIs, Option.some.injEq] at named
      subst named
      simp only [structural.collection, List.map_append, List.map_cons, structural.unit] at typed ⊢
      have sourceTyped : HasType language free bound (.collection .hashBag (List.map map pre ++
          .apply block.unit [] :: List.map map post) none) (.base block.proc) := by
        rcases typed with typed | typed
        · exact typed
        · have members := members_of_bag typed
          apply bag_typed
          intro element member
          simp only [List.mem_append, List.mem_cons] at member
          rcases member with inBefore | rfl | inAfter
          · exact members element (by simp [inBefore])
          · exact laws.unit_typed
          · exact members element (by simp [inAfter])
      exact ⟨laws.unitElim sourceTyped, sourceTyped⟩
  | @emptyUnit _ _ _ unit declaration unitIs _ =>
      obtain ⟨rfl, named⟩ := laws.algebra_shape declaration
      rw [unitIs, Option.some.injEq] at named
      subst named
      simp only [structural.collection, List.map_nil, structural.unit] at typed ⊢
      have sourceTyped : HasType language free bound (.collection .hashBag [] none) (.base block.proc) :=
        bag_typed Members.nil
      exact ⟨laws.emptyUnit, sourceTyped⟩

/-! ## A law at a multiset's argument -/

omit laws in
/-- An application has no collection type. -/
theorem apply_not_collection {free : FreeTypeContext} {bound : List TypeExpr} {constructor : String}
    {arguments : List Pattern} {kind : CollType} {elementType : TypeExpr}
    (typed : HasType language free bound (.apply constructor arguments) (.collection kind elementType)) : False := by
  obtain ⟨_, _, _, _, typeIs, _⟩ := hasType_apply_inversion typed
  cases typeIs

omit laws in
/-- **A typed object of a collection type is a collection**, in a context of base sorts. -/
theorem collection_of_typed {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {term : Pattern} {kind : CollType} {elementType : TypeExpr}
    (typed : HasType language free bound term (.collection kind elementType)) (object : isObjectPattern term = true) :
    ∃ kind' elements rest, term = .collection kind' elements rest := by
  cases term with
  | collection kind' elements rest => exact ⟨kind', elements, rest, rfl⟩
  | bvar index =>
      cases typed with
      | bvar lookup =>
          obtain ⟨sort, isBase⟩ := context.bound _ (List.mem_of_getElem? lookup)
          cases isBase
  | fvar name =>
      cases typed with
      | fvar lookup =>
          obtain ⟨sort, isBase⟩ := context.free name _ lookup
          cases isBase
  | apply constructor arguments => exact (apply_not_collection typed).elim
  | lambda binder body => cases typed
  | multiLambda arity binders body => cases typed
  | subst body replacement => simp [isObjectPattern] at object

include laws in
/-- **At a multiset's argument, a law is a reordering of the multiset**: under a map acting on bags member by member
and keeping applications applications, a law whose two images have the type of a multiset's argument is an instance
of the bag's reordering. -/
theorem generator_at_multiset {map : Pattern → Pattern} (structural : Structural block map)
    (applies : ∀ constructor arguments, ∃ arguments', map (.apply constructor arguments) = .apply constructor arguments')
    {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {source target : Pattern} (generator : BlockGenerator language block source target) {type : TypeExpr}
    (multiset : MultisetType language block type)
    (sourceTyped : HasType language free bound (map source) type)
    (targetTyped : HasType language free bound (map target) type)
    (targetObject : isObjectPattern (map target) = true) :
    DerivedInstance language (map source) (map target) := by
  obtain ⟨sort, other, rfl, rule, member, parameter, parameterMember, occurs⟩ := multiset
  have notApply : ∀ constructor arguments, ¬ HasType language free bound (map (.apply constructor arguments))
      (.collection .hashBag (.base sort)) := by
    intro constructor arguments typed
    obtain ⟨arguments', equal⟩ := applies constructor arguments
    rw [equal] at typed
    exact apply_not_collection typed
  have membersTyped : ∀ {elements : List Pattern},
      HasType language free bound (.collection .hashBag elements none) (.collection .hashBag (.base sort)) →
      ∀ element ∈ elements, HasType language free bound element (.base sort) := by
    intro elements typed element inside
    rcases hasType_collection_inversion typed with ⟨elementType, typeIs, elementsTyped⟩ |
      ⟨_, _, _, _, _, typeIs, _⟩
    · simp only [TypeExpr.collection.injEq, true_and] at typeIs
      subst typeIs
      exact elementsHaveType_iff.mp elementsTyped element inside
    · cases typeIs
  cases generator with
  | nil binder => exact (notApply _ _ sourceTyped).elim
  | nilReverse => exact (notApply _ _ sourceTyped).elim
  | extrusionReverse => exact (notApply _ _ sourceTyped).elim
  | exchange => exact (notApply _ _ sourceTyped).elim
  | emptyUnit => exact (notApply _ _ sourceTyped).elim
  | emptyUnitReverse => exact (notApply _ _ sourceTyped).elim
  | extrusion members selected binder body inside chosen =>
      rw [structural.collection] at sourceTyped
      have selectedTyped := membersTyped sourceTyped _ (List.mem_map_of_mem (List.getElem_mem inside))
      rw [chosen] at selectedTyped
      obtain ⟨arguments', equal⟩ := applies block.restrict [.lambda binder body]
      rw [equal] at selectedTyped
      obtain ⟨restrictRule, restrictMember, labelIs, -, typeIs, -⟩ := hasType_apply_inversion selectedTyped
      simp only [TypeExpr.base.injEq] at typeIs
      exact absurd (typeIs.trans (laws.restrictShape restrictRule restrictMember labelIs.symm).1) other
  | derived derivedInstance =>
      cases derivedInstance with
      | @bagPerm _ elements elements' _ _ permutation =>
          rw [structural.collection] at sourceTyped ⊢
          rw [structural.collection]
          exact .bagPerm member ⟨parameter, parameterMember, .base sort, occurs, free, bound, sourceTyped⟩
            (permutation.map map)
      | setPerm declaration kindTyped _ => exact absurd kindTyped (laws.no_set_rule declaration)
      | setDedup declaration kindTyped => exact absurd kindTyped (laws.no_set_rule declaration)
      | @flatten _ _ _ pre inner post algebraRule _ _ =>
          obtain ⟨rfl, -⟩ := laws.algebra_shape algebraRule
          rw [structural.collection] at sourceTyped
          have innerTyped := membersTyped sourceTyped (map (.collection .hashBag inner none)) (by simp)
          rw [structural.collection] at innerTyped
          exact absurd (laws.bag_members innerTyped).2.1 other
      | @singleton _ _ _ element algebraRule _ _ =>
          obtain ⟨rfl, -⟩ := laws.algebra_shape algebraRule
          obtain ⟨kind', elements, rest, isCollection⟩ := collection_of_typed context targetTyped
            targetObject
          rw [structural.collection] at sourceTyped
          have elementTyped := membersTyped sourceTyped (map target) (by simp)
          rw [isCollection] at elementTyped
          exact absurd (laws.bag_members elementTyped).2.1 other
      | @unitElim _ _ _ unit pre post algebraRule declaredUnit _ =>
          obtain ⟨rfl, unitIs⟩ := laws.algebra_shape algebraRule
          rw [declaredUnit, Option.some.injEq] at unitIs
          subst unitIs
          rw [structural.collection] at sourceTyped
          have unitTyped := membersTyped sourceTyped (map (.apply block.unit [])) (by simp)
          rw [structural.unit] at unitTyped
          obtain ⟨unitRule, unitMember, labelIs, -, typeIs, -⟩ := hasType_apply_inversion unitTyped
          simp only [TypeExpr.base.injEq] at typeIs
          exact absurd (typeIs.trans (laws.unitShape unitRule unitMember labelIs.symm)) other
      | @emptyUnit _ _ _ unit algebraRule declaredUnit _ =>
          obtain ⟨-, unitIs⟩ := laws.algebra_shape algebraRule
          rw [declaredUnit, Option.some.injEq] at unitIs
          subst unitIs
          rw [structural.unit] at targetTyped
          exact (apply_not_collection targetTyped).elim

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
