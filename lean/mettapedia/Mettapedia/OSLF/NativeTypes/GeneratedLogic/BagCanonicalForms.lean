import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions
import Mettapedia.OSLF.MeTTaIL.CanonicalBags
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Canonical forms for bags

A language whose collections are bags reads them modulo the order of their elements: its bag laws
permute the elements of a bag sorted at a bag carrier. Sorting every bag bottom up
(`CanonicalBags.canon`) gives canonical forms in the sense of `Canonical`, and rules whose premises are
guards, or queries over captured values in a relation environment that respects canonical forms, are
coherent with them. The front door computes them by structural recursion (`sortBags`, equal to
`canon` by `sortBags_eq`), which the kernel evaluates.

- **The domain** (`domain`): object terms with no set whose canonical form sorts every bag at a bag
  carrier of the language, by the well-sortedness checker.
- **Canonical forms** (`canonical`): in a language with no authored equations and no collection
  algebra, an admitted term is equivalent to its canonical form (`equivalent_canon`), and equivalent
  terms have the same canonical form (`canon_eq_of_equivalent`).
- **Matching commutes with sorting** (`matchRel_canon`): a match at a term with no set is a match at its
  canonical form, with every capture replaced by its canonical form. A bag pattern's elements select
  from the sorted elements, and what remains of a sorted list is sorted, so a rest captures the
  canonical form of what it captured before.
- **Instantiation respects sorting** (`applyBindingsScoped_same`): captures with the same canonical
  forms give right sides with the same canonical form.
- **Coherence** (`coherent`): when every premise is a guard, a relation query with no arguments, a step
  from an admitted term is matched by a step of the same rule from its canonical form (`simulates`). A
  guard reads no binding, so it holds at canonical captures whenever it holds (`guards_canon`), in every
  relation environment.
- **Queries over captured values** (`coherentQueries`): a relation query whose arguments are
  metavariables reads the presentation of what they captured. When the relation environment respects
  canonical forms (`RespectsCanon`: the answers to the canonical forms of a query include the canonical
  forms of its answers), a query answered at a match is answered at the canonical match
  (`query_canon`), and such rules are coherent too. The builtin relations respect canonical forms
  (`builtin_canon`).

Sets are left out of the domain. The matcher selects a set's elements by position, as it does a
bag's, so `{A, A}` and `{A}` have different matches although the set laws identify them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagForms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
  (RelationEnv premiseStepWithEnv relationQueryStep matchRelationArgs builtinRelationTuples matchRelationArgument)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags
  (canon Same BagStep arrange Presents canon_collection canon_apply canon_idempotent to_canon setFree
    setFreeList setFreeList_iff setFree_collection arrange_bag arrange_vec same_refl same_of_bagStep same_map
    same_apply_congr same_collection_congr same_lambda_congr same_multiLambda_congr instantiateBVar_same
    same_collection same_splice select_partner arrange_eq arrange_eq_of_presents arrange_mem)
open Mettapedia.OSLF.MeTTaIL.PatternLexOrder (sortLex PatternLe sortLex_perm sortLex_pairwise)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.WellSorted
  (isObjectPattern isObjectPatternList FreeTypeContext checkOpenPatternWellSorted checkOpenPatternWellSorted_sound)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance SortedAt CollectionCarrierRule AlgebraRule)

/-! ## What sorting keeps -/

theorem objectList_eq_all : ∀ patterns : List Pattern, isObjectPatternList patterns = patterns.all isObjectPattern
  | [] => rfl
  | pattern :: patterns => by simp [isObjectPatternList, objectList_eq_all patterns]

theorem objectList_iff (patterns : List Pattern) :
    isObjectPatternList patterns = true ↔ ∀ pattern ∈ patterns, isObjectPattern pattern = true := by
  rw [objectList_eq_all, List.all_eq_true]

theorem setFreeList_eq_all : ∀ patterns : List Pattern, setFreeList patterns = patterns.all setFree
  | [] => rfl
  | pattern :: patterns => by simp [setFreeList, setFreeList_eq_all patterns]

private theorem all_eq_of_members {test : Pattern → Bool} {left right : List Pattern}
    (members : ∀ a, a ∈ left ↔ a ∈ right) : left.all test = right.all test :=
  Bool.eq_iff_iff.mpr (by
    simp only [List.all_eq_true]
    exact ⟨fun all a member => all a ((members a).mpr member), fun all a member => all a ((members a).mp member)⟩)

/-- A permutation keeps objectness. -/
theorem bagStep_object {left right : Pattern} (step : BagStep left right) :
    isObjectPattern left = isObjectPattern right := by
  induction step with
  | permute _ permutation =>
    simp only [isObjectPattern, objectList_eq_all, all_eq_of_members fun a => permutation.mem_iff]
  | members same => simp only [isObjectPattern, objectList_eq_all, all_eq_of_members same]
  | apply _ ih => simp only [isObjectPattern, objectList_eq_all, List.all_append, List.all_cons, ih]
  | lambda _ ih => simp only [isObjectPattern, ih]
  | multiLambda _ ih => simp only [isObjectPattern, ih]
  | substBody _ _ => simp only [isObjectPattern]
  | substReplacement _ _ => simp only [isObjectPattern]
  | element _ ih => simp only [isObjectPattern, objectList_eq_all, List.all_append, List.all_cons, ih]

/-- A permutation keeps the absence of sets. -/
theorem bagStep_setFree {left right : Pattern} (step : BagStep left right) : setFree left = setFree right := by
  induction step with
  | permute _ permutation =>
    simp only [setFree, setFreeList_eq_all, all_eq_of_members fun a => permutation.mem_iff]
  | members same => simp only [setFree, setFreeList_eq_all, all_eq_of_members same]
  | apply _ ih => simp only [setFree, setFreeList_eq_all, List.all_append, List.all_cons, ih]
  | lambda _ ih => simp only [setFree, ih]
  | multiLambda _ ih => simp only [setFree, ih]
  | substBody _ ih => simp only [setFree, ih]
  | substReplacement _ ih => simp only [setFree, ih]
  | element _ ih => simp only [setFree, setFreeList_eq_all, List.all_append, List.all_cons, ih]

theorem eqvGen_invariant {α : Type} {test : Pattern → α} (keeps : ∀ {a b : Pattern}, BagStep a b → test a = test b)
    {a b : Pattern} (related : Relation.EqvGen BagStep a b) : test a = test b := by
  induction related with
  | rel _ _ step => exact keeps step
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem canon_object (term : Pattern) : isObjectPattern (canon term) = isObjectPattern term :=
  (eqvGen_invariant bagStep_object (to_canon term)).symm

theorem canon_setFree (term : Pattern) : setFree (canon term) = setFree term :=
  (eqvGen_invariant bagStep_setFree (to_canon term)).symm

theorem canon_wellScoped (term : Pattern) (depth : ℕ) :
    (canon term).isWellScopedAt depth = term.isWellScopedAt depth :=
  (eqvGen_invariant (fun step => step.wellScoped depth) (to_canon term)).symm

/-! ## Sorting by structural recursion -/

mutual
/-- `CanonicalBags.canon` by structural recursion: every bag sorted, every set sorted without repetition,
bottom up. -/
def sortBags : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply label arguments => .apply label (sortBagsList arguments)
  | .lambda binder body => .lambda binder (sortBags body)
  | .multiLambda arity binders body => .multiLambda arity binders (sortBags body)
  | .subst body replacement => .subst (sortBags body) (sortBags replacement)
  | .collection kind elements rest => .collection kind (arrange kind (sortBagsList elements)) rest

/-- Sorting each term of a list. -/
def sortBagsList : List Pattern → List Pattern
  | [] => []
  | pattern :: patterns => sortBags pattern :: sortBagsList patterns
end

theorem sortBagsList_eq_map : ∀ patterns : List Pattern, sortBagsList patterns = patterns.map sortBags
  | [] => rfl
  | pattern :: patterns => by simp only [sortBagsList, List.map_cons, sortBagsList_eq_map patterns]

/-- **Structural sorting is `canon`.** -/
theorem sortBags_eq : ∀ pattern : Pattern, sortBags pattern = canon pattern
  | .bvar _ => by rw [canon, sortBags]
  | .fvar _ => by rw [canon, sortBags]
  | .apply label arguments => by
    rw [canon_apply, sortBags, sortBagsList_eq_map]
    congr 1
    exact List.map_congr_left fun argument member =>
      have : sizeOf argument < sizeOf (Pattern.apply label arguments) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
      sortBags_eq argument
  | .lambda binder body => by rw [canon, sortBags, sortBags_eq body]
  | .multiLambda arity binders body => by rw [canon, sortBags, sortBags_eq body]
  | .subst body replacement => by rw [canon, sortBags, sortBags_eq body, sortBags_eq replacement]
  | .collection kind elements rest => by
    rw [canon_collection, sortBags, sortBagsList_eq_map]
    congr 2
    exact List.map_congr_left fun element member =>
      have : sizeOf element < sizeOf (Pattern.collection kind elements rest) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
      sortBags_eq element
termination_by pattern => sizeOf pattern

theorem sortBags_eq_canon : sortBags = canon := funext sortBags_eq

/-! ## The domain -/

/-- **A bag carrier**: a constructor whose one parameter is a bag. -/
def bagCarrier (rule : GrammarRule) : Bool :=
  match rule.params with
  | [.simple _ (.collection .hashBag _)] => true
  | _ => false

variable (language : LanguageDef)

/-- **A bag sorted at a bag carrier** of the language, by the well-sortedness checker. -/
def sortedBag (bag : Pattern) : Bool :=
  language.terms.any fun rule =>
    bagCarrier rule && checkOpenPatternWellSorted language FreeTypeContext.empty [] (.base rule.category) bag

mutual
/-- Every bag of a term is sorted at a bag carrier. -/
def bagsSorted : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .apply _ arguments => bagsSortedList arguments
  | .lambda _ body => bagsSorted body
  | .multiLambda _ _ body => bagsSorted body
  | .subst body replacement => bagsSorted body && bagsSorted replacement
  | .collection .hashBag elements rest =>
    sortedBag language (.collection .hashBag elements rest) && bagsSortedList elements
  | .collection _ elements _ => bagsSortedList elements

/-- Every bag of every term of a list is sorted at a bag carrier. -/
def bagsSortedList : List Pattern → Bool
  | [] => true
  | pattern :: patterns => bagsSorted pattern && bagsSortedList patterns
end

/-- **The domain**: object terms with no set whose canonical form sorts every bag at a bag carrier. -/
def domain (term : Pattern) : Bool :=
  isObjectPattern (sortBags term) && setFree (sortBags term) && bagsSorted language (sortBags term)

variable {language}

theorem bagsSortedList_iff : ∀ patterns : List Pattern,
    bagsSortedList language patterns = true ↔ ∀ pattern ∈ patterns, bagsSorted language pattern = true
  | [] => by simp [bagsSortedList]
  | pattern :: patterns => by simp [bagsSortedList, bagsSortedList_iff patterns]

theorem bagCarrier_sound {rule : GrammarRule} (carrier : bagCarrier rule = true) :
    ∃ parameterName elementType, rule.params = [.simple parameterName (.collection .hashBag elementType)] := by
  unfold bagCarrier at carrier
  split at carrier
  · rename_i name elementType parameters
    exact ⟨name, elementType, parameters⟩
  · cases carrier

/-- A sorted bag has a carrier and is sorted at its category. -/
theorem sortedBag_sound {bag : Pattern} (sorted : sortedBag language bag = true) :
    ∃ rule, CollectionCarrierRule language rule .hashBag ∧ SortedAt language bag rule.category := by
  obtain ⟨rule, member, checks⟩ := List.any_eq_true.mp sorted
  rw [Bool.and_eq_true] at checks
  exact ⟨rule, ⟨member, bagCarrier_sound checks.1⟩,
    ⟨FreeTypeContext.empty, [], (checkOpenPatternWellSorted_sound checks.2).1⟩⟩

/-! ## Canonical forms -/

variable {relEnv : RelationEnv}

/-- **An admitted term is equivalent to its canonical form**: each element is replaced by its canonical
form inside its context, and each bag is then sorted by one bag law, read from the sorted side. -/
theorem equivalent_canon : ∀ term : Pattern, isObjectPattern term = true → setFree term = true →
    bagsSorted language (canon term) = true → ObjectEquivalent relEnv language .syntax term (canon term)
  | .bvar _, _, _, _ => by rw [canon]; exact Relation.EqvGen.refl _
  | .fvar _, _, _, _ => by rw [canon]; exact Relation.EqvGen.refl _
  | .apply label arguments, object, free, sorted => by
    rw [canon_apply] at sorted ⊢
    have objects := (objectList_iff arguments).mp object
    have frees := setFreeList_iff.mp free
    have sorteds := (bagsSortedList_iff _).mp sorted
    have each : ∀ argument ∈ arguments,
        IsObject argument ∧ ObjectEquivalent relEnv language .syntax argument (canon argument) := fun argument member =>
      have : sizeOf argument < sizeOf (Pattern.apply label arguments) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
      ⟨objects argument member, equivalent_canon argument (objects argument member) (frees argument member)
        (sorteds _ (List.mem_map_of_mem member))⟩
    have congr := ObjectEquivalent.list_congr canon (fun pattern object => (canon_object pattern).trans object)
      (.apply label) (.apply label · .hole ·) (fun _ _ _ => rfl)
      (fun patterns all => (objectList_iff patterns).mpr all) arguments [] (fun _ member => nomatch member) each
    rw [List.nil_append, List.nil_append] at congr
    exact congr
  | .lambda binder body, object, free, sorted => by
    rw [canon] at sorted ⊢
    exact ObjectEquivalent.fill (.lambda binder .hole) (fun _ inner => inner) (equivalent_canon body object free sorted)
  | .multiLambda arity binders body, object, free, sorted => by
    rw [canon] at sorted ⊢
    exact ObjectEquivalent.fill (.multiLambda arity binders .hole) (fun _ inner => inner)
      (equivalent_canon body object free sorted)
  | .subst _ _, object, _, _ => by simp [isObjectPattern] at object
  | .collection kind elements rest, object, free, sorted => by
    cases rest with
    | some _ => simp [isObjectPattern] at object
    | none =>
      have objects : ∀ element ∈ elements, isObjectPattern element = true :=
        (objectList_iff elements).mp (by simpa [isObjectPattern] using object)
      obtain ⟨notSet, frees⟩ := setFree_collection free
      rw [canon_collection] at sorted ⊢
      have sortedElements : ∀ element ∈ elements, bagsSorted language (canon element) = true := by
        intro element member
        have inArranged : canon element ∈ arrange kind (elements.map canon) :=
          (arrange_mem _).mpr (List.mem_map_of_mem member)
        cases kind <;> simp only [bagsSorted, Bool.and_eq_true] at sorted
        · exact (bagsSortedList_iff _).mp sorted _ inArranged
        · exact (bagsSortedList_iff _).mp sorted.2 _ inArranged
        · exact (bagsSortedList_iff _).mp sorted _ inArranged
      have each : ∀ element ∈ elements,
          IsObject element ∧ ObjectEquivalent relEnv language .syntax element (canon element) := fun element member =>
        have : sizeOf element < sizeOf (Pattern.collection kind elements none) := by
          have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
        ⟨objects element member, equivalent_canon element (objects element member) (frees element member)
          (sortedElements element member)⟩
      have collectionObject : ∀ patterns : List Pattern, (∀ pattern ∈ patterns, IsObject pattern) →
          IsObject (.collection kind patterns none) := fun patterns all => by
        show isObjectPattern (.collection kind patterns none) = true
        simpa [isObjectPattern] using (objectList_iff patterns).mpr all
      have mapped := ObjectEquivalent.list_congr canon (fun pattern object => (canon_object pattern).trans object)
        (.collection kind · none) (.collection kind · .hole · none) (fun _ _ _ => rfl) collectionObject elements []
        (fun _ member => nomatch member) each
      rw [List.nil_append, List.nil_append] at mapped
      cases kind with
      | vec => exact mapped
      | hashSet => exact absurd rfl notSet
      | hashBag =>
        rw [arrange_bag] at sorted ⊢
        simp only [bagsSorted, Bool.and_eq_true] at sorted
        obtain ⟨_, _, sortedAt⟩ := sortedBag_sound sorted.1
        have mappedObject : ∀ pattern ∈ elements.map canon, IsObject pattern := by
          intro pattern member
          obtain ⟨element, inside, rfl⟩ := List.mem_map.mp member
          exact (canon_object element).trans (objects element inside)
        have step : ObjectStep relEnv language .syntax (.collection .hashBag (sortLex (elements.map canon)) none)
            (.collection .hashBag (elements.map canon) none) :=
          ⟨collectionObject _ fun pattern member => mappedObject pattern ((sortLex_perm _).subset member),
            collectionObject _ mappedObject,
            .inContext .hole (Or.inr (.bagPerm_of_sorted sortedAt (sortLex_perm _)))⟩
        exact Relation.EqvGen.trans _ _ _ mapped (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ step))
termination_by term => sizeOf term

/-- A permutation inside a context is a permutation. -/
theorem bagStep_fill (context : OneHoleContext) {left right : Pattern} (step : BagStep left right) :
    BagStep (context.fill left) (context.fill right) := by
  induction context with
  | hole => exact step
  | apply _ _ _ _ ih => exact .apply ih
  | lambda _ _ ih => exact .lambda ih
  | multiLambda _ _ _ ih => exact .multiLambda ih
  | substBody _ _ ih => exact .substBody ih
  | substReplacement _ _ ih => exact .substReplacement ih
  | collection _ _ _ _ _ ih => exact .element ih

/-- A language without collection-algebra declarations has no algebra rule. -/
theorem no_algebraRule (noAlgebra : language.hasAlgebraDeclarations = false) {rule : GrammarRule}
    {kind : CollType} {algebra : CollectionAlgebra} (declared : AlgebraRule language rule kind algebra) : False := by
  have declares : language.hasAlgebraDeclarations = true :=
    List.any_eq_true.mpr ⟨rule, declared.authored, by simp [declared.declared]⟩
  rw [noAlgebra] at declares
  cases declares

/-- **Each generator is a permutation** when no equation is authored and no algebra is declared. -/
theorem generator_bagStep (noEquations : language.equations = []) (noAlgebra : language.hasAlgebraDeclarations = false)
    {source target : Pattern} (generator : Generator relEnv language source target) : BagStep source target := by
  rcases generator with authored | derived
  · cases authored with
    | forward member _ _ _ => rw [noEquations] at member; cases member
    | reverse member _ _ _ => rw [noEquations] at member; cases member
    | declared member _ _ => rw [noEquations] at member; cases member
    | premised member _ _ _ => rw [noEquations] at member; cases member
  · cases derived with
    | bagPerm _ _ permutation => exact .permute rfl permutation
    | setPerm _ _ permutation => exact .permute rfl permutation
    | setDedup _ _ => exact .members fun a => by simp
    | flatten declared _ _ => exact (no_algebraRule noAlgebra declared).elim
    | singleton declared _ _ => exact (no_algebraRule noAlgebra declared).elim
    | unitElim declared _ _ => exact (no_algebraRule noAlgebra declared).elim
    | emptyUnit declared _ _ => exact (no_algebraRule noAlgebra declared).elim

/-- **Equivalent terms have the same canonical form.** -/
theorem canon_eq_of_equivalent (noEquations : language.equations = [])
    (noAlgebra : language.hasAlgebraDeclarations = false) {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv language .syntax first second) : canon first = canon second := by
  induction equivalent with
  | rel _ _ step =>
    obtain ⟨_, _, step⟩ := step
    cases step with
    | inContext context generator =>
      exact (bagStep_fill context (generator_bagStep noEquations noAlgebra generator)).canon_eq
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Sorting every bag gives canonical forms on the domain**, which is read off them. -/
theorem canonicalDetermined (noEquations : language.equations = [])
    (noAlgebra : language.hasAlgebraDeclarations = false) :
    CanonicalDetermined relEnv language sortBags (domain language) := by
  rw [sortBags_eq_canon]
  exact {
    object := fun admitted => by
      simp only [domain, sortBags_eq_canon, Bool.and_eq_true] at admitted
      exact (canon_object _).symm.trans admitted.1.1
    determined := fun term => by simp only [domain, sortBags_eq_canon, canon_idempotent]
    equivalent := fun admitted => by
      simp only [domain, sortBags_eq_canon, Bool.and_eq_true] at admitted
      exact equivalent_canon _ ((canon_object _).symm.trans admitted.1.1) ((canon_setFree _).symm.trans admitted.1.2)
        admitted.2
    same := fun _ equivalent => canon_eq_of_equivalent noEquations noAlgebra equivalent
    closed := fun _ => canon_wellScoped _ 0 }

/-- **Sorting every bag gives canonical forms on the domain.** -/
theorem canonical (noEquations : language.equations = []) (noAlgebra : language.hasAlgebraDeclarations = false) :
    Canonical relEnv language sortBags (domain language) :=
  (canonicalDetermined noEquations noAlgebra).canonical

/-! ## Matching commutes with sorting -/

/-- Every capture replaced by its canonical form. -/
def canonBindings (bindings : Bindings) : Bindings := bindings.map fun entry => (entry.1, canon entry.2)

theorem find?_canonBindings (bindings : Bindings) (name : String) :
    (canonBindings bindings).find? (fun entry : String × Pattern => entry.1 == name) =
      (bindings.find? (fun entry : String × Pattern => entry.1 == name)).map fun entry => (entry.1, canon entry.2) := by
  simp only [canonBindings, List.find?_map]
  rfl

/-- **Merging commutes with taking canonical forms**: equal captures stay equal. -/
theorem mergeBindings_canon : ∀ (second : Bindings) {first result : Bindings},
    mergeBindings first second = some result →
      mergeBindings (canonBindings first) (canonBindings second) = some (canonBindings result)
  | [], first, result, merged => by
    simp only [mergeBindings, List.foldlM_nil] at merged
    cases merged
    rfl
  | (name, value) :: rest, first, result, merged => by
    have unfold : ∀ (initial : Bindings) (entries : List (String × Pattern)) (entry : String × Pattern),
        mergeBindings initial (entry :: entries) =
          (match initial.find? (fun item : String × Pattern => item.1 == entry.1) with
            | none => some (entry :: initial)
            | some (_, existing) => if existing == entry.2 then some initial else none).bind
            fun accumulated => mergeBindings accumulated entries := by
      intro initial entries entry
      obtain ⟨entryName, entryValue⟩ := entry
      rfl
    rw [unfold] at merged
    rw [show canonBindings ((name, value) :: rest) = (name, canon value) :: canonBindings rest from rfl, unfold,
      find?_canonBindings]
    cases found : first.find? (·.1 == name) with
    | none =>
      rw [found] at merged
      exact mergeBindings_canon rest merged
    | some entry =>
      obtain ⟨entryName, existing⟩ := entry
      rw [found] at merged
      by_cases same : existing = value
      · subst same
        simp only [beq_self_eq_true, ↓reduceIte, Option.bind_some, Option.map_some] at merged ⊢
        exact mergeBindings_canon rest merged
      · simp [beq_iff_eq, same] at merged

mutual
/-- **A match at a term with no set is a match at its canonical form**, with canonical captures. -/
theorem matchRel_canon : ∀ (pattern term : Pattern) (bindings : Bindings), setFree term = true →
    MatchRel pattern term bindings → MatchRel pattern (canon term) (canonBindings bindings)
  | .fvar _, _, _, _, matched => by
    cases matched
    exact .fvar
  | .bvar _, _, _, _, matched => by
    cases matched
    rw [canon]
    exact .bvar
  | .apply label patterns, _, bindings, free, matched => by
    cases matched with
    | apply arguments lengths =>
      rename_i terms
      rw [canon_apply]
      exact .apply (matchArgsRel_canon patterns terms bindings (setFreeList_iff.mp free) arguments)
        (by rw [List.length_map]; exact lengths)
  | .lambda _ body, _, bindings, free, matched => by
    cases matched with
    | lambda inner =>
      rw [canon]
      exact .lambda (matchRel_canon body _ bindings free inner)
  | .multiLambda _ _ body, _, bindings, free, matched => by
    cases matched with
    | multiLambda inner =>
      rw [canon]
      exact .multiLambda (matchRel_canon body _ bindings free inner)
  | .collection kind patterns rest, _, bindings, free, matched => by
    cases matched with
    | collection notVector bag =>
      rename_i terms termRest
      obtain ⟨notSet, frees⟩ := setFree_collection free
      have bagKind : kind = .hashBag := by cases kind <;> simp_all
      subst bagKind
      rw [canon_collection, arrange_bag]
      refine .collection notVector (matchBagRel_canon patterns rest terms (sortLex (terms.map canon)) bindings frees
        (sortLex_perm _) (sortLex_pairwise _) ?_ bag)
      intro other member
      obtain ⟨term, _, rfl⟩ := List.mem_map.mp ((sortLex_perm _).subset member)
      exact canon_idempotent term
    | vector arguments =>
      rename_i terms termRest
      obtain ⟨_, frees⟩ := setFree_collection free
      rw [canon_collection, arrange_vec]
      exact .vector (matchArgsRel_canon patterns terms bindings frees arguments)
    | vectorRest prefixMatch merged =>
      rename_i prefixBindings name terms termRest
      obtain ⟨_, frees⟩ := setFree_collection free
      rw [canon_collection, arrange_vec]
      refine .vectorRest (prefixBindings := canonBindings prefixBindings) ?_ ?_
      · rw [← List.map_take]
        exact matchArgsRel_canon patterns (terms.take patterns.length) prefixBindings
          (fun term member => frees term (List.mem_of_mem_take member)) prefixMatch
      · have canonMerged := mergeBindings_canon _ merged
        simpa [canonBindings, canon_collection, arrange_vec, List.map_drop] using canonMerged
  | .subst body replacement, _, bindings, free, matched => by
    cases matched with
    | subst bodyMatch replacementMatch merged =>
      rename_i termBody first termReplacement second
      simp only [setFree, Bool.and_eq_true] at free
      rw [canon]
      exact .subst (matchRel_canon body termBody first free.1 bodyMatch)
        (matchRel_canon replacement termReplacement second free.2 replacementMatch) (mergeBindings_canon _ merged)
termination_by pattern => sizeOf pattern

/-- Argument lists. -/
theorem matchArgsRel_canon : ∀ (patterns terms : List Pattern) (bindings : Bindings),
    (∀ term ∈ terms, setFree term = true) →
    MatchArgsRel patterns terms bindings → MatchArgsRel patterns (terms.map canon) (canonBindings bindings)
  | [], _, _, _, matched => by
    cases matched
    exact .nil
  | pattern :: patterns, _, _, free, matched => by
    cases matched with
    | cons head tail merged =>
      rename_i term headBindings terms tailBindings
      exact .cons (matchRel_canon pattern term headBindings (free term List.mem_cons_self) head)
        (matchArgsRel_canon patterns terms tailBindings (fun other member => free other (List.mem_cons_of_mem _ member))
          tail)
        (mergeBindings_canon _ merged)
termination_by patterns => sizeOf patterns

/-- **Bags**: a selection from a bag's elements has a counterpart among the sorted canonical elements, and
the rest captures the sorted remainder. -/
theorem matchBagRel_canon : ∀ (patterns : List Pattern) (rest : Option String) (terms others : List Pattern)
    (bindings : Bindings), (∀ term ∈ terms, setFree term = true) → others.Perm (terms.map canon) →
    others.Pairwise PatternLe → (∀ other ∈ others, canon other = other) →
    MatchBagRel patterns rest .hashBag terms bindings → MatchBagRel patterns rest .hashBag others (canonBindings bindings)
  | [], none, _, others, _, _, perm, _, _, matched => by
    cases matched
    rw [List.map_nil, List.perm_nil] at perm
    subst perm
    exact .nilNoRest
  | [], some _, terms, others, _, _, perm, sorted, _, matched => by
    cases matched
    have arranged : others = sortLex (terms.map canon) :=
      List.Perm.eq_of_pairwise' sorted (sortLex_pairwise _) (perm.trans (sortLex_perm _).symm)
    simp only [canonBindings, List.map_cons, List.map_nil, canon_collection, arrange_bag, ← arranged]
    exact .nilRest
  | pattern :: patterns, rest, terms, others, _, free, perm, sorted, fixed, matched => by
    cases matched with
    | cons index within head tail merged =>
      rename_i headBindings restBindings
      have othersFixed : others.map canon = others := by
        conv_rhs => rw [← List.map_id others]
        exact List.map_congr_left fixed
      obtain ⟨partner, partnerWithin, same, remainder⟩ :=
        select_partner (targets := terms) (others := others) (by rw [othersFixed]; exact perm.symm) within
      have atPartner : canon terms[index] = others[partner] :=
        (show canon terms[index] = canon others[partner] from same).trans (fixed _ (List.getElem_mem partnerWithin))
      have head' := matchRel_canon pattern terms[index] headBindings (free _ (List.getElem_mem within)) head
      rw [atPartner] at head'
      have eraseFixed : (others.eraseIdx partner).map canon = others.eraseIdx partner := by
        conv_rhs => rw [← List.map_id (others.eraseIdx partner)]
        exact List.map_congr_left fun other member => fixed other (List.mem_of_mem_eraseIdx member)
      have tail' := matchBagRel_canon patterns rest (terms.eraseIdx index) (others.eraseIdx partner) restBindings
        (fun other member => free other (List.mem_of_mem_eraseIdx member))
        (by rw [← eraseFixed]; exact remainder.symm)
        (sorted.sublist (List.eraseIdx_sublist _ _))
        (fun other member => fixed other (List.mem_of_mem_eraseIdx member))
        tail
      exact .cons partner partnerWithin head' tail' (mergeBindings_canon _ merged)
termination_by patterns => sizeOf patterns
end

/-! ## Instantiation respects sorting -/

/-- Bindings with the same names, in order, and captures with the same canonical forms. -/
def BindingsSame (left right : Bindings) : Prop :=
  List.Forall₂ (fun first second => first.1 = second.1 ∧ Same first.2 second.2) left right

theorem bindingsSame_canon (bindings : Bindings) : BindingsSame (canonBindings bindings) bindings := by
  induction bindings with
  | nil => exact .nil
  | cons entry rest ih => exact .cons ⟨rfl, canon_idempotent entry.2⟩ ih

theorem find?_same {left right : Bindings} (same : BindingsSame left right) (name : String) :
    (left.find? (·.1 == name) = none ∧ right.find? (·.1 == name) = none) ∨
      ∃ first second, left.find? (·.1 == name) = some first ∧ right.find? (·.1 == name) = some second ∧
        first.1 = second.1 ∧ Same first.2 second.2 := by
  induction same with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons heads tail ih =>
    rename_i first second _ _
    by_cases hit : first.1 = name
    · have hit' : second.1 = name := heads.1 ▸ hit
      exact Or.inr ⟨first, second, by simp [hit], by simp [hit'], heads⟩
    · have miss' : ¬ second.1 = name := heads.1 ▸ hit
      simpa [List.find?_cons, hit, miss'] using ih

/-- A value that is not a collection without a rest variable leaves a rest variable unresolved. -/
theorem restSplice_other (lhs : Pattern) {bindings : Bindings} (depth : ℕ) (kind : CollType) {name : String}
    {entry : String × Pattern} (found : bindings.find? (·.1 == name) = some entry)
    (other : ∀ boundKind elements, entry.2 ≠ .collection boundKind elements none) :
    restSplice lhs bindings depth kind (some name) = ([], some name) := by
  obtain ⟨entryName, value⟩ := entry
  simp only [restSplice, found]
  split
  · rename_i heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    exact absurd heq.2 (other _ _)
  · rfl

/-- What a rest variable bound to a collection splices. -/
theorem restSplice_collection (lhs : Pattern) {bindings : Bindings} (depth : ℕ) (kind boundKind : CollType)
    {name entryName : String} {elements : List Pattern}
    (found : bindings.find? (·.1 == name) = some (entryName, .collection boundKind elements none)) :
    restSplice lhs bindings depth kind (some name) =
      if boundKind == kind then
        ((match captureDepth name 0 lhs with
          | some captured => elements.map (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 (depth - captured))
          | none => elements), none)
      else ([], some name) := by
  simp only [restSplice, found]
  rfl

/-- Two values with the same canonical form are both collections without a rest variable, of one kind and
with elements presenting the same collection, or neither is. -/
theorem shape_same {first second : Pattern} (same : Same first second) :
    (∃ kind elements others, first = .collection kind elements none ∧ second = .collection kind others none ∧
        arrange kind (elements.map canon) = arrange kind (others.map canon)) ∨
      ((∀ kind elements, first ≠ .collection kind elements none) ∧
        (∀ kind elements, second ≠ .collection kind elements none)) := by
  cases first with
  | collection kind elements rest =>
    obtain ⟨others, rfl, arranged⟩ := same_collection same
    cases rest with
    | none => exact Or.inl ⟨kind, elements, others, rfl, rfl, arranged⟩
    | some _ => exact Or.inr ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  | _ =>
    refine Or.inr ⟨fun _ _ => by simp, fun kind elements equal => ?_⟩
    subst equal
    obtain ⟨_, impossible, _⟩ := same_collection same.symm
    cases impossible

theorem forall₂_map_of {f g : Pattern → Pattern} {relation : Pattern → Pattern → Prop} :
    ∀ {items : List Pattern}, (∀ item ∈ items, relation (f item) (g item)) →
      List.Forall₂ relation (items.map f) (items.map g)
  | [], _ => .nil
  | item :: _, each => .cons (each item List.mem_cons_self)
      (forall₂_map_of fun other member => each other (List.mem_cons_of_mem _ member))

/-- Lifting respects permutation-equality. -/
theorem lift_same {left right : Pattern} (same : Same left right) (cutoff shift : ℕ) :
    Same (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars cutoff shift left)
      (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars cutoff shift right) :=
  same_map (fun step => same_of_bagStep (step.liftBVars cutoff shift)) same

/-- Spliced elements present the same collection when the bound collections do. -/
theorem spliced_presents (kind : CollType) (transform : Pattern → Pattern)
    (respects : ∀ {a b : Pattern}, Same a b → Same (transform a) (transform b)) {elements others : List Pattern}
    (arranged : arrange kind (elements.map canon) = arrange kind (others.map canon)) :
    arrange kind ((elements.map transform).map canon) = arrange kind ((others.map transform).map canon) := by
  have through : ∀ items : List Pattern,
      (items.map transform).map canon = (items.map canon).map (canon ∘ transform) := by
    intro items
    simp only [List.map_map]
    exact List.map_congr_left fun item _ => respects (canon_idempotent item).symm
  rw [through, through]
  exact arrange_eq_of_presents ((arrange_eq arranged).map _)

/-- **Captures with the same canonical forms give right sides with the same canonical form.** -/
theorem applyBindingsScoped_same (lhs : Pattern) {left right : Bindings} (same : BindingsSame left right) :
    ∀ (depth : ℕ) (pattern : Pattern),
      Same (applyBindingsScoped lhs left depth pattern) (applyBindingsScoped lhs right depth pattern)
  | depth, .fvar name => by
    simp only [applyBindingsScoped]
    rcases find?_same same name with ⟨leftNone, rightNone⟩ |
        ⟨⟨_, firstValue⟩, ⟨_, secondValue⟩, leftFound, rightFound, _, sameValue⟩
    · rw [leftNone, rightNone]
      exact same_refl _
    · rw [leftFound, rightFound]
      cases captureDepth name 0 lhs with
      | none => exact sameValue
      | some captured => exact lift_same sameValue 0 (depth - captured)
  | _, .bvar _ => same_refl _
  | depth, .apply label arguments => by
    rw [applyBindingsScoped_apply, applyBindingsScoped_apply]
    refine same_apply_congr label (forall₂_map_of fun argument member => ?_)
    have : sizeOf argument < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
    exact applyBindingsScoped_same lhs same depth argument
  | depth, .lambda binder body => by
    simp only [applyBindingsScoped]
    exact same_lambda_congr binder (applyBindingsScoped_same lhs same (depth + 1) body)
  | depth, .multiLambda arity binders body => by
    simp only [applyBindingsScoped]
    exact same_multiLambda_congr arity binders (applyBindingsScoped_same lhs same (depth + arity) body)
  | depth, .subst body replacement => by
    simp only [applyBindingsScoped]
    exact instantiateBVar_same (applyBindingsScoped_same lhs same depth replacement)
      (applyBindingsScoped_same lhs same (depth + 1) body)
  | depth, .collection kind elements rest => by
    simp only [applyBindingsScoped, applyBindingsScopedList_eq_map]
    have pointwise : List.Forall₂ Same (elements.map (applyBindingsScoped lhs left depth))
        (elements.map (applyBindingsScoped lhs right depth)) := forall₂_map_of fun element member =>
      have : sizeOf element < sizeOf (Pattern.collection kind elements rest) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
      applyBindingsScoped_same lhs same depth element
    cases rest with
    | none =>
      simp only [restSplice, List.append_nil]
      exact same_collection_congr kind none pointwise
    | some name =>
      rcases find?_same same name with ⟨leftNone, rightNone⟩ |
          ⟨⟨firstName, firstValue⟩, ⟨secondName, secondValue⟩, leftFound, rightFound, _, sameValue⟩
      · simp only [restSplice, leftNone, rightNone, List.append_nil]
        exact same_collection_congr kind (some name) pointwise
      · rcases shape_same sameValue with ⟨boundKind, firstElements, secondElements, rfl, rfl, arranged⟩ |
            ⟨firstOther, secondOther⟩
        · rw [restSplice_collection lhs depth kind boundKind leftFound,
            restSplice_collection lhs depth kind boundKind rightFound]
          by_cases sameKind : boundKind = kind
          · subst sameKind
            simp only [beq_self_eq_true, ↓reduceIte]
            refine same_splice boundKind pointwise ?_
            cases captureDepth name 0 lhs with
            | none => exact arranged
            | some captured =>
              exact spliced_presents boundKind _ (fun same => lift_same same 0 (depth - captured)) arranged
          · have different : (boundKind == kind) = false := by simpa using sameKind
            simp only [different, Bool.false_eq_true, ↓reduceIte, List.append_nil]
            exact same_collection_congr kind (some name) pointwise
        · rw [restSplice_other lhs depth kind leftFound firstOther,
            restSplice_other lhs depth kind rightFound secondOther]
          simp only [List.append_nil]
          exact same_collection_congr kind (some name) pointwise
termination_by _ pattern => sizeOf pattern

/-! ## Coherence -/

/-- A label reads only a rule witness's rule and the steps among its premises. -/
theorem admits_rule (label : StepLabel) (index : ℕ) (first second : Bindings) {premises premises' : List Witness}
    (steps : premiseStepsList premises = premiseStepsList premises') :
    label.admits (.rule index first premises) = label.admits (.rule index second premises') := by
  cases label <;> simp only [StepLabel.admits, ruleOf, steps]

/-- **A guard**: a relation query with no arguments. It reads no binding. -/
def guard : Premise → Bool
  | .relationQuery _ [] => true
  | _ => false

/-- A guard holds or fails whatever the bindings, and adds none. -/
theorem guard_result {bindings result : Bindings} {relation : String}
    (member : result ∈ premiseStepWithEnv relEnv language bindings (.relationQuery relation [])) :
    result = bindings ∧ ∀ other : Bindings, other ∈ premiseStepWithEnv relEnv language other (.relationQuery relation []) := by
  simp only [premiseStepWithEnv, relationQueryStep, List.map_nil, List.mem_flatMap, List.mem_filterMap] at member ⊢
  obtain ⟨tuple, inTuples, extension, matched, merged⟩ := member
  cases tuple with
  | nil =>
    simp only [matchRelationArgs, List.mem_singleton] at matched
    subst matched
    simp only [mergeBindings, List.foldlM_nil] at merged
    cases merged
    refine ⟨rfl, fun other => ⟨[], inTuples, [], ?_, ?_⟩⟩
    · simp only [matchRelationArgs, List.mem_singleton]
    · simp only [mergeBindings, List.foldlM_nil]; rfl
  | cons _ _ => simp [matchRelationArgs] at matched

/-- **Guards hold at canonical captures** when they hold, and contribute no step. -/
theorem guards_canon : ∀ (premises : List Premise) {sites : Pattern} {initial final : Bindings}
    {witnesses : List Witness}, premises.all guard = true →
    PremisesValid relEnv language sites initial premises witnesses final →
    final = initial ∧ premiseStepsList witnesses = [] ∧ ∃ witnesses',
      PremisesValid relEnv language sites (canonBindings initial) premises witnesses' (canonBindings initial) ∧
        premiseStepsList witnesses' = []
  | [], _, _, _, _, _, valid => by
    cases valid
    exact ⟨rfl, rfl, [], .nil _, rfl⟩
  | premise :: premises, sites, initial, final, _, guarded, valid => by
    simp only [List.all_cons, Bool.and_eq_true] at guarded
    obtain ⟨isGuard, restGuards⟩ := guarded
    cases valid with
    | cons head tail =>
      rename_i middle witness witnesses
      cases premise with
      | relationQuery relation arguments =>
        cases arguments with
        | cons _ _ => simp [guard] at isGuard
        | nil =>
          cases head with
          | base _ member =>
            obtain ⟨same, holds⟩ := guard_result member
            subst same
            obtain ⟨finalSame, noSteps, witnesses', canonValid, canonNoSteps⟩ := guards_canon premises restGuards tail
            exact ⟨finalSame, by simpa [premiseStepsList, premiseSteps] using noSteps, .base _ :: witnesses',
              .cons (.base rfl (holds _)) canonValid, by simpa [premiseStepsList, premiseSteps] using canonNoSteps⟩
          | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
      | freshness _ => simp [guard] at isGuard
      | congruence _ _ => simp [guard] at isGuard
      | scopedStep _ => simp [guard] at isGuard
      | forAll _ _ _ => simp [guard] at isGuard

/-- **A step of a guarded rule from a term with no set is matched by a step of the same rule from its
canonical form**, to a term with the same canonical form. -/
theorem simulates (guarded : language.rewrites.all (fun rule => rule.premises.all guard) = true)
    {redex : Pattern} {witness : Witness} {contractum : Pattern} (free : setFree redex = true)
    (valid : StepValid relEnv language redex witness contractum) :
    ∃ witness' contractum', StepValid relEnv language (canon redex) witness' contractum' ∧
      (∀ label : StepLabel, label.admits witness = label.admits witness') ∧ canon contractum' = canon contractum := by
  cases valid with
  | rule found matched premises =>
    rename_i index rule initial final witnesses
    obtain ⟨finalSame, noSteps, witnesses', canonValid, canonNoSteps⟩ :=
      guards_canon rule.premises (List.all_eq_true.mp guarded rule (List.mem_of_getElem? found)) premises
    subst finalSame
    rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel] at matched
    refine ⟨.rule index (canonBindings final) witnesses',
      applyBindingsScoped (captureSites rule) (canonBindings final) 0 rule.right,
      .rule found ?_ canonValid, fun label => admits_rule label index _ _ (noSteps.trans canonNoSteps.symm), ?_⟩
    · rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel]
      exact matchRel_canon rule.left redex final free matched
    · exact applyBindingsScoped_same _ (bindingsSame_canon final) 0 rule.right

/-- **Guarded rules are coherent with sorted bags.** -/
theorem coherent (noEquations : language.equations = []) (noAlgebra : language.hasAlgebraDeclarations = false)
    (guarded : language.rewrites.all (fun rule => rule.premises.all guard) = true) (fuel : ℕ) :
    Coherent relEnv language fuel sortBags (domain language) List.singleton :=
  coherent_of_simulation (canonical noEquations noAlgebra) fun {redex _ _} _ admitted valid => by
    simp only [domain, sortBags_eq_canon, Bool.and_eq_true] at admitted
    rw [sortBags_eq_canon]
    exact simulates guarded ((canon_setFree redex).symm.trans admitted.1.2) valid

/-- **Canonical forms for a bag language** with no authored equations, no collection algebra, and rules whose
premises are guards, for the front door. -/
def forms (noEquations : language.equations = []) (noAlgebra : language.hasAlgebraDeclarations = false)
    (guarded : language.rewrites.all (fun rule => rule.premises.all guard) = true) (fuel : ℕ) :
    CanonicalForms relEnv language fuel :=
  .ofCoherent (canonical noEquations noAlgebra) (coherent noEquations noAlgebra guarded fuel)

/-! ## Relation queries over metavariables -/

/-- A metavariable. -/
def isMetavariable : Pattern → Bool
  | .fvar _ => true
  | _ => false

/-- **A query over metavariables**: a relation query whose arguments are metavariables. A guard is one. -/
def query : Premise → Bool
  | .relationQuery _ arguments => arguments.all isMetavariable
  | _ => false

/-- **A relation environment that respects canonical forms**: the answers to the canonical forms of a query
include the canonical forms of its answers. -/
def RespectsCanon (relEnv : RelationEnv) : Prop :=
  ∀ relation arguments tuple, tuple ∈ relEnv.tuples relation arguments →
    tuple.map canon ∈ relEnv.tuples relation (arguments.map canon)

/-- The empty relation environment respects canonical forms. -/
theorem respectsCanon_empty : RespectsCanon RelationEnv.empty := fun _ _ _ member => by
  simp [RelationEnv.empty] at member

/-- The builtin relations respect canonical forms. -/
theorem builtin_canon {relation : String} {arguments tuple : List Pattern}
    (member : tuple ∈ builtinRelationTuples language relation arguments) :
    tuple.map canon ∈ builtinRelationTuples language relation (arguments.map canon) := by
  unfold builtinRelationTuples at member
  split at member
  · rename_i lhs rhs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    simp only [List.map_cons, List.map_nil, builtinRelationTuples, List.mem_cons, List.not_mem_nil, or_false]
    rcases member with rfl | rfl <;> simp
  · simp at member

theorem lookup_canonBindings (bindings : Bindings) (name : String) :
    Bindings.lookup (canonBindings bindings) name = (Bindings.lookup bindings name).map canon := by
  simp only [Bindings.lookup, find?_canonBindings, Option.map_map]
  rfl

theorem applyBindings_var (bindings : Bindings) (name : String) :
    applyBindings bindings (.fvar name) = (Bindings.lookup bindings name).getD (.fvar name) := by
  simp only [applyBindings, Bindings.lookup]
  cases bindings.find? (fun pair => pair.1 == name) <;> rfl

/-- Binding application to a metavariable commutes with taking canonical forms. -/
theorem applyBindings_metavariable_canon (bindings : Bindings) {argument : Pattern}
    (metavariable : isMetavariable argument = true) :
    applyBindings (canonBindings bindings) argument = canon (applyBindings bindings argument) := by
  cases argument with
  | fvar name =>
    rw [applyBindings_var, applyBindings_var, lookup_canonBindings]
    cases Bindings.lookup bindings name with
    | none => show Pattern.fvar name = canon (.fvar name); rw [canon]
    | some value => rfl
  | _ => simp [isMetavariable] at metavariable

/-- **Matching a query's answer commutes with taking canonical forms**, for arguments that are
metavariables. -/
theorem matchRelationArgs_canon : ∀ (arguments : List Pattern) {seed : Bindings} {tuple : List Pattern}
    {extension : Bindings}, arguments.all isMetavariable = true →
    extension ∈ matchRelationArgs seed arguments tuple →
      canonBindings extension ∈ matchRelationArgs (canonBindings seed) arguments (tuple.map canon)
  | [], seed, tuple, extension, _, matched => by
    cases tuple with
    | nil =>
      simp only [matchRelationArgs, List.mem_singleton] at matched
      subst matched
      simp [matchRelationArgs, canonBindings]
    | cons _ _ => simp [matchRelationArgs] at matched
  | argument :: arguments, seed, tuple, extension, metavariables, matched => by
    simp only [List.all_cons, Bool.and_eq_true] at metavariables
    obtain ⟨isVar, restVars⟩ := metavariables
    cases argument with
    | fvar name =>
      cases tuple with
      | nil => simp [matchRelationArgs] at matched
      | cons value values =>
        simp only [matchRelationArgs, List.mem_flatMap] at matched
        obtain ⟨head, headMatched, inner⟩ := matched
        simp only [List.map_cons, matchRelationArgs, List.mem_flatMap]
        cases merged : mergeBindings seed head with
        | none => rw [merged] at inner; cases inner
        | some extended =>
          rw [merged] at inner
          simp only [List.mem_filterMap] at inner
          obtain ⟨tail, tailMatched, tailMerged⟩ := inner
          refine ⟨canonBindings head, ?_, ?_⟩
          · simp only [matchRelationArgument] at headMatched ⊢
            rw [lookup_canonBindings]
            cases found : Bindings.lookup seed name with
            | none =>
              rw [found] at headMatched
              simp only [List.mem_singleton] at headMatched
              subst headMatched
              simp [canonBindings]
            | some existing =>
              rw [found] at headMatched
              by_cases same : existing = value
              · subst same
                simp only [↓reduceIte, List.mem_singleton] at headMatched
                subst headMatched
                simp [canonBindings]
              · simp [same] at headMatched
          · rw [mergeBindings_canon _ merged]
            simp only [List.mem_filterMap]
            exact ⟨canonBindings tail, matchRelationArgs_canon arguments restVars tailMatched,
              mergeBindings_canon _ tailMerged⟩
    | _ => simp [isMetavariable] at isVar

/-- **A query over metavariables answered at a match is answered at the canonical match**, when the
relation environment respects canonical forms. -/
theorem query_canon (respects : RespectsCanon relEnv) {bindings result : Bindings} {relation : String}
    {arguments : List Pattern} (metavariables : arguments.all isMetavariable = true)
    (member : result ∈ premiseStepWithEnv relEnv language bindings (.relationQuery relation arguments)) :
    canonBindings result ∈
      premiseStepWithEnv relEnv language (canonBindings bindings) (.relationQuery relation arguments) := by
  simp only [premiseStepWithEnv, relationQueryStep, List.mem_flatMap, List.mem_filterMap, List.mem_append] at member ⊢
  obtain ⟨tuple, inTuples, extension, matched, merged⟩ := member
  have argumentsCanon : arguments.map (applyBindings (canonBindings bindings)) =
      (arguments.map (applyBindings bindings)).map canon := by
    rw [List.map_map]
    exact List.map_congr_left fun argument member =>
      applyBindings_metavariable_canon bindings (List.all_eq_true.mp metavariables argument member)
  refine ⟨tuple.map canon, ?_, canonBindings extension, matchRelationArgs_canon arguments metavariables matched,
    mergeBindings_canon _ merged⟩
  rw [argumentsCanon]
  rcases inTuples with builtin | environment
  · exact Or.inl (builtin_canon builtin)
  · exact Or.inr (respects _ _ _ environment)

/-- **Queries over metavariables hold at canonical captures** when they hold, and contribute no step. -/
theorem queries_canon (respects : RespectsCanon relEnv) : ∀ (premises : List Premise) {sites : Pattern}
    {initial final : Bindings} {witnesses : List Witness}, premises.all query = true →
    PremisesValid relEnv language sites initial premises witnesses final →
    premiseStepsList witnesses = [] ∧ ∃ witnesses',
      PremisesValid relEnv language sites (canonBindings initial) premises witnesses' (canonBindings final) ∧
        premiseStepsList witnesses' = []
  | [], _, _, _, _, _, valid => by
    cases valid
    exact ⟨rfl, [], .nil _, rfl⟩
  | premise :: premises, sites, initial, final, _, queried, valid => by
    simp only [List.all_cons, Bool.and_eq_true] at queried
    obtain ⟨isQuery, restQueries⟩ := queried
    cases valid with
    | cons head tail =>
      rename_i middle witness witnesses
      cases premise with
      | relationQuery relation arguments =>
        cases head with
        | base _ member =>
          obtain ⟨noSteps, witnesses', canonValid, canonNoSteps⟩ := queries_canon respects premises restQueries tail
          exact ⟨by simpa [premiseStepsList, premiseSteps] using noSteps, .base _ :: witnesses',
            .cons (.base rfl (query_canon respects (by simpa [query] using isQuery) member)) canonValid,
            by simpa [premiseStepsList, premiseSteps] using canonNoSteps⟩
        | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
      | freshness _ => simp [query] at isQuery
      | congruence _ _ => simp [query] at isQuery
      | scopedStep _ => simp [query] at isQuery
      | forAll _ _ _ => simp [query] at isQuery

/-- **A step of a rule whose premises are queries over metavariables is matched by a step of the same rule
from the canonical form**, when the relation environment respects canonical forms. -/
theorem simulatesQueries (respects : RespectsCanon relEnv)
    (queried : language.rewrites.all (fun rule => rule.premises.all query) = true)
    {redex : Pattern} {witness : Witness} {contractum : Pattern} (free : setFree redex = true)
    (valid : StepValid relEnv language redex witness contractum) :
    ∃ witness' contractum', StepValid relEnv language (canon redex) witness' contractum' ∧
      (∀ label : StepLabel, label.admits witness = label.admits witness') ∧ canon contractum' = canon contractum := by
  cases valid with
  | rule found matched premises =>
    rename_i index rule initial final witnesses
    obtain ⟨noSteps, witnesses', canonValid, canonNoSteps⟩ :=
      queries_canon respects rule.premises (List.all_eq_true.mp queried rule (List.mem_of_getElem? found)) premises
    rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel] at matched
    refine ⟨.rule index (canonBindings initial) witnesses',
      applyBindingsScoped (captureSites rule) (canonBindings final) 0 rule.right,
      .rule found ?_ canonValid, fun label => admits_rule label index _ _ (noSteps.trans canonNoSteps.symm), ?_⟩
    · rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel]
      exact matchRel_canon rule.left redex initial free matched
    · exact applyBindingsScoped_same _ (bindingsSame_canon final) 0 rule.right

/-- **Rules whose premises are queries over metavariables are coherent with sorted bags**, in a relation
environment that respects canonical forms. -/
theorem coherentQueries (noEquations : language.equations = []) (noAlgebra : language.hasAlgebraDeclarations = false)
    (queried : language.rewrites.all (fun rule => rule.premises.all query) = true) (respects : RespectsCanon relEnv)
    (fuel : ℕ) : Coherent relEnv language fuel sortBags (domain language) List.singleton :=
  coherent_of_simulation (canonical noEquations noAlgebra) fun {redex _ _} _ admitted valid => by
    simp only [domain, sortBags_eq_canon, Bool.and_eq_true] at admitted
    rw [sortBags_eq_canon]
    exact simulatesQueries respects queried ((canon_setFree redex).symm.trans admitted.1.2) valid

/-- **Canonical forms for a bag language whose rules query captured values**, in a relation environment that
respects canonical forms. -/
def formsQueries (noEquations : language.equations = []) (noAlgebra : language.hasAlgebraDeclarations = false)
    (queried : language.rewrites.all (fun rule => rule.premises.all query) = true) (respects : RespectsCanon relEnv)
    (fuel : ℕ) : CanonicalForms relEnv language fuel :=
  .ofCoherent (canonical noEquations noAlgebra) (coherentQueries noEquations noAlgebra queried respects fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagForms
