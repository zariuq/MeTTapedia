import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegionControls

/-!
# Controls: canonical forms for an equation with a metavariable

The equation `Wrap x = x` and the rule `Pair x y ⇒ x` (`wrapped`). The equation holds in both directions
in every context, so a term is equivalent to itself with `Wrap` added or removed anywhere inside.

- **Canonical forms remove every `Wrap`** (`unwrapCanon`). They meet the contract (`unwrap_canonical`).
- **The rule fires on terms that are not canonical**, such as `Pair (Wrap Ok) Err`, so coherence does not
  come for free. It holds because the canonical forms simulate steps (`unwrap_simulates`): the rule fires
  at the canonical form too, at the canonical forms of the same parts (`unwrap_coherent`).
- **Verdicts at `Wrap (Pair (Wrap Ok) Err)`**, from a closed canonical region grown for two rounds:
  - read as written it has no step, since the rule needs `Pair` at the root (`stuck_as_written`);
  - modulo the equation it steps (`wrapped_steps`), it reaches `Ok` (`wrapped_reaches_ok`), and it has
    exactly one result (`wrapped_one_result`).
- **The front door**, given these canonical forms, proves that it steps (`ask_wrapped_steps`); without
  them it leaves the question open (`front_door_open_as_written`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalUnwrapControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.Match (Bindings matchPattern mergeBindings applyBindingsScoped captureDepth)
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchArgsRel matchPattern_sound matchRel_complete
  mergeBindings_subsumed_left)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic_of_no_presentations)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars_zero)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.EquationSemantics
  (DerivedInstance CollectionCarrierRule AlgebraRule usesCollection_eq_true_of_collectionTypedAt)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegionControls (constant constantRule isObjectPatternList_iff)

/-! ## The language -/

def wrap (inner : Pattern) : Pattern := .apply "Wrap" [inner]

def pair (first second : Pattern) : Pattern := .apply "Pair" [first, second]

def wrapRule : GrammarRule :=
  { label := "Wrap", category := "Term", params := [.simple "x" (.base "Term")],
    syntaxPattern := [.terminal "wrap", .nonTerminal "x"] }

def pairRule : GrammarRule :=
  { label := "Pair", category := "Term", params := [.simple "x" (.base "Term"), .simple "y" (.base "Term")],
    syntaxPattern := [.nonTerminal "x", .nonTerminal "y"] }

/-- `Wrap x = x`. -/
def unwrapEquation : Equation :=
  { name := "Unwrap", typeContext := [], premises := [], left := wrap (.fvar "x"), right := .fvar "x" }

/-- `Pair x y ⇒ x`. -/
def firstRule : RewriteRule :=
  { name := "First", typeContext := [], premises := [], left := pair (.fvar "x") (.fvar "y"), right := .fvar "x" }

def wrapped : LanguageDef :=
  { name := "Wrapped", types := ["Term"], terms := [wrapRule, pairRule, constantRule "Ok", constantRule "Err"],
    equations := [unwrapEquation], rewrites := [firstRule] }

/-! ## Canonical forms -/

/-- A constructor applied to arguments, with `Wrap` removed. -/
def unwrapped (name : String) : List Pattern → Pattern
  | [] => .apply name []
  | [argument] => if name = "Wrap" then argument else .apply name [argument]
  | first :: second :: rest => .apply name (first :: second :: rest)

mutual
/-- Remove every `Wrap`. -/
def unwrap : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply name arguments => unwrapped name (unwrapList arguments)
  | .lambda binder body => .lambda binder (unwrap body)
  | .multiLambda arity names body => .multiLambda arity names (unwrap body)
  | .subst body replacement => .subst (unwrap body) (unwrap replacement)
  | .collection kind elements rest => .collection kind (unwrapList elements) rest

def unwrapList : List Pattern → List Pattern
  | [] => []
  | pattern :: patterns => unwrap pattern :: unwrapList patterns
end

/-- **Canonical forms**: object terms with every `Wrap` removed; other terms unchanged. -/
def unwrapCanon (term : Pattern) : Pattern := if isObjectPattern term then unwrap term else term

theorem unwrapList_eq_map : ∀ patterns : List Pattern, unwrapList patterns = patterns.map unwrap
  | [] => rfl
  | pattern :: patterns => by rw [unwrapList, unwrapList_eq_map patterns, List.map_cons]

theorem unwrapped_eq_apply {name : String} {arguments : List Pattern} (keep : name ≠ "Wrap" ∨ arguments.length ≠ 1) :
    unwrapped name arguments = .apply name arguments := by
  match arguments, keep with
  | [], _ => rfl
  | [argument], keep =>
    have other : name ≠ "Wrap" := by simpa using keep
    simp [unwrapped, other]
  | _ :: _ :: _, _ => rfl

theorem unwrap_wrap (inner : Pattern) : unwrap (wrap inner) = unwrap inner := by
  simp [wrap, unwrap, unwrapList, unwrapped]

theorem unwrap_pair (first second : Pattern) : unwrap (pair first second) = pair (unwrap first) (unwrap second) := by
  simp [pair, unwrap, unwrapList, unwrapped]

mutual
theorem unwrap_object : ∀ term : Pattern, isObjectPattern (unwrap term) = isObjectPattern term
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply _ [] => rfl
  | .apply name [argument] => by
    have list := unwrapList_object [argument]
    simp only [unwrapList, isObjectPatternList, Bool.and_true] at list
    by_cases isWrap : name = "Wrap"
    · simp [unwrap, unwrapList, unwrapped, isWrap, isObjectPattern, isObjectPatternList, list]
    · simp [unwrap, unwrapList, unwrapped, isWrap, isObjectPattern, isObjectPatternList, list]
  | .apply name (first :: second :: rest) => by
    have list := unwrapList_object (first :: second :: rest)
    simp only [unwrap, unwrapped, unwrapList] at list ⊢
    simpa only [isObjectPattern] using list
  | .lambda _ body => by simpa only [unwrap, isObjectPattern] using unwrap_object body
  | .multiLambda _ _ body => by simpa only [unwrap, isObjectPattern] using unwrap_object body
  | .subst _ _ => rfl
  | .collection _ elements _ => by simp only [unwrap, isObjectPattern, unwrapList_object elements]

theorem unwrapList_object : ∀ patterns : List Pattern,
    isObjectPatternList (unwrapList patterns) = isObjectPatternList patterns
  | [] => rfl
  | pattern :: patterns => by
    simp only [unwrapList, isObjectPatternList, unwrap_object pattern, unwrapList_object patterns]
end

mutual
theorem unwrap_scoped : ∀ (term : Pattern) (depth : ℕ), (unwrap term).isWellScopedAt depth = term.isWellScopedAt depth
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply _ [], _ => rfl
  | .apply name [argument], depth => by
    have list := unwrapList_scoped [argument] depth
    simp only [unwrapList, Pattern.isWellScopedListAt, Bool.and_true] at list
    by_cases isWrap : name = "Wrap"
    · simp [unwrap, unwrapList, unwrapped, isWrap, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, list]
    · simp [unwrap, unwrapList, unwrapped, isWrap, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, list]
  | .apply name (first :: second :: rest), depth => by
    have list := unwrapList_scoped (first :: second :: rest) depth
    simp only [unwrap, unwrapped, unwrapList] at list ⊢
    simpa only [Pattern.isWellScopedAt] using list
  | .lambda _ body, depth => by simpa only [unwrap, Pattern.isWellScopedAt] using unwrap_scoped body (depth + 1)
  | .multiLambda arity _ body, depth => by
    simpa only [unwrap, Pattern.isWellScopedAt] using unwrap_scoped body (depth + arity)
  | .subst body replacement, depth => by
    simp only [unwrap, Pattern.isWellScopedAt, unwrap_scoped body (depth + 1), unwrap_scoped replacement depth]
  | .collection _ elements _, depth => by
    simp only [unwrap, Pattern.isWellScopedAt, unwrapList_scoped elements depth]

theorem unwrapList_scoped : ∀ (patterns : List Pattern) (depth : ℕ),
    Pattern.isWellScopedListAt depth (unwrapList patterns) = Pattern.isWellScopedListAt depth patterns
  | [], _ => rfl
  | pattern :: patterns, depth => by
    simp only [unwrapList, Pattern.isWellScopedListAt, unwrap_scoped pattern depth, unwrapList_scoped patterns depth]
end

/-- The context with every `Wrap` removed outside its hole, including a `Wrap` directly around it. -/
def unwrapContext : OneHoleContext → OneHoleContext
  | .hole => .hole
  | .apply name before inner after =>
    if name = "Wrap" ∧ before = [] ∧ after = [] then unwrapContext inner
    else .apply name (before.map unwrap) (unwrapContext inner) (after.map unwrap)
  | .lambda binder inner => .lambda binder (unwrapContext inner)
  | .multiLambda arity names inner => .multiLambda arity names (unwrapContext inner)
  | .substBody inner replacement => .substBody (unwrapContext inner) (unwrap replacement)
  | .substReplacement body inner => .substReplacement (unwrap body) (unwrapContext inner)
  | .collection kind before inner after rest =>
    .collection kind (before.map unwrap) (unwrapContext inner) (after.map unwrap) rest

/-- **Removing `Wrap` commutes with filling a context.** -/
theorem unwrap_fill : ∀ (context : OneHoleContext) (pattern : Pattern),
    unwrap (context.fill pattern) = (unwrapContext context).fill (unwrap pattern)
  | .hole, _ => rfl
  | .apply name before inner after, pattern => by
    by_cases frame : name = "Wrap" ∧ before = [] ∧ after = []
    · obtain ⟨rfl, rfl, rfl⟩ := frame
      rw [unwrapContext, if_pos ⟨rfl, rfl, rfl⟩, ← unwrap_fill inner pattern]
      simp [OneHoleContext.fill, unwrap, unwrapList, unwrapped]
    · rw [unwrapContext, if_neg frame]
      simp only [OneHoleContext.fill, unwrap, unwrapList_eq_map, List.map_append, List.map_cons,
        unwrap_fill inner pattern]
      apply unwrapped_eq_apply
      by_cases isWrap : name = "Wrap"
      · refine Or.inr ?_
        have : ¬ (before = [] ∧ after = []) := fun both => frame ⟨isWrap, both⟩
        simp only [List.length_append, List.length_map, List.length_cons]
        intro length
        apply this
        constructor
        · exact List.length_eq_zero_iff.mp (by omega)
        · exact List.length_eq_zero_iff.mp (by omega)
      · exact Or.inl isWrap
  | .lambda _ inner, pattern => by simp only [OneHoleContext.fill, unwrapContext, unwrap, unwrap_fill inner pattern]
  | .multiLambda _ _ inner, pattern => by
    simp only [OneHoleContext.fill, unwrapContext, unwrap, unwrap_fill inner pattern]
  | .substBody inner _, pattern => by simp only [OneHoleContext.fill, unwrapContext, unwrap, unwrap_fill inner pattern]
  | .substReplacement _ inner, pattern => by
    simp only [OneHoleContext.fill, unwrapContext, unwrap, unwrap_fill inner pattern]
  | .collection _ before inner after _, pattern => by
    simp only [OneHoleContext.fill, unwrapContext, unwrap, unwrapList_eq_map, List.map_append, List.map_cons,
      unwrap_fill inner pattern]

/-! ## Matching and instantiating -/

theorem matchRel_var {term : Pattern} {bindings : Bindings} (matched : MatchRel (.fvar "x") term bindings) :
    bindings = [("x", term)] := by
  cases matched
  rfl

theorem matchRel_wrap {term : Pattern} {bindings : Bindings} (matched : MatchRel (wrap (.fvar "x")) term bindings) :
    ∃ inner, term = wrap inner ∧ bindings.find? (·.1 == "x") = some ("x", inner) := by
  cases matched with
  | apply arguments _ =>
    cases arguments with
    | @cons _ inner _ _ _ _ _ head tail merged =>
      cases head
      cases tail
      exact ⟨inner, rfl, mergeBindings_subsumed_left merged (by simp)⟩

theorem matchRel_pair {term : Pattern} {bindings : Bindings}
    (matched : MatchRel (pair (.fvar "x") (.fvar "y")) term bindings) :
    ∃ first second, term = pair first second ∧ bindings.find? (·.1 == "x") = some ("x", first) := by
  cases matched with
  | apply arguments _ =>
    cases arguments with
    | @cons _ first _ _ _ _ _ head tail merged =>
      cases head
      cases tail with
      | @cons _ second _ _ _ _ _ head' tail' _ =>
        cases head'
        cases tail'
        exact ⟨first, second, rfl, mergeBindings_subsumed_left merged (by simp)⟩

/-- Instantiating `x` at depth zero, where the sites bind it at depth zero, gives its value. -/
theorem scoped_x {sites : Pattern} {bindings : Bindings} {value : Pattern}
    (found : bindings.find? (·.1 == "x") = some ("x", value)) (depth : captureDepth "x" 0 sites = some 0) :
    applyBindingsScoped sites bindings 0 (.fvar "x") = value := by
  simp only [applyBindingsScoped, found, depth, Nat.sub_zero, liftBVars_zero]

theorem params_simple {rule : GrammarRule} (member : rule ∈ wrapped.terms) :
    ∀ name kind element, rule.params ≠ [.simple name (.collection kind element)] := by
  simp only [wrapped, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp [wrapRule, pairRule, constantRule]

/-- The language declares no collections, so it derives no laws. -/
theorem no_derived {source target : Pattern} : ¬ DerivedInstance wrapped source target := by
  have notAlgebra : ∀ {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra},
      ¬ AlgebraRule wrapped rule kind algebra := by
    intro rule kind algebra declared
    obtain ⟨name, params⟩ := declared.selfSorted
    exact params_simple declared.authored name kind _ params
  intro derived
  cases derived with
  | bagPerm member kindTyped _ =>
      exact absurd (usesCollection_eq_true_of_collectionTypedAt member kindTyped) (by decide +kernel)
  | setPerm member kindTyped _ =>
      exact absurd (usesCollection_eq_true_of_collectionTypedAt member kindTyped) (by decide +kernel)
  | setDedup member kindTyped =>
      exact absurd (usesCollection_eq_true_of_collectionTypedAt member kindTyped) (by decide +kernel)
  | flatten declared => exact notAlgebra declared
  | singleton declared => exact notAlgebra declared
  | unitElim declared => exact notAlgebra declared
  | emptyUnit declared => exact notAlgebra declared

variable {relEnv : RelationEnv}

/-- The equation's instances: unwrapping, and wrapping any term. -/
theorem authored_unwrap {source target : Pattern} (authored : AuthoredEquation relEnv wrapped source target) :
    source = wrap target ∨ target = wrap source := by
  cases authored with
  | forward member _ matched premises =>
    simp only [wrapped, List.mem_singleton] at member
    subst member
    cases premises
    obtain ⟨inner, rfl, found⟩ := matchRel_wrap (matchPattern_sound matched)
    left
    show wrap inner = wrap (applyBindingsScoped (captureSitesOf (wrap (.fvar "x")) []) _ 0 (.fvar "x"))
    rw [scoped_x (sites := captureSitesOf (wrap (.fvar "x")) []) found (by decide)]
  | reverse member _ matched premises =>
    simp only [wrapped, List.mem_singleton] at member
    subst member
    cases premises
    have bound := matchRel_var (matchPattern_sound matched)
    subst bound
    right
    show wrap (applyBindingsScoped (captureSitesOf (.fvar "x") []) [("x", source)] 0 (.fvar "x")) = wrap source
    rw [scoped_x (sites := captureSitesOf (.fvar "x") []) (value := source) (by simp) (by decide)]
  | declared member notRaw _ =>
    simp only [wrapped, List.mem_singleton] at member
    subst member
    exact absurd notRaw (by decide)
  | premised member notRaw _ _ =>
    simp only [wrapped, List.mem_singleton] at member
    subst member
    exact absurd notRaw (by decide)

theorem unwrap_generator {source target : Pattern} (generator : Generator relEnv wrapped source target) :
    unwrap source = unwrap target := by
  rcases generator with authored | derived
  · rcases authored_unwrap authored with rfl | rfl
    · exact unwrap_wrap target
    · exact (unwrap_wrap source).symm
  · exact absurd derived no_derived

theorem canon_of_object {term : Pattern} (object : IsObject term) : unwrapCanon term = unwrap term := if_pos object

theorem canon_of_not_object {term : Pattern} (notObject : ¬ IsObject term) : unwrapCanon term = term :=
  if_neg notObject

theorem unwrap_same {first second : Pattern} (equivalent : ObjectEquivalent relEnv wrapped .syntax first second) :
    unwrapCanon first = unwrapCanon second := by
  induction equivalent with
  | rel first second step =>
    obtain ⟨firstObject, secondObject, step⟩ := step
    rw [canon_of_object firstObject, canon_of_object secondObject]
    cases step with
    | inContext context generator => rw [unwrap_fill, unwrap_fill, unwrap_generator generator]
  | refl => rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- `Wrap t` is `t` by one instance of the equation. -/
theorem unwrap_step {inner : Pattern} (object : IsObject inner) : ObjectStep relEnv wrapped .syntax (wrap inner) inner := by
  have instance_ : AuthoredEquation relEnv wrapped (wrap inner)
      (applyBindingsScoped (captureSitesOf (wrap (.fvar "x")) []) [("x", inner)] 0 (.fvar "x")) :=
    AuthoredEquation.forward (equation := unwrapEquation) (initial := [("x", inner)]) (List.mem_singleton_self _) rfl
      (matchRel_complete (.apply (.cons .fvar .nil rfl) rfl)) (PremisesValid.nil _)
  rw [scoped_x (sites := captureSitesOf (wrap (.fvar "x")) []) (value := inner) (by simp) (by decide)] at instance_
  have objectWrap : IsObject (wrap inner) := by
    show isObjectPatternList [inner] = true
    simpa [isObjectPatternList] using object
  exact ⟨objectWrap, object, EquationStep.inContext .hole (Or.inl instance_)⟩

theorem fills_apply (name : String) (before after : List Pattern) (pattern : Pattern) :
    (OneHoleContext.apply name before .hole after).fill pattern = .apply name (before ++ pattern :: after) := rfl

mutual
/-- **Every object term is equivalent to its unwrapping.** -/
theorem unwrap_equivalent : ∀ term : Pattern, IsObject term → ObjectEquivalent relEnv wrapped .syntax term (unwrap term)
  | .bvar _, _ => Relation.EqvGen.refl _
  | .fvar _, _ => Relation.EqvGen.refl _
  | .apply _ [], _ => Relation.EqvGen.refl _
  | .apply name [argument], object => by
    have listObject : isObjectPatternList [argument] = true := object
    have argumentObject : IsObject argument := by simpa [isObjectPatternList] using listObject
    have inner := (unwrapList_equivalent [argument] listObject) argument List.mem_cons_self
    by_cases isWrap : name = "Wrap"
    · subst isWrap
      rw [show unwrap (.apply "Wrap" [argument]) = unwrap argument by simp [unwrap, unwrapList, unwrapped]]
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (unwrap_step argumentObject)) inner
    · rw [show unwrap (.apply name [argument]) = .apply name [unwrap argument] by
        simp [unwrap, unwrapList, unwrapped, isWrap]]
      exact ObjectEquivalent.fill (.apply name [] .hole []) (fun pattern patternObject => by
        show isObjectPatternList [pattern] = true
        simpa [isObjectPatternList] using patternObject) inner
  | .apply name (first :: second :: rest), object => by
    have listObject : isObjectPatternList (first :: second :: rest) = true := object
    have each := unwrapList_equivalent (first :: second :: rest) listObject
    have congr := ObjectEquivalent.list_congr unwrap (fun pattern object => (unwrap_object pattern).trans object)
      (.apply name) (.apply name · .hole ·) (fun _ _ _ => rfl)
      (fun patterns all => (isObjectPatternList_iff patterns).mpr all) (first :: second :: rest) []
      (fun _ member => nomatch member)
      fun member inside => ⟨(isObjectPatternList_iff _).mp listObject member inside, each member inside⟩
    rw [List.nil_append, List.nil_append] at congr
    rw [show unwrap (.apply name (first :: second :: rest)) = .apply name ((first :: second :: rest).map unwrap) by
      simp only [unwrap, unwrapList, unwrapped, unwrapList_eq_map, List.map_cons]]
    exact congr
  | .lambda binder body, object =>
    ObjectEquivalent.fill (.lambda binder .hole) (fun _ inner => inner) (unwrap_equivalent body object)
  | .multiLambda arity names body, object =>
    ObjectEquivalent.fill (.multiLambda arity names .hole) (fun _ inner => inner) (unwrap_equivalent body object)
  | .subst _ _, object => by simp [IsObject, isObjectPattern] at object
  | .collection kind elements rest, object => by
    cases rest with
    | some _ => simp [IsObject, isObjectPattern] at object
    | none =>
      have listObject : isObjectPatternList elements = true := by simpa [IsObject, isObjectPattern] using object
      have each := unwrapList_equivalent elements listObject
      have congr := ObjectEquivalent.list_congr unwrap (fun pattern object => (unwrap_object pattern).trans object)
        (.collection kind · none) (.collection kind · .hole · none) (fun _ _ _ => rfl)
        (fun patterns all => by
          show isObjectPattern (.collection kind patterns none) = true
          simpa [isObjectPattern] using (isObjectPatternList_iff patterns).mpr all) elements []
        (fun _ member => nomatch member)
        fun member inside => ⟨(isObjectPatternList_iff _).mp listObject member inside, each member inside⟩
      rw [List.nil_append, List.nil_append] at congr
      rw [show unwrap (.collection kind elements none) = .collection kind (elements.map unwrap) none by
        simp only [unwrap, unwrapList_eq_map]]
      exact congr

theorem unwrapList_equivalent : ∀ patterns : List Pattern, isObjectPatternList patterns = true →
    ∀ pattern ∈ patterns, ObjectEquivalent relEnv wrapped .syntax pattern (unwrap pattern)
  | [], _ => fun _ member => nomatch member
  | pattern :: patterns, objects => by
    simp only [isObjectPatternList, Bool.and_eq_true] at objects
    have head := unwrap_equivalent pattern objects.1
    have tail := unwrapList_equivalent patterns objects.2
    intro member inside
    rcases List.mem_cons.mp inside with rfl | inside
    · exact head
    · exact tail member inside
end

/-- The domain of the canonical forms: object terms. -/
def unwrapDomain (term : Pattern) : Bool := isObjectPattern term

/-- **Removing `Wrap` gives canonical forms for the equation** on object terms, read off them. -/
theorem unwrap_canonicalDetermined (relEnv : RelationEnv) :
    CanonicalDetermined relEnv wrapped unwrapCanon unwrapDomain where
  object admitted := admitted
  determined term := by
    by_cases object : IsObject term
    · rw [unwrapDomain, unwrapDomain, canon_of_object object]
      exact unwrap_object term
    · rw [canon_of_not_object object]
  equivalent object := by
    rw [canon_of_object object]
    exact unwrap_equivalent _ object
  same _ equivalent := unwrap_same equivalent
  closed object := by
    rw [canon_of_object object]
    exact unwrap_scoped _ 0

/-- **Removing `Wrap` gives canonical forms for the equation** on object terms. -/
theorem unwrap_canonical (relEnv : RelationEnv) : Canonical relEnv wrapped unwrapCanon unwrapDomain :=
  (unwrap_canonicalDetermined relEnv).canonical

/-! ## Coherence by simulation -/

/-- **The rule fires at the canonical form too**, at the canonical forms of the same parts. -/
theorem unwrap_simulates {redex : Pattern} {witness : Witness} {contractum : Pattern} (state : IsState redex)
    (_ : unwrapDomain redex = true) (valid : StepValid relEnv wrapped redex witness contractum) :
    ∃ witness' contractum', StepValid relEnv wrapped (unwrapCanon redex) witness' contractum' ∧
      (∀ label : StepLabel, label.admits witness = label.admits witness') ∧ unwrapCanon contractum' = unwrapCanon contractum := by
  cases valid with
  | @rule _ index rule initial final witnesses found matched premises =>
    obtain ⟨rfl, rfl⟩ : index = 0 ∧ rule = firstRule := by
      cases index with
      | zero =>
        simp only [wrapped, List.getElem?_cons_zero, Option.some.injEq] at found
        exact ⟨rfl, found.symm⟩
      | succ _ => simp [wrapped] at found
    cases premises
    rw [matchPatternForRule, matchPatternForRule_eq_syntactic_of_no_presentations rfl] at matched
    obtain ⟨first, second, rfl, foundFirst⟩ := matchRel_pair (matchPattern_sound matched)
    have pairObject : IsObject (pair first second) := state.2
    have firstObject : IsObject first := by
      have := (isObjectPatternList_iff [first, second]).mp pairObject
      exact this first List.mem_cons_self
    rw [canon_of_object pairObject, unwrap_pair]
    refine ⟨.rule 0 [("y", unwrap second), ("x", unwrap first)] [], unwrap first, ?_, fun label => ?_, ?_⟩
    · have valid' := StepValid.rule (relEnv := relEnv) (language := wrapped) (index := 0) (rule := firstRule)
        (source := pair (unwrap first) (unwrap second)) (initial := [("y", unwrap second), ("x", unwrap first)])
        (witnesses := []) rfl
        (by
          rw [matchPatternForRule, matchPatternForRule_eq_syntactic_of_no_presentations rfl]
          exact matchRel_complete (.apply (.cons .fvar (.cons .fvar .nil rfl) (by simp [mergeBindings])) rfl))
        (PremisesValid.nil _)
      rwa [show firstRule.right = .fvar "x" from rfl,
        scoped_x (sites := captureSites firstRule) (value := unwrap first) (by simp) (by decide)] at valid'
    · cases label <;> rfl
    · rw [show firstRule.right = .fvar "x" from rfl,
        scoped_x (sites := captureSites firstRule) foundFirst (by decide), canon_of_object firstObject]
      have twice := (unwrap_canonical relEnv).idempotent (term := first) firstObject
      rw [canon_of_object firstObject] at twice
      exact twice

theorem unwrap_coherent (fuel : ℕ) : Coherent relEnv wrapped fuel unwrapCanon unwrapDomain List.singleton :=
  coherent_of_simulation (unwrap_canonical relEnv) unwrap_simulates

/-! ## Verdicts -/

def ok : Pattern := constant "Ok"
def err : Pattern := constant "Err"

/-- `Wrap (Pair (Wrap Ok) Err)`. -/
def start : Pattern := wrap (pair (wrap ok) err)

/-- **Read as written it has no step**: the rule needs `Pair` at the root. -/
theorem stuck_as_written {witness : Witness} {target : Pattern} : ¬ StepValid relEnv wrapped start witness target := by
  intro valid
  cases valid with
  | @rule _ index rule _ _ _ found matched _ =>
    have isFirst : rule = firstRule := by
      cases index with
      | zero =>
        simp only [wrapped, List.getElem?_cons_zero, Option.some.injEq] at found
        exact found.symm
      | succ _ => simp [wrapped] at found
    subst isFirst
    rw [matchPatternForRule, matchPatternForRule_eq_syntactic_of_no_presentations rfl] at matched
    obtain ⟨_, _, same, -⟩ := matchRel_pair (matchPattern_sound matched)
    simp [start, wrap, pair] at same

abbrev Wrapped := referenceStructure RelationEnv.empty wrapped

def steps : Formula 0 := .possibly .any .top
def reachesOk : Formula 0 := .possibly .any (.is ok)
def oneResult : Formula 0 := Formula.exactlyOne .forward .any

theorem decided_true {formula : Formula 0} (behavioural : formula.behaviouralForward = true)
    (decided : decideCanonical RelationEnv.empty wrapped 2 unwrapCanon unwrapDomain List.singleton formula start 2 =
      some true) :
    Wrapped.sat Env.closed formula start :=
  (decideCanonical_sound (unwrap_canonical _) (unwrap_coherent 2) behavioural decided).mp rfl

/-- **Modulo the equation it steps.** -/
theorem wrapped_steps : Wrapped.sat Env.closed steps start := decided_true rfl (by decide +kernel)

/-- **It reaches `Ok`.** -/
theorem wrapped_reaches_ok : Wrapped.sat Env.closed reachesOk start := decided_true rfl (by decide +kernel)

/-- **It has exactly one result.** -/
theorem wrapped_one_result : Wrapped.sat Env.closed oneResult start := decided_true rfl (by decide +kernel)

/-! ## The front door -/

def wrapSignature : Mettapedia.OSLF.Framework.FiniteModels.Signature :=
  [.operation "Wrap" 1, .operation "Pair" 2, .operation "Ok" 0, .operation "Err" 0]

/-- The canonical forms, with their contract, as the front door takes them. -/
def wrapForms : CanonicalForms RelationEnv.empty wrapped 2 :=
  .ofCoherent (unwrap_canonical _) (unwrap_coherent 2)

theorem ask_wrapped_steps_answer :
    ask RelationEnv.empty wrapSignature wrapped 2 steps start none 2 (some wrapForms) = .proved (.canonicalRegion 2) := by
  decide +kernel

/-- **Given the canonical forms, the front door proves that it steps.** -/
theorem ask_wrapped_steps : Wrapped.sat Env.closed steps start := ask_proved ask_wrapped_steps_answer

/-- **Without them it leaves the question open.** -/
theorem front_door_open_as_written : ask RelationEnv.empty wrapSignature wrapped 2 steps start none 2 = .unknown 2 := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalUnwrapControls
