import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Resumption

/-!
# Controls: closed regions modulo an equation

Three constants, the equation `A = B` and the rule `B ⇒ C` (`aliased`). Read as written, `A` has no
step (`a_stuck_as_written`). Modulo the equation, `A` and `B` are one element, and it steps to `C`.

- **Canonical forms** replace `A` by `B` throughout object terms (`aliasCanon`). They meet the contract
  (`alias_canonical`): the equation holds in every context, so `A` is replaced under constructors,
  binders and collections alike.
- **Coherence**: the rule fires only at `B` (`fires_only_at_b`), a canonical term, so every step from an
  equivalent of a canonical state is a step from the state itself (`alias_coherent`).
- **Verdicts from a closed canonical region**, grown for two rounds:
  - `A` steps (`a_steps`), and reaches `C` (`a_reaches_c`);
  - `C` has no step, so `A` has no two steps in a row (`a_no_two_steps`);
  - `A` is `B` (`a_is_b`), and is not `C` (`a_is_not_c`);
  - `A` has exactly one result (`a_one_result`): the steps from `A`'s class all lead to `C`.
- **The front door, given the canonical forms, answers with that evidence** (`ask_steps`,
  `ask_no_two_steps`, `ask_one_result`). Without them it leaves the question open
  (`front_door_open_as_written`): the language has an equation, so a closed region read as written gives
  no verdict, and nothing else found decides it.
- **Every behavioural formula about `A` is decided** in two rounds (`alias_decided`): `B` and `C` are a
  finite canonical closure of `A`.
- **Resumed work**: with no rounds the question is open (`progress_open`); resuming that progress for one
  round proves it from the canonical region the progress kept (`progress_resumed`), as asking afresh
  with one round does (`resumed_answer`).
- **Coherence is needed.** With the rule `A ⇒ C` instead, the same canonical forms still meet their
  contract, since it depends only on the equation (`AliasLaws`), but they are not coherent
  (`wrong_not_coherent`): `B` stands for `A`, and no step is listed at `B`. The canonical region then says
  that `A` cannot step (`wrong_region_says_stuck`), yet it does (`a_steps_wrong`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegionControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.Match (Bindings matchPattern)
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchArgsRel matchPattern_sound matchRel_complete)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic_of_no_presentations)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance CollectionCarrierRule AlgebraRule)

/-! ## The language -/

def constant (name : String) : Pattern := .apply name []

def constantRule (name : String) : GrammarRule :=
  { label := name, category := "Term", params := [], syntaxPattern := [.terminal name] }

/-- `A = B`. -/
def aliasEquation : Equation :=
  { name := "Alias", typeContext := [], premises := [], left := constant "A", right := constant "B" }

/-- `B ⇒ C`. -/
def fire : RewriteRule :=
  { name := "Fire", typeContext := [], premises := [], left := constant "B", right := constant "C" }

def aliased : LanguageDef :=
  { name := "Aliased", types := ["Term"], terms := [constantRule "A", constantRule "B", constantRule "C"],
    equations := [aliasEquation], rewrites := [fire] }

/-! ## Canonical forms -/

/-- A constructor applied to arguments, with `B` for `A`. -/
def renamed (name : String) : List Pattern → Pattern
  | [] => if name = "A" then constant "B" else .apply name []
  | argument :: arguments => .apply name (argument :: arguments)

mutual
/-- Replace every `A` by `B`. -/
def rename : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply name arguments => renamed name (renameList arguments)
  | .lambda binder body => .lambda binder (rename body)
  | .multiLambda arity names body => .multiLambda arity names (rename body)
  | .subst body replacement => .subst (rename body) (rename replacement)
  | .collection kind elements rest => .collection kind (renameList elements) rest

def renameList : List Pattern → List Pattern
  | [] => []
  | pattern :: patterns => rename pattern :: renameList patterns
end

/-- **Canonical forms**: object terms with every `A` replaced by `B`; other terms unchanged. -/
def aliasCanon (term : Pattern) : Pattern := if isObjectPattern term then rename term else term

theorem renameList_eq_map : ∀ patterns : List Pattern, renameList patterns = patterns.map rename
  | [] => rfl
  | pattern :: patterns => by rw [renameList, renameList_eq_map patterns, List.map_cons]

theorem renamed_of_ne_nil {name : String} {arguments : List Pattern} (nonempty : arguments ≠ []) :
    renamed name arguments = .apply name arguments := by
  cases arguments with
  | nil => exact absurd rfl nonempty
  | cons => rfl

theorem rename_a : rename (constant "A") = constant "B" := by simp [rename, renameList, renamed, constant]

theorem rename_b : rename (constant "B") = constant "B" := by simp [rename, renameList, renamed, constant]

theorem isObjectPatternList_iff : ∀ patterns : List Pattern,
    isObjectPatternList patterns = true ↔ ∀ pattern ∈ patterns, isObjectPattern pattern = true
  | [] => by simp [isObjectPatternList]
  | pattern :: patterns => by simp [isObjectPatternList, isObjectPatternList_iff patterns]

mutual
theorem rename_object : ∀ term : Pattern, isObjectPattern (rename term) = isObjectPattern term
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply name [] => by by_cases isA : name = "A" <;> simp [rename, renameList, renamed, isA, constant, isObjectPattern]
  | .apply name (argument :: arguments) => by
    have list := renameList_object (argument :: arguments)
    simp only [rename, renamed, renameList] at list ⊢
    simpa only [isObjectPattern] using list
  | .lambda _ body => by simpa only [rename, isObjectPattern] using rename_object body
  | .multiLambda _ _ body => by simpa only [rename, isObjectPattern] using rename_object body
  | .subst _ _ => rfl
  | .collection _ elements _ => by simp only [rename, isObjectPattern, renameList_object elements]

theorem renameList_object : ∀ patterns : List Pattern,
    isObjectPatternList (renameList patterns) = isObjectPatternList patterns
  | [] => rfl
  | pattern :: patterns => by
    simp only [renameList, isObjectPatternList, rename_object pattern, renameList_object patterns]
end

mutual
theorem rename_scoped : ∀ (term : Pattern) (depth : ℕ), (rename term).isWellScopedAt depth = term.isWellScopedAt depth
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply name [], _ => by
    by_cases isA : name = "A" <;> simp [rename, renameList, renamed, isA, constant, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]
  | .apply name (argument :: arguments), depth => by
    have list := renameList_scoped (argument :: arguments) depth
    simp only [rename, renamed, renameList] at list ⊢
    simpa only [Pattern.isWellScopedAt] using list
  | .lambda _ body, depth => by simpa only [rename, Pattern.isWellScopedAt] using rename_scoped body (depth + 1)
  | .multiLambda arity _ body, depth => by
    simpa only [rename, Pattern.isWellScopedAt] using rename_scoped body (depth + arity)
  | .subst body replacement, depth => by
    simp only [rename, Pattern.isWellScopedAt, rename_scoped body (depth + 1), rename_scoped replacement depth]
  | .collection _ elements _, depth => by
    simp only [rename, Pattern.isWellScopedAt, renameList_scoped elements depth]

theorem renameList_scoped : ∀ (patterns : List Pattern) (depth : ℕ),
    Pattern.isWellScopedListAt depth (renameList patterns) = Pattern.isWellScopedListAt depth patterns
  | [], _ => rfl
  | pattern :: patterns, depth => by
    simp only [renameList, Pattern.isWellScopedListAt, rename_scoped pattern depth, renameList_scoped patterns depth]
end

/-- The context with every `A` replaced by `B` outside its hole. -/
def renameContext : OneHoleContext → OneHoleContext
  | .hole => .hole
  | .apply name before inner after => .apply name (before.map rename) (renameContext inner) (after.map rename)
  | .lambda binder inner => .lambda binder (renameContext inner)
  | .multiLambda arity names inner => .multiLambda arity names (renameContext inner)
  | .substBody inner replacement => .substBody (renameContext inner) (rename replacement)
  | .substReplacement body inner => .substReplacement (rename body) (renameContext inner)
  | .collection kind before inner after rest =>
    .collection kind (before.map rename) (renameContext inner) (after.map rename) rest

/-- **Renaming commutes with filling a context.** -/
theorem rename_fill : ∀ (context : OneHoleContext) (pattern : Pattern),
    rename (context.fill pattern) = (renameContext context).fill (rename pattern)
  | .hole, _ => rfl
  | .apply name before inner after, pattern => by
    simp only [OneHoleContext.fill, renameContext, rename, renameList_eq_map, List.map_append, List.map_cons,
      rename_fill inner pattern]
    exact renamed_of_ne_nil (by simp)
  | .lambda _ inner, pattern => by simp only [OneHoleContext.fill, renameContext, rename, rename_fill inner pattern]
  | .multiLambda _ _ inner, pattern => by
    simp only [OneHoleContext.fill, renameContext, rename, rename_fill inner pattern]
  | .substBody inner _, pattern => by simp only [OneHoleContext.fill, renameContext, rename, rename_fill inner pattern]
  | .substReplacement _ inner, pattern => by
    simp only [OneHoleContext.fill, renameContext, rename, rename_fill inner pattern]
  | .collection _ before inner after _, pattern => by
    simp only [OneHoleContext.fill, renameContext, rename, renameList_eq_map, List.map_append, List.map_cons,
      rename_fill inner pattern]

/-! ## The equation's instances -/

theorem matchRel_constant {name : String} {term : Pattern} {bindings : Bindings}
    (matched : MatchRel (constant name) term bindings) : term = constant name := by
  cases matched with
  | apply arguments _ =>
    cases arguments
    rfl

/-- **The laws of the language**: the equation `A = B` over the three constants. The canonical forms
depend only on these, whatever the rules. -/
structure AliasLaws (language : LanguageDef) : Prop where
  equations : language.equations = [aliasEquation]
  terms : language.terms = [constantRule "A", constantRule "B", constantRule "C"]

theorem aliased_laws : AliasLaws aliased := ⟨rfl, rfl⟩

variable {language : LanguageDef}

theorem params_nil (laws : AliasLaws language) {rule : GrammarRule} (member : rule ∈ language.terms) :
    rule.params = [] := by
  rw [laws.terms] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem not_carrier (laws : AliasLaws language) {rule : GrammarRule} {kind : CollType} :
    ¬ CollectionCarrierRule language rule kind := by
  rintro ⟨authored, _, _, params⟩
  rw [params_nil laws authored] at params
  cases params

theorem not_algebra (laws : AliasLaws language) {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra} :
    ¬ AlgebraRule language rule kind algebra := by
  intro declared
  obtain ⟨_, params⟩ := declared.selfSorted
  rw [params_nil laws declared.authored] at params
  cases params

/-- Nullary declarations contain no collection-typed data occurrence. -/
theorem not_typed_collection (laws : AliasLaws language) {rule : GrammarRule} {kind : CollType}
    {elements : List Pattern} (member : rule ∈ language.terms) :
    ¬ Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule kind elements := by
  rintro ⟨_,inParams,_⟩
  rw [params_nil laws member] at inParams
  cases inParams

/-- The language declares no collections, so it derives no laws. -/
theorem no_derived (laws : AliasLaws language) {source target : Pattern} : ¬ DerivedInstance language source target := by
  intro derived
  cases derived with
  | bagPerm member kindTyped _ => exact not_typed_collection laws member kindTyped
  | setPerm member kindTyped _ => exact not_typed_collection laws member kindTyped
  | setDedup member kindTyped => exact not_typed_collection laws member kindTyped
  | flatten declared => exact not_algebra laws declared
  | singleton declared => exact not_algebra laws declared
  | unitElim declared => exact not_algebra laws declared
  | emptyUnit declared => exact not_algebra laws declared

variable {relEnv : RelationEnv}

/-- The equation's instances: `A` to `B`, and back. -/
theorem authored_alias (laws : AliasLaws language) {source target : Pattern}
    (authored : AuthoredEquation relEnv language source target) :
    (source = constant "A" ∧ target = constant "B") ∨ (source = constant "B" ∧ target = constant "A") := by
  cases authored with
  | forward member _ matched _ =>
    rw [laws.equations, List.mem_singleton] at member
    subst member
    exact Or.inl ⟨matchRel_constant (matchPattern_sound matched), rfl⟩
  | reverse member _ matched _ =>
    rw [laws.equations, List.mem_singleton] at member
    subst member
    exact Or.inr ⟨matchRel_constant (matchPattern_sound matched), rfl⟩
  | declared member notRaw _ =>
    rw [laws.equations, List.mem_singleton] at member
    subst member
    exact absurd notRaw (by decide)
  | premised member notRaw _ _ =>
    rw [laws.equations, List.mem_singleton] at member
    subst member
    exact absurd notRaw (by decide)

theorem rename_generator (laws : AliasLaws language) {source target : Pattern}
    (generator : Generator relEnv language source target) : rename source = rename target := by
  rcases generator with authored | derived
  · rcases authored_alias laws authored with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [rename_a, rename_b]
    · rw [rename_a, rename_b]
  · exact absurd derived (no_derived laws)

theorem canon_of_object {term : Pattern} (object : IsObject term) : aliasCanon term = rename term := if_pos object

theorem canon_of_not_object {term : Pattern} (notObject : ¬ IsObject term) : aliasCanon term = term :=
  if_neg notObject

theorem alias_same (laws : AliasLaws language) {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv language .syntax first second) : aliasCanon first = aliasCanon second := by
  induction equivalent with
  | rel first second step =>
    obtain ⟨firstObject, secondObject, step⟩ := step
    rw [canon_of_object firstObject, canon_of_object secondObject]
    cases step with
    | inContext context generator => rw [rename_fill, rename_fill, rename_generator laws generator]
  | refl => rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- `A` is `B` by one instance of the equation. -/
theorem alias_step (laws : AliasLaws language) : ObjectStep relEnv language .syntax (constant "A") (constant "B") := by
  refine ⟨rfl, rfl, ?_⟩
  exact EquationStep.inContext .hole (Or.inl (AuthoredEquation.forward (equation := aliasEquation) (initial := [])
    (by rw [laws.equations]; exact List.mem_singleton_self _) rfl (matchRel_complete (.apply .nil rfl))
    (PremisesValid.nil _)))

mutual
/-- **Every object term is equivalent to its renaming.** -/
theorem rename_equivalent (laws : AliasLaws language) :
    ∀ term : Pattern, IsObject term → ObjectEquivalent relEnv language .syntax term (rename term)
  | .bvar _, _ => Relation.EqvGen.refl _
  | .fvar _, _ => Relation.EqvGen.refl _
  | .apply name [], _ => by
    by_cases isA : name = "A"
    · subst isA
      rw [show rename (.apply "A" []) = constant "B" from rename_a]
      exact Relation.EqvGen.rel _ _ (alias_step laws)
    · rw [show rename (.apply name []) = .apply name [] by simp [rename, renameList, renamed, isA]]
      exact Relation.EqvGen.refl _
  | .apply name (argument :: arguments), object => by
    have listObject : isObjectPatternList (argument :: arguments) = true := object
    have each := renameList_equivalent laws (argument :: arguments) listObject
    have congr := ObjectEquivalent.list_congr rename (fun pattern object => (rename_object pattern).trans object)
      (.apply name) (.apply name · .hole ·) (fun _ _ _ => rfl)
      (fun patterns all => (isObjectPatternList_iff patterns).mpr all) (argument :: arguments) []
      (fun _ member => nomatch member)
      fun member inside => ⟨(isObjectPatternList_iff _).mp listObject member inside, each member inside⟩
    rw [List.nil_append, List.nil_append] at congr
    rw [show rename (.apply name (argument :: arguments)) = .apply name ((argument :: arguments).map rename) by
      simp only [rename, renameList, renamed, renameList_eq_map, List.map_cons]]
    exact congr
  | .lambda binder body, object =>
    ObjectEquivalent.fill (.lambda binder .hole) (fun _ inner => inner) (rename_equivalent laws body object)
  | .multiLambda arity names body, object =>
    ObjectEquivalent.fill (.multiLambda arity names .hole) (fun _ inner => inner)
      (rename_equivalent laws body object)
  | .subst _ _, object => by simp [IsObject, isObjectPattern] at object
  | .collection kind elements rest, object => by
    cases rest with
    | some _ => simp [IsObject, isObjectPattern] at object
    | none =>
      have listObject : isObjectPatternList elements = true := by simpa [IsObject, isObjectPattern] using object
      have each := renameList_equivalent laws elements listObject
      have congr := ObjectEquivalent.list_congr rename (fun pattern object => (rename_object pattern).trans object)
        (.collection kind · none) (.collection kind · .hole · none) (fun _ _ _ => rfl)
        (fun patterns all => by
          show isObjectPattern (.collection kind patterns none) = true
          simpa [isObjectPattern] using (isObjectPatternList_iff patterns).mpr all) elements []
        (fun _ member => nomatch member)
        fun member inside => ⟨(isObjectPatternList_iff _).mp listObject member inside, each member inside⟩
      rw [List.nil_append, List.nil_append] at congr
      rw [show rename (.collection kind elements none) = .collection kind (elements.map rename) none by
        simp only [rename, renameList_eq_map]]
      exact congr

theorem renameList_equivalent (laws : AliasLaws language) : ∀ patterns : List Pattern,
    isObjectPatternList patterns = true → ∀ pattern ∈ patterns, ObjectEquivalent relEnv language .syntax pattern (rename pattern)
  | [], _ => fun _ member => nomatch member
  | pattern :: patterns, objects => by
    simp only [isObjectPatternList, Bool.and_eq_true] at objects
    have head := rename_equivalent laws pattern objects.1
    have tail := renameList_equivalent laws patterns objects.2
    intro member inside
    rcases List.mem_cons.mp inside with rfl | inside
    · exact head
    · exact tail member inside
end

/-- The domain of the canonical forms: object terms. -/
def aliasDomain (term : Pattern) : Bool := isObjectPattern term

/-- **Replacing `A` by `B` gives canonical forms for the equation** on object terms, in any language with
these laws. -/
theorem alias_canonicalDetermined (laws : AliasLaws language) (relEnv : RelationEnv) :
    CanonicalDetermined relEnv language aliasCanon aliasDomain where
  object admitted := admitted
  determined term := by
    by_cases object : IsObject term
    · rw [aliasDomain, aliasDomain, canon_of_object object]
      exact rename_object term
    · rw [canon_of_not_object object]
  equivalent object := by
    rw [canon_of_object object]
    exact rename_equivalent laws _ object
  same _ equivalent := alias_same laws equivalent
  closed object := by
    rw [canon_of_object object]
    exact rename_scoped _ 0

/-- And so canonical forms on their domain. -/
theorem alias_canonical (laws : AliasLaws language) (relEnv : RelationEnv) :
    Canonical relEnv language aliasCanon aliasDomain :=
  (alias_canonicalDetermined laws relEnv).canonical

/-! ## Coherence -/

/-- **The rule fires only at `B`.** -/
theorem fires_only_at_b {redex : Pattern} {witness : Witness} {contractum : Pattern}
    (valid : StepValid relEnv aliased redex witness contractum) : redex = constant "B" := by
  cases valid with
  | @rule _ index rule _ _ _ found matched _ =>
    have isFire : rule = fire := by
      cases index with
      | zero =>
        simp only [aliased, List.getElem?_cons_zero, Option.some.injEq] at found
        exact found.symm
      | succ _ => simp [aliased] at found
    subst isFire
    rw [matchPatternForRule, matchPatternForRule_eq_syntactic_of_no_presentations rfl] at matched
    exact matchRel_constant (matchPattern_sound matched)

theorem alias_coherent (fuel : ℕ) : Coherent relEnv aliased fuel aliasCanon aliasDomain List.singleton :=
  coherent_of_canonical_redexes (alias_canonical aliased_laws relEnv) fun _ valid => by
    rw [fires_only_at_b valid, canon_of_object rfl, rename_b]

/-- **Read as written, `A` has no step.** -/
theorem a_stuck_as_written {witness : Witness} {target : Pattern} :
    ¬ StepValid relEnv aliased (constant "A") witness target := fun valid =>
  absurd (fires_only_at_b valid) (by decide)

/-! ## Verdicts -/

abbrev Aliased := referenceStructure RelationEnv.empty aliased

def steps : Formula 0 := .possibly .any .top
def reachesC : Formula 0 := .possibly .any (.is (constant "C"))
def twoSteps : Formula 0 := .possibly .any steps
def isB : Formula 0 := .is (constant "B")
def isNotC : Formula 0 := .isNot (constant "C")
def oneResult : Formula 0 := Formula.exactlyOne .forward .any

theorem decided_true {formula : Formula 0} (behavioural : formula.behaviouralForward = true)
    (decided : decideCanonical RelationEnv.empty aliased 2 aliasCanon aliasDomain List.singleton formula
      (constant "A") 2 = some true) :
    Aliased.sat Env.closed formula (constant "A") :=
  (decideCanonical_sound (alias_canonical aliased_laws _) (alias_coherent 2) behavioural decided).mp rfl

theorem decided_false {formula : Formula 0} (behavioural : formula.behaviouralForward = true)
    (decided : decideCanonical RelationEnv.empty aliased 2 aliasCanon aliasDomain List.singleton formula
      (constant "A") 2 =
      some false) :
    ¬ Aliased.sat Env.closed formula (constant "A") := fun holds =>
  Bool.false_ne_true
    ((decideCanonical_sound (alias_canonical aliased_laws _) (alias_coherent 2) behavioural decided).mpr holds)

/-- **Modulo the equation, `A` steps.** -/
theorem a_steps : Aliased.sat Env.closed steps (constant "A") := decided_true rfl (by decide +kernel)

/-- **It reaches `C`.** -/
theorem a_reaches_c : Aliased.sat Env.closed reachesC (constant "A") := decided_true rfl (by decide +kernel)

/-- **`C` has no step, so there are no two steps in a row.** -/
theorem a_no_two_steps : ¬ Aliased.sat Env.closed twoSteps (constant "A") := decided_false rfl (by decide +kernel)

/-- **`A` is `B`.** -/
theorem a_is_b : Aliased.sat Env.closed isB (constant "A") := decided_true rfl (by decide +kernel)

/-- **`A` is not `C`.** -/
theorem a_is_not_c : Aliased.sat Env.closed isNotC (constant "A") := decided_true rfl (by decide +kernel)

/-- **`A` has exactly one result.** -/
theorem a_one_result : Aliased.sat Env.closed oneResult (constant "A") := decided_true rfl (by decide +kernel)

/-! ## The front door -/

def aliasSignature : Mettapedia.OSLF.Framework.FiniteModels.Signature :=
  [.operation "A" 0, .operation "B" 0, .operation "C" 0]

/-- The canonical forms, with their contract, as the front door takes them. -/
def aliasForms : CanonicalForms RelationEnv.empty aliased 2 :=
  .ofCoherent (alias_canonical aliased_laws _) (alias_coherent 2)

theorem ask_steps_answer :
    ask RelationEnv.empty aliasSignature aliased 2 steps (constant "A") none 2 (some aliasForms) =
      .proved (.canonicalRegion 2) := by
  decide +kernel

/-- **Given the canonical forms, the front door proves that `A` steps.** -/
theorem ask_steps : Aliased.sat Env.closed steps (constant "A") := ask_proved ask_steps_answer

theorem ask_no_two_steps_answer :
    ask RelationEnv.empty aliasSignature aliased 2 twoSteps (constant "A") none 2 (some aliasForms) =
      .refuted (.canonicalRegion 2) := by
  decide +kernel

/-- **And refutes two steps in a row.** -/
theorem ask_no_two_steps : ¬ Aliased.sat Env.closed twoSteps (constant "A") := ask_refuted ask_no_two_steps_answer

theorem ask_one_result_answer :
    ask RelationEnv.empty aliasSignature aliased 2 oneResult (constant "A") none 2 (some aliasForms) =
      .proved (.canonicalRegion 2) := by
  decide +kernel

/-- **And proves exactly one result.** -/
theorem ask_one_result : Aliased.sat Env.closed oneResult (constant "A") := ask_proved ask_one_result_answer

/-- **Without canonical forms the front door leaves it open.** -/
theorem front_door_open_as_written :
    ask RelationEnv.empty aliasSignature aliased 2 steps (constant "A") none 2 = .unknown 2 := by
  decide +kernel

/-! ## Completeness -/

/-- The canonical forms `A` reaches. -/
def aliasClosure : List Pattern := [constant "B", constant "C"]

theorem alias_closure :
    CanonicalClosure RelationEnv.empty aliased 2 aliasCanon aliasDomain List.singleton (constant "A") aliasClosure where
  subject := by decide +kernel
  admitted := by decide +kernel
  canonical := by decide +kernel
  start := by decide +kernel
  presented := by decide +kernel
  closed := by decide +kernel
  listed := by decide +kernel

/-- **Every behavioural formula about `A` is decided** by the front door in two rounds. -/
theorem alias_decided {formula : Formula 0} (behavioural : formula.behaviouralForward = true)
    (hint : Option CertificateCandidate) :
    ∃ evidence,
      ask RelationEnv.empty aliasSignature aliased 2 formula (constant "A") hint 2 (some aliasForms) = .proved evidence ∨
        ask RelationEnv.empty aliasSignature aliased 2 formula (constant "A") hint 2 (some aliasForms) =
          .refuted evidence :=
  ask_decides_modulo aliasForms alias_closure ((Formula.behaviouralIn_all formula).trans behavioural) (by decide) hint

/-! ## Resumed work -/

theorem progress_open :
    (Progress.at RelationEnv.empty aliased 2 aliasSignature steps (constant "A") aliasCanon List.singleton 0).answer
      RelationEnv.empty 2
      (some aliasForms) none = .unknown 0 := by
  decide +kernel

theorem progress_resumed :
    ((Progress.at RelationEnv.empty aliased 2 aliasSignature steps (constant "A") aliasCanon List.singleton 0).resume
      RelationEnv.empty 2
      aliasCanon List.singleton 1).answer RelationEnv.empty 2 (some aliasForms) none = .proved (.canonicalRegion 1) :=
        by
  decide +kernel

/-- The resumed answer is the front door's with one round. -/
theorem progress_resumed_is_ask :
    ask RelationEnv.empty aliasSignature aliased 2 steps (constant "A") none 1 (some aliasForms) =
      .proved (.canonicalRegion 1) :=
  (resumed_answer RelationEnv.empty 2 (some aliasForms) none 0 1).symm.trans progress_resumed

/-! ## Coherence is needed -/

/-- `A ⇒ C`: the rule fires at `A`, which the canonical forms replace. -/
def fireA : RewriteRule := { fire with name := "FireA", left := constant "A" }

def aliasedWrong : LanguageDef := { aliased with name := "AliasedWrong", rewrites := [fireA] }

theorem aliasedWrong_laws : AliasLaws aliasedWrong := ⟨rfl, rfl⟩

/-- `A` steps to `C` as written. -/
theorem a_fires : StepValid RelationEnv.empty aliasedWrong (constant "A") (.rule 0 [] []) (constant "C") :=
  .rule (rule := fireA) rfl
    (by
      rw [matchPatternForRule, matchPatternForRule_eq_syntactic_of_no_presentations rfl]
      exact matchRel_complete (.apply .nil rfl))
    (PremisesValid.nil _)

/-- **The canonical forms are not coherent for this rule**: `B` stands for `A`, and no step is listed at `B`. -/
theorem wrong_not_coherent : ¬ Coherent RelationEnv.empty aliasedWrong 2 aliasCanon aliasDomain List.singleton := by
  intro coherent
  obtain ⟨entry, member, -⟩ := @coherent (constant "B") (constant "A") (.rule 0 [] []) (constant "C") ⟨rfl, rfl⟩
    rfl (by decide +kernel) (by decide +kernel)
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (alias_step aliasedWrong_laws))) ⟨rfl, rfl⟩ a_fires
  have empty : stepsAt RelationEnv.empty aliasedWrong 2 (constant "B") = [] := by decide +kernel
  rw [listedAt_singleton, empty] at member
  cases member

/-- **Without coherence the canonical region misleads**: it says that `A` cannot step. -/
theorem wrong_region_says_stuck :
    decideCanonical RelationEnv.empty aliasedWrong 2 aliasCanon aliasDomain List.singleton steps (constant "A") 2 =
      some false := by
  decide +kernel

theorem a_steps_wrong_answer :
    ask RelationEnv.empty aliasSignature aliasedWrong 2 steps (constant "A") none 2 = .proved (.exploration 2) := by
  decide +kernel

/-- **Yet `A` steps.** -/
theorem a_steps_wrong : (referenceStructure RelationEnv.empty aliasedWrong).sat Env.closed steps (constant "A") :=
  ask_proved a_steps_wrong_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegionControls
