import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetDriver
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationFreeReadings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LanguageEquality

/-!
# Set readings declared with a language

A rule `{x, ...rest} ⇒ …` can read a set three ways (`SetReadings`): **consume** a matched member, **keep** it, or
**either**, the language's own semantics modulo the set laws. A language declares which (`DeclaredLanguage`), and the
reading holds at every boundary inside a step, through the reference relation's internal boundary policies:

- consume and keep present every term one way, the canonical form or the saturated one
  (`InternalBoundaryPolicy.presented`): a premise steps the presented child, and matches its target and a relation's
  answers as presented (`Readings.presentedOf`);
- either reads every boundary modulo the set laws (`InternalBoundaryPolicy.equational` with the equivalence of terms
  with one canonical form, `SetReadings.lawsReading`): a premise steps any presentation of its child, and matches its
  target and a relation's answers at any presentations of their values.

A language also declares where its native types range (`DeclaredStates`): over all its terms, or over the hereditary
terms of a sort with what they reach (`NativeStructure.GeneratedBy`), so that past modalities, counting of
predecessors and quantifiers over a type look only at those.

- **The structure a declaration fixes** (`nativeStructure`), and **what a verdict says** (`Holds`): the native type at
  the term's point in that structure, or, over the hereditary terms, at the term in the substructure they generate.
- **The front door of a declared language** (`askDeclared`). Over all terms (`askTerms`), consume and keep are decided
  by closed regions of their readings at the canonical form, listed by the fuel or, where derivations nest without
  bound, by a table of the region tabulated within the fuel (`decidePresented`); either is asked at the front door,
  with canonical forms for the reading modulo the set laws (`CanonicalCaptureModulo.moduloForms` and `tabledFormsAt`
  for hereditary set languages), or without them when the rules have no premises. Over the hereditary terms, the set
  driver (`SetReadings.askHereditary`) answers the membership language read as its own semantics, for formulas
  without relations (`setDriverAdmits`): the language has no premises, so its structure is the same in every relation
  environment but for its relations (`hereditary_membership_iff`). Every answer is exact in the declared structure
  (`askDeclared_sound`).
- **Either is consume over all presentations**: consume fires the rules at the canonical presentation and reads each
  internal boundary at the canonical presentation (`consume_step_iff`); either fires them at any presentation and reads
  each internal boundary at any presentation (`either_step_iff`); a step of consume is a step of either
  (`consume_either`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open SetReadings (consumeStructure keepStructure eitherStructure lawsReading saturate setWidth
  eitherStructure_of_premises_nil Hereditary IsHF HFNative membership hfRule hereditary_generated askHereditary
  askHereditary_sound)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern)

/-- **How a language reads its sets.** -/
inductive SetReading where
  /-- A member a rule matches leaves the set. -/
  | consume
  /-- A member a rule matches stays. -/
  | keep
  /-- Either, as the set laws allow: the language's own semantics. -/
  | either
  deriving DecidableEq, Repr

/-- **Where a language's native types range.** -/
inductive DeclaredStates where
  /-- Over all its terms. -/
  | terms
  /-- Over the hereditary terms of the sort, with what they reach. -/
  | hereditary (sort : String)
  deriving DecidableEq, Repr

/-- **A language with the set reading it declares**, and where its native types range. -/
structure DeclaredLanguage where
  language : LanguageDef
  sets : SetReading := .either
  states : DeclaredStates := .terms

variable (relEnv : RelationEnv) (declared : DeclaredLanguage)

/-- **The structure a declaration fixes.** -/
def nativeStructure : NativeStructure Pattern :=
  match declared.sets with
  | .consume => consumeStructure relEnv declared.language
  | .keep => keepStructure relEnv declared.language
  | .either => eitherStructure relEnv declared.language

/-- **Where a verdict is about**: the canonical form, whose sets the readings of consume and keep write their own way;
the term itself for the language's own semantics. -/
def pointOf (term : Pattern) : Pattern :=
  match declared.sets with
  | .either => term
  | _ => BagForms.sortBags term

/-- Whether a language's rules have no premises. -/
def premiseFree (language : LanguageDef) : Bool := language.rewrites.all fun rule => rule.premises.isEmpty

theorem premises_nil_of_premiseFree {language : LanguageDef} (free : premiseFree language = true) :
    ∀ rule ∈ language.rewrites, rule.premises = [] := fun rule member => by
  simpa using List.all_eq_true.mp free rule member

/-- **What a verdict of a declared language says**: over all terms, the native type at the term's point in the declared
structure; over the hereditary terms of a sort, the native type at the term in the substructure they generate. -/
def Holds (formula : Formula 0) (term : Pattern) : Prop :=
  match declared.states with
  | .terms => (nativeStructure relEnv declared).sat Env.closed formula (pointOf declared term)
  | .hereditary sort =>
    ∃ holds : (nativeStructure relEnv declared).GeneratedBy (Hereditary declared.language sort) term,
      (NativeStructure.restrict ((nativeStructure relEnv declared).generatedBy_generated
        (Hereditary declared.language sort))).sat Env.closed formula ⟨term, holds⟩

/-- **Canonical forms suit a declared language** when the structure they read is the declared one. -/
def FormsSuit {fuel : ℕ} (forms : Option (CanonicalForms relEnv declared.language fuel)) : Prop :=
  ∀ found, forms = some found → referenceStructure relEnv declared.language found.reading = nativeStructure relEnv declared

theorem formsSuit_none {fuel : ℕ} : FormsSuit relEnv declared (fuel := fuel) none := fun _ found => by cases found

/-- The verdict an answer gives. -/
def verdictOf : Answer → Option Bool
  | .proved _ => some true
  | .refuted _ => some false
  | _ => none

/-- **Decide in a presented reading**: by the fuel's listing, or, where that region does not close, by the table of the
region tabulated within the fuel. -/
def decidePresented (present : Pattern → Pattern) (fuel rounds : ℕ) (formula : Formula 0) (term : Pattern) :
    Option Bool :=
  (decideReading relEnv declared.language fuel present BagForms.sortBags formula term rounds).orElse fun _ =>
    decideTabled relEnv declared.language fuel present BagForms.sortBags formula term rounds

/-- **The front door over all terms**: consume and keep by closed regions of their readings; either by the front door,
with canonical forms for the reading modulo the set laws, or without them when the rules have no premises. -/
def askTerms (fuel rounds : ℕ) (formula : Formula 0) (term : Pattern)
    (forms : Option (CanonicalForms relEnv declared.language fuel) := none) : Option Bool :=
  match declared.sets with
  | .consume => decidePresented relEnv declared id fuel rounds formula term
  | .keep => decidePresented relEnv declared (saturate (setWidth declared.language + 1)) fuel rounds formula term
  | .either =>
    match forms with
    | some _ => verdictOf (ask relEnv [] declared.language fuel formula term none rounds forms)
    | none =>
      if premiseFree declared.language then verdictOf (ask relEnv [] declared.language fuel formula term none rounds none)
      else none

/-- **The set driver serves a declaration** over the hereditary terms of a sort: the membership language at its sort,
read as its own semantics, and a formula without relations. -/
def setDriverAdmits (sort : String) (formula : Formula 0) : Bool :=
  decide (declared.language = membership) && decide (sort = hfRule.category) && decide (declared.sets = .either) &&
    formula.relationFree

/-- **The front door of a declared language**: over all terms by the readings' front doors; over the hereditary terms
by the set driver, where it serves. -/
def askDeclared (fuel rounds : ℕ) (formula : Formula 0) (term : Pattern)
    (forms : Option (CanonicalForms relEnv declared.language fuel) := none) : Option Bool :=
  match declared.states with
  | .terms => askTerms relEnv declared fuel rounds formula term forms
  | .hereditary sort => if setDriverAdmits declared sort formula then askHereditary formula term else none

variable {relEnv declared}

/-- **A verdict of a presented reading is exact** at the canonical form. -/
theorem decidePresented_sound {present : Pattern → Pattern} {fuel rounds : ℕ} {formula : Formula 0}
    (behavioural : formula.behaviouralForward = true) {term : Pattern} {verdict : Bool}
    (decided : decidePresented relEnv declared present fuel rounds formula term = some verdict) :
    (verdict = true ↔
      (readingStructure relEnv declared.language present BagForms.sortBags).sat Env.closed formula
        (BagForms.sortBags term)) := by
  unfold decidePresented at decided
  cases listed : decideReading relEnv declared.language fuel present BagForms.sortBags formula term rounds with
  | some found =>
    rw [listed, Option.orElse_some] at decided
    cases decided
    exact decideReading_sound behavioural listed
  | none =>
    rw [listed, Option.orElse_none] at decided
    exact decideTabled_sound decided

theorem verdict_sound {fuel rounds : ℕ} {formula : Formula 0} {term : Pattern}
    {forms : Option (CanonicalForms relEnv declared.language fuel)} {verdict : Bool}
    (decided : verdictOf (ask relEnv [] declared.language fuel formula term none rounds forms) = some verdict) :
    (verdict = true ↔ (referenceStructure relEnv declared.language (formsReading forms)).sat Env.closed formula term) := by
  unfold verdictOf at decided
  split at decided
  · rename_i answered
    cases decided
    exact iff_of_true rfl (ask_proved answered)
  · rename_i answered
    cases decided
    exact iff_of_false (fun same => Bool.false_ne_true same) (ask_refuted answered)
  · cases decided

/-- **Every answer of the front door over all terms is exact** in the declared structure. -/
theorem askTerms_sound {fuel rounds : ℕ} {formula : Formula 0} (behavioural : formula.behaviouralForward = true)
    {term : Pattern} {verdict : Bool} {forms : Option (CanonicalForms relEnv declared.language fuel)}
    (suit : FormsSuit relEnv declared forms)
    (decided : askTerms relEnv declared fuel rounds formula term forms = some verdict) :
    (verdict = true ↔ (nativeStructure relEnv declared).sat Env.closed formula (pointOf declared term)) := by
  unfold askTerms at decided
  unfold pointOf
  split at decided
  · rename_i reading
    unfold nativeStructure
    rw [reading]
    exact decidePresented_sound behavioural decided
  · rename_i reading
    unfold nativeStructure
    rw [reading]
    exact decidePresented_sound behavioural decided
  · rename_i reading
    simp only [reading]
    split at decided
    · rename_i found
      rw [← suit found rfl]
      exact verdict_sound decided
    · split at decided
      · rename_i free
        have same := eitherStructure_of_premises_nil relEnv declared.language (premises_nil_of_premiseFree free)
        unfold nativeStructure
        rw [reading]
        simp only
        rw [same]
        exact verdict_sound decided
      · cases decided

/-- **The membership language has no premises.** -/
theorem membership_premiseFree : PremiseFree membership where
  rules rule member := by
    rw [show membership.rewrites = [SetReadings.memberRule] from rfl, List.mem_singleton] at member
    subst member
    rfl
  equations equation member := by
    rw [show membership.equations = [] from rfl] at member
    exact absurd member List.not_mem_nil

variable (relEnv) in
/-- **The hereditary terms of the membership language, in any relation environment**: a formula without relations
holds at a term among what the hereditary terms generate exactly where it holds among the hereditary terms with no
relations. -/
theorem hereditary_membership_iff {formula : Formula 0} (free : formula.relationFree = true) {term : Pattern} :
    (∃ holds : (eitherStructure relEnv membership).GeneratedBy (Hereditary membership hfRule.category) term,
        (NativeStructure.restrict ((eitherStructure relEnv membership).generatedBy_generated
          (Hereditary membership hfRule.category))).sat Env.closed formula ⟨term, holds⟩) ↔
      ∃ holds : IsHF term, HFNative.sat Env.closed formula ⟨term, holds⟩ := by
  obtain ⟨relations, same⟩ := referenceStructure_withRelations (reading := .syntax) relEnv RelationEnv.empty
    membership_premiseFree rfl
  rw [eitherStructure_of_premises_nil relEnv membership membership_premiseFree.rules, same,
    NativeStructure.sat_generatedBy_iff (hereditary_generated.withRelations relations)]
  refine exists_congr fun holds => ?_
  rw [NativeStructure.restrict_withRelations]
  exact NativeStructure.sat_withRelations _ _ formula free _ _

/-- **Every answer of a declared language's front door is exact** in the declared structure. -/
theorem askDeclared_sound {fuel rounds : ℕ} {formula : Formula 0}
    (behavioural : declared.states = .terms → formula.behaviouralForward = true)
    {term : Pattern} {verdict : Bool} {forms : Option (CanonicalForms relEnv declared.language fuel)}
    (suit : FormsSuit relEnv declared forms)
    (decided : askDeclared relEnv declared fuel rounds formula term forms = some verdict) :
    (verdict = true ↔ Holds relEnv declared formula term) := by
  unfold askDeclared at decided
  unfold Holds
  split at decided
  · rename_i states
    exact askTerms_sound (behavioural states) suit decided
  · rename_i sort states
    split at decided
    · rename_i admitted
      simp only [setDriverAdmits, Bool.and_eq_true, decide_eq_true_eq] at admitted
      obtain ⟨⟨⟨language, rfl⟩, sets⟩, free⟩ := admitted
      have structureEq : nativeStructure relEnv declared = eitherStructure relEnv membership := by
        unfold nativeStructure
        simp only [sets, language]
      rw [NativeStructure.sat_generatedBy_congr structureEq (congrArg (Hereditary · hfRule.category) language) formula
        term _ ((eitherStructure relEnv membership).generatedBy_generated _), hereditary_membership_iff relEnv free]
      obtain ⟨holds, answer⟩ := askHereditary_sound decided
      exact answer.trans ⟨fun satisfied => ⟨holds, satisfied⟩, fun ⟨_, satisfied⟩ => satisfied⟩
    · cases decided

/-! ## Either is consume over all presentations -/

variable (relEnv) in
/-- **Either fires the rules at any presentation and reads each internal boundary at any presentation**: under the
language's own labels, a step of either is a step of the reference relation at some presentation of the state, each
internal boundary read modulo the set laws, to an equivalent of the target. -/
theorem either_step_iff (language : LanguageDef) {label : StepLabel} (own : label.isContext = false)
    {source target : Pattern} :
    (eitherStructure relEnv language).step source label target ↔
      IsState source ∧ IsState target ∧ ∃ presentation, ObjectEquivalent relEnv language .syntax source presentation ∧
        IsState presentation ∧ ∃ witness contractum,
          StepValid relEnv language presentation witness contractum (.equational (canonSetoid BagForms.sortBags)) ∧
            IsState contractum ∧ ObjectEquivalent relEnv language .syntax contractum target ∧ label.admits witness = true := by
  constructor
  · rintro ⟨sourceState, targetState, presentation, contractum, witness, placed, presentationState, valid,
      contractumState, after, admits⟩
    rw [placed_iff own] at placed
    rw [StepLabel.base_of_isContext own] at admits
    exact ⟨sourceState, targetState, presentation, placed, presentationState, witness, contractum, valid, contractumState,
      after, admits⟩
  · rintro ⟨sourceState, targetState, presentation, presents, presentationState, witness, contractum, valid,
      contractumState, after, admits⟩
    refine ⟨sourceState, targetState, presentation, contractum, witness, (placed_iff own).mpr presents, presentationState,
      valid, contractumState, after, ?_⟩
    rw [StepLabel.base_of_isContext own]
    exact admits

variable (relEnv) in
/-- **Consume fires the rules at the canonical presentation and reads each internal boundary at the canonical
presentation**: its steps are the reference relation's at the state, through canonical forms at every internal boundary,
taken to canonical targets. -/
theorem consume_step_iff (language : LanguageDef) {label : StepLabel} {source target : Pattern} :
    (consumeStructure relEnv language).step source label target ↔
      IsState source ∧ IsState target ∧ ∃ witness contractum,
        StepValid relEnv language source witness contractum (.presented fun term => [BagForms.sortBags term]) ∧
          label.admits witness = true ∧ BagForms.sortBags contractum = target :=
  Iff.rfl

theorem isState_of_sortBags {term : Pattern} (state : IsState (BagForms.sortBags term)) : IsState term := by
  rw [BagForms.sortBags_eq_canon] at state
  refine ⟨?_, ?_⟩
  · rw [← BagForms.canon_wellScoped term 0]
    exact state.1
  · show isObjectPattern term = true
    rw [← BagForms.canon_object term]
    exact state.2

variable (relEnv) in
/-- **A step of consume is a step of either**, in a language whose states are equivalent to their canonical forms: the
canonical presentation of the state and of each internal boundary is one of the presentations either may read. -/
theorem consume_either (language : LanguageDef)
    (equivalent : ∀ term, IsState term → ObjectEquivalent relEnv language .syntax term (BagForms.sortBags term))
    {label : StepLabel} (own : label.isContext = false) {source target : Pattern}
    (step : (consumeStructure relEnv language).step source label target) :
    (eitherStructure relEnv language).step source label target := by
  obtain ⟨sourceState, targetState, witness, contractum, valid, admits, reached⟩ :=
    (consume_step_iff relEnv language).mp step
  subst reached
  have contractumState : IsState contractum := isState_of_sortBags targetState
  refine (either_step_iff relEnv language own).mpr ⟨sourceState, targetState, source, Relation.EqvGen.refl _,
    sourceState, witness, contractum, ?_, contractumState, equivalent contractum contractumState, admits⟩
  refine stepValid_equational_of_presented (fun term shown listed => ?_) _ valid
  rw [List.mem_singleton.mp listed]
  show BagForms.sortBags term = BagForms.sortBags (BagForms.sortBags term)
  rw [BagForms.sortBags_eq_canon, Mettapedia.OSLF.MeTTaIL.CanonicalBags.canon_idempotent]

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings
