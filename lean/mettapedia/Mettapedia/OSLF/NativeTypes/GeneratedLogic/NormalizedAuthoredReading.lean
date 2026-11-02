import Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedDriverReading
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.AuthoredControls

/-!
# The authored normalized profile, read at the front door

The authored profile (`Instances.Normalized.AuthoredControls.profile`) runs the language `One`, `Two`, `Done` with the
conditional equation `One = Two if allow(One)` and two rules `Two ⇒ Done`, natively: the plan's primitive receipts
modulo the equation, decided by the normal form that sends `One` to `Two`. The front door reads the same language in
its reference structure, with the provider's rows as the relation environment (`providerEnv`).

- **Equation steps between atoms are the authored ones** (`equationStep_cases`): a step either relates `One` and
  `Two`, by the equation, or relates two compound terms, since a hole inside a term leaves a term with arguments. The
  language declares no collections, so it derives no collection laws.
- **So identification is the normal form's equality** on the admitted atoms (`objectEquivalent_iff`), with `One`
  identified with `Two` by the equation, its query answered by the provider (`one_equivalent_two`).
- **Steps agree** (`reference_step_iff`, `driver_step_iff`): from an admitted atom, both step exactly from `One` and
  `Two` to `Done`.
- **The reading** (`reading`): the agreement, and the observation `Done` as the formula `is Done`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedReading.Authored

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchArgsRel matchPattern_iff_matchRel)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance)
open Mettapedia.OSLF.MeTTaIL.GeneralCompletedFrontierControls (language one two done equation consume snapshot term)
open Mettapedia.OSLF.NativeTypes.Instances.Normalized.AuthoredControls (profile generated normal raw raw_step_iff
  source_cases_of_typed literal_source generated_snapshot generated_plan normalizer)

/-- **The relation environment of the provider**: the rows `allow(One)`. -/
def providerEnv : RelationEnv :=
  Mettapedia.OSLF.Framework.GeneralCanonicalAgreement.providerRelEnv (snapshot true).provider

/-! ## Admitted terms -/

/-- **The admitted terms are the three atoms.** -/
theorem admitted_iff (source : Pattern) :
    Instances.Normalized.Source generated [] term source ↔ source = one ∨ source = two ∨ source = done := by
  constructor
  · intro typed
    rw [Instances.Normalized.Source, generated_snapshot] at typed
    exact source_cases_of_typed language rfl typed.1 typed.2.2.1
  · intro chosen
    have typed := literal_source source chosen
    unfold Instances.Normalized.Source
    rw [generated_snapshot]
    exact typed

/-! ## Equation steps -/

/-- A term with no arguments: an atom. -/
def IsAtom (pattern : Pattern) : Prop := ∃ label, pattern = .apply label []

theorem fill_not_atom {context : OneHoleContext} (inner : context ≠ .hole) (value : Pattern) :
    ¬ IsAtom (context.fill value) := by
  rintro ⟨label, same⟩
  cases context with
  | hole => exact inner rfl
  | apply constructor before inside after =>
    simp only [OneHoleContext.fill, Pattern.apply.injEq] at same
    have := congrArg List.length same.2
    simp at this
  | lambda => simp [OneHoleContext.fill] at same
  | multiLambda => simp [OneHoleContext.fill] at same
  | collection => simp [OneHoleContext.fill] at same
  | substBody => simp [OneHoleContext.fill] at same
  | substReplacement => simp [OneHoleContext.fill] at same

/-- The language declares no collections, so it derives no collection laws. -/
theorem no_derived {first second : Pattern} (derived : DerivedInstance language first second) : False := by
  cases derived with
  | bagPerm member typed _ | setPerm member typed _ | setDedup member typed =>
    obtain ⟨parameter, inside, _⟩ := typed
    simp only [language, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp at inside
  | flatten algebra _ _ | singleton algebra _ _ | unitElim algebra _ _ | emptyUnit algebra _ _ =>
    have member := algebra.authored
    have declared := algebra.declared
    simp only [language, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp at declared

theorem matchPattern_atom {label : String} {source : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (.apply label []) source) : source = .apply label [] := by
  rw [matchPattern_iff_matchRel] at matched
  cases matched with
  | apply arguments _ =>
    cases arguments
    rfl

/-- **An authored equation instance relates `One` and `Two`.** -/
theorem authored_cases {first second : Pattern} (instance' : AuthoredEquation providerEnv language first second) :
    (first = one ∧ second = two) ∨ (first = two ∧ second = one) := by
  cases instance' with
  | forward member _ matched _ =>
    simp only [language, List.mem_singleton] at member
    subst member
    exact .inl ⟨matchPattern_atom matched, rfl⟩
  | reverse member _ matched _ =>
    simp only [language, List.mem_singleton] at member
    subst member
    exact .inr ⟨matchPattern_atom matched, rfl⟩
  | declared member notRaw _ =>
    simp only [language, List.mem_singleton] at member
    subst member
    exact absurd notRaw (by decide)
  | premised member notRaw _ _ =>
    simp only [language, List.mem_singleton] at member
    subst member
    exact absurd notRaw (by decide)

/-- **An equation step relates `One` and `Two`, or two compound terms.** -/
theorem equationStep_cases {first second : Pattern} (step : EquationStep providerEnv language first second) :
    (first = one ∧ second = two) ∨ (first = two ∧ second = one) ∨ (¬ IsAtom first ∧ ¬ IsAtom second) := by
  cases step with
  | inContext context generator =>
    by_cases inner : context = .hole
    · subst inner
      rcases generator with authored | derived
      · rcases authored_cases authored with same | same
        · exact .inl same
        · exact .inr (.inl same)
      · exact absurd derived (fun derived => no_derived derived)
    · exact .inr (.inr ⟨fill_not_atom inner _, fill_not_atom inner _⟩)

/-- Whether a term is one of the admitted atoms. -/
def Admitted (pattern : Pattern) : Prop := pattern = one ∨ pattern = two ∨ pattern = done

theorem admitted_atom {pattern : Pattern} (admitted : Admitted pattern) : IsAtom pattern := by
  rcases admitted with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- **Equation steps keep which atom a term is**: `Done` only with itself, and the admitted atoms among themselves. -/
theorem objectStep_keeps {first second : Pattern} (step : ObjectStep providerEnv language .syntax first second) :
    (first = done ↔ second = done) ∧ (Admitted first ↔ Admitted second) := by
  obtain ⟨-, -, step⟩ := step
  rcases equationStep_cases step with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨firstCompound, secondCompound⟩
  · exact ⟨by simp [one, two, done], by simp [Admitted]⟩
  · exact ⟨by simp [one, two, done], by simp [Admitted]⟩
  · refine ⟨⟨fun same => absurd ⟨_, same⟩ firstCompound, fun same => absurd ⟨_, same⟩ secondCompound⟩,
      ⟨fun admitted => absurd (admitted_atom admitted) firstCompound,
        fun admitted => absurd (admitted_atom admitted) secondCompound⟩⟩

theorem objectEquivalent_keeps {first second : Pattern}
    (equivalent : ObjectEquivalent providerEnv language .syntax first second) :
    (first = done ↔ second = done) ∧ (Admitted first ↔ Admitted second) := by
  induction equivalent with
  | rel _ _ step => exact objectStep_keeps step
  | refl => exact ⟨Iff.rfl, Iff.rfl⟩
  | symm _ _ _ ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | trans _ _ _ _ _ first second => exact ⟨first.1.trans second.1, first.2.trans second.2⟩

/-- **`One` is identified with `Two`**: the equation's query is answered by the provider's rows. -/
theorem one_equivalent_two : ObjectEquivalent providerEnv language .syntax one two := by
  refine Relation.EqvGen.rel _ _ ⟨rfl, rfl, ?_⟩
  show EquationStep providerEnv language one two
  have instance' : AuthoredEquation providerEnv language one two := by
    have step := AuthoredEquation.forward (relEnv := providerEnv) (language := language) (equation := equation)
      (source := one) (initial := []) (final := []) (witnesses := [.base []]) (by simp [language]) rfl
      (by decide +kernel)
      (.cons (.base rfl (by decide +kernel)) (.nil []))
    have instantiated : applyBindingsScoped (captureSitesOf equation.left equation.premises) [] 0 equation.right = two := by
      decide +kernel
    rw [instantiated] at step
    exact step
  exact .inContext .hole (.inl instance')

/-- **On admitted atoms, identification is the normal form's equality.** -/
theorem objectEquivalent_iff {first second : Pattern} (firstAdmitted : Admitted first)
    (secondAdmitted : Admitted second) :
    ObjectEquivalent providerEnv language .syntax first second ↔ normal first = normal second := by
  constructor
  · intro equivalent
    have keeps := objectEquivalent_keeps equivalent
    rcases firstAdmitted with rfl | rfl | rfl <;> rcases secondAdmitted with rfl | rfl | rfl <;>
      simp_all [normal, one, two, done]
  · intro same
    rcases firstAdmitted with rfl | rfl | rfl <;> rcases secondAdmitted with rfl | rfl | rfl <;>
      first
      | exact .refl _
      | exact one_equivalent_two
      | exact .symm _ _ one_equivalent_two
      | (simp [normal, one, two, done] at same)

/-! ## Steps -/

/-- **A reference step from a term ends at `Done` and starts from a presentation of `Two`.** -/
theorem stepValid_cases {redex contractum : Pattern} {witness : Witness}
    (valid : StepValid providerEnv language redex witness contractum) : redex = two ∧ contractum = done := by
  cases valid with
  | rule found matched premises =>
    rename_i index rule initial final witnesses
    have shape : rule.left = two ∧ rule.right = done ∧ rule.premises = [] := by
      simp only [language] at found
      rcases index with _ | _ | index
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        exact ⟨rfl, rfl, rfl⟩
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        exact ⟨rfl, rfl, rfl⟩
      · simp at found
    obtain ⟨left, right, premiseFree⟩ := shape
    rw [ReflectiveCanonical.matchPatternForRule_eq_syntactic, left] at matched
    refine ⟨matchPattern_atom matched, ?_⟩
    rw [right]
    rfl

theorem isState_atom {pattern : Pattern} (admitted : Admitted pattern) : IsState pattern := by
  rcases admitted with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- **From an admitted atom, a reference step goes from `One` or `Two` to `Done`.** -/
theorem reference_step_iff {source target : Pattern} (admitted : Admitted source) :
    (referenceStructure providerEnv language).step source .any target ↔
      (source = one ∨ source = two) ∧ target = done := by
  constructor
  · rintro ⟨-, -, redex, contractum, witness, placed, -, valid, -, after, -⟩
    rw [placed_iff rfl] at placed
    obtain ⟨rfl, rfl⟩ := stepValid_cases valid
    have before := objectEquivalent_keeps placed
    have afterKeeps := objectEquivalent_keeps after
    refine ⟨?_, afterKeeps.1.mp rfl⟩
    rcases admitted with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr rfl
    · exact absurd (before.1.mp rfl) (by decide)
  · rintro ⟨from', rfl⟩
    have sourceAdmitted : Admitted source := admitted
    refine ⟨isState_atom sourceAdmitted, isState_atom (.inr (.inr rfl)), two, done, .rule 0 [] [], ?_,
      isState_atom (.inr (.inl rfl)), ?_, isState_atom (.inr (.inr rfl)), .refl _, rfl⟩
    · rw [placed_iff rfl]
      rcases from' with rfl | rfl
      · exact one_equivalent_two
      · exact .refl _
    · show StepValid providerEnv language two (.rule 0 [] []) done
      exact .rule (rule := consume "consume-first") rfl (by decide +kernel) (.nil [])

theorem normal_eq_iff_eqvGen (first second : Pattern) :
    Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan [] term) first second ↔
      normal first = normal second := by
  rw [generated_plan]
  exact ⟨normalizer.eqvGen_eq, fun same => .trans _ _ _ (normalizer.sound first)
    (same ▸ .symm _ _ (normalizer.sound second))⟩

/-- **The profile steps from `One` or `Two` to `Done`, and from nothing else.** -/
theorem driver_step_iff (source target : Pattern) :
    profile.system.Step source target ↔ (source = one ∨ source = two) ∧ target = done := by
  change (∃ representative result,
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan [] term) source representative ∧
        (∃ receipt, GeneralOccurrenceSemantics.Primitive generated.plan [] term representative receipt ∧
          receipt.target = result) ∧
        Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan [] term) result target) ↔ _
  simp only [normal_eq_iff_eqvGen]
  rw [generated_plan]
  constructor
  · rintro ⟨representative, result, before, firing, after⟩
    obtain ⟨rfl, rfl⟩ := (raw_step_iff representative result).mp firing
    constructor
    · by_cases same : source = one
      · exact .inl same
      · simp only [normal, same, if_false] at before
        exact .inr (before.trans (by decide))
    · by_cases same : target = one
      · subst same
        simp [normal, one, two, done] at after
      · simp only [normal, same, if_false] at after
        exact after.symm.trans (by decide)
  · rintro ⟨from', rfl⟩
    refine ⟨two, done, ?_, (raw_step_iff two done).mpr ⟨rfl, rfl⟩, rfl⟩
    rcases from' with rfl | rfl <;> decide

/-! ## The reading -/

theorem admitted_of_source {source : Pattern} (typed : Instances.Normalized.Source generated [] term source) :
    Admitted source :=
  (admitted_iff source).mp typed

/-- **The agreement**: on admitted atoms, steps and identification agree. -/
theorem agreement : Agreement profile providerEnv language .syntax (Instances.Normalized.Source generated [] term) where
  object _ typed := (LocalReading.isState_of_typed typed).2
  steps source typed target := by
    rw [reference_step_iff (admitted_of_source typed), driver_step_iff]
  closed source target _ step := by
    obtain ⟨-, rfl⟩ := (driver_step_iff source target).mp step
    exact (admitted_iff done).mpr (.inr (.inr rfl))
  equal first second firstTyped secondTyped :=
    objectEquivalent_iff (admitted_of_source firstTyped) (admitted_of_source secondTyped)

/-- The observation `Done` tests for `Done`. -/
theorem done_tests : Tests profile ⟨0, by decide⟩ done where
  observe pattern := by
    show (pattern == done) = true ↔ pattern = done
    exact beq_iff_eq
  admitted := (admitted_iff done).mpr (.inr (.inr rfl))
  normal := by decide

/-- **The authored profile's faithful reading at the front door.** -/
def reading : Embeddings.Faithful profile.driver providerEnv language
    (fun leaf : profile.Leaf => LocalReading.pairVariable leaf true)
    (fun leaf : profile.Leaf => LocalReading.pairVariable leaf false) :=
  NormalizedReading.reading profile providerEnv language .syntax agreement fun _ => some done

/-! ## Canonical forms -/

/-- The admitted atoms, decided. -/
def domain (pattern : Pattern) : Bool := pattern == one || pattern == two || pattern == done

theorem admitted_of_domain {pattern : Pattern} (inside : domain pattern = true) : Admitted pattern := by
  simp only [domain, Bool.or_eq_true, beq_iff_eq] at inside
  rcases inside with (rfl | rfl) | rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

theorem domain_of_admitted {pattern : Pattern} (admitted : Admitted pattern) : domain pattern = true := by
  rcases admitted with rfl | rfl | rfl <;> decide

theorem admitted_normal {pattern : Pattern} (admitted : Admitted pattern) : Admitted (normal pattern) := by
  rcases admitted with rfl | rfl | rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-- **The normal form gives canonical forms on the admitted atoms.** -/
theorem canonical : Canonical providerEnv language normal domain where
  object inside := (isState_atom (admitted_of_domain inside)).2
  admitted_canon inside := domain_of_admitted (admitted_normal (admitted_of_domain inside))
  invariant inside equivalent :=
    domain_of_admitted ((objectEquivalent_keeps equivalent).2.mp (admitted_of_domain inside))
  stepsAdmitted _ _ valid _ := by
    obtain ⟨-, rfl⟩ := stepValid_cases valid
    decide
  equivalent inside := by
    rcases admitted_of_domain inside with rfl | rfl | rfl
    · exact one_equivalent_two
    · exact .refl _
    · exact .refl _
  same inside equivalent := by
    have firstAdmitted := admitted_of_domain inside
    exact (objectEquivalent_iff firstAdmitted ((objectEquivalent_keeps equivalent).2.mp firstAdmitted)).mp
      equivalent
  closed inside := by
    rcases admitted_of_domain inside with rfl | rfl | rfl <;> rfl

/-- **Steps are listed at the canonical form itself**: a step from an equivalent of a canonical atom fires at `Two`,
which is the atom. -/
theorem coherent (fuel : ℕ) : Coherent providerEnv language (fuel + 1) normal domain List.singleton := by
  intro state redex witness contractum _ inside canonState complete before _ valid
  have stateAdmitted := admitted_of_domain inside
  obtain ⟨rfl, rfl⟩ := stepValid_cases valid
  have stateTwo : state = two := by
    rcases stateAdmitted with rfl | rfl | rfl
    · exact absurd canonState (by decide)
    · rfl
    · exact absurd ((objectEquivalent_keeps before).1.mp rfl) (by decide)
  subst stateTwo
  rw [enoughAt_singleton] at complete
  exact ⟨(witness, done), by rw [listedAt_singleton]; exact mem_stepsAt_of_enough complete valid, fun _ => rfl, rfl⟩

/-- **The canonical forms of the authored language**, for the front door. -/
def forms (fuel : ℕ) : CanonicalForms providerEnv language (fuel + 1) :=
  .ofCoherent canonical (coherent fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedReading.Authored
