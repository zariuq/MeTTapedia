import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceProjection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.AbsenceNotCompositional
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps

/-!
# Take-and-make rule sets are process calculi, through heating

A **rule set** is a property of rule instances. Being in a fragment is a property of rule sets; no
rule of the language is forbidden. The **take–make fragment** (`TakeMake`) holds the rule sets
whose rules read nothing and check nothing: their firings only take and make (and tell).

Fix one solution `σ` of the knowledge, as a hosted calculus does when it reads a store as a term
(rho uses the identity). The step restricted to a rule set `R` at `σ` (`RuleStep`) fires a rule of
`R` and keeps `σ` a model of the result's knowledge. Its view of a configuration is the bag of its
labels read at `σ` (`view`), and the reaction of `R` (`reaction`) consumes a rule's takes and
produces its makes.

* `view_functionalBisimulation`: on a take–make rule set, the view is a functional bisimulation
  from the step at `σ` onto the store step of the reaction (from
  `PositiveResourceProjection.no_read_firing_iff_frame`).
* `heating_bisimulation`: composed with heating, the relation "the view is the heating of the term"
  is a **strong bisimulation** between the step restricted to `R` and reduction of terms modulo
  associativity, unit and symmetry of their composition (`StoreComposition.Reduces`). Every
  take–make rule set is a process calculus in the chemical-abstract-machine sense.

**Where the structural congruence enters.** Only on the term side, and only through heating:
`encodes_iff_congruent` shows that a configuration encodes exactly one congruence class, so the
store is the class itself; the step never applies the congruence. On the term side it is needed,
since context rules alone miss reactions across components
(`StoreComposition.Controls.local_misses_joint`).

## Controls

* Positive: every rule set without reads and checks is in the fragment; the theorem asks nothing
  else of the rule set (of the step it asks equality as the matching relation and a supply of fresh
  occurrence identities). `Controls.make_has_heating_bisimulation`: the rule set holding only
  `make T`, which is `spawn` without its guard, has one over ground terms (`Controls.fresh_supply`).
* `Controls.absence_has_no_heating_bisimulation`: the rule set holding only `spawn` (make `T` where
  `U` is absent), just outside the fragment (`Controls.spawn_outside`), has **no** reaction whose
  reduction modulo the congruence is bisimilar to its step through heating, on the same modelled
  configurations. Reduction is closed under parallel composition (`Composition.reduces_parClosed`),
  while `spawn` is refused beside a `U`.
* `Controls.make_has_none_over_all_configurations`: over all configurations, with the knowledge
  ignored, even `make T` has no such bisimulation, since a configuration whose knowledge has no
  solution encodes a term and never fires. A negation stated there would not isolate absence, so the
  comparison is made on modelled configurations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep

open MeTTaCalculus.OccurrenceCommits (labels)
open PositiveResourceProjection StoreComposition
open TransitionMaps

namespace HeatingBisimulation

universe uT uS uO

/-- A rule set: a property of rule instances. -/
abbrev RuleSet (T : Type uT) := RuleInstance T → Prop

/-- **The take–make fragment**: every rule reads nothing and checks nothing. -/
def TakeMake {T : Type uT} (R : RuleSet T) : Prop :=
  ∀ rule, R rule → rule.read = [] ∧ rule.checks = []

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T) (σ : S)

/-- **The step restricted to a rule set, at one solution.** -/
def RuleStep (R : RuleSet T) (before after : Configuration T O) : Prop :=
  ∃ rule, R rule ∧ ConstraintMultisetRewriting.Step A label rule before after ∧ A.Models σ after.equations

/-- The view of a configuration at `σ`: the bag of its labels read at `σ`. -/
def view (C : Configuration T O) : Multiset T := labels (realized A σ label) C.present

/-- The reaction of a rule set at `σ`: a rule's takes become its makes, where `σ` models its tells. -/
def reaction (R : RuleSet T) : Reaction T := fun consumed produced =>
  ∃ rule, R rule ∧ A.Models σ rule.tell ∧ consumed = (rule.take.map (A.apply σ) : Multiset T) ∧
    produced = (rule.produce.map (A.apply σ) : Multiset T)

/-- The configurations whose knowledge `σ` models. -/
abbrev Modelled := {C : Configuration T O // A.Models σ C.equations}

/-- The step restricted to `R`, on configurations modelled by `σ`. -/
def modelledStep (R : RuleSet T) (C C' : Modelled A σ (O := O)) : Prop := RuleStep A label σ R C.1 C'.1

variable {A label σ}

theorem RuleStep.modelled {R : RuleSet T} {C C' : Configuration T O}
    (step : RuleStep A label σ R C C') : A.Models σ C'.equations := by
  obtain ⟨_, _, _, solved⟩ := step
  exact solved

/-- **Projection**: a firing of a take–make rule moves the view by a store step of the reaction. -/
theorem view_step [DecidableEq T] {R : RuleSet T} (fragment : TakeMake R) (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    {C C' : Configuration T O} (step : RuleStep A label σ R C C') :
    StoreStep (reaction A σ R) (view A label σ C) (view A label σ C') := by
  obtain ⟨rule, member, ⟨selection, valid, rfl⟩, solved⟩ := step
  obtain ⟨noReads, noChecks⟩ := fragment rule member
  obtain ⟨_, tells, frame, source, target⟩ :=
    (no_read_firing_iff_frame A σ label structural supply rule noReads noChecks C _).mp
      ⟨selection, valid, solved, rfl⟩
  exact ⟨_, _, frame, ⟨rule, member, tells, rfl, rfl⟩, source.trans (add_comm _ _),
    target.trans (add_comm _ _)⟩

/-- **Lift**: every store step of the reaction from the view of a modelled configuration is the
view of a firing of the rule set. -/
theorem view_lift [DecidableEq T] {R : RuleSet T} (fragment : TakeMake R) (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    {C : Configuration T O} (modelled : A.Models σ C.equations) {after : Multiset T}
    (step : StoreStep (reaction A σ R) (view A label σ C) after) :
    ∃ C', RuleStep A label σ R C C' ∧ view A label σ C' = after := by
  obtain ⟨_, _, frame, ⟨rule, member, tells, rfl, rfl⟩, source, rfl⟩ := step
  obtain ⟨noReads, noChecks⟩ := fragment rule member
  obtain ⟨selection, valid, solved, target⟩ :=
    (no_read_firing_iff_frame A σ label structural supply rule noReads noChecks C
      (frame + (rule.produce.map (A.apply σ) : Multiset T))).mpr
      ⟨modelled, tells, frame, source.trans (add_comm _ _), rfl⟩
  exact ⟨_, ⟨rule, member, ⟨selection, valid, rfl⟩, solved⟩, target.trans (add_comm _ _)⟩

/-- **The view is a functional bisimulation** from the step restricted to a take–make rule set at
`σ` onto the store step of its reaction. -/
theorem view_functionalBisimulation [DecidableEq T] {R : RuleSet T} (fragment : TakeMake R)
    (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value) :
    FunctionalBisimulation (modelledStep A label σ R) (StoreStep (reaction A σ R))
      (fun C : Modelled A σ (O := O) => view A label σ C.1) := by
  refine ⟨fun step => view_step fragment structural supply step, fun {C after} step => ?_⟩
  obtain ⟨C', step', viewed⟩ := view_lift fragment structural supply C.2 step
  exact ⟨⟨C', step'.modelled⟩, step', viewed⟩

/-- A configuration encodes a term when its view is the term's heating. -/
def Encodes (C : Modelled A σ (O := O)) (t : Term T) : Prop := view A label σ C.1 = Term.heat t

/-- **Heating is a strong bisimulation between the step restricted to a take–make rule set and
reduction modulo the congruence.** The step is `RuleStep`, which keeps only firings whose resulting
knowledge is satisfied at the chosen solution (`A.Models σ after.equations`). -/
theorem heating_bisimulation [DecidableEq T] {R : RuleSet T} (fragment : TakeMake R)
    (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value) :
    IsBisimulation (modelledStep A label σ R) (Reduces (reaction A σ R)) (Encodes (label := label)) := by
  refine ⟨fun {C t C'} encodes step => ?_, fun {C t t'} encodes reduces => ?_⟩
  · have moved := view_step fragment structural supply step
    rw [show view A label σ C.1 = Term.heat t from encodes] at moved
    obtain ⟨t', reduces, heated⟩ := storeStep_reduces moved
    exact ⟨t', reduces, heated.symm⟩
  · have moved := reduces_heat reduces
    rw [← show view A label σ C.1 = Term.heat t from encodes] at moved
    obtain ⟨C', step, viewed⟩ := view_lift fragment structural supply C.2 moved
    exact ⟨⟨C', step.modelled⟩, step, viewed⟩

omit [DecidableEq O] in
/-- **A configuration encodes exactly one congruence class**: the structural congruence enters only
through heating. -/
theorem encodes_iff_congruent {C : Modelled A σ (O := O)} {t u : Term T}
    (encodes : Encodes (label := label) C t) :
    Encodes (label := label) C u ↔ Term.Congruent t u := by
  rw [Term.congruent_iff_heat]
  exact ⟨fun other => (show Term.heat t = view A label σ C.1 from encodes.symm).trans other,
    fun same => (show view A label σ C.1 = Term.heat t from encodes).trans same⟩

end HeatingBisimulation

/-! ## Absence has no heating bisimulation -/

namespace HeatingBisimulation.Controls

open NamesOnTheStep NamesOnTheStep.IssuingControls

/-- The rule set holding only `spawn`: make `T` where `U` is absent. -/
def spawnOnly : RuleSet Expr := (· = NullsOnTheStep.Separations.spawn)

/-- `spawn` checks, so its rule set is just outside the take–make fragment. -/
theorem spawn_outside : ¬ TakeMake spawnOnly := by
  intro fragment
  have noChecks := (fragment NullsOnTheStep.Separations.spawn rfl).2
  simp [NullsOnTheStep.Separations.spawn, rule] at noChecks

/-- The rule `make T`: `spawn` without its guard. -/
def makeT : RuleInstance Expr := rule [] [] [factT]

/-- The rule set holding only `make T`. -/
def makeOnly : RuleSet Expr := (· = makeT)

/-- `make T` reads and checks nothing: its rule set is in the take–make fragment. -/
theorem make_inside : TakeMake makeOnly := by
  rintro r rfl
  exact ⟨rfl, rfl⟩

/-- **Fresh occurrence identities for every label** over ground terms: a copy number beyond those in
use. -/
theorem fresh_supply (used : Finset Occ) (value : Expr) :
    ∃ occurrence : Occ, occurrence ∉ used ∧ occurrence.1 = value := by
  refine ⟨(value, used.sup Prod.snd + 1), fun member => ?_, rfl⟩
  have bound : (value, used.sup Prod.snd + 1).2 ≤ used.sup Prod.snd :=
    Finset.le_sup (f := Prod.snd) member
  change used.sup Prod.snd + 1 ≤ used.sup Prod.snd at bound
  omega

/-- **Comparison inside the fragment**: `make T` has a heating bisimulation on the configurations
whose knowledge the identity models (`heating_bisimulation`). -/
theorem make_has_heating_bisimulation :
    ∃ react : Reaction Expr, IsBisimulation (modelledStep ground (Prod.fst : Occ → Expr) () makeOnly)
      (Reduces react) (Encodes (label := (Prod.fst : Occ → Expr))) :=
  ⟨reaction ground () makeOnly, heating_bisimulation make_inside rfl fresh_supply⟩

/-- **Control.** No reaction's reduction modulo the congruence is bisimilar, through heating, to the
step of the absence-guarded rule set `spawnOnly`, on the configurations whose knowledge the identity
models: the setting of `heating_bisimulation`, where `make T`, the same rule without its guard, has
one (`make_has_heating_bisimulation`). -/
theorem absence_has_no_heating_bisimulation :
    ¬ ∃ react : Reaction Expr, IsBisimulation (modelledStep ground (Prod.fst : Occ → Expr) () spawnOnly)
      (Reduces react) (Encodes (label := (Prod.fst : Occ → Expr))) := by
  rintro ⟨react, forward, backward⟩
  have valid : NullsOnTheStep.Separations.spawnAt.1.selection.Valid ground Prod.fst
      NullsOnTheStep.Separations.spawn NullsOnTheStep.Separations.emptyS.1 :=
    (PredicateQueryAdmission.valid_empty_iff ground Prod.fst NullsOnTheStep.Separations.spawn
      NullsOnTheStep.Separations.emptyS.1 _).mp NullsOnTheStep.Separations.spawn_admitted.1
  have after : ground.Models ()
      (NullsOnTheStep.Separations.spawnAt.1.selection.result Prod.fst
        NullsOnTheStep.Separations.spawn NullsOnTheStep.Separations.emptyS.1).equations := by
    obtain ⟨u, solved⟩ := valid.consistent
    exact solved
  have fires : modelledStep ground (Prod.fst : Occ → Expr) () spawnOnly
      ⟨NullsOnTheStep.Separations.emptyS.1, fun _ member => absurd member List.not_mem_nil⟩
      ⟨NullsOnTheStep.Separations.spawnAt.1.selection.result Prod.fst
        NullsOnTheStep.Separations.spawn NullsOnTheStep.Separations.emptyS.1, after⟩ :=
    ⟨NullsOnTheStep.Separations.spawn, rfl, ⟨_, valid, rfl⟩, after⟩
  have encodesEmpty : Encodes (label := (Prod.fst : Occ → Expr))
      (⟨NullsOnTheStep.Separations.emptyS.1, fun _ member => absurd member List.not_mem_nil⟩ :
        Modelled ground () (O := Occ)) Term.unit := by
    show labels Prod.fst NullsOnTheStep.Separations.emptyS.1.present = Term.heat Term.unit
    simp [labels, NullsOnTheStep.Separations.emptyS]
  obtain ⟨t', reduces, _⟩ := forward encodesEmpty fires
  have beside : Reduces react (Term.join Term.unit (Term.atom factU)) (Term.join t' (Term.atom factU)) :=
    NullsOnTheStep.Composition.reduces_parClosed react _ _ _ reduces
  have encodesU : Encodes (label := (Prod.fst : Occ → Expr))
      (⟨NullsOnTheStep.Separations.onlyU.1, fun _ member => absurd member List.not_mem_nil⟩ :
        Modelled ground () (O := Occ)) (Term.join Term.unit (Term.atom factU)) := by
    show labels Prod.fst NullsOnTheStep.Separations.onlyU.1.present =
      Term.heat (Term.join Term.unit (Term.atom factU))
    simp [labels, NullsOnTheStep.Separations.onlyU]
  obtain ⟨C', ⟨_, rfl, ⟨selection, refused, _⟩, _⟩, _⟩ := backward encodesU beside
  exact absent_refuted refused (p := factU) (List.mem_singleton.mpr rfl)
    (o := (factU, 0)) (Finset.mem_singleton_self _) rfl

/-- The step of a rule over ground terms, on every configuration. -/
def groundStep (r : RuleInstance Expr) (C C' : Conf) : Prop :=
  ConstraintMultisetRewriting.Step ground Prod.fst r C C'

/-- A configuration encodes a term when its labels are the term's heating; its knowledge is not
read. -/
def encodes (C : Conf) (t : Term Expr) : Prop := labels Prod.fst C.present = Term.heat t

/-- A configuration whose knowledge has no solution, `T = U`, with nothing present. -/
def clashing : Conf := ⟨[(factT, factU)], ∅⟩

/-- **Control: over all configurations the negation does not isolate absence.** With the knowledge
ignored, even `make T`, inside the fragment, has no reaction bisimilar to its step through heating:
`clashing` encodes the empty term and never fires, while `make T` fires at the empty store. -/
theorem make_has_none_over_all_configurations :
    ¬ ∃ react : Reaction Expr, IsBisimulation (groundStep makeT) (Reduces react) encodes := by
  rintro ⟨react, forward, backward⟩
  have valid : (⟨[], [], [(factT, 0)]⟩ : Selection Occ).Valid ground Prod.fst makeT ⟨[], ∅⟩ :=
    ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, by decide,
      ⟨(), fun e member => by simp [Selection.problem, Selection.equations, makeT, rule] at member⟩,
      fun c member => absurd member List.not_mem_nil⟩
  have fires : groundStep makeT ⟨[], ∅⟩
      ((⟨[], [], [(factT, 0)]⟩ : Selection Occ).result Prod.fst makeT ⟨[], ∅⟩) := ⟨_, valid, rfl⟩
  obtain ⟨t', reduces, _⟩ := forward (y := Term.unit) (by simp [encodes, labels]) fires
  obtain ⟨_, ⟨selection, refused, _⟩, _⟩ :=
    backward (x := clashing) (y' := t') (by simp [encodes, labels, clashing]) reduces
  obtain ⟨u, solved⟩ := refused.consistent
  have same : factT = factU := solved (factT, factU) (by simp [Selection.problem, clashing])
  simp [factT, factU] at same

end HeatingBisimulation.Controls

open HeatingBisimulation in
#print axioms view_functionalBisimulation
open HeatingBisimulation in
#print axioms heating_bisimulation
open HeatingBisimulation in
#print axioms encodes_iff_congruent
#print axioms HeatingBisimulation.Controls.spawn_outside
#print axioms HeatingBisimulation.Controls.make_inside
#print axioms HeatingBisimulation.Controls.make_has_heating_bisimulation
#print axioms HeatingBisimulation.Controls.absence_has_no_heating_bisimulation
#print axioms HeatingBisimulation.Controls.make_has_none_over_all_configurations

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep
