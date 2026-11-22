import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Classes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicity

/-!
# Source choices and classes of named hosted histories

The compilation supplies an indexed rule family (`ruleNamed`), retaining
the equation ordinal. A target state is a word of these names with actual
hosted histories; its choices are the names extending that word. Thus fresh
openings and occurrence allocation do not create extra alternatives, while
distinct source equation ordinals remain distinct.

The equivalence of enabled names follows from the existing named simulation
and reflection. This constructs an event-multiplicity bisimulation between
source alternatives and these named history classes. It is not a bijection
between source choices and all raw firings, and does not recover ordinals
from a program that has already forgotten them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedEvents

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
  {κ : Keys S} {D : Discipline S Γ star} (P : SourceLanguage.Program κ Γ star D.Ty)
  (q : Comp κ Γ star D.Ty)

abbrev SourceState := World κ Γ star × Branch κ Γ star D.Ty

def sourceEnabled (current : SourceState (κ := κ) (D := D)) (name : RuleName) : Prop :=
  ∃ next : SourceState (κ := κ) (D := D),
    NamedMove P current.1 current.2 name next.1 next.2 ∧ Solvable next.2.store

/-- The selected successor is computed from the name and source syntax.
Solvability determines eligibility, not the construction of this datum. -/
def sourceNext? (current : SourceState (κ := κ) (D := D)) (name : RuleName) :
    Option (SourceState (κ := κ) (D := D)) :=
  match name, current.2.focus with
  | .ret, .eval (.ret term) => some (current.1, {current.2 with focus := .value term})
  | .unmatched, .eval (.apply term) => some (current.1, {current.2 with focus := .value term})
  | .left, .eval (.choice left _) => some (current.1, {current.2 with focus := .eval left})
  | .right, .eval (.choice _ right) => some (current.1, {current.2 with focus := .eval right})
  | .eqn index, .eval (.apply term) => (P.equations[index]?).map fun equation =>
      (current.1.fresh, callBranch D current.1.scope current.2.store term
        current.2.frames current.2.pending equation)
  | _, _ => none

theorem sourceNext_of_move {current next : SourceState (κ := κ) (D := D)} {name : RuleName}
    (move : NamedMove P current.1 current.2 name next.1 next.2) :
    sourceNext? P current name = some next := by
  rcases current with ⟨world, branch⟩
  rcases next with ⟨nextWorld, nextBranch⟩
  cases move <;> simp_all [sourceNext?, World.fresh, callBranch]

def sourceSystem : EventMultiplicity.System (SourceState (κ := κ) (D := D)) RuleName where
  Choice current := {name : RuleName // sourceEnabled P current name}
  next current choice := (sourceNext? P current choice.1).get (by
    obtain ⟨next, move, _⟩ := choice.2
    rw [sourceNext_of_move P move]
    rfl)
  action _ choice := choice.1

theorem source_next_spec (current : SourceState (κ := κ) (D := D))
    (choice : (sourceSystem P).Choice current) :
    NamedMove P current.1 current.2 choice.1 ((sourceSystem P).next current choice).1
      ((sourceSystem P).next current choice).2 ∧ Solvable ((sourceSystem P).next current choice).2.store := by
  obtain ⟨next, move, live⟩ := choice.2
  have same : (sourceSystem P).next current choice = next := by
    simp [sourceSystem, sourceNext_of_move P move]
  rw [same]
  exact ⟨move, live⟩

def targetEnabled (word : List RuleName) (name : RuleName) : Prop :=
  ∃ state active, NamedFrom N P q (word ++ [name]) state active

def targetSystem : EventMultiplicity.System (List RuleName) RuleName where
  Choice word := {name : RuleName // targetEnabled N P q word name}
  next word choice := word ++ [choice.1]
  action _ choice := choice.1

structure Related (current : SourceState (D := D)) (word : List RuleName) : Prop where
  plain : PlainBranch current.2
  live : Solvable current.2.store
  reached : ∃ state active, NamedFrom N P q word state active
  uniform : ∀ state active, NamedFrom N P q word state active →
    Hosting.Represents N P current.1.scope current.2 state active

variable {N P q}

theorem enabled_iff (plainP : PlainProgram P) {current : SourceState (D := D)} {word : List RuleName}
    (related : Related N P q current word) (name : RuleName) :
    sourceEnabled P current name ↔ targetEnabled N P q word name := by
  constructor
  · rintro ⟨next, moved, live⟩
    obtain ⟨state, active, history⟩ := related.reached
    let fresh := state.present.sup id + 1
    have absent : fresh ∉ state.present := by
      intro member
      have bound : fresh ≤ state.present.sup id := Finset.le_sup (f := id) member
      dsimp [fresh] at bound
      omega
    obtain ⟨after, fired, _, _⟩ := simulation_named N plainP moved
      (related.uniform state active history) related.plain live absent
    exact ⟨after, fresh, .snoc history fired⟩
  · rintro ⟨state, active, history⟩
    obtain ⟨before, prior, historyBefore, fired⟩ := history.snoc_inv
    obtain ⟨world, branch, moved, represented, _⟩ := reflection_named N plainP
      (related.uniform before prior historyBefore) related.plain fired
    exact ⟨⟨world, branch⟩, moved, live_of_named N fired represented⟩

/-- An enabled name is realizable from every representative history, at
every fresh occurrence identity. Enabledness is not a lucky choice of lift. -/
theorem enabled_from_every_representative (plainP : PlainProgram P)
    {current : SourceState (D := D)} {word : List RuleName} {name : RuleName}
    (related : Related N P q current word) (enabled : targetEnabled N P q word name)
    {state : HostState S} {active fresh : Nat} (history : NamedFrom N P q word state active)
    (absent : fresh ∉ state.present) :
    ∃ next, FiresNamed N P name state active next fresh := by
  obtain ⟨after, move, live⟩ := (enabled_iff plainP related name).mpr enabled
  obtain ⟨next, fired, _, _⟩ := simulation_named N plainP move
    (related.uniform state active history) related.plain live absent
  exact ⟨next, fired⟩

/-- Each source ordinal is exactly one enabled name on the history-class
side. All representative hosted histories satisfy the same successor relation. -/
def bisimulation (plainP : PlainProgram P) :
    EventMultiplicity.Bisimulation (sourceSystem P) (targetSystem N P q) (Related N P q) where
  choices related := Equiv.subtypeEquivRight (enabled_iff plainP related)
  actions _ _ := rfl
  successors := by
    intro current word related choice
    change Related N P q ((sourceSystem P).next current choice) (word ++ [choice.1])
    let next := (sourceSystem P).next current choice
    have moved : NamedMove P current.1 current.2 choice.1 next.1 next.2 ∧ Solvable next.2.store :=
      source_next_spec P current choice
    have reached := (enabled_iff plainP related choice.1).mp choice.2
    have uniform : ∀ state active, NamedFrom N P q (word ++ [choice.1]) state active →
        Hosting.Represents N P next.1.scope next.2 state active ∧ PlainBranch next.2 := by
      intro state active history
      obtain ⟨before, prior, historyBefore, fired⟩ := history.snoc_inv
      obtain ⟨world, branch, move, represented, plain⟩ := reflection_named N plainP
        (related.uniform before prior historyBefore) related.plain fired
      obtain ⟨worldEq, branchEq⟩ := NamedMove.unique moved.1 move
      rw [← worldEq, ← branchEq] at represented
      rw [← branchEq] at plain
      exact ⟨represented, plain⟩
    obtain ⟨state, active, history⟩ := reached
    exact ⟨(uniform state active history).2, moved.2,
      ⟨state, active, history⟩, fun state active history => (uniform state active history).1⟩

theorem finished_iff {current : SourceState (D := D)} {word : List RuleName}
    (related : Related N P q current word) :
    current.2.Finished (D := D) ↔ FinishedClass N P q word := by
  constructor
  · intro finished
    obtain ⟨state, active, history⟩ := related.reached
    exact ⟨state, active, history,
      (Hosting.finished_iff N (related.uniform state active history)).mp ⟨finished, related.live⟩⟩
  · rintro ⟨state, active, history, finished⟩
    exact ((Hosting.finished_iff N (related.uniform state active history)).mpr finished).1

theorem answer_eq {current : SourceState (D := D)} {word : List RuleName}
    (related : Related N P q current word) (finished : current.2.Finished (D := D)) :
    classAnswer N P q word = current.2.answer (D := D) := by
  ext value
  constructor
  · rintro ⟨state, active, history, answered⟩
    rw [Hosting.answer_eq N (related.uniform state active history) finished] at answered
    exact answered
  · intro answered
    obtain ⟨state, active, history⟩ := related.reached
    refine ⟨state, active, history, ?_⟩
    rw [Hosting.answer_eq N (related.uniform state active history) finished]
    exact answered

theorem initial (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    Related N P q ((Config.initial spaces q).world, initialBranch q) [] where
  plain := ⟨rfl, .inl ⟨q, rfl, plainQ⟩⟩
  live := initial_live
  reached := ⟨start N P q, P.equations.length, .nil _ _⟩
  uniform := by
    intro state active history
    obtain ⟨rfl, rfl⟩ := history.nil_inv
    exact start_represents N P q unopened

/-- The equivalence counts executions by their compiled origin names,
with no enumeration of fresh target identities or solutions. -/
def executions (plainP : PlainProgram P) (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) (count : Nat) :
    (sourceSystem P).Execution count ((Config.initial spaces q).world, initialBranch q) ≃
      (targetSystem N P q).Execution count [] :=
  (bisimulation plainP).executions count (initial spaces plainQ unopened)

theorem execution_words (plainP : PlainProgram P) (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {count : Nat}
    (run : (sourceSystem P).Execution count ((Config.initial spaces q).world, initialBranch q)) :
    (targetSystem N P q).word (executions plainP spaces plainQ unopened count run) =
      (sourceSystem P).word run :=
  (bisimulation plainP).execution_word (initial spaces plainQ unopened) run

theorem execution_answers (plainP : PlainProgram P) (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {count : Nat}
    (run : (sourceSystem P).Execution count ((Config.initial spaces q).world, initialBranch q))
    (finished : ((sourceSystem P).last run).2.Finished (D := D)) :
    classAnswer N P q ((targetSystem N P q).last (executions plainP spaces plainQ unopened count run)) =
      ((sourceSystem P).last run).2.answer (D := D) :=
  answer_eq ((bisimulation plainP).execution_last (initial spaces plainQ unopened) run) finished

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedEvents

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedEvents.enabled_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedEvents.bisimulation
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedEvents.answer_eq
