import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CandidateReindexing

/-!
# Finite programs with typed publication

Rule indices, occurrence choices and certified answers remain in the execution
word. Source transitions use the independently quantified schema judgment;
target transitions use the concrete publication step's local checks. The
correspondence retains complete intermediate states and endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head : Type} {rules : Rules Head}
variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L) (O : Type)

abbrev Program := (Γ : Context rules) → List (Schema levels O Γ)

variable {levels O}

structure Candidate (program : Program levels O) (state : State rules O) where
  ruleIndex : Fin (program state.frame).length
  pick : Pick ((program state.frame).get ruleIndex)
  target : Context rules
  answer : target ⟶ ((program state.frame).get ruleIndex).helpers.frame
  basis : Basis levels O ((program state.frame).get ruleIndex) pick answer

namespace Candidate

variable {program : Program levels O} {state : State rules O}

abbrev schema (candidate : Candidate program state) : Schema levels O state.frame :=
  (program state.frame).get candidate.ruleIndex

abbrev application (candidate : Candidate program state) : Application levels O state :=
  ⟨candidate.schema, candidate.pick, candidate.target, candidate.answer, candidate.basis⟩

end Candidate

namespace Program

variable [DecidableEq O] (program : Program levels O)
  (permission : {state : State rules O} → Candidate program state → Prop)

def toStep : Interface.Step (frames levels) O (State rules O) (Candidate program) :=
  (realizationStep levels O).reindexCandidates Candidate.application permission

theorem admits_iff {state : State rules O} (candidate : Candidate program state) :
    (program.toStep permission).Admits candidate ↔
      candidate.schema.Admits candidate.pick ∧ permission candidate :=
  and_congr (realization_admits_iff candidate.application) Iff.rfl

theorem result_eq {state : State rules O} (candidate : Candidate program state)
    (admitted : candidate.schema.Admits candidate.pick) (allowed : permission candidate) :
    (program.toStep permission).result candidate
        ((program.admits_iff permission candidate).mpr ⟨admitted, allowed⟩) =
      candidate.application.sourceResult admitted :=
  realization_result candidate.application admitted

inductive Transition : State rules O → State rules O → Prop where
  | fire {state : State rules O} (candidate : Candidate program state)
      (admitted : candidate.schema.Admits candidate.pick) (allowed : permission candidate) :
      Transition state (candidate.application.sourceResult admitted)

theorem transition_iff_event {source target : State rules O} :
    program.Transition permission source target ↔
      Nonempty ((program.toStep permission).effectCore.Event
        (program.toStep permission).eventAdmission source target) := by
  constructor
  · intro transition
    cases transition with
    | fire candidate admitted allowed =>
        let valid := (program.admits_iff permission candidate).mpr ⟨admitted, allowed⟩
        have event := (program.toStep permission).event candidate valid
        rw [program.result_eq permission candidate admitted allowed] at event
        exact ⟨event⟩
  · rintro ⟨event⟩
    have admitted : (program.toStep permission).Admits event.firing := event.permitted
    obtain ⟨sourceAdmitted, allowed⟩ := (program.admits_iff permission event.firing).mp admitted
    have endpoint : event.firing.application.sourceResult sourceAdmitted = target := by
      rw [← program.result_eq permission event.firing sourceAdmitted allowed]
      exact event.target_eq
    rw [← endpoint]
    exact .fire event.firing sourceAdmitted allowed

inductive Execution : State rules O → Type where
  | nil (state : State rules O) : Execution state
  | cons {state : State rules O} (candidate : Candidate program state)
      (admitted : candidate.schema.Admits candidate.pick) (allowed : permission candidate)
      (rest : Execution (candidate.application.sourceResult admitted)) : Execution state

namespace Execution

variable {program permission}

def last : {state : State rules O} → program.Execution permission state → State rules O
  | _, .nil state => state
  | _, .cons _ _ _ rest => rest.last

def word : {state : State rules O} → program.Execution permission state →
    List (Σ next : State rules O, Candidate program next)
  | _, .nil _ => []
  | state, .cons candidate _ _ rest => ⟨state, candidate⟩ :: rest.word

theorem last_cast {source target : State rules O} (same : source = target)
    (execution : program.Execution permission source) : (same ▸ execution).last = execution.last := by
  cases same
  rfl

theorem word_cast {source target : State rules O} (same : source = target)
    (execution : program.Execution permission source) : (same ▸ execution).word = execution.word := by
  cases same
  rfl

def toRun : {state : State rules O} → program.Execution permission state →
    (program.toStep permission).Run state
  | _, .nil state => .nil state
  | _, .cons candidate admitted allowed rest =>
      .cons candidate ((program.admits_iff permission candidate).mpr ⟨admitted, allowed⟩)
        ((program.result_eq permission candidate admitted allowed).symm ▸ toRun rest)

def ofRun : {state : State rules O} → (program.toStep permission).Run state →
    program.Execution permission state
  | _, .nil state => .nil state
  | _, .cons candidate admitted rest =>
      let sourceAdmitted := ((program.admits_iff permission candidate).mp admitted).1
      let allowed := ((program.admits_iff permission candidate).mp admitted).2
      .cons candidate sourceAdmitted allowed
        (program.result_eq permission candidate sourceAdmitted allowed ▸ ofRun rest)

theorem toRun_last : {state : State rules O} →
    (execution : program.Execution permission state) → execution.toRun.last = execution.last
  | _, .nil _ => rfl
  | _, .cons candidate admitted allowed rest => by
      simp only [toRun, Step.Run.last, Step.Run.last_cast, last]
      exact toRun_last rest

theorem toRun_word : {state : State rules O} →
    (execution : program.Execution permission state) → execution.toRun.word = execution.word
  | _, .nil _ => rfl
  | _, .cons candidate admitted allowed rest => by
      simp only [toRun, Step.Run.word, Step.Run.word_cast, word]
      exact congrArg (List.cons _) (toRun_word rest)

theorem ofRun_last : {state : State rules O} →
    (run : (program.toStep permission).Run state) → (ofRun run).last = run.last
  | _, .nil _ => rfl
  | _, .cons candidate admitted rest => by
      simp only [ofRun, last, last_cast, Step.Run.last]
      exact ofRun_last rest

theorem ofRun_word : {state : State rules O} →
    (run : (program.toStep permission).Run state) → (ofRun run).word = run.word
  | _, .nil _ => rfl
  | _, .cons candidate admitted rest => by
      simp only [ofRun, word, word_cast, Step.Run.word]
      exact congrArg (List.cons _) (ofRun_word rest)

theorem eq_of_word_eq {state : State rules O} (first : program.Execution permission state) :
    ∀ second : program.Execution permission state, first.word = second.word → first = second := by
  induction first with
  | nil state =>
      intro second same
      cases second with
      | nil => rfl
      | cons candidate admitted allowed rest => cases same
  | @cons state candidate admitted allowed rest ih =>
      intro second same
      cases second with
      | nil => cases same
      | cons other accepted permitted tail =>
          have words := List.cons.inj same
          have candidates : candidate = other := eq_of_heq (Sigma.mk.inj words.1).2
          subst other
          have tails := ih tail words.2
          subst tail
          rfl

theorem toRun_ofRun {state : State rules O} (run : (program.toStep permission).Run state) :
    (ofRun run).toRun = run := by
  apply Step.Run.eq_of_word_eq
  rw [toRun_word, ofRun_word]

theorem ofRun_toRun {state : State rules O} (execution : program.Execution permission state) :
    ofRun execution.toRun = execution := by
  apply eq_of_word_eq
  rw [ofRun_word, toRun_word]

/-- Both translations retain the entire candidate word and every state,
including each chosen answer and resulting dependent frame. -/
def runEquiv (state : State rules O) :
    program.Execution permission state ≃ (program.toStep permission).Run state where
  toFun := toRun
  invFun := ofRun
  left_inv := ofRun_toRun
  right_inv := toRun_ofRun

end Execution
end Program

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Program.transition_iff_event
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Program.Execution.runEquiv
