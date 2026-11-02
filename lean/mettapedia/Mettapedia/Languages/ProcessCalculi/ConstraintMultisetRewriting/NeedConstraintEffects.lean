import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationStore
import Mettapedia.Machines.BranchLocalNeed.EffectPrefixes
import Mettapedia.Machines.OccurrenceMachineRestriction

/-!
# Persistent equation effects on actual Need execution

This profile interprets every effect occurrence as a logical tell. The store
is the initial equations followed by the actual chronological effect history.
The checked machine filters the existing local-step successor list using a
sound and complete consistency test. It changes no application, capture,
allocation, force, cache or return instruction.

Consistency is backwards closed along actual executions because equation
effects only accumulate. Therefore early rejection gives exactly the original
ordered completed-state occurrences filtered by final consistency. There are
no asks or irreversible external effects in this profile: moving such an
observation to the end would require an additional theorem and can be false.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedConstraintEffects

open Mettapedia.Machines
open Mettapedia.Machines.BranchLocalNeed
open NeedReference

variable {T S Origin Local Resume Rule Value StableFault RetryableFault : Type}

abbrev State (Origin Local Resume Rule Value StableFault RetryableFault T : Type) :=
  Machine Origin Local Resume Rule Value StableFault RetryableFault (Equation T)

def equations (initial : EquationStore T)
    (state : State Origin Local Resume Rule Value StableFault RetryableFault T) : EquationStore T :=
  initial ++ state.world.receipts.effects

theorem step_refines (action : SubstitutionAction T S) (initial : EquationStore T)
    (extension : NeedLocalSteps.Extension Origin Local Resume Rule Value StableFault RetryableFault (Equation T))
    {before after : State Origin Local Resume Rule Value StableFault RetryableFault T}
    (selected : after ∈ NeedLocalSteps.step extension before) :
    action.Refines (equations initial after) (equations initial before) := by
  obtain ⟨later, grows⟩ := EffectPrefixes.local_step extension selected
  intro assignment models
  unfold equations at models ⊢
  rw [← grows, ← List.append_assoc] at models
  exact ((action.models_append assignment _ _).mp models).1

theorem step_consistent_back (action : SubstitutionAction T S) (initial : EquationStore T)
    (extension : NeedLocalSteps.Extension Origin Local Resume Rule Value StableFault RetryableFault (Equation T))
    {before after : State Origin Local Resume Rule Value StableFault RetryableFault T}
    (selected : after ∈ NeedLocalSteps.step extension before)
    (consistent : action.Consistent (equations initial after)) :
    action.Consistent (equations initial before) := by
  obtain ⟨assignment, models⟩ := consistent
  exact ⟨assignment, step_refines action initial extension selected assignment models⟩

/-- Original execution with a complete terminal-state observation. No store
predicate is built into this independent machine. -/
def rawCore
    (extension : NeedLocalSteps.Extension Origin Local Resume Rule Value StableFault RetryableFault (Equation T)) :
    OccurrenceMachineCore
      (State Origin Local Resume Rule Value StableFault RetryableFault T)
      (State Origin Local Resume Rule Value StableFault RetryableFault T)
      (State Origin Local Resume Rule Value StableFault RetryableFault T) where
  load := id
  next := NeedLocalSteps.step extension
  answer state := if isHalted state then some state else none
  answer_final state answer returned := by
    cases control : state.control <;>
      simp [isHalted, control, NeedLocalSteps.step, NeedReference.step] at returned ⊢

theorem raw_answer_iff
    (extension : NeedLocalSteps.Extension Origin Local Resume Rule Value StableFault RetryableFault (Equation T))
    (state answer : State Origin Local Resume Rule Value StableFault RetryableFault T) :
    (rawCore extension).answer state = some answer ↔ state = answer ∧ isHalted state = true := by
  cases halted : isHalted state <;> simp [rawCore, halted]

/-- The actual successor computation is retained; inconsistent descendants
are removed as refuted logical branches, preserving every admitted duplicate. -/
def checkedCore
    (extension : NeedLocalSteps.Extension Origin Local Resume Rule Value StableFault RetryableFault (Equation T))
    (initial : EquationStore T) (check : EquationStore T → Bool) :=
  (rawCore extension).restrict (fun state => check (equations initial state))
    (fun state => check (equations initial state))

/-- Admission tests the actual next store before the successor is scheduled. -/
theorem checked_successor_iff (action : SubstitutionAction T S)
    (extension : NeedLocalSteps.Extension Origin Local Resume Rule Value StableFault RetryableFault (Equation T))
    (initial : EquationStore T) (check : EquationStore T → Bool)
    (checkLaw : ∀ store, check store = true ↔ action.Consistent store)
    (before after : State Origin Local Resume Rule Value StableFault RetryableFault T) :
    after ∈ (checkedCore extension initial check).next before ↔
      after ∈ NeedLocalSteps.step extension before ∧ action.Consistent (equations initial after) := by
  change after ∈ (NeedLocalSteps.step extension before).filter
    (fun state => check (equations initial state)) ↔ _
  rw [List.mem_filter, checkLaw]

theorem checked_occurrences_exact (action : SubstitutionAction T S)
    (extension : NeedLocalSteps.Extension Origin Local Resume Rule Value StableFault RetryableFault (Equation T))
    (initial : EquationStore T) (check : EquationStore T → Bool)
    (checkLaw : ∀ store, check store = true ↔ action.Consistent store)
    (fuel : Nat) (state : State Origin Local Resume Rule Value StableFault RetryableFault T) :
    (checkedCore extension initial check).answerOccurrences fuel state =
      ((rawCore extension).answerOccurrences fuel state).filter
        (fun final => check (equations initial final)) := by
  apply OccurrenceMachineCore.restrict_answerOccurrences
  · intro before after selected accepted
    exact (checkLaw _).mpr (step_consistent_back action initial extension selected
      ((checkLaw _).mp accepted))
  · intro before answer returned
    have same := ((raw_answer_iff extension before answer).mp returned).1
    subst answer
    rfl

theorem path_has_trace
    (extension : NeedLocalSteps.Extension Origin Local Resume Rule Value StableFault RetryableFault (Equation T))
    {count : Nat} {before after : State Origin Local Resume Rule Value StableFault RetryableFault T}
    (path : NeedLocalSteps.Steps extension count before after) :
    ∃ trace, trace.length = count ∧ (rawCore extension).follow before trace = some after := by
  induction path with
  | refl => exact ⟨[], rfl, rfl⟩
  | cons selected rest ih =>
    obtain ⟨trace, length, follows⟩ := ih
    refine ⟨selected.index :: trace, by simp [length], ?_⟩
    simpa [OccurrenceMachineCore.follow, rawCore, selected.successorAt] using follows

theorem trace_has_path
    (extension : NeedLocalSteps.Extension Origin Local Resume Rule Value StableFault RetryableFault (Equation T))
    {trace : List Nat} {before after : State Origin Local Resume Rule Value StableFault RetryableFault T}
    (follows : (rawCore extension).follow before trace = some after) :
    NeedLocalSteps.Steps extension trace.length before after := by
  induction trace generalizing before with
  | nil =>
    simp only [OccurrenceMachineCore.follow, Option.some.injEq] at follows
    subst after
    exact .refl _
  | cons index trace ih =>
    change ((NeedLocalSteps.step extension before)[index]? >>= fun next =>
      (rawCore extension).follow next trace) = some after at follows
    cases selected : (NeedLocalSteps.step extension before)[index]? with
    | none => simp [selected] at follows
    | some next =>
      simp only [selected] at follows
      exact .cons ⟨index, selected⟩ (ih follows)

theorem raw_occurrence_iff
    (extension : NeedLocalSteps.Extension Origin Local Resume Rule Value StableFault RetryableFault (Equation T))
    (fuel : Nat) (before after : State Origin Local Resume Rule Value StableFault RetryableFault T) :
    after ∈ (rawCore extension).answerOccurrences fuel before ↔
      ∃ count ≤ fuel, NeedLocalSteps.Steps extension count before after ∧ isHalted after = true := by
  constructor
  · intro member
    rw [← OccurrenceMachineCore.answerTraces_map_fst] at member
    obtain ⟨⟨answer, trace⟩, member, same⟩ := List.mem_map.mp member
    dsimp only at same
    subst answer
    obtain ⟨final, followed, observed, bounded⟩ :=
      (OccurrenceMachineCore.mem_answerTraces_iff (rawCore extension)).mp member
    obtain ⟨rfl, halted⟩ := (raw_answer_iff extension final after).mp observed
    exact ⟨trace.length, bounded, trace_has_path extension followed, halted⟩
  · rintro ⟨count, bounded, path, halted⟩
    obtain ⟨trace, length, followed⟩ := path_has_trace extension path
    have traced := OccurrenceMachineCore.answerTraces_complete (rawCore extension) followed
      ((raw_answer_iff extension after after).mpr ⟨rfl, halted⟩) (length ▸ bounded)
    rw [← OccurrenceMachineCore.answerTraces_map_fst]
    exact List.mem_map.mpr ⟨(after, trace), traced, rfl⟩

/-- Finite checked executions coincide with actual source-machine paths whose
joint final equation store is consistent. Earlier checks are derived from
persistent refinement, not assumed for the whole path. -/
theorem checked_occurrence_iff (action : SubstitutionAction T S)
    (extension : NeedLocalSteps.Extension Origin Local Resume Rule Value StableFault RetryableFault (Equation T))
    (initial : EquationStore T) (check : EquationStore T → Bool)
    (checkLaw : ∀ store, check store = true ↔ action.Consistent store)
    (fuel : Nat) (before after : State Origin Local Resume Rule Value StableFault RetryableFault T) :
    after ∈ (checkedCore extension initial check).answerOccurrences fuel before ↔
      (∃ count ≤ fuel, NeedLocalSteps.Steps extension count before after ∧ isHalted after = true) ∧
        action.Consistent (equations initial after) := by
  rw [checked_occurrences_exact action extension initial check checkLaw,
    List.mem_filter, raw_occurrence_iff, checkLaw]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedConstraintEffects
