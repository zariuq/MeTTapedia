import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingEvents
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.FairRuns

/-!
# Scheduling actual contextual source invocations across declaration families

Readiness uses independent source admission. Executed events contain the
existing compiler's actual family-changing firing. Their source index is
checked by Allowed, while their target is that firing's computed world.
The wake invariant bridges source readiness to an awake scheduler task.
Queued tasks are installation names. A commit label carries its mathematical
input index and compiler witness; it does not require a runtime comparison
or a physical copy of whole worlds.

The reference index conservatively rechecks live installations after a
public firing, using the strictly increasing allocation ledger. It supplies
a correctness baseline, not a chosen native wait-index or cost claim. Other
indexes enter through their explicit no-lost-wakeup proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingScheduler

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
open ContextualRuleCode ContextualStandingEvents

variable {S : Signature} {atom : S.Srt} {O : Type} {Γ : Ctx S}
    [DecidableEq O] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]

structure State (S : Signature) (atom : S.Srt) (O : Type) (context : Ctx S) : Type 1 where
  world : World S atom O context
  awake : Set O

inductive Label (S : Signature) (atom : S.Srt) (O : Type) (context : Ctx S)
    [DecidableEq O] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] : Type 1 where
  | commit (before : World S atom O context) (action : ContextualStandingEvents.Action before)
  | sleep (installation : O)
  | idle

abbrev Index := (before : World S atom O Γ) → Action before → O → Prop

def Allowed (state : State S atom O Γ) : Label S atom O Γ → Prop
  | .commit before action => state.world = before ∧ action.Admissible ∧
      match action.installation with
      | none => True
      | some installation => installation ∈ state.awake
  | .sleep installation => installation ∈ state.awake ∧ ¬ Ready state.world installation
  | .idle => True

def next (index : Index (S := S) (atom := atom) (O := O) (Γ := Γ))
    (state : State S atom O Γ) : Label S atom O Γ → State S atom O Γ
  | .commit before action =>
      ⟨action.target, {installation | installation ∈ action.target.current.present ∧
        (installation ∈ state.awake ∨ index before action installation)}⟩
  | .sleep installation => {state with awake := state.awake \ {installation}}
  | .idle => state

def system (index : Index (S := S) (atom := atom) (O := O) (Γ := Γ)) :
    LTS (State S atom O Γ) (Label S atom O Γ) := ⟨Allowed, next index⟩

def NoLostWakeup (index : Index (S := S) (atom := atom) (O := O) (Γ := Γ)) : Prop :=
  ∀ (before : World S atom O Γ) (action : Action before), action.Admissible → ∀ installation,
    ¬ Ready before installation → Ready action.target installation → index before action installation

def referenceIndex : Index (S := S) (atom := atom) (O := O) (Γ := Γ) :=
  fun before action _ => epoch before ≠ epoch action.target

theorem reference_no_lost_wakeup : NoLostWakeup (referenceIndex (S := S) (atom := atom) (O := O) (Γ := Γ)) := by
  intro before action _ installation _ _
  exact Nat.ne_of_lt action.epoch_increases

structure WakeInv (state : State S atom O Γ) : Prop where
  present_born : state.world.current.present ⊆ state.world.born
  ready_awake : ∀ installation, Ready state.world installation → installation ∈ state.awake

theorem wakeInv_next {index : Index (S := S) (atom := atom) (O := O) (Γ := Γ)}
    (adequate : NoLostWakeup index) {state : State S atom O Γ} (inv : WakeInv state)
    {event : Label S atom O Γ} (allowed : Allowed state event) : WakeInv (next index state event) := by
  cases event with
  | commit before action =>
      have born : before.current.present ⊆ before.born := by rw [← allowed.1]; exact inv.present_born
      refine ⟨action.present_born born, ?_⟩
      intro installation ready
      refine ⟨ready_present ready, ?_⟩
      by_cases earlier : Ready before installation
      · left
        exact inv.ready_awake installation (allowed.1.symm ▸ earlier)
      · exact Or.inr (adequate before action allowed.2.1 installation earlier ready)
  | sleep installation =>
      refine ⟨inv.present_born, ?_⟩
      intro other ready
      refine ⟨inv.ready_awake other ready, ?_⟩
      intro same
      have only := Set.mem_singleton_iff.mp same
      subst other
      exact allowed.2 ready
  | idle => exact inv

theorem Run.wakeInv {index : Index (S := S) (atom := atom) (O := O) (Γ := Γ)}
    (adequate : NoLostWakeup index) (run : Liveness.Run (system index)) (initial : WakeInv (run.state 0)) :
    ∀ n, WakeInv (run.state n) := by
  intro n
  induction n with
  | zero => exact initial
  | succ n ih =>
      rw [run.step n]
      exact wakeInv_next adequate ih (run.allowed n)

def runTask (installation : O) : Label S atom O Γ → Prop
  | .commit _ action => action.installation = some installation
  | _ => False

/-- Source readiness constructs the compiler event; wake adequacy supplies
its queue availability. The task is an actual invocation commit. -/
theorem ready_task_enabled {index : Index (S := S) (atom := atom) (O := O) (Γ := Γ)}
    {state : State S atom O Γ} (inv : WakeInv state) {installation : O} (ready : Ready state.world installation) :
    (system index).TaskEnabled (runTask installation) state := by
  obtain ⟨invocation, selected, admissible, _⟩ := realize_ready ready 0
  refine ⟨.commit state.world (.invoke invocation), ?_, rfl, admissible, ?_⟩
  · exact congrArg some selected
  · exact inv.ready_awake invocation.installation (selected.symm ▸ ready)

theorem whenever_fires_often {index : Index (S := S) (atom := atom) (O := O) (Γ := Γ)}
    (adequate : NoLostWakeup index) (run : Liveness.Run (system index)) (initial : WakeInv (run.state 0))
    (installation : O) (often : InfinitelyOften fun n => Ready (run.state n).world installation)
    (fair : run.StronglyFair (runTask installation)) :
    InfinitelyOften fun n => runTask installation (run.label n) := by
  apply fair
  intro start
  obtain ⟨n, later, ready⟩ := often start
  exact ⟨n, later, ready_task_enabled (Run.wakeInv adequate run initial n) ready⟩

theorem weak_fair_fires_of_stable {index : Index (S := S) (atom := atom) (O := O) (Γ := Γ)}
    (adequate : NoLostWakeup index) (run : Liveness.Run (system index)) (initial : WakeInv (run.state 0))
    (installation : O) (start : Nat)
    (readyUntil : ∀ n ≥ start, (∀ m, start ≤ m → m < n → ¬ runTask installation (run.label m)) →
      Ready (run.state n).world installation)
    (fair : run.WeaklyFair (runTask installation)) :
    ∃ n ≥ start, runTask installation (run.label n) := by
  apply fair.fires start
  intro n later notYet
  exact ready_task_enabled (Run.wakeInv adequate run initial n) (readyUntil n later notYet)

theorem sleeping_preserves_world (index : Index (S := S) (atom := atom) (O := O) (Γ := Γ))
    (state : State S atom O Γ) (installation : O) :
    (next index state (.sleep installation)).world = state.world := rfl

theorem invocation_keeps_its_installation (index : Index (S := S) (atom := atom) (O := O) (Γ := Γ))
    (state : State S atom O Γ) {before : World S atom O Γ} (invocation : Invocation before) :
    invocation.installation ∈ (next index state (.commit before (.invoke invocation))).world.current.present :=
  invocation.installation_kept

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingScheduler
