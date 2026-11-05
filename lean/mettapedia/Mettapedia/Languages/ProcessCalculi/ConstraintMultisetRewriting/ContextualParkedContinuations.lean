import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingScheduler

/-!
# Linear parked continuations shared by competing source arms

A pending continuation is an ordinary occurrence. Each arm adds a take of
that same occurrence to its source body. The existing clause compiler
executes the whole body atomically, retaining its code installation. One
arm consumes the pending continuation; competing arms then cannot run.

The branch code is reusable program data, distinct from the linear pending
continuation. No fairness premise is needed for the at-most-once law.
Logical occurrence identities are not reused, as required by the existing
born ledger. Fresh physical allocations may implement fresh logical names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualParkedContinuations

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
open ContextualRuleCode ContextualStandingEvents ContextualStandingScheduler

variable {S : Signature} {atom : S.Srt} {O : Type} {Γ : Ctx S}
    [DecidableEq O] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]

def arm {T : Type} (held : T) (body : Declaration T) : Declaration T where
  mode := body.mode
  plan := ⟨{body.plan.rule with take := held :: body.plan.rule.take}, body.plan.reusable, body.plan.shape⟩

def selected (continuation : O) (picked : Selection O) : Selection O :=
  {picked with taken := continuation :: picked.taken}

def SourceReady (before : World S atom O Γ) (installation continuation : O)
    (held : Term (signature (codeSignature S atom)
      (ContextualSelectionViews.source before.locals before.current.declarations)) Γ atom)
    (body : Declaration (Term (signature (codeSignature S atom)
      (ContextualSelectionViews.source before.locals before.current.declarations)) Γ atom))
    (picked : Selection O) : Prop :=
  ContextualStandingEntry.Admitted before.locals before.current installation
    (arm held body) (selected continuation picked) ∧ Disjoint picked.made.toFinset before.born

omit [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] in
theorem source_needs_the_continuation {before : World S atom O Γ} {installation continuation : O}
    {held body picked} (source : SourceReady before installation continuation held body picked) :
    continuation ∈ before.current.present :=
  source.1.body.taken_present (by simp [ContextualStandingEntry.selected,
    StandingRuleRows.selection, selected])

theorem realize_source_arm {before : World S atom O Γ} {installation continuation : O}
    {held body picked} (source : SourceReady before installation continuation held body picked) (fuel : Nat) :
    ∃ invocation : Invocation before, invocation.installation = installation ∧
      invocation.declaration = arm held body ∧ invocation.picked = selected continuation picked ∧
      invocation.Admissible ∧ invocation.fuel = fuel := by
  let _ := before.equality
  obtain ⟨actual, budget⟩ := ContextualStandingEntry.realize before.locals before.current
    installation (arm held body) (selected continuation picked) source.1 fuel
  refine ⟨⟨installation, arm held body, selected continuation picked, actual⟩,
    rfl, rfl, rfl, ⟨source.2, ?_⟩, budget⟩
  exact StandingRuleRows.consuming_fresh installation (arm held body).mode
    (selected continuation picked) (by simp [selected]) before.history

theorem source_iff_compiled_arm {before : World S atom O Γ} {installation continuation : O}
    {held body picked} (fuel : Nat) :
    SourceReady before installation continuation held body picked ↔
      ∃ invocation : Invocation before, invocation.installation = installation ∧
        invocation.declaration = arm held body ∧ invocation.picked = selected continuation picked ∧
        invocation.Admissible ∧ invocation.fuel = fuel := by
  let _ := before.equality
  constructor
  · exact fun source => realize_source_arm source fuel
  · rintro ⟨⟨code, declaration, chosen, actual⟩, rfl, rfl, rfl, admissible, _⟩
    exact ⟨actual.source_admitted, admissible.1⟩

theorem an_executed_arm_consumes_the_continuation {before : World S atom O Γ}
    (invocation : Invocation before) (continuation : O) (picked : Selection O)
    (shape : invocation.picked = selected continuation picked) :
    continuation ∉ invocation.target.current.present :=
  (Action.invoke invocation).consumed_removed (by simp [Action.taken, shape, selected])

def Retired (world : World S atom O Γ) (continuation : O) : Prop :=
  continuation ∈ world.born ∧ continuation ∉ world.current.present

theorem retired_next {index : Index (S := S) (atom := atom) (O := O) (Γ := Γ)}
    {state : State S atom O Γ} {event : Label S atom O Γ} {continuation : O}
    (retired : Retired state.world continuation) (allowed : Allowed state event) :
    Retired (next index state event).world continuation := by
  cases event with
  | commit before action =>
      have old : Retired before continuation := allowed.1 ▸ retired
      exact ⟨action.born_mono old.1, action.absent_stays_absent allowed.2.1 old.1 old.2⟩
  | sleep installation => exact retired
  | idle => exact retired

theorem Run.retired_forever {index : Index (S := S) (atom := atom) (O := O) (Γ := Γ)}
    (run : Liveness.Run (system index)) {continuation : O} {start : Nat}
    (retired : Retired (run.state start).world continuation) :
    ∀ time ≥ start, Retired (run.state time).world continuation := by
  intro time later
  induction time, later using Nat.le_induction with
  | base => exact retired
  | succ time _ ih =>
      rw [run.step time]
      exact retired_next ih (run.allowed time)

def takesContinuation (continuation : O) : Label S atom O Γ → Prop
  | .commit _ action => continuation ∈ action.taken
  | _ => False

theorem allowed_take_is_present {state : State S atom O Γ} {event : Label S atom O Γ}
    {continuation : O} (allowed : Allowed state event) (takes : takesContinuation continuation event) :
    continuation ∈ state.world.current.present := by
  cases event with
  | commit before action =>
      rw [allowed.1]
      exact action.taken_present (List.mem_toFinset.mpr takes)
  | sleep installation => exact takes.elim
  | idle => exact takes.elim

theorem allowed_take_retires {index : Index (S := S) (atom := atom) (O := O) (Γ := Γ)}
    {state : State S atom O Γ} {event : Label S atom O Γ} {continuation : O}
    (born : state.world.current.present ⊆ state.world.born)
    (allowed : Allowed state event) (takes : takesContinuation continuation event) :
    Retired (next index state event).world continuation := by
  have wasBorn := born (allowed_take_is_present allowed takes)
  cases event with
  | commit before action =>
      have old : continuation ∈ before.born := allowed.1 ▸ wasBorn
      exact ⟨action.born_mono old, action.consumed_removed takes⟩
  | sleep installation => exact takes.elim
  | idle => exact takes.elim

/-- Competing arms share this physical take. The no-replay law holds for
every permitted run, independently of wake policy or scheduler fairness. -/
theorem at_most_one_arm {index : Index (S := S) (atom := atom) (O := O) (Γ := Γ)}
    (run : Liveness.Run (system index)) (continuation : O) (first later : Nat)
    (ordered : first < later)
    (born : (run.state first).world.current.present ⊆ (run.state first).world.born)
    (fired : takesContinuation continuation (run.label first)) :
    ¬ takesContinuation continuation (run.label later) := by
  have retired : Retired (run.state (first + 1)).world continuation := by
    rw [run.step first]
    exact allowed_take_retires born (run.allowed first) fired
  have still := Run.retired_forever run retired later (by omega)
  intro again
  exact still.2 (allowed_take_is_present (run.allowed later) again)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualParkedContinuations
