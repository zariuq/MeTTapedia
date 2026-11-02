import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationWakeups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FairFiringRuns

/-!
# A proved coarse recheck trigger on the actual equation-appending step

This finite observation detects every false-to-true readiness transition on
an actual ordinary CMR step. It is not a new queue, a scheduler, an assumed
NoLostWakeup contract, or an identity for arbitrary equation-store branches.
Native registration/recheck and awake retention remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationRecheck

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

def changed (before after : Configuration T O) : Bool :=
  decide (before.present ≠ after.present) ||
    decide (before.equations.length ≠ after.equations.length)

theorem changed_iff (before after : Configuration T O) :
    changed before after = true ↔
      before.present ≠ after.present ∨ before.equations.length ≠ after.equations.length := by
  simp [changed]

theorem detects_selected_readiness (action : SubstitutionAction T S) (label : O → T)
    {event pending : RuleInstance T} {before after : Configuration T O}
    (step : Step action label event before after) (picked : Selection O)
    (asleep : ¬ picked.Valid action label pending before)
    (ready : picked.Valid action label pending after) : changed before after = true :=
  (changed_iff before after).mpr
    (EquationWakeups.readiness_flip_requires_world_or_equations action label step picked asleep ready)

/-- A fixed admitted row set may change selections without weakening the
event-detection theorem. This does not assert fixed-row fairness for it. -/
theorem detects_catalog_readiness (action : SubstitutionAction T S) (label : O → T)
    {event : RuleInstance T} {before after : Configuration T O}
    (step : Step action label event before after)
    (catalog : Set (ConditionalSchedule.Firing T O))
    (asleep : ¬ ∃ firing ∈ catalog, firing.2.Valid action label firing.1 before)
    (ready : ∃ firing ∈ catalog, firing.2.Valid action label firing.1 after) :
    changed before after = true := by
  obtain ⟨firing, member, valid⟩ := ready
  exact detects_selected_readiness action label step firing.2
    (fun beforeValid => asleep ⟨firing, member, beforeValid⟩) valid

/-- An unchanged trigger preserves readiness in both directions only along
the actual append-only step, not across arbitrary equal-length branches. -/
theorem unchanged_preserves_selected_readiness (action : SubstitutionAction T S)
    (label : O → T) {event pending : RuleInstance T} {before after : Configuration T O}
    (step : Step action label event before after) (picked : Selection O)
    (unchanged : changed before after = false) :
    picked.Valid action label pending before ↔ picked.Valid action label pending after := by
  have noChange : ¬ (before.present ≠ after.present ∨
      before.equations.length ≠ after.equations.length) := by
    intro change
    have yes := (changed_iff before after).mpr change
    rw [unchanged] at yes
    cases yes
  have sameWorld : before.present = after.present := by
    by_contra missing
    exact noChange (.inl missing)
  have sameLength : after.equations.length = before.equations.length := by
    by_contra missing
    exact noChange (.inr (Ne.symm missing))
  exact EquationWakeups.unchanged_step_preserves_readiness action label step sameWorld sameLength picked

/-- The trigger completeness also applies to runs in the existing selected
firing LTS. An idle label cannot create semantic readiness. -/
theorem detects_on_actual_run (action : SubstitutionAction T S) (label : O → T)
    (run : Run (FairFiringRuns.system action label).withIdle) (n : Nat)
    (pending : ConditionalSchedule.Firing T O)
    (asleep : ¬ pending.2.Valid action label pending.1 (run.state n))
    (ready : pending.2.Valid action label pending.1 (run.state (n + 1))) :
    changed (run.state n) (run.state (n + 1)) = true := by
  have result := run.step n
  have allowed := run.allowed n
  cases event : run.label n with
  | none =>
      rw [event] at result
      change run.state (n + 1) = run.state n at result
      rw [result] at ready
      exact False.elim (asleep ready)
  | some firing =>
      rw [event] at result allowed
      apply detects_selected_readiness action label (pending := pending.1)
        (event := firing.1) (picked := pending.2) _ asleep ready
      exact ⟨firing.2, allowed, result⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationRecheck
