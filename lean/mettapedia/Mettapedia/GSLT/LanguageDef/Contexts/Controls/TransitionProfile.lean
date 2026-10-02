import Mettapedia.GSLT.Contexts.TransitionProfile
import Mettapedia.Languages.TransitionSystem.Contexts

/-!
# Primitive and nonempty computation profiles differ

An authored three-state request protocol performs preparation and delivery
as two separate reductions. The nonempty computation profile can observe
the complete request as one transition. The underlying path still records
two reductions, and the terminal state cannot acquire an inaction step.

This control illustrates profile selection. It does not assert that changing
a profile preserves strong bisimilarity or the number of runtime steps.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Contexts.Controls.TransitionProfile

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.Languages.TransitionSystem

/-- A request first becomes ready, then receives its reply. -/
def protocol : Table where
  states := ["Request", "Ready", "Reply"]
  moves := [("prepare", "Request", "Ready"), ("deliver", "Ready", "Reply")]

theorem protocol_wellFormed : protocol.WellFormed := by decide

abbrev theory : ContextTheory.{0} := Table.theory protocol_wellFormed

def proc : Interface := ⟨.base "Proc", []⟩

def request : theory.Term proc := Table.stateTerm rfl (by decide : "Request" ∈ protocol.states)

def ready : theory.Term proc := Table.stateTerm rfl (by decide : "Ready" ∈ protocol.states)

def reply : theory.Term proc := Table.stateTerm rfl (by decide : "Reply" ∈ protocol.states)

theorem prepare_step : theory.rewrites request ready :=
  (Table.rewrites_iff protocol_wellFormed).mpr
    ⟨("prepare", "Request", "Ready"), by decide, rfl, rfl⟩

theorem deliver_step : theory.rewrites ready reply :=
  (Table.rewrites_iff protocol_wellFormed).mpr
    ⟨("deliver", "Ready", "Reply"), by decide, rfl, rfl⟩

/-- The retained primitive path records both administrative stages. -/
def requestPath : (theory.gslt proc).RewritePath request reply :=
  GSLT.RewritePath.cons (S := theory.gslt proc) prepare_step
    (GSLT.RewritePath.cons (S := theory.gslt proc) deliver_step
      (GSLT.RewritePath.nil (S := theory.gslt proc) reply))

theorem requestPath_length : requestPath.length = 2 := rfl

theorem request_macroStep : theory.nonemptyReduction.rewrites request reply :=
  theory.nonemptyReduction_trans (theory.nonemptyReduction_of_step prepare_step)
    (theory.nonemptyReduction_of_step deliver_step)

/-- The authored table has no direct request-to-reply reduction. -/
theorem request_no_directStep : ¬ theory.rewrites request reply := by
  intro step
  obtain ⟨move, membership, source, target⟩ := (Table.rewrites_iff protocol_wellFormed).mp step
  have listed : move ∈ [("prepare", "Request", "Ready"), ("deliver", "Ready", "Reply")] :=
    membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl
  · change state "Reply" = state "Ready" at target
    exact (by decide : "Reply" ≠ "Ready") (state_injective target)
  · change state "Request" = state "Ready" at source
    exact (by decide : "Request" ≠ "Ready") (state_injective source)

/-- The reply state has no outgoing authored reduction. -/
theorem reply_no_step (next : theory.Term proc) : ¬ theory.rewrites reply next := by
  intro step
  obtain ⟨move, membership, source, -⟩ := (Table.rewrites_iff protocol_wellFormed).mp step
  have listed : move ∈ [("prepare", "Request", "Ready"), ("deliver", "Ready", "Reply")] :=
    membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl
  · change state "Reply" = state "Request" at source
    exact (by decide : "Reply" ≠ "Request") (state_injective source)
  · change state "Reply" = state "Ready" at source
    exact (by decide : "Reply" ≠ "Ready") (state_injective source)

/-- Transitive closure does not turn a terminal state into a self-loop. -/
theorem reply_no_macroStep (next : theory.Term proc) :
    ¬ theory.nonemptyReduction.rewrites reply next := by
  intro computation
  obtain ⟨middle, first, -⟩ := Relation.TransGen.head'_iff.mp computation
  exact reply_no_step middle first

/-- A profile transition can comprise several primitive steps, while its
retained execution path continues to measure their actual number. -/
theorem profiles_distinguish_cost :
    theory.nonemptyReduction.rewrites request reply ∧
      ¬ theory.rewrites request reply ∧ requestPath.length = 2 :=
  ⟨request_macroStep, request_no_directStep, requestPath_length⟩

end Mettapedia.GSLT.LanguageDef.Contexts.Controls.TransitionProfile
