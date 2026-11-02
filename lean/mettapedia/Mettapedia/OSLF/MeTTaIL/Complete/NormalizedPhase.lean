import Mettapedia.OSLF.MeTTaIL.Complete.Normalized

/-! The complete class search reports pending or complete. Consequently a
reached normalized runner is running or done, never an unsupported phase.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Normalized

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open Mettapedia.Machines.ResumableSearchRunner

theorem reached_phase (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr) (mode : Commit)
    (machine : Machine Pattern (Classes.State plan) GeneralOccurrenceSemantics.Receipt)
    (reached : Reached (search plan bound expected mode) machine) :
    machine.phase = .running ∨ machine.phase = .done := by
  cases phase : machine.phase with
  | running => exact .inl rfl
  | done => exact .inr rfl
  | blocked =>
    obtain ⟨_, stopped⟩ := reached.stopped (by simp [phase])
    simp only [search, Classes.search, Classes.status] at stopped
    split at stopped <;> simp [phaseOf, phase] at stopped

#print axioms reached_phase

end Mettapedia.OSLF.MeTTaIL.Complete.Normalized
