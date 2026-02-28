import Mettapedia.Languages.ProcessCalculi.MQCalculus.MQCalculus
import Mettapedia.Languages.ProcessCalculi.MORK.MORKCommBridge

/-!
# MQ-Calculus Interoperability Bridges

Cross-calculus coherence theorems showing that MQ COMM non-determinism aligns
with the existing MORK binary-fold semantics.

This module is intentionally theorem-only: it reuses already-proven bridges
without introducing duplicate operational definitions.
-/

namespace Mettapedia.Languages.ProcessCalculi.MQCalculus

open Process
open Mettapedia.Languages.ProcessCalculi.MORK (FoldStep FoldPicksSubResult)

/-- MQ COMM binary branching is equivalent to MORK binary-fold branching. -/
theorem comm_nondeterminism_iff_mork_binary (i : ℕ) (p q : Process) :
    (CommReduction i p q ⟨.zero, p⟩ ∧ CommReduction i p q ⟨.one, q⟩) ↔
    ∀ (fold : FoldStep) (_hb : fold.isBinary),
      (∃ (f0 : FoldStep) (_ : f0.isBinary), FoldPicksSubResult f0 ‹_› .subResult0) ∧
      (∃ (f1 : FoldStep) (_ : f1.isBinary), FoldPicksSubResult f1 ‹_› .subResult1) := by
  simpa using
    Mettapedia.Languages.ProcessCalculi.MORK.mork_mq_nondeterminism_corresponds i p q

/-- Every MORK binary outcome has a matching MQ COMM branch witness. -/
theorem mork_outcome_realized_by_comm
    (o : Mettapedia.Languages.ProcessCalculi.MORK.MorkOutcome) :
    ∃ (i : ℕ) (p q : Process) (b : MeasurementBranch),
      b.outcome = Mettapedia.Languages.ProcessCalculi.MORK.morkOutcomeToMQ o ∧
      CommReduction i p q b := by
  simpa using
    Mettapedia.Languages.ProcessCalculi.MORK.canary_comm_reduction_matches_mork_outcome o

end Mettapedia.Languages.ProcessCalculi.MQCalculus
