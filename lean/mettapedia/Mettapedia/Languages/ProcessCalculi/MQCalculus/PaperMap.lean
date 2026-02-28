import Mettapedia.Languages.ProcessCalculi.MQCalculus.MQCalculus
import Mettapedia.Languages.ProcessCalculi.MQCalculus.Interoperability

/-!
# MQ-Calculus Paper Clause Map

A theorem-level index from the paper clauses (`mq-calculus.pdf`) to concrete Lean
lemma names in this repository.

This keeps review/audit work straightforward: each clause has an explicit theorem
handle that can be imported by downstream modules.
-/

namespace Mettapedia.Languages.ProcessCalculi.MQCalculus

open Process

/-! ## Section 6.3 denotational clauses -/

/-- Paper §6.3: `⟦MQNil⟧(st) = st`. -/
theorem paper63_nil (backend : MQSemanticsBackend) (st : QState) :
    denoteWith backend MQNil st = some st :=
  clause63_nil backend st

/-- Paper §6.3: `⟦MQOut i⟧(st) = st`. -/
theorem paper63_out (backend : MQSemanticsBackend) (i : ℕ) (st : QState) :
    denoteWith backend (MQOut i) st = some st :=
  clause63_out backend i st

/-- Paper §6.3: `⟦MQGate U P⟧(st) = ⟦P⟧(applyGate(U, st))`. -/
theorem paper63_gate (backend : MQSemanticsBackend)
    (g : GateSpec) (p : Process) (st : QState) :
    denoteWith backend (MQGate g p) st =
      denoteWith backend p (backend.applyGate g st) :=
  denoteWith_gate_clause backend g p st

/-- Paper §6.3: `⟦new P⟧(st) = ⟦P⟧(allocFresh(st))`. -/
theorem paper63_new (backend : MQSemanticsBackend)
    (p : Process) (st : QState) :
    denoteWith backend (MQNu p) st =
      denoteWith backend p (backend.allocFresh st) :=
  denoteWith_new_clause backend p st

/-- Paper §6.3: `⟦P | Q⟧(st) = (⟦P⟧ st) >>= ⟦Q⟧`. -/
theorem paper63_par (backend : MQSemanticsBackend)
    (p q : Process) (st : QState) :
    denoteWith backend (MQPar p q) st =
      (denoteWith backend p st).bind (denoteWith backend q) :=
  denoteWith_par_clause backend p q st

/-- Paper §6.3: branch selection clause for `MQIn`. -/
theorem paper63_in (backend : MQSemanticsBackend) (i : ℕ)
    (p q : Process) (st : QState) :
    denoteWith backend (MQIn i p q) st =
      (if backend.branchProb i .zero st ≥ backend.branchProb i .one st then
         denoteWith backend p (backend.collapse i .zero st)
       else
         denoteWith backend q (backend.collapse i .one st)) :=
  clause63_in backend i p q st

/-- Paper §6.3: measurement branch probabilities normalize to 1. -/
theorem paper63_measurement_probs_sum_one (backend : MQSemanticsBackend)
    (i : ℕ) (p q : Process) (st : QState) :
    (denote_measurementWith backend i p q st).prob_zero +
      (denote_measurementWith backend i p q st).prob_one = 1 :=
  denote_measurementWith_prob_sum_eq_one backend i p q st

/-- Paper §6.3 branch-0 post-state is evaluated from collapsed state `collapse(i,0,st)`. -/
theorem paper63_measurement_state_zero (backend : MQSemanticsBackend)
    (i : ℕ) (p q : Process) (st : QState) :
    (denote_measurementWith backend i p q st).state_zero =
      (denoteWith backend p (backend.collapse i .zero st)).getD (backend.collapse i .zero st) :=
  denote_measurementWith_state_zero_eq backend i p q st

/-- Paper §6.3 branch-1 post-state is evaluated from collapsed state `collapse(i,1,st)`. -/
theorem paper63_measurement_state_one (backend : MQSemanticsBackend)
    (i : ℕ) (p q : Process) (st : QState) :
    (denote_measurementWith backend i p q st).state_one =
      (denoteWith backend q (backend.collapse i .one st)).getD (backend.collapse i .one st) :=
  denote_measurementWith_state_one_eq backend i p q st

/-- Paper §6.3 (statevector backend): positive-mass collapse normalizes to unit norm. -/
theorem paper63_statevector_collapse_norm_one_of_raw_pos
    (i : ℕ) (out : Outcome) (st : QState)
    (hraw : 0 < rawOutcomeProb i out st) :
    norm ((statevectorBackend.collapse i out st).ψ) = 1 := by
  simpa [statevectorBackend] using
    collapseByOutcome_norm_eq_one_of_raw_pos i out st hraw

/-- Executable COMM denotation equals explicit branch-state selection record. -/
theorem paper63_comm_denote_eq_measurement_selection (i : ℕ) (p q : Process) (st : QState) :
    denote (MQIn i p q) st =
      (if statevectorBackend.branchProb i .zero st ≥ statevectorBackend.branchProb i .one st then
         some (denote_measurement i p q st).state_zero
       else
         some (denote_measurement i p q st).state_one) :=
  denote_comm_eq_measurement i p q st

/-! ## Section 3 communication reduction facts -/

/-- Paper §3: COMM has both outcomes constructively available. -/
theorem paper3_comm_both_outcomes (i : ℕ) (p q : Process) :
    CommReduction i p q ⟨.zero, p⟩ ∧ CommReduction i p q ⟨.one, q⟩ :=
  comm_both_outcomes i p q

/-- Paper §3: COMM branch set is exhaustive (`p` or `q`). -/
theorem paper3_comm_exhaustive (i : ℕ) (p q : Process) (b : MeasurementBranch) :
    CommReduction i p q b → b = ⟨.zero, p⟩ ∨ b = ⟨.one, q⟩ :=
  comm_branches_exhaustive i p q b

/-! ## Cross-calculus coherence (MORK) -/

/-- MORK binary fold branching is equivalent to MQ COMM branching. -/
theorem paper_mork_mq_branching_equiv (i : ℕ) (p q : Process) :
    (CommReduction i p q ⟨.zero, p⟩ ∧ CommReduction i p q ⟨.one, q⟩) ↔
    ∀ (fold : Mettapedia.Languages.ProcessCalculi.MORK.FoldStep) (_hb : fold.isBinary),
      (∃ (f0 : Mettapedia.Languages.ProcessCalculi.MORK.FoldStep) (_ : f0.isBinary),
        Mettapedia.Languages.ProcessCalculi.MORK.FoldPicksSubResult f0 ‹_› .subResult0) ∧
      (∃ (f1 : Mettapedia.Languages.ProcessCalculi.MORK.FoldStep) (_ : f1.isBinary),
        Mettapedia.Languages.ProcessCalculi.MORK.FoldPicksSubResult f1 ‹_› .subResult1) :=
  comm_nondeterminism_iff_mork_binary i p q

end Mettapedia.Languages.ProcessCalculi.MQCalculus
