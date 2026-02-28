import Mettapedia.Languages.ProcessCalculi.MQCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.MQCalculus.Backend

/-!
# MQ-Calculus: Denotational Semantics

Following Stay & Meredith (2026), Section 6.3.

## Semantic clauses

```
⟦MQNil⟧(st)        = st
⟦MQOut i⟧(st)      = st
⟦MQGate U P⟧(st)   = ⟦P⟧(applyGate(U, st))
⟦MQNu P⟧(st)       = ⟦P⟧(allocFresh(st))
⟦MQPar P Q⟧(st)    = (⟦P⟧ st) >>= ⟦Q⟧
⟦MQIn i P Q⟧(st)   = if Pr(0) ≥ Pr(1) then ⟦P⟧(collapse 0) else ⟦Q⟧(collapse 1)
```

The denotation is backend-parametric via `MQSemanticsBackend`.
`denote` is the default instantiation with `statevectorBackend`.
-/

namespace Mettapedia.Languages.ProcessCalculi.MQCalculus

open Process

noncomputable section

/-- Denotation parameterized by a semantic backend. -/
def denoteWith (backend : MQSemanticsBackend) : Process → QState → Option QState
  | .MQNil,      st => some st
  | .MQOut _,    st => some st
  | .MQGate s p, st => denoteWith backend p (backend.applyGate s st)
  | .MQNu p,     st => denoteWith backend p (backend.allocFresh st)
  | .MQPar p q,  st => (denoteWith backend p st).bind (denoteWith backend q)
  | .MQIn i p q, st =>
      if backend.branchProb i .zero st ≥ backend.branchProb i .one st then
        denoteWith backend p (backend.collapse i .zero st)
      else
        denoteWith backend q (backend.collapse i .one st)

/-- Default denotation (statevector backend). -/
def denote : Process → QState → Option QState :=
  denoteWith statevectorBackend

/-! ### Paper-clause alignment lemmas (`mq-calculus.pdf`, §6.3) -/

/-- Paper §6.3 (`MQNil` clause): `⟦MQNil⟧(st) = st`. -/
@[simp] theorem clause63_nil (backend : MQSemanticsBackend) (st : QState) :
    denoteWith backend MQNil st = some st := rfl

/-- Paper §6.3 (`MQOut` clause): `⟦MQOut i⟧(st) = st`. -/
@[simp] theorem clause63_out (backend : MQSemanticsBackend) (i : ℕ) (st : QState) :
    denoteWith backend (MQOut i) st = some st := rfl

@[simp] theorem denoteWith_gate_clause (backend : MQSemanticsBackend)
    (g : GateSpec) (p : Process) (st : QState) :
    denoteWith backend (MQGate g p) st =
      denoteWith backend p (backend.applyGate g st) := rfl

@[simp] theorem denoteWith_new_clause (backend : MQSemanticsBackend)
    (p : Process) (st : QState) :
    denoteWith backend (MQNu p) st =
      denoteWith backend p (backend.allocFresh st) := rfl

@[simp] theorem denoteWith_par_clause (backend : MQSemanticsBackend)
    (p q : Process) (st : QState) :
    denoteWith backend (MQPar p q) st =
      (denoteWith backend p st).bind (denoteWith backend q) := rfl

theorem denoteWith_comm_clause (backend : MQSemanticsBackend) (i : ℕ)
    (p q : Process) (st : QState) :
    denoteWith backend (MQIn i p q) st =
      (if backend.branchProb i .zero st ≥ backend.branchProb i .one st then
         denoteWith backend p (backend.collapse i .zero st)
       else
         denoteWith backend q (backend.collapse i .one st)) := rfl

/-- Paper §6.3 (`MQIn` clause): branch selection by Born-style probabilities. -/
theorem clause63_in (backend : MQSemanticsBackend) (i : ℕ)
    (p q : Process) (st : QState) :
    denoteWith backend (MQIn i p q) st =
      (if backend.branchProb i .zero st ≥ backend.branchProb i .one st then
         denoteWith backend p (backend.collapse i .zero st)
       else
         denoteWith backend q (backend.collapse i .one st)) :=
  denoteWith_comm_clause backend i p q st

/-- Denotation is total for any backend in the current process language. -/
theorem denote_totalWith (backend : MQSemanticsBackend) :
    ∀ (p : Process) (st : QState), ∃ st', denoteWith backend p st = some st'
  | .MQNil, st => ⟨st, rfl⟩
  | .MQOut _, st => ⟨st, rfl⟩
  | .MQGate g p, st => denote_totalWith backend p (backend.applyGate g st)
  | .MQNu p, st => denote_totalWith backend p (backend.allocFresh st)
  | .MQPar p q, st => by
      rcases denote_totalWith backend p st with ⟨st1, h1⟩
      rcases denote_totalWith backend q st1 with ⟨st2, h2⟩
      refine ⟨st2, ?_⟩
      simp [denoteWith, h1, h2]
  | .MQIn i p q, st => by
      by_cases hchoose : backend.branchProb i .zero st ≥ backend.branchProb i .one st
      · rcases denote_totalWith backend p (backend.collapse i .zero st) with ⟨st', hst'⟩
        refine ⟨st', ?_⟩
        simp [denoteWith, hchoose, hst']
      · rcases denote_totalWith backend q (backend.collapse i .one st) with ⟨st', hst'⟩
        refine ⟨st', ?_⟩
        simp [denoteWith, hchoose, hst']

/-- Default denotation is total. -/
theorem denote_total (p : Process) (st : QState) : ∃ st', denote p st = some st' :=
  denote_totalWith statevectorBackend p st

/-- A probabilistic mixture of two quantum branches, with probabilities summing ≤ 1. -/
structure WeightedBranch where
  prob_zero    : ℝ
  prob_one     : ℝ
  state_zero   : QState
  state_one    : QState
  prob_zero_nn : 0 ≤ prob_zero
  prob_one_nn  : 0 ≤ prob_one
  prob_sum_le  : prob_zero + prob_one ≤ 1

def denote_measurementWith (backend : MQSemanticsBackend) (i : ℕ)
    (p q : Process) (st : QState) : WeightedBranch :=
  let st0 := backend.collapse i .zero st
  let st1 := backend.collapse i .one st
  { prob_zero    := backend.branchProb i .zero st
    prob_one     := backend.branchProb i .one st
    state_zero   := (denoteWith backend p st0).getD st0
    state_one    := (denoteWith backend q st1).getD st1
    prob_zero_nn := backend.branchProb_nonneg i .zero st
    prob_one_nn  := backend.branchProb_nonneg i .one st
    prob_sum_le  := by
      exact le_of_eq (backend.branchProb_sum_one i st)
  }

theorem denote_measurementWith_state_zero_eq (backend : MQSemanticsBackend)
    (i : ℕ) (p q : Process) (st : QState) :
    (denote_measurementWith backend i p q st).state_zero =
      (denoteWith backend p (backend.collapse i .zero st)).getD (backend.collapse i .zero st) := by
  simp [denote_measurementWith]

theorem denote_measurementWith_state_one_eq (backend : MQSemanticsBackend)
    (i : ℕ) (p q : Process) (st : QState) :
    (denote_measurementWith backend i p q st).state_one =
      (denoteWith backend q (backend.collapse i .one st)).getD (backend.collapse i .one st) := by
  simp [denote_measurementWith]

theorem denote_measurementWith_prob_sum_eq_one (backend : MQSemanticsBackend)
    (i : ℕ) (p q : Process) (st : QState) :
    (denote_measurementWith backend i p q st).prob_zero +
      (denote_measurementWith backend i p q st).prob_one = 1 := by
  simp [denote_measurementWith, backend.branchProb_sum_one]

theorem denote_measurementWith_prob_zero_nonneg (backend : MQSemanticsBackend)
    (i : ℕ) (p q : Process) (st : QState) :
    0 ≤ (denote_measurementWith backend i p q st).prob_zero := by
  simp [denote_measurementWith, backend.branchProb_nonneg]

theorem denote_measurementWith_prob_one_nonneg (backend : MQSemanticsBackend)
    (i : ℕ) (p q : Process) (st : QState) :
    0 ≤ (denote_measurementWith backend i p q st).prob_one := by
  simp [denote_measurementWith, backend.branchProb_nonneg]

/-- Default weighted measurement interpretation (using `statevectorBackend`). -/
def denote_measurement (i : ℕ) (p q : Process) (st : QState) : WeightedBranch :=
  denote_measurementWith statevectorBackend i p q st

theorem denote_measurement_prob_sum_eq_one (i : ℕ) (p q : Process) (st : QState) :
    (denote_measurement i p q st).prob_zero + (denote_measurement i p q st).prob_one = 1 := by
  simpa [denote_measurement] using
    denote_measurementWith_prob_sum_eq_one statevectorBackend i p q st

theorem denote_measurement_prob_zero_nonneg (i : ℕ) (p q : Process) (st : QState) :
    0 ≤ (denote_measurement i p q st).prob_zero := by
  simpa [denote_measurement] using
    denote_measurementWith_prob_zero_nonneg statevectorBackend i p q st

theorem denote_measurement_prob_one_nonneg (i : ℕ) (p q : Process) (st : QState) :
    0 ≤ (denote_measurement i p q st).prob_one := by
  simpa [denote_measurement] using
    denote_measurementWith_prob_one_nonneg statevectorBackend i p q st

/-- For structurally congruent terms, default denotation is defined on both sides. -/
theorem denote_sc_invariant (p q : Process) (st : QState) :
    SC p q → (denote p st).isSome ∧ (denote q st).isSome := by
  intro _
  constructor
  · rcases denote_total p st with ⟨st', hst'⟩
    simp [hst']
  · rcases denote_total q st with ⟨st', hst'⟩
    simp [hst']

/-- Direct COMM branching produces either branch `p` or branch `q`. -/
theorem denote_comm_step (i : ℕ) (p q : Process) (b : MeasurementBranch)
    (h : CommReduction i p q b) : b.result = p ∨ b.result = q := by
  cases h with
  | outcome_zero => left; rfl
  | outcome_one  => right; rfl

/-- `MQIn` denotation equals explicit branch-state selection from measurement semantics. -/
theorem denoteWith_comm_eq_measurementWith (backend : MQSemanticsBackend)
    (i : ℕ) (p q : Process) (st : QState) :
    denoteWith backend (MQIn i p q) st =
      (if backend.branchProb i .zero st ≥ backend.branchProb i .one st then
         some (denote_measurementWith backend i p q st).state_zero
       else
         some (denote_measurementWith backend i p q st).state_one) := by
  by_cases hchoose : backend.branchProb i .zero st ≥ backend.branchProb i .one st
  · rcases denote_totalWith backend p (backend.collapse i .zero st) with ⟨st0, h0⟩
    simp [denoteWith, denote_measurementWith, hchoose, h0]
  · rcases denote_totalWith backend q (backend.collapse i .one st) with ⟨st1, h1⟩
    simp [denoteWith, denote_measurementWith, hchoose, h1]

/-- Statevector specialization of `denoteWith_comm_eq_measurementWith`. -/
theorem denote_comm_eq_measurement (i : ℕ) (p q : Process) (st : QState) :
    denote (MQIn i p q) st =
      (if statevectorBackend.branchProb i .zero st ≥ statevectorBackend.branchProb i .one st then
         some (denote_measurement i p q st).state_zero
       else
         some (denote_measurement i p q st).state_one) := by
  simpa [denote, denote_measurement] using
    denoteWith_comm_eq_measurementWith statevectorBackend i p q st

end

end Mettapedia.Languages.ProcessCalculi.MQCalculus
