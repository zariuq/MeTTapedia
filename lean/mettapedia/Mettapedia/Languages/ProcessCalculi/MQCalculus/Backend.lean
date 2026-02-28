import Mettapedia.Languages.ProcessCalculi.MQCalculus.CommRule

/-!
# MQ-Calculus: Semantic Backend Interface

A denotational backend with explicit runtime state and wire-growth support.

This layer supports:
- gate application,
- fresh-wire allocation,
- measurement branch probabilities,
- post-measurement collapse.
-/

namespace Mettapedia.Languages.ProcessCalculi.MQCalculus

open Process

noncomputable section

/-- A runtime quantum state with explicit wire count. -/
structure QState where
  n : ℕ
  ψ : QVec n

/-- Helper constructor for readability at call sites. -/
def QState.mkOf (n : ℕ) (ψ : QVec n) : QState := ⟨n, ψ⟩

/-- `2^n < 2^(n+1)`: used for fresh-wire embedding. -/
private theorem pow2_lt_pow2_succ (n : ℕ) : 2 ^ n < 2 ^ (n + 1) := by
  calc
    2 ^ n < 2 ^ n + 2 ^ n := Nat.lt_add_of_pos_right (pow_pos (by decide : 0 < (2:ℕ)) n)
    _ = 2 ^ (n + 1) := by
      simp [pow_succ, Nat.two_mul, Nat.mul_comm]

/-- Embed `ψ : QVec n` into `QVec (n+1)` as `|0⟩ ⊗ ψ` in block form. -/
def allocFreshVec {n : ℕ} (ψ : QVec n) : QVec (n + 1) :=
  Finset.univ.sum (fun k : Fin (2 ^ n) =>
    EuclideanSpace.single
      (i := (⟨k.1, lt_trans k.2 (pow2_lt_pow2_succ n)⟩ : Fin (2 ^ (n + 1))))
      (a := ψ.ofLp k))

/-- Boolean view of outcomes (`false = 0`, `true = 1`). -/
def outcomeToBit : Outcome → Bool
  | .zero => false
  | .one  => true

/-- Whether basis index `k` has the measured bit `i` equal to `out`. -/
def bitMatches (i k : ℕ) (out : Outcome) : Bool :=
  Nat.testBit k i == outcomeToBit out

/-- Unnormalized branch probability from amplitudes on basis states matching `out`. -/
def rawOutcomeProb (i : ℕ) (out : Outcome) (st : QState) : ℝ :=
  Finset.univ.sum (fun k : Fin (2 ^ st.n) =>
    if bitMatches i k.1 out then Complex.normSq (st.ψ.ofLp k) else 0)

theorem rawOutcomeProb_nonneg (i : ℕ) (out : Outcome) (st : QState) :
    0 ≤ rawOutcomeProb i out st := by
  unfold rawOutcomeProb
  refine Finset.sum_nonneg ?_
  intro k _hk
  by_cases h : bitMatches i k.1 out = true
  · simp [h, Complex.normSq_nonneg]
  · simp [h]

/--
Normalized branch probability.
If both raw branch masses are zero, we choose `(1,0)` as a total fallback.
-/
def branchProbOf (i : ℕ) (out : Outcome) (st : QState) : ℝ :=
  let p0 := rawOutcomeProb i .zero st
  let p1 := rawOutcomeProb i .one st
  let t := p0 + p1
  if t = 0 then
    match out with
    | .zero => 1
    | .one  => 0
  else
    match out with
    | .zero => p0 / t
    | .one  => p1 / t

theorem branchProbOf_nonneg (i : ℕ) (out : Outcome) (st : QState) :
    0 ≤ branchProbOf i out st := by
  let p0 := rawOutcomeProb i .zero st
  let p1 := rawOutcomeProb i .one st
  have hp0 : 0 ≤ p0 := by
    simpa [p0] using rawOutcomeProb_nonneg i .zero st
  have hp1 : 0 ≤ p1 := by
    simpa [p1] using rawOutcomeProb_nonneg i .one st
  by_cases ht : p0 + p1 = 0
  · cases out <;> simp [branchProbOf, p0, p1, ht]
  · cases out
    · simpa [branchProbOf, p0, p1, ht] using
        div_nonneg hp0 (add_nonneg hp0 hp1)
    · simpa [branchProbOf, p0, p1, ht] using
        div_nonneg hp1 (add_nonneg hp0 hp1)

theorem branchProbOf_sum_one (i : ℕ) (st : QState) :
    branchProbOf i .zero st + branchProbOf i .one st = 1 := by
  let p0 := rawOutcomeProb i .zero st
  let p1 := rawOutcomeProb i .one st
  by_cases ht : p0 + p1 = 0
  · simp [branchProbOf, p0, p1, ht]
  · have htnz : p0 + p1 ≠ 0 := ht
    have hdiv : p0 / (p0 + p1) + p1 / (p0 + p1) = 1 := by
      field_simp [htnz]
    simpa [branchProbOf, p0, p1, ht] using hdiv

/-- Collapse by outcome: project to matching basis components and renormalize. -/
def collapseByOutcome (i : ℕ) (out : Outcome) (st : QState) : QState :=
  let p := rawOutcomeProb i out st
  if p = 0 then
    st
  else
    let z : ℂ := ((Real.sqrt p) : ℂ)
    let ψ' : QVec st.n :=
      Finset.univ.sum (fun k : Fin (2 ^ st.n) =>
        EuclideanSpace.single k
          (if bitMatches i k.1 out then st.ψ.ofLp k / z else 0))
    ⟨st.n, ψ'⟩

/-- Backend operations required by denotational semantics. -/
structure MQSemanticsBackend where
  /-- Branch probability on measuring wire `i` with outcome `0/1`. -/
  branchProb : ℕ → Outcome → QState → ℝ
  /-- Branch probabilities are non-negative. -/
  branchProb_nonneg : ∀ (i : ℕ) (out : Outcome) (st : QState), 0 ≤ branchProb i out st
  /-- Branch probabilities form a total split. -/
  branchProb_sum_one : ∀ (i : ℕ) (st : QState),
      branchProb i .zero st + branchProb i .one st = 1
  /-- Gate action for named gate symbols. -/
  applyGate : String → QState → QState
  /-- Fresh-wire allocation action (paper: `|0⟩ ⊗ ψ`). -/
  allocFresh : QState → QState
  /-- Collapse/update of a selected wire after observing an outcome. -/
  collapse : ℕ → Outcome → QState → QState

/-- Conservative backend (idealized branch split, identity gate/collapse). -/
noncomputable def idealizedBackend : MQSemanticsBackend where
  branchProb := fun _ out _ =>
    match out with
    | .zero => 1
    | .one  => 0
  branchProb_nonneg := by
    intro _ out _
    cases out <;> simp
  branchProb_sum_one := by
    intro _ _
    simp
  applyGate := fun _gate st => st
  allocFresh := fun st => ⟨st.n + 1, allocFreshVec st.ψ⟩
  collapse := fun _i _outcome st => st

/-- `n = 1` cast helper for optional one-qubit gate semantics. -/
noncomputable def castQVec {n m : ℕ} (h : n = m) : QVec n → QVec m := by
  subst h
  exact id

/-- Dense 2x2 complex matrix for one-qubit gates. -/
structure OneQubitMatrix where
  m00 : ℂ
  m01 : ℂ
  m10 : ℂ
  m11 : ℂ

/-- Hadamard gate matrix. -/
noncomputable def hadamardM : OneQubitMatrix :=
  let c : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)
  { m00 := c, m01 := c, m10 := c, m11 := -c }

/-- Pauli-X gate matrix. -/
noncomputable def pauliXM : OneQubitMatrix :=
  { m00 := 0, m01 := 1, m10 := 1, m11 := 0 }

/-- Pauli-Z gate matrix. -/
noncomputable def pauliZM : OneQubitMatrix :=
  { m00 := 1, m01 := 0, m10 := 0, m11 := -1 }

/-- Lookup matrix for gate names in the paper examples. -/
def gateMatrixOfName : String → Option OneQubitMatrix
  | "H" => some hadamardM
  | "X" => some pauliXM
  | "Z" => some pauliZM
  | _   => none

/-- Parse gate spec `NAME@i`; legacy `NAME` defaults to wire `0`. -/
def parseGateSpec (gate : String) : String × Nat :=
  match gate.splitOn "@" with
  | [name] => (name, 0)
  | [name, idx] => (name, idx.toNat?.getD 0)
  | name :: _ => (name, 0)
  | [] => (gate, 0)

/-- Partner basis index obtained by toggling bit `i` and projecting to width `n`. -/
def partnerIndexNat (n i k : Nat) : Nat :=
  (k ^^^ (2 ^ i)) % (2 ^ n)

/-- One-qubit gate action on target wire `i` of an `n`-qubit statevector. -/
noncomputable def applyOneQubitMatrix (M : OneQubitMatrix) (i : Nat) (st : QState) : QState :=
  if _hi : i < st.n then
    let ψ' : QVec st.n :=
      Finset.univ.sum (fun k : Fin (2 ^ st.n) =>
        let partnerNat := partnerIndexNat st.n i k.1
        have hPartner : partnerNat < 2 ^ st.n := by
          exact Nat.mod_lt _ (pow_pos (by decide : 0 < (2:ℕ)) st.n)
        let partner : Fin (2 ^ st.n) := ⟨partnerNat, hPartner⟩
        let bit := Nat.testBit k.1 i
        let amp0 : ℂ := if bit then st.ψ.ofLp partner else st.ψ.ofLp k
        let amp1 : ℂ := if bit then st.ψ.ofLp k else st.ψ.ofLp partner
        let out : ℂ :=
          if bit
          then M.m10 * amp0 + M.m11 * amp1
          else M.m00 * amp0 + M.m01 * amp1
        EuclideanSpace.single k out)
    ⟨st.n, ψ'⟩
  else
    st

/-- Apply a named gate spec to a state (`"H@2"`, `"X@0"`, legacy `"Z"`). -/
noncomputable def applyNamedGate (gate : String) (st : QState) : QState :=
  let (name, i) := parseGateSpec gate
  match gateMatrixOfName name with
  | none => st
  | some M => applyOneQubitMatrix M i st

@[simp] theorem collapseByOutcome_n (i : ℕ) (out : Outcome) (st : QState) :
    (collapseByOutcome i out st).n = st.n := by
  unfold collapseByOutcome
  by_cases h : rawOutcomeProb i out st = 0
  · simp [h]
  · simp [h]

@[simp] theorem collapseByOutcome_zero_mass (i : ℕ) (out : Outcome) (st : QState)
    (h : rawOutcomeProb i out st = 0) :
    collapseByOutcome i out st = st := by
  simp [collapseByOutcome, h]

@[simp] theorem applyOneQubitMatrix_n (M : OneQubitMatrix) (i : ℕ) (st : QState) :
    (applyOneQubitMatrix M i st).n = st.n := by
  unfold applyOneQubitMatrix
  split_ifs <;> rfl

@[simp] theorem applyNamedGate_n (gate : String) (st : QState) :
    (applyNamedGate gate st).n = st.n := by
  unfold applyNamedGate
  cases hspec : parseGateSpec gate with
  | mk name i =>
      cases hmat : gateMatrixOfName name <;> simp [hmat, applyOneQubitMatrix_n]

/-- Statevector backend with concrete branch probabilities/collapse semantics. -/
noncomputable def statevectorBackend : MQSemanticsBackend where
  branchProb := branchProbOf
  branchProb_nonneg := branchProbOf_nonneg
  branchProb_sum_one := branchProbOf_sum_one
  applyGate := applyNamedGate
  allocFresh := fun st => ⟨st.n + 1, allocFreshVec st.ψ⟩
  collapse := collapseByOutcome

@[simp] theorem idealizedBackend_applyGate_id (s : String) (st : QState) :
    idealizedBackend.applyGate s st = st := rfl

@[simp] theorem idealizedBackend_allocFresh_n (st : QState) :
    (idealizedBackend.allocFresh st).n = st.n + 1 := rfl

@[simp] theorem idealizedBackend_collapse_id (i : ℕ) (r : Outcome) (st : QState) :
    idealizedBackend.collapse i r st = st := rfl

@[simp] theorem idealizedBackend_branchProb_zero (i : ℕ) (st : QState) :
    idealizedBackend.branchProb i .zero st = 1 := rfl

@[simp] theorem idealizedBackend_branchProb_one (i : ℕ) (st : QState) :
    idealizedBackend.branchProb i .one st = 0 := rfl

@[simp] theorem statevectorBackend_allocFresh_n (st : QState) :
    (statevectorBackend.allocFresh st).n = st.n + 1 := rfl

@[simp] theorem statevectorBackend_applyGate_n (s : String) (st : QState) :
    (statevectorBackend.applyGate s st).n = st.n := by
  simp [statevectorBackend, applyNamedGate_n]

@[simp] theorem statevectorBackend_collapse_n (i : ℕ) (out : Outcome) (st : QState) :
    (statevectorBackend.collapse i out st).n = st.n := by
  simp [statevectorBackend, collapseByOutcome_n]

end

end Mettapedia.Languages.ProcessCalculi.MQCalculus
