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
  applyGate : GateSpec → QState → QState
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

/-- Lookup matrix by typed gate operator. -/
def gateMatrixOfOp : GateOp → Option OneQubitMatrix
  | .H => some hadamardM
  | .X => some pauliXM
  | .Z => some pauliZM
  | .custom _ => none

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

/-- Apply a typed gate spec to a state. -/
noncomputable def applyGateSpec (g : GateSpec) (st : QState) : QState :=
  match gateMatrixOfOp g.op with
  | none => st
  | some M => applyOneQubitMatrix M g.target st

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

/-- Pointwise norm scaling for collapse amplitudes. -/
private theorem term_norm_scaled
    (i : ℕ) (out : Outcome) (st : QState) (p : ℝ)
    (hp_nonneg : 0 ≤ p) (hp_ne : p ≠ 0) (k : Fin (2 ^ st.n)) :
    norm (if bitMatches i k.1 out then
        st.ψ.ofLp k / (((Real.sqrt p) : ℝ) : ℂ) else 0) ^ 2
      = (if bitMatches i k.1 out then Complex.normSq (st.ψ.ofLp k) / p else 0) := by
  by_cases hbit : bitMatches i k.1 out = true
  · have hsqrt_nonneg : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
    have habs : |Real.sqrt p| = Real.sqrt p := abs_of_nonneg hsqrt_nonneg
    have hsq : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp_nonneg
    simp [hbit, Complex.normSq_eq_norm_sq, habs]
    ring_nf
    field_simp [hp_ne]
    nlinarith
  · simp [hbit]

/-- Pull a constant denominator out of a finite masked sum. -/
private theorem sum_scaled_div (i : ℕ) (out : Outcome) (st : QState) (p : ℝ) :
    (∑ k : Fin (2 ^ st.n), if bitMatches i k.1 out then Complex.normSq (st.ψ.ofLp k) / p else 0)
      =
    (∑ k : Fin (2 ^ st.n), if bitMatches i k.1 out then Complex.normSq (st.ψ.ofLp k) else 0) / p := by
  have hdiv :=
    (Finset.sum_div (s := (Finset.univ : Finset (Fin (2 ^ st.n))))
      (f := fun k : Fin (2 ^ st.n) =>
        if bitMatches i k.1 out then Complex.normSq (st.ψ.ofLp k) else 0)
      (a := p))
  have hpoint :
      (∑ x : Fin (2 ^ st.n),
          (if bitMatches i x.1 out then Complex.normSq (st.ψ.ofLp x) else 0) / p)
      =
      (∑ x : Fin (2 ^ st.n),
          if bitMatches i x.1 out then Complex.normSq (st.ψ.ofLp x) / p else 0) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    by_cases hbx : bitMatches i x.1 out = true
    · simp [hbx]
    · simp [hbx]
  calc
    (∑ k : Fin (2 ^ st.n), if bitMatches i k.1 out then Complex.normSq (st.ψ.ofLp k) / p else 0)
        = (∑ x : Fin (2 ^ st.n),
            (if bitMatches i x.1 out then Complex.normSq (st.ψ.ofLp x) else 0) / p) := by
              symm
              exact hpoint
    _ = (∑ k : Fin (2 ^ st.n), if bitMatches i k.1 out then Complex.normSq (st.ψ.ofLp k) else 0) / p := by
          exact hdiv.symm

/-- If the selected branch has positive raw mass, collapsed state has unit squared norm. -/
theorem collapseByOutcome_norm_sq_eq_one_of_raw_pos (i : ℕ) (out : Outcome) (st : QState)
    (hraw : 0 < rawOutcomeProb i out st) :
    norm ((collapseByOutcome i out st).ψ) ^ 2 = 1 := by
  let p : ℝ := rawOutcomeProb i out st
  have hp : p = rawOutcomeProb i out st := rfl
  have hp_pos : 0 < p := by simpa [hp] using hraw
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  unfold collapseByOutcome
  rw [if_neg (by simpa [hp] using hp_ne)]
  rw [← hp]
  set z : ℂ := (((Real.sqrt p) : ℝ) : ℂ)
  set ψ' : QVec st.n :=
      Finset.univ.sum (fun k : Fin (2 ^ st.n) =>
        EuclideanSpace.single k
          (if bitMatches i k.1 out then st.ψ.ofLp k / z else 0))
  change norm ψ' ^ 2 = 1
  have hnormsq :
      norm ψ' ^ 2 =
        ∑ k : Fin (2 ^ st.n),
          norm (if bitMatches i k.1 out then st.ψ.ofLp k / z else 0) ^ 2 := by
    simpa [ψ'] using
      (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin (2 ^ st.n) => ℂ) ψ')
  have hsum1 :
      (∑ k : Fin (2 ^ st.n), norm (if bitMatches i k.1 out then st.ψ.ofLp k / z else 0) ^ 2)
      =
      (∑ k : Fin (2 ^ st.n), if bitMatches i k.1 out then Complex.normSq (st.ψ.ofLp k) / p else 0) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    simpa [z] using term_norm_scaled i out st p hp_nonneg hp_ne k
  have hraw_eq :
      (∑ k : Fin (2 ^ st.n), if bitMatches i k.1 out then Complex.normSq (st.ψ.ofLp k) else 0) = p := by
    simp [rawOutcomeProb, hp]
  calc
    norm ψ' ^ 2
        = (∑ k : Fin (2 ^ st.n), norm (if bitMatches i k.1 out then st.ψ.ofLp k / z else 0) ^ 2) := hnormsq
    _ = (∑ k : Fin (2 ^ st.n), if bitMatches i k.1 out then Complex.normSq (st.ψ.ofLp k) / p else 0) := hsum1
    _ = (∑ k : Fin (2 ^ st.n), if bitMatches i k.1 out then Complex.normSq (st.ψ.ofLp k) else 0) / p := by
          exact sum_scaled_div i out st p
    _ = p / p := by simp [hraw_eq]
    _ = 1 := by field_simp [hp_ne]

/-- Positive-mass collapse renormalizes to unit norm. -/
theorem collapseByOutcome_norm_eq_one_of_raw_pos (i : ℕ) (out : Outcome) (st : QState)
    (hraw : 0 < rawOutcomeProb i out st) :
    norm ((collapseByOutcome i out st).ψ) = 1 := by
  have hsq : norm ((collapseByOutcome i out st).ψ) ^ 2 = 1 :=
    collapseByOutcome_norm_sq_eq_one_of_raw_pos i out st hraw
  have hnonneg : 0 ≤ norm ((collapseByOutcome i out st).ψ) := by
    exact norm_nonneg _
  rcases (sq_eq_one_iff.mp hsq) with h | h
  · exact h
  · exfalso
    linarith

@[simp] theorem applyOneQubitMatrix_n (M : OneQubitMatrix) (i : ℕ) (st : QState) :
    (applyOneQubitMatrix M i st).n = st.n := by
  unfold applyOneQubitMatrix
  split_ifs <;> rfl

@[simp] theorem applyGateSpec_n (g : GateSpec) (st : QState) :
    (applyGateSpec g st).n = st.n := by
  unfold applyGateSpec
  cases hmat : gateMatrixOfOp g.op <;> simp [applyOneQubitMatrix_n]

/-- Statevector backend with concrete branch probabilities/collapse semantics. -/
noncomputable def statevectorBackend : MQSemanticsBackend where
  branchProb := branchProbOf
  branchProb_nonneg := branchProbOf_nonneg
  branchProb_sum_one := branchProbOf_sum_one
  applyGate := applyGateSpec
  allocFresh := fun st => ⟨st.n + 1, allocFreshVec st.ψ⟩
  collapse := collapseByOutcome

@[simp] theorem idealizedBackend_applyGate_id (g : GateSpec) (st : QState) :
    idealizedBackend.applyGate g st = st := rfl

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

@[simp] theorem statevectorBackend_applyGate_n (g : GateSpec) (st : QState) :
    (statevectorBackend.applyGate g st).n = st.n := by
  simp [statevectorBackend, applyGateSpec_n]

@[simp] theorem statevectorBackend_collapse_n (i : ℕ) (out : Outcome) (st : QState) :
    (statevectorBackend.collapse i out st).n = st.n := by
  simp [statevectorBackend, collapseByOutcome_n]

end

end Mettapedia.Languages.ProcessCalculi.MQCalculus
