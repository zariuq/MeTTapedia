import Mettapedia.Languages.ProcessCalculi.MQCalculus.Denotational

/-!
# MQ-Calculus: Facade and Integration Tests

**Canary theorems** requiring every layer to typecheck correctly.

## Note on `MQPar` vs `‖` notation

Theorem types use `MQPar` directly (rather than the `‖` notation) to avoid
a conflict with Mathlib's `‖·‖` norm notation (both use U+2016).
The `‖` notation can be used inside `by`-tactic blocks where Lean's parser
context disambiguates it, but not in binder/type positions.

## Connection to ρ-calculus

Both share par-comm, par-assoc, new-nil, scope-extrusion, and congruence closure.
MQ is strictly simpler: no reflection, no name type.  Born-rule COMM is the
sole source of quantum behavior.

## Connection to π-calculus

`MQIn i P P` (equal branches) recovers deterministic synchronous communication.

## Connection to MORK parallel-fold

`MQOut i | MQIn i P Q` fires ALL matching pairs simultaneously (Born-rule per pair),
identical to MORK's parallel multi-subcall (unfold N; fold all N).
-/

namespace Mettapedia.Languages.ProcessCalculi.MQCalculus

open Process

-- Canary 1: COMM is non-deterministic
theorem canary_comm_both_branches (i : ℕ) (p q : Process) :
    Reduces (MQPar (MQOut i) (MQIn i p q)) p ∧
    Reduces (MQPar (MQOut i) (MQIn i p q)) q :=
  ⟨comm_zero i p q, comm_one i p q⟩

-- Canary 2: COMM inside a parallel context
theorem canary_comm_in_context (i : ℕ) (p q r : Process) :
    Reduces (MQPar (MQPar (MQOut i) (MQIn i p q)) r) (MQPar p r) :=
  Reduces.par_l _ _ _ (comm_zero i p q)

-- Canary 3: shift distributes over par
theorem canary_shift_par (c : ℕ) (p q : Process) :
    shift c (MQPar p q) = MQPar (shift c p) (shift c q) := rfl

-- Canary 4: scope extrusion uses shift at cutoff 0
theorem canary_scope_extrusion (p q : Process) :
    SC (MQNu (MQPar (shift 0 p) q)) (MQPar p (MQNu q)) :=
  SC.scope_extrusion p q

-- Canary 5: multi-step chain: COMM to p, then p steps to p'
theorem canary_multistep_chain (i : ℕ) (p p' q : Process) (h : Reduces p p') :
    MQPar (MQOut i) (MQIn i p q) →* p' :=
  MultiStep.trans (MultiStep.one (comm_zero i p q))
                  (MultiStep.one h)

-- Canary 6: SC is an equivalence
theorem canary_sc_equiv : Equivalence SC := SC_equivalence

-- Canary 7: Born-rule weights are non-negative
theorem canary_born_nonneg (r : Outcome) (ψ : QVec 1) :
    0 ≤ born_prob r ψ :=
  born_prob_nonneg r ψ

-- Canary 8: shift_comm applies to COMM-capable processes
theorem canary_shift_comm_instance (c d : ℕ) (hcd : c ≤ d) (p q : Process) :
    shift c (shift d (MQPar (MQOut 0) (MQIn 0 p q))) =
    shift (d + 1) (shift c (MQPar (MQOut 0) (MQIn 0 p q))) :=
  shift_comm _ c d hcd

-- Canary 9: stateful denotation typechecks end-to-end
theorem canary_denote_typechecks (n : ℕ) (ψ : QVec n) :
    ∃ r, r = denote (MQPar (MQOut 0) (MQIn 0 MQNil MQNil)) (QState.mkOf n ψ) :=
  ⟨_, rfl⟩

-- Canary 10: `new` allocates one fresh wire in denotation.
theorem canary_new_increments_wires (n : ℕ) (ψ : QVec n) :
    ∃ st', denote (MQNu MQNil) (QState.mkOf n ψ) = some st' ∧ st'.n = n + 1 := by
  refine ⟨statevectorBackend.allocFresh (QState.mkOf n ψ), ?_, ?_⟩
  · rfl
  · exact statevectorBackend_allocFresh_n (QState.mkOf n ψ)

-- Canary 11: branch probabilities are normalized for any state.
theorem canary_branch_probs_sum_one (i : ℕ) (n : ℕ) (ψ : QVec n) :
    statevectorBackend.branchProb i .zero (QState.mkOf n ψ) +
      statevectorBackend.branchProb i .one (QState.mkOf n ψ) = 1 :=
  statevectorBackend.branchProb_sum_one i (QState.mkOf n ψ)

-- Canary 12: collapse keeps wire count unchanged.
theorem canary_collapse_preserves_wires (i : ℕ) (r : Outcome) (n : ℕ) (ψ : QVec n) :
    (statevectorBackend.collapse i r (QState.mkOf n ψ)).n = n := by
  unfold statevectorBackend collapseByOutcome
  by_cases h : rawOutcomeProb i r (QState.mkOf n ψ) = 0
  · simp [h]
    rfl
  · simp [h]
    rfl

-- Canary 13: gate application preserves wire count for all gate specs.
theorem canary_apply_gate_preserves_wires (g : GateSpec) (n : ℕ) (ψ : QVec n) :
    (statevectorBackend.applyGate g (QState.mkOf n ψ)).n = n :=
  statevectorBackend_applyGate_n g (QState.mkOf n ψ)

-- Canary 14: measurement branch probabilities are normalized in denotation.
theorem canary_measurement_probs_sum_one (i : ℕ) (p q : Process) (n : ℕ) (ψ : QVec n) :
    (denote_measurement i p q (QState.mkOf n ψ)).prob_zero +
      (denote_measurement i p q (QState.mkOf n ψ)).prob_one = 1 :=
  denote_measurement_prob_sum_eq_one i p q (QState.mkOf n ψ)

-- Canary 15: positive-mass collapse is properly renormalized.
theorem canary_collapse_norm_one_of_raw_pos (i : ℕ) (r : Outcome) (n : ℕ) (ψ : QVec n)
    (hraw : 0 < rawOutcomeProb i r (QState.mkOf n ψ)) :
    norm ((statevectorBackend.collapse i r (QState.mkOf n ψ)).ψ) = 1 := by
  simpa [statevectorBackend] using
    collapseByOutcome_norm_eq_one_of_raw_pos i r (QState.mkOf n ψ) hraw

/-! ## π-calculus correspondence -/

-- Equal-branch measurement recovers deterministic π-calculus COMM
theorem pi_like_comm (i : ℕ) (p : Process) :
    Reduces (MQPar (MQOut i) (MQIn i p p)) p :=
  comm_zero i p p

/-- For equal branches, every direct COMM outcome has the same target process. -/
theorem pi_like_comm_unique (i : ℕ) (p : Process) (b : MeasurementBranch)
    (h : CommReduction i p p b) : b.result = p := by
  cases h <;> rfl

/-! ## ρ-calculus correspondence -/

theorem mq_matches_rho_par_laws (p q r : Process) :
    SC (MQPar p q) (MQPar q p) ∧ SC (MQPar (MQPar p q) r) (MQPar p (MQPar q r)) :=
  ⟨SC.par_comm p q, SC.par_assoc p q r⟩

theorem mq_nu_nil : SC (MQNu MQNil) MQNil := SC.nu_nil

end Mettapedia.Languages.ProcessCalculi.MQCalculus
