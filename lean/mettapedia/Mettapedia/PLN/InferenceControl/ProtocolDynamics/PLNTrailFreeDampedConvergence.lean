import Mettapedia.PLN.InferenceControl.ProtocolDynamics.PLNTrailFreeDynamicsCounterexample

/-!
# Damped SP/SPN Dynamics with Fresh-BinaryEvidence Convergence

This module adds a positive Chapter-9 counterpart to the trail-free non-convergence
counterexample:

- `spStep`: unstable trail-free update (`toggle`),
- `spnStep`: fresh-evidence injection update,
- `dampedSPNStep`: damped blend using a freshness gate,
- constructive convergence theorem on finite state (`Bool`) under eventual fresh evidence.
-/

namespace Mettapedia.PLN.InferenceControl.ProtocolDynamics.PLNTrailFreeDampedConvergence

open Mettapedia.PLN.InferenceControl.ProtocolDynamics.PLNTrailFreeDynamicsCounterexample

abbrev TVState := Bool

/-- SP operator: unstable trail-free update. -/
def spStep : TVState → TVState :=
  trailFreeStep

/-- SPN operator: overwrite with the fresh-evidence state. -/
def spnStep (freshState : TVState) (_x : TVState) : TVState :=
  freshState

/-- Damped SP/SPN blend:
- if fresh evidence is present, inject it (SPN),
- otherwise apply the trail-free SP step. -/
def dampedSPNStep (fresh : Bool) (freshState : TVState) (x : TVState) : TVState :=
  if fresh then spnStep freshState x else spStep x

/-- Orbit under the damped SP/SPN dynamics with freshness schedule `freshAt`. -/
def dampedOrbit (freshAt : Nat → Bool) (freshState : TVState) (x0 : TVState) : Nat → TVState
  | 0 => x0
  | n + 1 => dampedSPNStep (freshAt n) freshState (dampedOrbit freshAt freshState x0 n)

/-- Inconsistency metric against the fresh-evidence state. -/
def inconsistency (freshState x : TVState) : Nat :=
  if x = freshState then 0 else 1

theorem inconsistency_eq_zero_iff (freshState x : TVState) :
    inconsistency freshState x = 0 ↔ x = freshState := by
  unfold inconsistency
  by_cases h : x = freshState <;> simp [h]

theorem dampedSPNStep_eq_freshState_of_fresh
    (freshState x : TVState) :
    dampedSPNStep true freshState x = freshState := by
  simp [dampedSPNStep, spnStep]

/-- If fresh evidence is available from step `N` onward, then all states from
time `N+1` onward equal the fresh-evidence state. -/
theorem dampedOrbit_eq_freshState_of_eventual_fresh
    (freshAt : Nat → Bool) (freshState x0 : TVState)
    (N : Nat) (hFresh : ∀ n, N ≤ n → freshAt n = true) :
    ∀ n, N + 1 ≤ n → dampedOrbit freshAt freshState x0 n = freshState := by
  intro n hn
  rcases Nat.exists_eq_add_of_le hn with ⟨k, hk⟩
  subst hk
  cases k with
  | zero =>
      -- n = N + 1
      simp [dampedOrbit, dampedSPNStep, spnStep, hFresh N (Nat.le_refl N)]
  | succ k =>
      -- n = N + 1 + (k + 1), so the freshness gate at index `N + 1 + k` fires.
      have hNk : N ≤ N + 1 + k := by
        simp [Nat.add_assoc]
      have hFreshNow : freshAt (N + 1 + k) = true := hFresh (N + 1 + k) hNk
      simp [dampedOrbit, dampedSPNStep, spnStep, hFreshNow]

/-- Eventual-constant notion for damped SP/SPN orbits. -/
def EventuallyConstantDamped (freshAt : Nat → Bool) (freshState x0 : TVState) : Prop :=
  ∃ M y, ∀ n, M ≤ n → dampedOrbit freshAt freshState x0 n = y

/-- Constructive positive convergence theorem:
eventual fresh evidence implies eventual stabilization. -/
theorem damped_sp_spn_eventually_constant_of_eventual_fresh
    (freshAt : Nat → Bool) (freshState x0 : TVState)
    (hFreshEventually : ∃ N, ∀ n, N ≤ n → freshAt n = true) :
    EventuallyConstantDamped freshAt freshState x0 := by
  rcases hFreshEventually with ⟨N, hFresh⟩
  refine ⟨N + 1, freshState, ?_⟩
  intro n hn
  exact dampedOrbit_eq_freshState_of_eventual_fresh freshAt freshState x0 N hFresh n hn

/-- Inconsistency drops to zero after the eventual-freshness point. -/
theorem inconsistency_eventually_zero_of_eventual_fresh
    (freshAt : Nat → Bool) (freshState x0 : TVState)
    (hFreshEventually : ∃ N, ∀ n, N ≤ n → freshAt n = true) :
    ∃ M, ∀ n, M ≤ n → inconsistency freshState (dampedOrbit freshAt freshState x0 n) = 0 := by
  rcases hFreshEventually with ⟨N, hFresh⟩
  refine ⟨N + 1, ?_⟩
  intro n hn
  have hEq :
      dampedOrbit freshAt freshState x0 n = freshState :=
    dampedOrbit_eq_freshState_of_eventual_fresh freshAt freshState x0 N hFresh n hn
  exact (inconsistency_eq_zero_iff freshState (dampedOrbit freshAt freshState x0 n)).2 hEq

/-! ## Bounded-gap fairness schedules with constructive reset bounds -/

/-- Freshness fairness: every window of length `B` contains a fresh-evidence tick. -/
def BoundedGapFresh (freshAt : Nat → Bool) (B : Nat) : Prop :=
  ∀ n, ∃ m, n ≤ m ∧ m ≤ n + B ∧ freshAt m = true

/-- Eventual bounded-gap freshness. -/
def EventuallyBoundedGapFresh (freshAt : Nat → Bool) (B : Nat) : Prop :=
  ∃ N, ∀ n, N ≤ n → ∃ m, n ≤ m ∧ m ≤ n + B ∧ freshAt m = true

/-- Constructive bound:
under bounded-gap freshness, within at most `B+1` steps from any time `n`,
the damped orbit hits inconsistency `0` (a fresh reset state). -/
theorem inconsistency_zero_within_bound_of_boundedGapFresh
    (freshAt : Nat → Bool) (freshState x0 : TVState) (B : Nat)
    (hGap : BoundedGapFresh freshAt B) :
    ∀ n, ∃ m, n + 1 ≤ m ∧ m ≤ n + B + 1
      ∧ inconsistency freshState (dampedOrbit freshAt freshState x0 m) = 0 := by
  intro n
  rcases hGap n with ⟨k, hnk, hknB, hkFresh⟩
  refine ⟨k + 1, Nat.succ_le_succ hnk, ?_, ?_⟩
  · exact Nat.succ_le_succ hknB
  · have hEq : dampedOrbit freshAt freshState x0 (k + 1) = freshState := by
      simp [dampedOrbit, dampedSPNStep, spnStep, hkFresh]
    exact (inconsistency_eq_zero_iff freshState (dampedOrbit freshAt freshState x0 (k + 1))).2 hEq

/-- Eventual bounded-gap variant of the constructive reset bound. -/
theorem inconsistency_zero_within_bound_of_eventually_boundedGapFresh
    (freshAt : Nat → Bool) (freshState x0 : TVState) (B : Nat)
    (hGap : EventuallyBoundedGapFresh freshAt B) :
    ∃ N, ∀ n, N ≤ n → ∃ m, n + 1 ≤ m ∧ m ≤ n + B + 1
      ∧ inconsistency freshState (dampedOrbit freshAt freshState x0 m) = 0 := by
  rcases hGap with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rcases hN n hn with ⟨k, hnk, hknB, hkFresh⟩
  refine ⟨k + 1, Nat.succ_le_succ hnk, Nat.succ_le_succ hknB, ?_⟩
  have hEq : dampedOrbit freshAt freshState x0 (k + 1) = freshState := by
    simp [dampedOrbit, dampedSPNStep, spnStep, hkFresh]
  exact (inconsistency_eq_zero_iff freshState (dampedOrbit freshAt freshState x0 (k + 1))).2 hEq

/-- No-freshness schedule recovers the original trail-free dynamics. -/
def noFresh : Nat → Bool := fun _ => false

theorem dampedOrbit_noFresh_eq_orbit (freshState x0 : TVState) :
    ∀ n, dampedOrbit noFresh freshState x0 n = orbit x0 n
  | 0 => rfl
  | n + 1 => by
      simp [dampedOrbit, noFresh, dampedSPNStep, spStep, orbit, dampedOrbit_noFresh_eq_orbit]

/-- Negative counterpart: without fresh evidence, damped dynamics does not stabilize. -/
theorem dampedOrbit_noFresh_not_eventually_constant
    (freshState x0 : TVState) :
    ¬ EventuallyConstantDamped noFresh freshState x0 := by
  intro h
  rcases h with ⟨M, y, hM⟩
  have hOld :
      EventuallyConstant x0 := by
    refine ⟨M, y, ?_⟩
    intro n hn
    have hNew := hM n hn
    simpa [dampedOrbit_noFresh_eq_orbit] using hNew
  exact orbit_not_eventually_constant x0 hOld

end Mettapedia.PLN.InferenceControl.ProtocolDynamics.PLNTrailFreeDampedConvergence
