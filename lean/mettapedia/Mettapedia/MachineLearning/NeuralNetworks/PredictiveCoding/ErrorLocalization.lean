import Mathlib.Tactic

/-!
# Predictive-coding error localization

This file contains the pure local backward-relaxation theorem: after `t`
applied local relaxation steps, nodes farther than `t` from the output still
have zero error, plus the tight depth-3 coupled-rule fixture.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Local backward error propagation -/

/-- Error values on the nodes of a scalar chain. -/
abbrev ErrorState (d : ℕ) := Fin (d + 1) → ℝ

/-- Node distance from the output node. -/
def distanceFromOutput {d : ℕ} (i : Fin (d + 1)) : ℕ :=
  d - i.val

/-- A synchronous local backward relaxation rule. Node `0` is the clamped input
when the chain has positive length. -/
structure LocalBackwardRelaxation (d : ℕ) where
  step : ErrorState d → ErrorState d
  output_fixed : ∀ ε, step ε (Fin.last d) = ε (Fin.last d)
  input_clamped : ∀ ε, 0 < d → step ε 0 = 0
  local_zero : ∀ ε (i : Fin d),
    ε i.castSucc = 0 → ε i.succ = 0 → step ε i.castSucc = 0

/-- P3 crown: after `t` applied local relaxation steps, nodes farther than
`t` from the output still have zero error. -/
theorem error_localization {d : ℕ}
    (R : LocalBackwardRelaxation d) (ε₀ : ErrorState d)
    (hInit : ∀ i : Fin (d + 1), i ≠ Fin.last d → ε₀ i = 0) :
    ∀ t (i : Fin (d + 1)), distanceFromOutput i > t →
      (Nat.iterate R.step t ε₀) i = 0 := by
  intro t
  induction t with
  | zero =>
      intro i hdist
      apply hInit
      intro hlast
      have hv := congrArg Fin.val hlast
      simp [distanceFromOutput] at hdist hv
      omega
  | succ t ih =>
      intro i hdist
      by_cases hlast : i.val = d
      · simp [distanceFromOutput, hlast] at hdist
      · have hi_lt_d : i.val < d := by omega
        let k : Fin d := ⟨i.val, hi_lt_d⟩
        have hk_cast : k.castSucc = i := by
          ext
          simp [k]
        have hself : (Nat.iterate R.step t ε₀) k.castSucc = 0 := by
          apply ih
          simp [distanceFromOutput, k] at hdist ⊢
          omega
        have hsucc : (Nat.iterate R.step t ε₀) k.succ = 0 := by
          apply ih
          simp [distanceFromOutput, k] at hdist ⊢
          omega
        have hstep := R.local_zero (Nat.iterate R.step t ε₀) k hself hsucc
        rw [Function.iterate_succ_apply']
        simpa [hk_cast] using hstep

/-- Node `1` receives no error before its distance-from-output horizon. -/
theorem error_localization_node_one {d : ℕ}
    (R : LocalBackwardRelaxation d) (ε₀ : ErrorState d)
    (hInit : ∀ i : Fin (d + 1), i ≠ Fin.last d → ε₀ i = 0)
    (hd : 1 < d) {t : ℕ} (ht : t < d - 1) :
    (Nat.iterate R.step t ε₀) (⟨1, by omega⟩ : Fin (d + 1)) = 0 := by
  apply error_localization R ε₀ hInit
  simp [distanceFromOutput]
  omega

/-- A concrete coupled relaxation rule: each non-input, non-output node copies
its successor's previous error multiplied by a coupling. -/
noncomputable def coupledBackwardStep {d : ℕ} (coupling : ℝ)
    (ε : ErrorState d) : ErrorState d :=
  fun i =>
    if hlast : i.val = d then ε i
    else if h0 : i.val = 0 then 0
    else coupling * ε ⟨i.val + 1, by omega⟩

/-- The concrete coupled rule as a local relaxation instance. -/
noncomputable def coupledBackwardRelaxation (d : ℕ) (coupling : ℝ) :
    LocalBackwardRelaxation d where
  step := coupledBackwardStep coupling
  output_fixed := by
    intro ε
    unfold coupledBackwardStep
    simp
  input_clamped := by
    intro ε hd
    unfold coupledBackwardStep
    split
    · rename_i hlast
      simp at hlast
      omega
    · split
      · rfl
      · rename_i h0
        exfalso
        exact h0 rfl
  local_zero := by
    intro ε i _hself hsucc
    unfold coupledBackwardStep
    split
    · rename_i hlast
      have hv : i.val = d := by
        simpa using hlast
      omega
    · split
      · rfl
      · have hsucc_node :
            (⟨i.castSucc.val + 1, by omega⟩ : Fin (d + 1)) = i.succ := by
          ext
          simp
        rw [hsucc_node, hsucc]
        ring

/-- A depth-3 fixture with only the output error initially nonzero. -/
noncomputable def outputOnlyError3 : ErrorState 3 :=
  fun i => if i.val = 3 then 1 else 0

theorem outputOnlyError3_initial :
    ∀ i : Fin 4, i ≠ Fin.last 3 → outputOnlyError3 i = 0 := by
  intro i hne
  unfold outputOnlyError3
  simp
  intro hval
  apply hne
  ext
  simp [hval]

theorem coupled_node_one_zero_before_horizon_d3 :
    (Nat.iterate (coupledBackwardRelaxation 3 2).step 1 outputOnlyError3)
        (⟨1, by omega⟩ : Fin 4) = 0 := by
  exact error_localization_node_one (coupledBackwardRelaxation 3 2) outputOnlyError3
    outputOnlyError3_initial (by norm_num) (t := 1) (by norm_num)

theorem coupled_error_arrives_at_node_one_d3 :
    (Nat.iterate (coupledBackwardRelaxation 3 2).step 2 outputOnlyError3)
        (⟨1, by omega⟩ : Fin 4) = 4 := by
  norm_num [coupledBackwardRelaxation, coupledBackwardStep, outputOnlyError3]

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
