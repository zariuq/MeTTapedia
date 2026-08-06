import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.ProspectiveInterference

/-!
# Exact minimum-interference characterization of prospective repair

In the shared-hidden scalar model, prospective correction changes the old
readout so that the old output is preserved after the hidden state moves.
This file proves that the compensation is not merely one preserving choice:
when the new hidden path is live, it is the unique preserving readout and
therefore the minimum-change preserving repair for every reference readout.

This exact constraint result complements first-order half-space projection.
It does not claim that every predictive-coding implementation computes a
Euclidean projection.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

/-! ## Unique exact preservation -/

/-- With a live new hidden path, exact preservation uniquely determines the
compensating readout. -/
theorem preservingReadout_eq_prospectiveCorrectReadout
    (input oldHidden oldCorrectReadout newHidden candidate : ℝ)
    (input_ne_zero : input ≠ 0) (newHidden_ne_zero : newHidden ≠ 0)
    (preserves :
      sharedHiddenOutput candidate newHidden input =
        sharedHiddenOutput oldCorrectReadout oldHidden input) :
    candidate =
      prospectiveCorrectReadout oldHidden oldCorrectReadout newHidden := by
  have after_cancel_input :
      candidate * newHidden = oldCorrectReadout * oldHidden := by
    apply mul_right_cancel₀ input_ne_zero
    simpa [sharedHiddenOutput, mul_assoc] using preserves
  rw [prospectiveCorrectReadout]
  exact (eq_div_iff newHidden_ne_zero).2 after_cancel_input

/-- Thus the prospective readout is the unique member of the exact
old-output-preserving feasible set. -/
theorem preservingReadout_iff_eq_prospectiveCorrectReadout
    (input oldHidden oldCorrectReadout newHidden candidate : ℝ)
    (input_ne_zero : input ≠ 0) (newHidden_ne_zero : newHidden ≠ 0) :
    sharedHiddenOutput candidate newHidden input =
        sharedHiddenOutput oldCorrectReadout oldHidden input ↔
      candidate =
        prospectiveCorrectReadout oldHidden oldCorrectReadout newHidden := by
  constructor
  · exact preservingReadout_eq_prospectiveCorrectReadout input oldHidden
      oldCorrectReadout newHidden candidate input_ne_zero newHidden_ne_zero
  · intro candidate_eq
    rw [candidate_eq]
    exact prospectiveCorrectReadout_preserves_output input oldHidden
      oldCorrectReadout newHidden newHidden_ne_zero

/-- Uniqueness makes prospective compensation the minimum-change repair from
any proposed readout, not only from the old readout. -/
theorem prospectiveCorrectReadout_minimumChange
    (input oldHidden oldCorrectReadout newHidden proposed candidate : ℝ)
    (input_ne_zero : input ≠ 0) (newHidden_ne_zero : newHidden ≠ 0)
    (candidate_preserves :
      sharedHiddenOutput candidate newHidden input =
        sharedHiddenOutput oldCorrectReadout oldHidden input) :
    |prospectiveCorrectReadout oldHidden oldCorrectReadout newHidden -
        proposed| ≤ |candidate - proposed| := by
  have candidate_eq := preservingReadout_eq_prospectiveCorrectReadout input
    oldHidden oldCorrectReadout newHidden candidate input_ne_zero
    newHidden_ne_zero candidate_preserves
  rw [candidate_eq]

/-- In particular, prospective compensation is the closest exact-preserving
readout to the unchanged BP readout. -/
theorem prospectiveCorrectReadout_minimumChange_from_bp
    (input oldHidden oldCorrectReadout newHidden candidate : ℝ)
    (input_ne_zero : input ≠ 0) (newHidden_ne_zero : newHidden ≠ 0)
    (candidate_preserves :
      sharedHiddenOutput candidate newHidden input =
        sharedHiddenOutput oldCorrectReadout oldHidden input) :
    |prospectiveCorrectReadout oldHidden oldCorrectReadout newHidden -
        oldCorrectReadout| ≤ |candidate - oldCorrectReadout| :=
  prospectiveCorrectReadout_minimumChange input oldHidden oldCorrectReadout
    newHidden oldCorrectReadout candidate input_ne_zero newHidden_ne_zero
    candidate_preserves

/-! ## Positive and negative boundaries -/

/-- If the hidden state does not move, the prospective correction is exactly
the unchanged readout; there is no intervention to prefer. -/
theorem prospectiveCorrectReadout_eq_self_of_hidden_unchanged
    (hidden readout : ℝ) (hidden_ne_zero : hidden ≠ 0) :
    prospectiveCorrectReadout hidden readout hidden = readout := by
  rw [prospectiveCorrectReadout]
  exact mul_div_cancel_right₀ readout hidden_ne_zero

/-- Positive crown: the half-target example has a unique old-output-preserving
readout, namely two, while the unchanged BP readout does not preserve the old
output. -/
theorem halfTarget_unique_minimumInterference :
    (∀ candidate : ℝ,
      sharedHiddenOutput candidate (bpRepairedHidden 1 1 (1 / 2)) 1 = 1 ↔
        candidate = 2) ∧
      sharedHiddenOutput 1 (bpRepairedHidden 1 1 (1 / 2)) 1 ≠ 1 := by
  constructor
  · intro candidate
    have unique := preservingReadout_iff_eq_prospectiveCorrectReadout
      1 1 1 (bpRepairedHidden 1 1 (1 / 2)) candidate
      (by norm_num) (by norm_num [bpRepairedHidden])
    simpa [sharedHiddenOutput, prospectiveCorrectReadout, bpRepairedHidden]
      using unique
  · norm_num [sharedHiddenOutput, bpRepairedHidden]

/-- Negative boundary: without a live input path every readout preserves the
zero output, so uniqueness and a distinguished minimum-interference repair
are impossible. -/
theorem zeroInput_preservation_not_unique :
    sharedHiddenOutput 0 1 0 = sharedHiddenOutput 1 1 0 ∧ (0 : ℝ) ≠ 1 := by
  norm_num [sharedHiddenOutput]

#print axioms preservingReadout_eq_prospectiveCorrectReadout
#print axioms preservingReadout_iff_eq_prospectiveCorrectReadout
#print axioms prospectiveCorrectReadout_minimumChange
#print axioms prospectiveCorrectReadout_eq_self_of_hidden_unchanged
#print axioms halfTarget_unique_minimumInterference
#print axioms zeroInput_preservation_not_unique

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
