import Mathlib

/-!
# SwitchHead's exact symbolic cost boundary

Csordás et al., *SwitchHead: Accelerating Transformers with
Mixture-of-Experts Attention* (arXiv:2312.07987), Appendix A.2,
Equations (11)--(13), give symbolic multiply-accumulate and training-storage
counts for Transformer-XL attention and SwitchHead.

This file recovers those integer cost models without turning their hardware
or language-model measurements into theorems.  It also makes the decisive
boundary explicit: at fixed head count and width, any positive number of
SwitchHead experts costs strictly more MACs than the dense projection model.
The reported saving is therefore licensed only when the architecture reduces
the number of attention matrices (or otherwise changes dimensions); expert
routing alone is not a free speedup.

The storage equation is the source's smart-kernel model.  It proves symbolic
independence from expert count, not that a particular runtime implements the
required fusion or attains the declared memory usage.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace SwitchHeadCostBoundary

/-- Equation (11): declared MAC count for one Transformer-XL attention layer
and one sequence. -/
def transformerXLMACs
    (heads sequence context modelWidth headWidth : ℕ) : ℕ :=
  heads *
    (4 * sequence * headWidth * modelWidth +
      2 * context * sequence ^ 2 * headWidth +
      2 * context * sequence * headWidth * modelWidth)

/-- Equation (13): declared MAC count for SwitchHead with value/output
experts and shared key/query projections. -/
def switchHeadMACs
    (heads activeExperts sequence context modelWidth headWidth : ℕ) : ℕ :=
  heads *
    (2 * sequence * headWidth * modelWidth +
      2 * sequence * activeExperts * headWidth * (modelWidth + 1) +
      2 * context * sequence ^ 2 * headWidth +
      2 * context * sequence * headWidth * modelWidth)

/-- Equation (12): the paper's smart-kernel training-storage model.  Expert
count is intentionally absent because selected expert intermediates are
assumed to be fused rather than materialized separately. -/
def declaredTrainingStorage
    (heads sequence context headWidth : ℕ) : ℕ :=
  heads *
    (4 * sequence * headWidth +
      2 * context * sequence ^ 2 +
      2 * context * sequence * headWidth)

/-- With `experts + 1` active experts and otherwise identical geometry,
SwitchHead has an exact positive projection/mixing overhead relative to the
dense cost model. -/
theorem switchHeadMACs_succExperts_eq_transformerXL_add_overhead
    (heads experts sequence context modelWidth headWidth : ℕ) :
    switchHeadMACs heads (experts + 1) sequence context modelWidth headWidth =
      transformerXLMACs heads sequence context modelWidth headWidth +
        heads *
          (2 * sequence * headWidth *
            (experts * modelWidth + experts + 1)) := by
  simp [switchHeadMACs, transformerXLMACs]
  ring

/-- Consequently, expert routing cannot reduce the declared MAC count at
fixed head count and dimensions.  At least one positive dimension and one
head are required for a strict inequality. -/
theorem transformerXLMACs_lt_switchHeadMACs_sameGeometry
    (heads experts sequence context modelWidth headWidth : ℕ)
    (heads_pos : 0 < heads)
    (sequence_pos : 0 < sequence)
    (headWidth_pos : 0 < headWidth) :
    transformerXLMACs heads sequence context modelWidth headWidth <
      switchHeadMACs heads (experts + 1) sequence context modelWidth
        headWidth := by
  rw [switchHeadMACs_succExperts_eq_transformerXL_add_overhead]
  apply Nat.lt_add_of_pos_right
  positivity

/-- Under the source's fused-storage model, fewer heads are exactly
equivalent to lower storage whenever a nonempty sequence is present. -/
theorem declaredTrainingStorage_lt_iff_heads_lt
    {leftHeads rightHeads sequence context headWidth : ℕ}
    (sequence_pos : 0 < sequence)
    (headWidth_pos : 0 < headWidth) :
    declaredTrainingStorage leftHeads sequence context headWidth <
        declaredTrainingStorage rightHeads sequence context headWidth ↔
      leftHeads < rightHeads := by
  unfold declaredTrainingStorage
  apply Nat.mul_lt_mul_right
  positivity

/-- A parameter choice with fewer SwitchHead heads has four times fewer
declared attention-layer storage cells and substantially fewer MACs.  This is
an arithmetic fixture for the symbolic model, not a wall-clock claim. -/
theorem fewer_heads_can_reduce_declared_cost :
    transformerXLMACs 8 10 2 16 4 = 53760 ∧
      switchHeadMACs 2 2 10 2 16 4 = 16320 ∧
      declaredTrainingStorage 8 10 2 4 = 5760 ∧
      declaredTrainingStorage 2 10 2 4 = 1440 ∧
      4 * declaredTrainingStorage 2 10 2 4 =
        declaredTrainingStorage 8 10 2 4 := by
  norm_num [transformerXLMACs, switchHeadMACs,
    declaredTrainingStorage]

/-- Holding all geometry fixed reverses the preceding comparison: two active
experts add routing/projection work and make the declared MAC count larger. -/
theorem same_heads_experts_increase_declared_cost :
    transformerXLMACs 8 10 2 16 4 = 53760 ∧
      switchHeadMACs 8 2 10 2 16 4 = 65280 ∧
      transformerXLMACs 8 10 2 16 4 <
        switchHeadMACs 8 2 10 2 16 4 := by
  norm_num [transformerXLMACs, switchHeadMACs]

#print axioms switchHeadMACs_succExperts_eq_transformerXL_add_overhead
#print axioms transformerXLMACs_lt_switchHeadMACs_sameGeometry
#print axioms declaredTrainingStorage_lt_iff_heads_lt
#print axioms fewer_heads_can_reduce_declared_cost
#print axioms same_heads_experts_increase_declared_cost

end SwitchHeadCostBoundary

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
