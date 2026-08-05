import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.GFlowNetConservation
import Mathlib.Tactic

/-!
# Residual budgets for approximate flow-matching execution

The exact GFlowNet correspondence theorem assumes exact local conservation.
Training and finite-precision execution instead expose a nonzero flow residual.
This file proves a reusable finite-state stability theorem: under a
subnormalized nonnegative forward kernel, the terminal `L¹` discrepancy is at
most the sum of the measured one-step conservation residuals.

The exact-flow result is the zero-residual boundary.  A one-state fixture shows
that dropping subnormalization permits transport to amplify an existing error.

This generalizes the finite-DAG flow equations in:

* Bengio et al., *Flow Network based Generative Models for Non-Iterative
  Diverse Candidate Generation* (2021), arXiv:2106.04399;
* Bengio et al., *GFlowNet Foundations* (2023), arXiv:2111.09266.

Primary source artifact SHA-256:
`b27eab696862ec01c2661905129afce0834c2c54a4aa9d35f323777f7d9db257`.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.VerifierGuidance

universe uN

namespace FlowResidual

variable {Node : Type uN} [Fintype Node]

/-- Push a signed finite mass through one forward kernel. -/
def transport (kernel : Node → Node → ℚ) (mass : Node → ℚ) (child : Node) : ℚ :=
  ∑ parent : Node, mass parent * kernel parent child

/-- Exact finite `L¹` distance between two signed masses. -/
def l1Distance (left right : Node → ℚ) : ℚ :=
  ∑ node : Node, |left node - right node|

/-- The local mismatch between transporting the declared current mass and the
declared mass at the next layer. -/
def conservationResidual
    (kernel : Node → Node → ℚ) (current next : Node → ℚ) (child : Node) : ℚ :=
  transport kernel current child - next child

theorem transport_sub_next_eq
    (kernel : Node → Node → ℚ) (actual current next : Node → ℚ)
    (child : Node) :
    transport kernel actual child - next child =
      (∑ parent : Node,
        (actual parent - current parent) * kernel parent child) +
      conservationResidual kernel current next child := by
  simp only [transport, conservationResidual]
  have hsum :
      (∑ parent : Node,
          (actual parent - current parent) * kernel parent child) =
        (∑ parent : Node, actual parent * kernel parent child) -
          ∑ parent : Node, current parent * kernel parent child := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro parent _hparent
    ring
  rw [hsum]
  ring

/-- Pointwise transport error is bounded by propagated current error plus the
local conservation residual. -/
theorem abs_transport_sub_next_le
    (kernel : Node → Node → ℚ) (actual current next : Node → ℚ)
    (hkernel : ∀ parent child, 0 ≤ kernel parent child)
    (child : Node) :
    |transport kernel actual child - next child| ≤
      (∑ parent : Node,
        |actual parent - current parent| * kernel parent child) +
      |conservationResidual kernel current next child| := by
  rw [transport_sub_next_eq]
  calc
    |(∑ parent : Node,
          (actual parent - current parent) * kernel parent child) +
        conservationResidual kernel current next child|
        ≤
      |∑ parent : Node,
          (actual parent - current parent) * kernel parent child| +
        |conservationResidual kernel current next child| := abs_add_le _ _
    _ ≤
      (∑ parent : Node,
          |(actual parent - current parent) * kernel parent child|) +
        |conservationResidual kernel current next child| :=
      add_le_add_left
        (by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (fun parent : Node =>
                (actual parent - current parent) * kernel parent child)
              Finset.univ))
        _
    _ =
      (∑ parent : Node,
          |actual parent - current parent| * kernel parent child) +
        |conservationResidual kernel current next child| := by
      congr 1
      apply Finset.sum_congr rfl
      intro parent _hparent
      rw [abs_mul, abs_of_nonneg (hkernel parent child)]

/-- One approximate flow-matching layer is `L¹` nonexpansive up to its measured
conservation residual. -/
theorem l1Distance_transport_le
    (kernel : Node → Node → ℚ) (actual current next : Node → ℚ)
    (hkernel : ∀ parent child, 0 ≤ kernel parent child)
    (hrow : ∀ parent, (∑ child : Node, kernel parent child) ≤ 1) :
    l1Distance (transport kernel actual) next ≤
      l1Distance actual current +
        ∑ child : Node, |conservationResidual kernel current next child| := by
  calc
    l1Distance (transport kernel actual) next
        ≤ ∑ child : Node,
            ((∑ parent : Node,
                |actual parent - current parent| * kernel parent child) +
              |conservationResidual kernel current next child|) := by
          apply Finset.sum_le_sum
          intro child _hchild
          exact abs_transport_sub_next_le
            kernel actual current next hkernel child
    _ =
      (∑ parent : Node,
          |actual parent - current parent| *
            ∑ child : Node, kernel parent child) +
        ∑ child : Node,
          |conservationResidual kernel current next child| := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro parent _hparent
      rw [Finset.mul_sum]
    _ ≤
      (∑ parent : Node, |actual parent - current parent|) +
        ∑ child : Node,
          |conservationResidual kernel current next child| := by
      apply add_le_add_left
      apply Finset.sum_le_sum
      intro parent _hparent
      simpa using
        mul_le_mul_of_nonneg_left (hrow parent)
          (abs_nonneg (actual parent - current parent))
    _ =
      l1Distance actual current +
        ∑ child : Node,
          |conservationResidual kernel current next child| := rfl

/-- Actual mass generated by repeatedly applying a time-indexed kernel. -/
noncomputable def forwardTrajectory
    (initial : Node → ℚ) (kernel : ℕ → Node → Node → ℚ) :
    ℕ → Node → ℚ
  | 0, node => initial node
  | step + 1, node =>
      transport (kernel step) (forwardTrajectory initial kernel step) node

/-- Cumulative measured conservation error through a finite number of layers. -/
def cumulativeResidual (budget : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | step + 1 => cumulativeResidual budget step + budget step

@[simp] theorem cumulativeResidual_zero (step : ℕ) :
    cumulativeResidual (fun _ => 0) step = 0 := by
  induction step with
  | zero => rfl
  | succ step ih => simp [cumulativeResidual, ih]

/-- A trace-dischargeable approximate GFlowNet certificate.  No convergence
claim about the learning objective is needed: each premise is a finite
nonnegativity, row-mass, initialization, or residual check. -/
theorem forwardTrajectory_l1Distance_le_cumulativeResidual
    (initial : Node → ℚ) (kernel : ℕ → Node → Node → ℚ)
    (target : ℕ → Node → ℚ) (budget : ℕ → ℚ)
    (hinitial : ∀ node, target 0 node = initial node)
    (hkernel : ∀ step parent child, 0 ≤ kernel step parent child)
    (hrow : ∀ step parent, (∑ child : Node, kernel step parent child) ≤ 1)
    (hresidual :
      ∀ step,
        (∑ child : Node,
          |conservationResidual
            (kernel step) (target step) (target (step + 1)) child|) ≤
          budget step)
    (step : ℕ) :
    l1Distance (forwardTrajectory initial kernel step) (target step) ≤
      cumulativeResidual budget step := by
  induction step with
  | zero =>
      simp [l1Distance, forwardTrajectory, hinitial, cumulativeResidual]
  | succ step ih =>
      calc
        l1Distance
            (forwardTrajectory initial kernel (step + 1))
            (target (step + 1))
            ≤
          l1Distance
              (forwardTrajectory initial kernel step) (target step) +
            ∑ child : Node,
              |conservationResidual
                (kernel step) (target step) (target (step + 1)) child| := by
              exact l1Distance_transport_le
                (kernel step) (forwardTrajectory initial kernel step)
                (target step) (target (step + 1))
                (hkernel step) (hrow step)
        _ ≤ cumulativeResidual budget step + budget step :=
          add_le_add ih (hresidual step)
        _ = cumulativeResidual budget (step + 1) := rfl

/-- Exact conservation is recovered by the zero residual budget. -/
theorem forwardTrajectory_eq_of_zeroResidual
    (initial : Node → ℚ) (kernel : ℕ → Node → Node → ℚ)
    (target : ℕ → Node → ℚ)
    (hinitial : ∀ node, target 0 node = initial node)
    (hkernel : ∀ step parent child, 0 ≤ kernel step parent child)
    (hrow : ∀ step parent, (∑ child : Node, kernel step parent child) ≤ 1)
    (hresidual :
      ∀ step child,
        conservationResidual
          (kernel step) (target step) (target (step + 1)) child = 0)
    (step : ℕ) (node : Node) :
    forwardTrajectory initial kernel step node = target step node := by
  have hbound :=
    forwardTrajectory_l1Distance_le_cumulativeResidual
      initial kernel target (fun _ => 0) hinitial hkernel hrow
      (fun step => by simp [hresidual step]) step
  have hsum :
      l1Distance (forwardTrajectory initial kernel step) (target step) = 0 := by
    exact le_antisymm (by simpa using hbound)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hterm :
      |forwardTrajectory initial kernel step node - target step node| = 0 := by
    apply le_antisymm
    · have hle :
          |forwardTrajectory initial kernel step node - target step node| ≤
            l1Distance
              (forwardTrajectory initial kernel step) (target step) := by
          exact Finset.single_le_sum
            (fun current _ => abs_nonneg
              (forwardTrajectory initial kernel step current -
                target step current))
            (Finset.mem_univ node)
      simpa [hsum] using hle
    · exact abs_nonneg _
  exact sub_eq_zero.mp (abs_eq_zero.mp hterm)

/-- Exact layered networks have normalized positive-flow rows.  To use the
approximate theorem on every row, zero-flow rows need a separate subnormalizing
convention; exact flow matching alone leaves them observationally free. -/
theorem forwardRow_le_one
    [DecidableEq Node] {depth : ℕ} (network : LayeredGFlowNet depth Node)
    (layer : Fin depth) (parent : Node)
    (hzero :
      network.stateFlow layer.castSucc parent = 0 →
        (∑ child : Node, network.forward layer parent child) ≤ 1) :
    (∑ child : Node, network.forward layer parent child) ≤ 1 := by
  by_cases hpositive : 0 < network.stateFlow layer.castSucc parent
  · rw [network.sum_forward_eq_one_of_stateFlow_pos layer parent hpositive]
  · apply hzero
    exact le_antisymm
      (not_lt.mp hpositive)
      (network.stateFlow_nonnegative layer.castSucc parent)

end FlowResidual

/-! ## Sharp finite fixtures -/

namespace FlowResidualFixture

open FlowResidual

def singletonKernel (weight : ℚ) (_parent _child : Fin 1) : ℚ := weight

def singletonMass (value : ℚ) (_node : Fin 1) : ℚ := value

/-- Without row subnormalization, transport can double a pre-existing error
even when the declared target has zero conservation residual. -/
theorem supernormalized_kernel_doubles_error :
    l1Distance
        (transport (singletonKernel 2) (singletonMass 1))
        (singletonMass 0) =
      2 ∧
    l1Distance (singletonMass 1) (singletonMass 0) = 1 ∧
    conservationResidual
        (singletonKernel 2) (singletonMass 0) (singletonMass 0) 0 = 0 := by
  norm_num [l1Distance, transport, singletonKernel, singletonMass,
    conservationResidual, Fin.sum_univ_succ]

/-- A zero residual budget cannot certify a genuinely drifting target. -/
theorem zero_budget_rejects_unit_drift :
    ¬l1Distance (singletonMass 1) (singletonMass 0) ≤ 0 := by
  norm_num [l1Distance, singletonMass, Fin.sum_univ_succ]

#print axioms FlowResidual.l1Distance_transport_le
#print axioms FlowResidual.forwardTrajectory_l1Distance_le_cumulativeResidual
#print axioms FlowResidual.forwardTrajectory_eq_of_zeroResidual
#print axioms FlowResidual.forwardRow_le_one
#print axioms supernormalized_kernel_doubles_error
#print axioms zero_budget_rejects_unit_drift

end FlowResidualFixture

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.VerifierGuidance
