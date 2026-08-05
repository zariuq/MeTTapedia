import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Discrete Lagrangian boundary residuals

The first variation of a trajectory action separates into interior
Euler-residual terms and endpoint momentum terms.  This finite theorem is an
exact summation-by-parts analogue of the boundary calculation used by
Lagrangian Equilibrium Propagation.

It makes the boundary-condition distinction explicit:

* zero interior residuals and variations vanishing at both endpoints give a
  stationary action;
* fixing only the initial endpoint leaves the final momentum residual;
* interior equations alone do not imply stationarity for arbitrary endpoint
  variations.

No continuous differentiability, ODE solver, or Hamiltonian equivalence is
claimed here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace LagrangianBoundary

open scoped BigOperators

/-- Velocity contribution to a discrete first variation over `steps + 1`
edges and `steps + 2` nodes. -/
def velocityVariation
    (steps : ℕ) (momentum variation : ℕ → ℝ) : ℝ :=
  ∑ time ∈ Finset.range (steps + 1),
    momentum time * (variation (time + 1) - variation time)

/-- Interior state contribution, indexed by the `steps` internal nodes. -/
def interiorVariation
    (steps : ℕ) (stateForce variation : ℕ → ℝ) : ℝ :=
  ∑ time ∈ Finset.range steps,
    stateForce time * variation (time + 1)

/-- Discrete action first variation. -/
def firstVariation
    (steps : ℕ)
    (momentum stateForce variation : ℕ → ℝ) : ℝ :=
  velocityVariation steps momentum variation +
    interiorVariation steps stateForce variation

/-- Residual of the discrete interior Euler equation at one internal node. -/
def eulerResidual
    (momentum stateForce : ℕ → ℝ) (time : ℕ) : ℝ :=
  stateForce time + momentum time - momentum (time + 1)

/-- Endpoint contribution left by discrete summation by parts. -/
def boundaryResidual
    (steps : ℕ) (momentum variation : ℕ → ℝ) : ℝ :=
  momentum steps * variation (steps + 1) -
    momentum 0 * variation 0

/-- Exact finite summation by parts for the velocity contribution. -/
theorem velocityVariation_eq_boundary_add_interior
    (steps : ℕ) (momentum variation : ℕ → ℝ) :
    velocityVariation steps momentum variation =
      boundaryResidual steps momentum variation +
        ∑ time ∈ Finset.range steps,
          (momentum time - momentum (time + 1)) *
            variation (time + 1) := by
  induction steps with
  | zero =>
      simp [velocityVariation, boundaryResidual]
      ring
  | succ steps inductionHypothesis =>
      rw [velocityVariation, Finset.sum_range_succ,
        show steps + 1 + 1 = (steps + 1) + 1 by omega]
      change
        velocityVariation steps momentum variation +
            momentum (steps + 1) *
              (variation (steps + 1 + 1) - variation (steps + 1)) =
          boundaryResidual (steps + 1) momentum variation +
            ∑ time ∈ Finset.range (steps + 1),
              (momentum time - momentum (time + 1)) *
                variation (time + 1)
      rw [inductionHypothesis, Finset.sum_range_succ]
      simp only [boundaryResidual]
      ring

/-- **Boundary decomposition.**  The first variation is exactly the endpoint
residual plus the pairing of every interior variation with its Euler
residual. -/
theorem firstVariation_eq_boundary_add_residuals
    (steps : ℕ)
    (momentum stateForce variation : ℕ → ℝ) :
    firstVariation steps momentum stateForce variation =
      boundaryResidual steps momentum variation +
        ∑ time ∈ Finset.range steps,
          eulerResidual momentum stateForce time *
            variation (time + 1) := by
  rw [firstVariation, velocityVariation_eq_boundary_add_interior]
  simp only [interiorVariation, eulerResidual]
  rw [add_assoc]
  apply congrArg (boundaryResidual steps momentum variation + ·)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro time _
  ring

/-- If every interior Euler residual vanishes, the entire first variation is
the boundary residual. -/
theorem firstVariation_eq_boundary_of_euler
    {steps : ℕ}
    {momentum stateForce variation : ℕ → ℝ}
    (euler : ∀ time, eulerResidual momentum stateForce time = 0) :
    firstVariation steps momentum stateForce variation =
      boundaryResidual steps momentum variation := by
  rw [firstVariation_eq_boundary_add_residuals]
  simp [euler]

/-- Boundary-vanishing variations turn an Euler solution into a stationary
trajectory. -/
theorem stationary_of_euler_and_vanishing_endpoints
    {steps : ℕ}
    {momentum stateForce variation : ℕ → ℝ}
    (euler : ∀ time, eulerResidual momentum stateForce time = 0)
    (initial : variation 0 = 0)
    (final : variation (steps + 1) = 0) :
    firstVariation steps momentum stateForce variation = 0 := by
  rw [firstVariation_eq_boundary_of_euler euler]
  simp [boundaryResidual, initial, final]

/-- With only the initial variation fixed, the final momentum term remains
exactly. -/
theorem causal_initial_condition_leaves_final_residual
    {steps : ℕ}
    {momentum stateForce variation : ℕ → ℝ}
    (euler : ∀ time, eulerResidual momentum stateForce time = 0)
    (initial : variation 0 = 0) :
    firstVariation steps momentum stateForce variation =
      momentum steps * variation (steps + 1) := by
  rw [firstVariation_eq_boundary_of_euler euler]
  simp [boundaryResidual, initial]

/-! ## Positive and negative fixtures -/

def constantMomentum (_ : ℕ) : ℝ := 2
def zeroStateForce (_ : ℕ) : ℝ := 0
def vanishingVariation (time : ℕ) : ℝ :=
  if time = 1 then 3 else 0

theorem constantMomentum_euler :
    ∀ time, eulerResidual constantMomentum zeroStateForce time = 0 := by
  intro time
  simp [eulerResidual, constantMomentum, zeroStateForce]

theorem two_endpoint_vanishing :
    firstVariation 2 constantMomentum zeroStateForce vanishingVariation = 0 := by
  apply stationary_of_euler_and_vanishing_endpoints constantMomentum_euler
  · simp [vanishingVariation]
  · simp [vanishingVariation]

def finalOnlyVariation (time : ℕ) : ℝ :=
  if time = 1 then 3 else 0

/-- Even with no interior nodes and hence no interior obstruction, a nonzero
final variation leaves a nonzero boundary residual. -/
theorem euler_interior_alone_does_not_imply_stationarity :
    firstVariation 0 constantMomentum zeroStateForce finalOnlyVariation = 6 := by
  norm_num [firstVariation, velocityVariation, interiorVariation,
    constantMomentum, finalOnlyVariation]

theorem causal_fixture_has_final_residual :
    firstVariation 0 constantMomentum zeroStateForce finalOnlyVariation =
      constantMomentum 0 * finalOnlyVariation 1 := by
  apply causal_initial_condition_leaves_final_residual
  · exact constantMomentum_euler
  · simp [finalOnlyVariation]

#print axioms velocityVariation_eq_boundary_add_interior
#print axioms firstVariation_eq_boundary_add_residuals
#print axioms stationary_of_euler_and_vanishing_endpoints
#print axioms causal_initial_condition_leaves_final_residual
#print axioms euler_interior_alone_does_not_imply_stationarity

end LagrangianBoundary

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
