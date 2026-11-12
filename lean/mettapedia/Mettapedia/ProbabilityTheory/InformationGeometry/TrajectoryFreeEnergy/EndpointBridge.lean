import Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.Basic
import Mettapedia.InformationTheory.FiniteRecovery
import Mathlib.Data.ENNReal.Operations

/-!
# Finite endpoint bridges and their dynamical remainder

Complete trajectories have declared initial and terminal observations.
Feasible laws preserve the initial law, attain the target terminal law and
are supported by the reference. Bridge and residual costs use extended
nonnegative reals: an empty feasible family has infinite cost.

The residual is independently defined as divergence from reference-conditional
recovery. The existing finite recovery theorem yields the endpoint-plus-
residual decomposition, including infeasible bridges. This is the finite
setting of Proposition 3.1 in Goertzel, *Schrödinger Bridges for Predictive
Coding and Active Inference* (2026).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.EndpointBridge

open scoped BigOperators ENNReal
open Mettapedia.InformationTheory Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.BayesianInference

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]

theorem endpoint_decomposition (reference law : Prob Ω) (endpoint : Ω → E) (target : Prob E)
    (supported : SupportedBy law reference.1) (terminal : Prob.coarsen law endpoint = target) :
    klSum law.1 reference.1 = klSum target.1 (Prob.coarsen reference endpoint).1 +
      klSum law.1 (FiniteRecovery.recover reference endpoint target).1 := by
  have loss := FiniteRecovery.klLoss_eq_recovery_divergence law reference endpoint supported
  unfold FiniteRecovery.klLoss at loss
  rw [terminal] at loss
  linarith

theorem endpoint_remainder_nonnegative (reference law : Prob Ω) (endpoint : Ω → E) (target : Prob E)
    (supported : SupportedBy law reference.1) (terminal : Prob.coarsen law endpoint = target) :
    0 ≤ klSum law.1 (FiniteRecovery.recover reference endpoint target).1 := by
  have nonnegative := FiniteRecovery.klLoss_nonneg law reference endpoint supported
  rw [FiniteRecovery.klLoss_eq_recovery_divergence law reference endpoint supported, terminal] at nonnegative
  exact nonnegative

theorem recovery_supported (reference : Prob Ω) (endpoint : Ω → E) (target : Prob E)
    (targetSupported : SupportedBy target (Prob.coarsen reference endpoint).1) :
    SupportedBy (FiniteRecovery.recover reference endpoint target) reference.1 := by
  intro history positive
  by_contra absent
  have zero : reference.1 history = 0 := le_antisymm (le_of_not_gt absent) (reference.2.1 history)
  rw [FiniteRecovery.recover_apply reference endpoint target targetSupported, zero, zero_mul, zero_div] at positive
  exact (lt_irrefl _ positive)

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Feasible (reference : Prob Ω) (start : Ω → I) (initial : Prob I)
    (endpoint : Ω → E) (target : Prob E) :=
  {law : Prob Ω // SupportedBy law reference.1 ∧
    Prob.coarsen law start = initial ∧ Prob.coarsen law endpoint = target}

def cost (reference : Prob Ω) (start : Ω → I) (initial : Prob I) (endpoint : Ω → E) (target : Prob E) : ℝ≥0∞ :=
  ⨅ law : Feasible reference start initial endpoint target, ENNReal.ofReal (klSum law.1.1 reference.1)

def residual (reference : Prob Ω) (start : Ω → I) (initial : Prob I) (endpoint : Ω → E) (target : Prob E) : ℝ≥0∞ :=
  ⨅ law : Feasible reference start initial endpoint target,
    ENNReal.ofReal (klSum law.1.1 (FiniteRecovery.recover reference endpoint target).1)

theorem cost_eq_endpoint_add_residual (reference : Prob Ω) (start : Ω → I) (initial : Prob I)
    (endpoint : Ω → E) (target : Prob E)
    (targetSupported : SupportedBy target (Prob.coarsen reference endpoint).1) :
    cost reference start initial endpoint target =
      ENNReal.ofReal (klSum target.1 (Prob.coarsen reference endpoint).1) +
        residual reference start initial endpoint target := by
  have marginalNonnegative : 0 ≤ klSum target.1 (Prob.coarsen reference endpoint).1 :=
    klSumOn_nonneg Finset.univ _ _ (fun x _ => target.2.1 x)
      (fun x _ => (Prob.coarsen reference endpoint).2.1 x) (fun x _ => targetSupported x)
      (by rw [target.2.2, (Prob.coarsen reference endpoint).2.2])
  have pointwise (law : Feasible reference start initial endpoint target) :
      ENNReal.ofReal (klSum law.1.1 reference.1) =
        ENNReal.ofReal (klSum target.1 (Prob.coarsen reference endpoint).1) +
          ENNReal.ofReal (klSum law.1.1 (FiniteRecovery.recover reference endpoint target).1) := by
    rw [endpoint_decomposition reference law.1 endpoint target law.2.1 law.2.2.2]
    exact ENNReal.ofReal_add marginalNonnegative
      (endpoint_remainder_nonnegative reference law.1 endpoint target law.2.1 law.2.2.2)
  unfold cost residual
  simp_rw [pointwise]
  exact ENNReal.add_iInf.symm

theorem cost_infinite_of_infeasible (reference : Prob Ω) (start : Ω → I) (initial : Prob I)
    (endpoint : Ω → E) (target : Prob E) (impossible : IsEmpty (Feasible reference start initial endpoint target)) :
    cost reference start initial endpoint target = ⊤ := by
  let := impossible
  simp [cost]

theorem residual_infinite_of_infeasible (reference : Prob Ω) (start : Ω → I) (initial : Prob I)
    (endpoint : Ω → E) (target : Prob E) (impossible : IsEmpty (Feasible reference start initial endpoint target)) :
    residual reference start initial endpoint target = ⊤ := by
  let := impossible
  simp [residual]

theorem residual_zero_of_recovery_feasible (reference : Prob Ω) (start : Ω → I) (initial : Prob I)
    (endpoint : Ω → E) (target : Prob E)
    (targetSupported : SupportedBy target (Prob.coarsen reference endpoint).1)
    (initialPreserved : Prob.coarsen (FiniteRecovery.recover reference endpoint target) start = initial) :
    residual reference start initial endpoint target = 0 := by
  let recovered : Feasible reference start initial endpoint target :=
    ⟨FiniteRecovery.recover reference endpoint target,
      recovery_supported reference endpoint target targetSupported, initialPreserved,
      FiniteRecovery.coarsen_recover reference endpoint target targetSupported⟩
  apply le_antisymm _ bot_le
  calc
    residual reference start initial endpoint target ≤
        ENNReal.ofReal (klSum recovered.1.1 (FiniteRecovery.recover reference endpoint target).1) :=
      iInf_le _ recovered
    _ = 0 := by
      rw [klSum_self_eq_zero _ (FiniteRecovery.recover reference endpoint target).2.1, ENNReal.ofReal_zero]

theorem cost_eq_endpoint_of_recovery_feasible (reference : Prob Ω) (start : Ω → I) (initial : Prob I)
    (endpoint : Ω → E) (target : Prob E)
    (targetSupported : SupportedBy target (Prob.coarsen reference endpoint).1)
    (initialPreserved : Prob.coarsen (FiniteRecovery.recover reference endpoint target) start = initial) :
    cost reference start initial endpoint target =
      ENNReal.ofReal (klSum target.1 (Prob.coarsen reference endpoint).1) := by
  rw [cost_eq_endpoint_add_residual reference start initial endpoint target targetSupported,
    residual_zero_of_recovery_feasible reference start initial endpoint target targetSupported initialPreserved, add_zero]

end Mettapedia.ProbabilityTheory.InformationGeometry.TrajectoryFreeEnergy.EndpointBridge
