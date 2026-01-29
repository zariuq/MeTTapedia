/-
# MetaMo Contractive Dynamics and Stability

This module establishes conditions under which motivational dynamics have
unique stable equilibria, using Banach's fixed-point theorem.

## Mathematical Framework

Given:
- A Q-module (Θ, •) over a commutative quantale Q
- Appraisal parameter q_sens ∈ Q
- Decision parameter q_dec ∈ Q

The motivational dynamics map is:

  Φ(θ) = App_{q_sens}(Dec_{q_dec}(θ)) = (q_sens * q_dec) • θ

When Θ has a metric structure and Φ is a contracting map (Lipschitz constant < 1),
Banach's theorem guarantees a unique fixed point: the motivational equilibrium.

## Key Results

1. **Definition**: `motivationalDynamics q_sens q_dec` as the composition
2. **Commutativity**: Order of appraisal/decision doesn't matter
3. **Equilibrium**: Under contractivity, a unique stable equilibrium exists

## References

- Goertzel & Lian, "Weakness and Its Quantale" (MetaMo Appendix)
- Banach, "Sur les opérations dans les ensembles abstraits" (1922)
-/

import Mettapedia.CognitiveArchitecture.MetaMo.Commutativity
import Mathlib.Topology.MetricSpace.Contracting

namespace Mettapedia.CognitiveArchitecture.MetaMo

open Mettapedia.Algebra.QuantaleWeakness
open scoped NNReal

variable {Q : Type*} {Θ : Type*}
  [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
  [CompleteLattice Θ] [QModule Q Θ]

/-! ## Motivational Dynamics Definition -/

/-- The motivational dynamics map: composition of appraisal and decision.

Given sensitivity q_sens and decision weight q_dec, this map represents
one "tick" of motivational update:
  Φ(θ) = q_sens • (q_dec • θ) = (q_sens * q_dec) • θ

By the commutativity theorem, this equals Dec(App(θ)). -/
def motivationalDynamics (q_sens q_dec : Q) : Θ → Θ :=
  appraisalFunctor q_sens ∘ decisionFunctor q_dec

/-- Alternative definition: decision first, then appraisal -/
def motivationalDynamics' (q_sens q_dec : Q) : Θ → Θ :=
  decisionFunctor q_dec ∘ appraisalFunctor q_sens

/-- The two orderings are equivalent -/
theorem motivationalDynamics_eq_dynamics' (q_sens q_dec : Q) :
    motivationalDynamics (Θ := Θ) q_sens q_dec = motivationalDynamics' q_sens q_dec := by
  unfold motivationalDynamics motivationalDynamics'
  exact appraisal_decision_commute_comp q_sens q_dec

/-! ### Basic Properties -/

@[simp]
theorem motivationalDynamics_apply (q_sens q_dec : Q) (θ : Θ) :
    motivationalDynamics q_sens q_dec θ = q_sens • (q_dec • θ) := rfl

/-- Dynamics equals scalar multiplication by the product -/
theorem motivationalDynamics_eq_smul (q_sens q_dec : Q) (θ : Θ) :
    motivationalDynamics q_sens q_dec θ = (q_sens * q_dec) • θ := by
  simp only [motivationalDynamics_apply]
  exact (mul_smul q_sens q_dec θ).symm

/-- Identity dynamics when parameters are 1 -/
@[simp]
theorem motivationalDynamics_one_one :
    motivationalDynamics (Θ := Θ) (1 : Q) 1 = id := by
  ext θ
  simp only [motivationalDynamics_apply, one_smul, id_eq]

/-- Composition of dynamics corresponds to multiplication of combined parameters -/
theorem motivationalDynamics_comp (q_s₁ q_d₁ q_s₂ q_d₂ : Q) :
    motivationalDynamics (Θ := Θ) q_s₁ q_d₁ ∘ motivationalDynamics q_s₂ q_d₂ =
    motivationalDynamics (q_s₁ * q_d₁ * q_s₂) q_d₂ := by
  ext θ
  simp only [Function.comp_apply, motivationalDynamics_eq_smul]
  rw [← mul_smul]
  congr 1
  simp only [mul_comm, mul_left_comm]

/-! ## Fixed Points and Equilibria

A motivational equilibrium is a fixed point of the dynamics:
  θ_eq = Φ(θ_eq) = (q_sens * q_dec) • θ_eq
-/

/-- A motivational equilibrium is a fixed point of the dynamics -/
def IsMotivationalEquilibrium (q_sens q_dec : Q) (θ_eq : Θ) : Prop :=
  motivationalDynamics q_sens q_dec θ_eq = θ_eq

/-- Equivalent characterization: scalar multiplication by the combined parameter -/
theorem isMotivationalEquilibrium_iff (q_sens q_dec : Q) (θ_eq : Θ) :
    IsMotivationalEquilibrium q_sens q_dec θ_eq ↔ (q_sens * q_dec) • θ_eq = θ_eq := by
  unfold IsMotivationalEquilibrium
  rw [motivationalDynamics_eq_smul]

/-! ## Contractive Dynamics and Stability

When the state space has a metric structure and the dynamics are contractive,
Banach's fixed-point theorem guarantees existence and uniqueness of equilibrium.
-/

section ContractiveCase

variable [EMetricSpace Θ] [CompleteSpace Θ]

/-- **Main Stability Theorem**: If the dynamics are contractive (Lipschitz constant < 1),
    a unique motivational equilibrium exists.

For the dynamics Φ(θ) = (q_sens * q_dec) • θ to be contractive, we need:
1. The function to be Lipschitz with some constant K
2. K < 1

This is the key stability result for MetaMo: under appropriate conditions
on the sensitivity and decision parameters, the system converges to a
unique stable equilibrium. -/
theorem motivational_equilibrium_exists
    (q_sens q_dec : Q) (K : ℝ≥0)
    (h_contract : ContractingWith K (motivationalDynamics (Θ := Θ) q_sens q_dec))
    (θ₀ : Θ) (h_finite : edist θ₀ (motivationalDynamics q_sens q_dec θ₀) ≠ ⊤) :
    ∃ θ_eq : Θ, IsMotivationalEquilibrium q_sens q_dec θ_eq ∧
      Filter.Tendsto (fun n => (motivationalDynamics q_sens q_dec)^[n] θ₀)
        Filter.atTop (nhds θ_eq) := by
  obtain ⟨θ_eq, h_fixed, h_tendsto, _⟩ := ContractingWith.exists_fixedPoint h_contract θ₀ h_finite
  exact ⟨θ_eq, h_fixed, h_tendsto⟩

omit [CompleteSpace Θ] in
/-- The equilibrium is unique (when it exists under contractivity) -/
theorem motivational_equilibrium_unique
    (q_sens q_dec : Q) (K : ℝ≥0)
    (h_contract : ContractingWith K (motivationalDynamics (Θ := Θ) q_sens q_dec))
    {θ₁ θ₂ : Θ}
    (h₁ : IsMotivationalEquilibrium q_sens q_dec θ₁)
    (h₂ : IsMotivationalEquilibrium q_sens q_dec θ₂)
    (h_finite : edist θ₁ θ₂ ≠ ⊤) :
    θ₁ = θ₂ :=
  (h_contract.eq_or_edist_eq_top_of_fixedPoints h₁ h₂).resolve_right h_finite

end ContractiveCase

/-! ## Qualitative Dynamics

Even without metric structure, we can establish qualitative properties
of motivational dynamics using the lattice structure.
-/

/-- Dynamics preserve the lattice order -/
theorem motivationalDynamics_mono (q_sens q_dec : Q) {θ₁ θ₂ : Θ} (h : θ₁ ≤ θ₂) :
    motivationalDynamics q_sens q_dec θ₁ ≤ motivationalDynamics q_sens q_dec θ₂ := by
  simp only [motivationalDynamics_eq_smul]
  exact smul_mono_right (q_sens * q_dec) h

/-- Dynamics distribute over joins -/
theorem motivationalDynamics_sup (q_sens q_dec : Q) (θ₁ θ₂ : Θ) :
    motivationalDynamics q_sens q_dec (θ₁ ⊔ θ₂) =
    motivationalDynamics q_sens q_dec θ₁ ⊔ motivationalDynamics q_sens q_dec θ₂ := by
  simp only [motivationalDynamics_eq_smul]
  exact smul_sup (q_sens * q_dec) θ₁ θ₂

end Mettapedia.CognitiveArchitecture.MetaMo
