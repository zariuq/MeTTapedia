import Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovModel
import Mettapedia.ProbabilityTheory.BayesianInference.Basic

/-!
# Bayesian conditioning of the existing controlled finite HMM

The real simplex distributions are obtained from the existing singleton
probabilities. Prediction and conditioning agree with the independently
defined extended-nonnegative filtering masses.
-/

namespace Mettapedia.ProbabilityTheory.HiddenMarkovModels.BayesianFiltering

open Finset
open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference
open ControlledFiniteHiddenMarkovModel
open scoped NNReal ENNReal

variable {A : Type*} {latent obs : ℕ}

private noncomputable def distribution (mass : Fin latent → ℝ≥0)
    (normalized : ∑ x, (mass x : ℝ≥0∞) = 1) : Prob (Fin latent) :=
  ⟨fun x => (mass x : ℝ), (fun x => (mass x).coe_nonneg), by
    have converted := congrArg ENNReal.toReal normalized
    rw [ENNReal.toReal_sum (fun _ _ => ENNReal.coe_ne_top)] at converted
    simpa using converted⟩

noncomputable def prior (θ : ControlledFiniteHMMParam A latent obs) : Prob (Fin latent) :=
  distribution (initProb θ) (initProb_sum_enn θ)

noncomputable def transition (θ : ControlledFiniteHMMParam A latent obs)
    (a : A) (s : Fin latent) : Prob (Fin latent) :=
  distribution (stepProb θ a s) (stepProb_sum_enn θ a s)

noncomputable def emission (θ : ControlledFiniteHMMParam A latent obs)
    (s : Fin latent) : Prob (Fin obs) :=
  distribution (emissionProb θ s) (emissionProb_sum_enn θ s)

/-- The joint next-state/observation kernel used by adaptive policies. -/
noncomputable def observedKernel (θ : ControlledFiniteHMMParam A latent obs)
    (a : A) (s : Fin latent) : Prob (Fin latent × Fin obs) :=
  joint (transition θ a s) (emission θ)

noncomputable def liftMass (belief : Prob (Fin latent)) : LatentMass latent :=
  fun s => ENNReal.ofReal (belief.1 s)

private theorem prediction_finite (θ : ControlledFiniteHMMParam A latent obs)
    (belief : Prob (Fin latent)) (a : A) (s : Fin latent) :
    predictiveLatentMass θ (liftMass belief) a s ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro t _
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top

theorem prediction_refines (θ : ControlledFiniteHMMParam A latent obs)
    (belief : Prob (Fin latent)) (a : A) (s : Fin latent) :
    (predictiveLatentMass θ (liftMass belief) a s).toReal =
      (Prob.bind belief (transition θ a)).1 s := by
  unfold predictiveLatentMass liftMass
  rw [ENNReal.toReal_sum
    (fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top)]
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal, belief.2.1,
    transition, distribution]

theorem filtering_mass_refines (θ : ControlledFiniteHMMParam A latent obs)
    (belief : Prob (Fin latent)) (a : A) (o : Fin obs) (s : Fin latent) :
    (filteringStepMass θ (liftMass belief) a o s).toReal =
      (Prob.bind belief (transition θ a)).1 s * (emission θ s).1 o := by
  rw [filteringStepMass, ENNReal.toReal_mul, prediction_refines]
  rfl

theorem evidence_refines (θ : ControlledFiniteHMMParam A latent obs)
    (belief : Prob (Fin latent)) (a : A) (o : Fin obs) :
    (observationMassGivenAction θ (liftMass belief) a o).toReal =
      evidence (Prob.bind belief (transition θ a)) (fun s => (emission θ s).1 o) := by
  rw [observationMassGivenAction, ENNReal.toReal_sum]
  · simp only [filtering_mass_refines, evidence]
  · intro s _
    exact ENNReal.mul_ne_top (prediction_finite θ belief a s) ENNReal.coe_ne_top

/-- The normalized existing filtering mass is exactly the new Bayesian posterior. -/
theorem posterior_refines (θ : ControlledFiniteHMMParam A latent obs)
    (belief : Prob (Fin latent)) (a : A) (o : Fin obs)
    (possible : 0 < evidence (Prob.bind belief (transition θ a))
      (fun s => (emission θ s).1 o)) (s : Fin latent) :
    (filteringStepMass θ (liftMass belief) a o s /
      observationMassGivenAction θ (liftMass belief) a o).toReal =
      (posterior (Prob.bind belief (transition θ a)) (fun s => (emission θ s).1 o)
        (fun s => (emission θ s).2.1 o) possible).1 s := by
  rw [ENNReal.toReal_div, filtering_mass_refines, evidence_refines, posterior_apply]

end Mettapedia.ProbabilityTheory.HiddenMarkovModels.BayesianFiltering
