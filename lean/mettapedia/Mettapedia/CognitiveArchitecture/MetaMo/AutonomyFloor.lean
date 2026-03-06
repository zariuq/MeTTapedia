import Mettapedia.CognitiveArchitecture.MetaMo.Dynamics

/-!
# MetaMo Autonomy-Floor Dynamics

This module packages a clean anti-collapse theorem family for the current
MetaMo stack:

- inject a standing autonomous impulse `ι : Θ` into each update step;
- every positive-time iterate lies above `ι`;
- every fixed point of the injected dynamics lies above `ι`;
- therefore a non-bottom impulse prevents collapse to bottom equilibrium.

Conceptual note:
- This is the strongest stack-native version of an "autonomy drift lower bound"
  theorem available without introducing a separate stochastic perturbation
  calculus.
-/

namespace Mettapedia.CognitiveArchitecture.MetaMo

open Mettapedia.Algebra.QuantaleWeakness

variable {Q : Type*} {Θ : Type*}
  [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
  [CompleteLattice Θ] [QModule Q Θ]

/-- Inject a standing autonomous impulse into every motivational update. -/
def autonomyInjectedDynamics (ι : Θ) (q_sens q_dec : Q) : Θ → Θ :=
  fun θ => ι ⊔ motivationalDynamics (Θ := Θ) q_sens q_dec θ

/-- Fixed points of the autonomy-injected dynamics. -/
def IsAutonomyInjectedEquilibrium (ι : Θ) (q_sens q_dec : Q) (θ_eq : Θ) : Prop :=
  autonomyInjectedDynamics (Θ := Θ) ι q_sens q_dec θ_eq = θ_eq

@[simp]
theorem autonomyInjectedDynamics_apply (ι : Θ) (q_sens q_dec : Q) (θ : Θ) :
    autonomyInjectedDynamics (Θ := Θ) ι q_sens q_dec θ =
      ι ⊔ motivationalDynamics (Θ := Θ) q_sens q_dec θ := rfl

/-- The standing impulse is immediately visible after one injected step. -/
theorem autonomyImpulse_le_step
    (ι : Θ) (q_sens q_dec : Q) (θ : Θ) :
    ι ≤ autonomyInjectedDynamics (Θ := Θ) ι q_sens q_dec θ := by
  simp [autonomyInjectedDynamics]

/-- The injected dynamics are monotone. -/
theorem autonomyInjectedDynamics_mono
    (ι : Θ) (q_sens q_dec : Q) {θ₁ θ₂ : Θ}
    (h : θ₁ ≤ θ₂) :
    autonomyInjectedDynamics (Θ := Θ) ι q_sens q_dec θ₁ ≤
      autonomyInjectedDynamics (Θ := Θ) ι q_sens q_dec θ₂ := by
  exact sup_le_sup_left (motivationalDynamics_mono (Θ := Θ) q_sens q_dec h) ι

/-- Every positive-time iterate lies above the autonomy impulse. -/
theorem autonomyImpulse_le_iterate_succ
    (ι : Θ) (q_sens q_dec : Q) (θ₀ : Θ) (n : ℕ) :
    ι ≤ (autonomyInjectedDynamics (Θ := Θ) ι q_sens q_dec)^[n + 1] θ₀ := by
  rw [Function.iterate_succ_apply']
  exact le_sup_left

/-- Any equilibrium of the injected dynamics lies above the impulse floor. -/
theorem autonomyInjectedEquilibrium_impulse_le
    (ι : Θ) (q_sens q_dec : Q) {θ_eq : Θ}
    (hEq : IsAutonomyInjectedEquilibrium (Θ := Θ) ι q_sens q_dec θ_eq) :
    ι ≤ θ_eq := by
  have hStep :
      ι ≤ autonomyInjectedDynamics (Θ := Θ) ι q_sens q_dec θ_eq := by
    exact le_sup_left
  rw [hEq] at hStep
  exact hStep

/-- A non-bottom standing impulse prevents bottom collapse. -/
theorem autonomyInjected_bottom_not_equilibrium_of_impulse_ne_bot
    (ι : Θ) (q_sens q_dec : Q)
    (hι : ι ≠ ⊥) :
    ¬ IsAutonomyInjectedEquilibrium (Θ := Θ) ι q_sens q_dec ⊥ := by
  intro hEq
  have hFloor :
      ι ≤ (⊥ : Θ) :=
    autonomyInjectedEquilibrium_impulse_le (Θ := Θ) ι q_sens q_dec hEq
  exact hι (le_bot_iff.mp hFloor)

end Mettapedia.CognitiveArchitecture.MetaMo
