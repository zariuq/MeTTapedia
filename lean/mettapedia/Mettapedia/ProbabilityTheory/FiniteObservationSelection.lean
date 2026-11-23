import Mettapedia.ProbabilityTheory.FiniteEventMass

/-!
# Selection and conditioning on a public observation

An observation fixes a fiber of possible worlds. A sampling or selection
weight preserves its conditional law exactly when it is constant over
the positive-weight worlds in this fiber. This covers visible acceptance
tests and cancelling the probability of an exogenous regime indicator.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.FiniteObservationSelection

open FiniteEventMass

variable {Ω : Type*} [Fintype Ω]

noncomputable def posterior (weight : Ω → ℝ) (shown event : Ω → Bool) : ℝ :=
  mass weight (fun w => event w && shown w) / mass weight shown

private theorem selected_mass (weight select : Ω → ℝ) (shown event : Ω → Bool) (scale : ℝ)
    (same : ∀ w, shown w = true → weight w ≠ 0 → select w = scale) :
    mass (fun w => select w * weight w) (fun w => event w && shown w) =
      scale * mass weight (fun w => event w && shown w) := by
  unfold mass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases inside : shown w = true
  · by_cases positive : weight w = 0
    · simp [positive]
    · cases h : event w <;> simp [inside, h, same w inside positive]
  · cases h : shown w <;> simp_all

theorem posterior_eq_of_constant (weight select : Ω → ℝ) (shown : Ω → Bool) (scale : ℝ)
    (positive : 0 < scale)
    (same : ∀ w, shown w = true → weight w ≠ 0 → select w = scale)
    (event : Ω → Bool) :
    posterior (fun w => select w * weight w) shown event = posterior weight shown event := by
  have denominator := selected_mass weight select shown (fun _ => true) scale same
  simp only [Bool.true_and] at denominator
  rw [posterior, posterior, selected_mass weight select shown event scale same, denominator,
    mul_div_mul_left _ _ positive.ne']

private theorem singleton_mass [DecidableEq Ω] (weight : Ω → ℝ) (shown : Ω → Bool)
    (world : Ω) (present : shown world = true) :
    mass weight (fun w => decide (w = world) && shown w) = weight world := by
  unfold mass
  calc
    _ = ∑ w, if w = world then weight w else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases eq : w = world
      · simp [eq, present]
      · simp [eq]
    _ = _ := by simp

/-- Checking all events is equivalent to checking that the relative
sampling weight is constant on the observed support. Singleton events
already detect every failure of this condition. -/
theorem posterior_eq_all_iff [DecidableEq Ω] (weight select : Ω → ℝ) (shown : Ω → Bool)
    (available : 0 < mass weight shown)
    (selected : 0 < mass (fun w => select w * weight w) shown) :
    (∀ event, posterior (fun w => select w * weight w) shown event = posterior weight shown event) ↔
      ∀ w, shown w = true → weight w ≠ 0 →
        select w = mass (fun w => select w * weight w) shown / mass weight shown := by
  constructor
  · intro every w present live
    have h := every (fun x => decide (x = w))
    unfold posterior at h
    rw [singleton_mass _ shown w present, singleton_mass _ shown w present] at h
    have step := (div_eq_div_iff selected.ne' available.ne').mp h
    apply (eq_div_iff available.ne').mpr
    apply mul_left_cancel₀ live
    calc
      weight w * (select w * mass weight shown) =
        select w * weight w * mass weight shown := by ring
      _ = _ := step
  · intro same
    exact posterior_eq_of_constant weight select shown _ (div_pos selected available) same

end Mettapedia.ProbabilityTheory.FiniteObservationSelection
