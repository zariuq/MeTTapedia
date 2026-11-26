import Mettapedia.GSLT.Distinction.Probabilistic.System
import Mathlib.Tactic.NormNum

/-!
# Conditional safety bounds for finite-horizon stochastic execution

Each row is the conditional law given the current configuration and time.
The configuration may include a controller, its revision history, and any
other information on which future choices depend. Probability lost to a
refused step is outside the mass of surviving runs.

If every safe configuration at time `i` sends at least `keep i` mass to safe
configurations, the mass of runs that remain safe through the horizon is at
least the product of those bounds. The proof uses conditional laws, so the
successive events may be dependent.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic

open scoped BigOperators

universe u

variable {State : Type u}

open Classical in
/-- Probability mass remaining in the safe set throughout the next
`steps` transitions, including the current configuration. -/
noncomputable def survival (transition : ℕ → State → SubDistribution State)
    (safe : State → Prop) : ℕ → (steps : ℕ) → State → ℝ :=
  fun time steps state =>
    match steps with
    | 0 => if safe state then 1 else 0
    | n + 1 =>
        if safe state then
          ∑ target ∈ (transition time state).weight.support,
            (transition time state).weight target *
              survival transition safe (time + 1) n target
        else 0

/-- Product of the conditional lower bounds over the given time interval. -/
def survivalBound (keep : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | time, n + 1 => keep time * survivalBound keep (time + 1) n

theorem survivalBound_nonneg (keep : ℕ → ℝ) (nonneg : ∀ i, 0 ≤ keep i) (time steps : ℕ) :
    0 ≤ survivalBound keep time steps := by
  induction steps generalizing time with
  | zero => simp [survivalBound]
  | succ n ih => exact mul_nonneg (nonneg time) (ih (time + 1))

theorem survival_nonneg (transition : ℕ → State → SubDistribution State) (safe : State → Prop)
    (time steps : ℕ) (state : State) : 0 ≤ survival transition safe time steps state := by
  classical
  induction steps generalizing time state with
  | zero => simp [survival]; split_ifs <;> norm_num
  | succ n ih =>
      by_cases admitted : safe state
      · rw [survival, if_pos admitted]
        exact Finset.sum_nonneg fun target _ =>
          mul_nonneg ((transition time state).nonneg target) (ih _ _)
      · simp [survival, admitted]

theorem survival_le_one (transition : ℕ → State → SubDistribution State) (safe : State → Prop)
    (time steps : ℕ) (state : State) : survival transition safe time steps state ≤ 1 := by
  classical
  induction steps generalizing time state with
  | zero => simp [survival]; split_ifs <;> norm_num
  | succ n ih =>
      by_cases admitted : safe state
      · rw [survival, if_pos admitted]
        calc
          _ ≤ ∑ target ∈ (transition time state).weight.support,
              (transition time state).weight target * 1 :=
            Finset.sum_le_sum fun target _ =>
              mul_le_mul_of_nonneg_left (ih _ _) ((transition time state).nonneg target)
          _ = (transition time state).total := by simp [SubDistribution.total]
          _ ≤ 1 := (transition time state).total_le_one'
      · simp [survival, admitted]

/-- Conditional local mass bounds multiply along the run. This also charges
the full missing mass of a subdistribution against the local bound. -/
theorem survival_ge (transition : ℕ → State → SubDistribution State) (safe : State → Prop)
    (keep : ℕ → ℝ) (nonneg : ∀ i, 0 ≤ keep i)
    (localBound : ∀ time state, safe state → keep time ≤ (transition time state).mass safe)
    (time steps : ℕ) (state : State) (admitted : safe state) :
    survivalBound keep time steps ≤ survival transition safe time steps state := by
  classical
  induction steps generalizing time state with
  | zero => simp [survivalBound, survival, admitted]
  | succ n ih =>
      let law := transition time state
      let weight := survivalBound keep (time + 1) n
      have weightNonneg : 0 ≤ weight := survivalBound_nonneg keep nonneg _ _
      rw [survival, if_pos admitted]
      calc
        survivalBound keep time (n + 1) = keep time * weight := rfl
        _ ≤ law.mass safe * weight :=
          mul_le_mul_of_nonneg_right (localBound time state admitted) weightNonneg
        _ = ∑ target ∈ law.weight.support, (if safe target then law.weight target else 0) * weight := by
          rw [SubDistribution.mass, Finset.sum_mul]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro target _
          by_cases stillSafe : safe target
          · rw [if_pos stillSafe]
            exact mul_le_mul_of_nonneg_left (ih _ _ stillSafe) (law.nonneg target)
          · rw [if_neg stillSafe, zero_mul]
            exact mul_nonneg (law.nonneg target) (survival_nonneg transition safe _ _ _)

theorem survivalBound_constant (keep : ℝ) (time steps : ℕ) :
    survivalBound (fun _ => keep) time steps = keep ^ steps := by
  induction steps generalizing time with
  | zero => simp [survivalBound]
  | succ n ih => simp [survivalBound, ih, pow_succ']

/-- A uniform bound on conditional failure gives a cumulative failure bound. -/
theorem failure_le (transition : ℕ → State → SubDistribution State) (safe : State → Prop)
    (risk : ℝ) (risk_le : risk ≤ 1)
    (localBound : ∀ time state, safe state → 1 - risk ≤ (transition time state).mass safe)
    (time steps : ℕ) (state : State) (admitted : safe state) :
    1 - survival transition safe time steps state ≤ 1 - (1 - risk) ^ steps := by
  have kept := survival_ge transition safe (fun _ => 1 - risk) (fun _ => sub_nonneg.mpr risk_le)
    localBound time steps state admitted
  rw [survivalBound_constant] at kept
  exact sub_le_sub_left kept 1

private theorem read_expectation {Code : Type*}
    (read : State → Code) (fine : SubDistribution State) (observed : SubDistribution Code)
    (agrees : ∀ code, fine.mass (fun state => read state = code) = observed.weight code)
    (value : Code → ℝ) :
    (∑ state ∈ fine.weight.support, fine.weight state * value (read state)) =
      ∑ code ∈ observed.weight.support, observed.weight code * value code := by
  classical
  let codes := fine.weight.support.image read ∪ observed.weight.support
  have seen (state : State) (member : state ∈ fine.weight.support) : read state ∈ codes :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ member)
  calc
    _ = ∑ code ∈ codes, ∑ state ∈ fine.weight.support.filter (fun state => read state = code),
        fine.weight state * value (read state) :=
      (Finset.sum_fiberwise_of_maps_to seen _).symm
    _ = ∑ code ∈ codes, observed.weight code * value code := by
      apply Finset.sum_congr rfl
      intro code _
      calc
        _ = ∑ state ∈ fine.weight.support.filter (fun state => read state = code),
            fine.weight state * value code := by
          apply Finset.sum_congr rfl
          intro state member
          rw [(Finset.mem_filter.mp member).2]
        _ = observed.weight code * value code := by
          rw [← Finset.sum_mul, Finset.sum_filter]
          change fine.mass (fun state => read state = code) * value code = _
          rw [agrees]
    _ = _ := (Finset.sum_subset
      (show observed.weight.support ⊆ codes from Finset.subset_union_right)
      (f := fun code => observed.weight code * value code)
      (fun code _ outside => by rw [Finsupp.notMem_support_iff.mp outside, zero_mul])).symm

/-- An implementation with the same probabilities on every readback class
preserves all finite-horizon safety probabilities expressed on the readback.
This applies even when the hidden state records changing implementations. -/
theorem survival_readback {Code : Type*} (read : State → Code)
    (fine : ℕ → State → SubDistribution State) (observed : ℕ → Code → SubDistribution Code)
    (agrees : ∀ time state code,
      (fine time state).mass (fun next => read next = code) = (observed time (read state)).weight code)
    (safe : Code → Prop) (time steps : ℕ) (state : State) :
    survival fine (safe ∘ read) time steps state = survival observed safe time steps (read state) := by
  classical
  induction steps generalizing time state with
  | zero => simp [survival]
  | succ n ih =>
      by_cases safeNow : safe (read state)
      · have fineSafe : (safe ∘ read) state := safeNow
        rw [survival, if_pos fineSafe, survival, if_pos safeNow]
        simp only [ih]
        exact read_expectation read _ _ (agrees time state) (survival observed safe (time + 1) n)
      · simp [survival, safeNow]

namespace SafetyControls

noncomputable def trial (keep : ℝ) (nonneg : 0 ≤ keep) (bounded : keep ≤ 1) :
    SubDistribution Bool :=
  SubDistribution.ofFunction (fun safe => if safe then keep else 1 - keep)
    (fun safe => by cases safe <;> simp [nonneg, sub_nonneg.mpr bounded])
    (by rw [Fintype.sum_bool]; simp)

theorem trial_safe_mass (keep : ℝ) (nonneg : 0 ≤ keep) (bounded : keep ≤ 1) :
    (trial keep nonneg bounded).mass (· = true) = keep := by
  rw [SubDistribution.mass_eq_sum, Fintype.sum_bool]
  simp [trial]

theorem trial_survival (keep : ℝ) (nonneg : 0 ≤ keep) (bounded : keep ≤ 1)
    (time steps : ℕ) :
    survival (fun _ _ => trial keep nonneg bounded) (· = true) time steps true = keep ^ steps := by
  classical
  induction steps generalizing time with
  | zero => simp [survival]
  | succ n ih =>
      rw [survival, if_pos rfl]
      rw [Finset.sum_subset (Finset.subset_univ (trial keep nonneg bounded).weight.support)
        (f := fun target => (trial keep nonneg bounded).weight target *
          survival (fun _ _ => trial keep nonneg bounded) (· = true) (time + 1) n target)
        (fun x _ outside => by rw [Finsupp.notMem_support_iff.mp outside, zero_mul])]
      rw [Fintype.sum_bool]
      have stopped : survival (fun _ _ => trial keep nonneg bounded) (· = true) (time + 1) n false = 0 := by
        cases n <;> simp [survival]
      rw [stopped, ih]
      simp [trial, pow_succ']

theorem two_steps_ninety_percent :
    survival (fun _ _ => trial (9 / 10) (by norm_num) (by norm_num)) (· = true) 0 2 true = 81 / 100 := by
  have computed := trial_survival (9 / 10 : ℝ) (by norm_num) (by norm_num) 0 2
  have squared : (9 / 10 : ℝ) ^ 2 = 81 / 100 := by norm_num
  exact computed.trans squared

theorem support_does_not_determine_safety :
    let low := trial (1 / 10) (by norm_num) (by norm_num)
    let high := trial (9 / 10) (by norm_num) (by norm_num)
    low.weight.support = high.weight.support ∧ low.mass (· = true) < high.mass (· = true) := by
  dsimp only
  constructor
  · ext safe
    cases safe <;> norm_num [trial, Finsupp.mem_support_iff]
  · rw [trial_safe_mass, trial_safe_mass]
    norm_num

end SafetyControls

#print axioms survival_ge
#print axioms failure_le
#print axioms survival_readback
#print axioms SafetyControls.support_does_not_determine_safety

end Mettapedia.GSLT.Distinction.Probabilistic
