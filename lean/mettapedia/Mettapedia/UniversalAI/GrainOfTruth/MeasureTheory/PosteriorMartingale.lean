import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PolicyFactorization
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorProcess
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Posterior Martingale under the On-Policy Mixture Measure

This file proves the standard “posterior is a martingale” fact in the concrete setting of the
Grain-of-Truth development:

* sample space: trajectories `Trajectory`
* filtration: `trajectoryFiltration` (prefix σ-algebras)
* measure: on-policy Bayes mixture `ξ^π`
* process: `t ↦ posteriorWeight ν_idx t` (converted to `ℝ` via `ENNReal.toReal`)

This is the backbone needed for Leike-style Chapter 7 proofs (Blackwell–Dubins / merging route).
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale

open _root_.MeasureTheory _root_.ProbabilityTheory Filter
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.MixtureMeasure
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PolicyFactorization
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorProcess
open Mettapedia.UniversalAI.ReflectiveOracles
open scoped ENNReal NNReal MeasureTheory

/-! ## Helpers: extending a finite prefix to a trajectory -/

/-- Extend a finite prefix `p : Fin t → Step` to an infinite trajectory by filling the tail with
`default`. -/
noncomputable def extendPrefix (t : ℕ) (p : Fin t → Step) : Trajectory :=
  fun n => if h : n < t then p ⟨n, h⟩ else default

@[simp] theorem truncate_extendPrefix (t : ℕ) (p : Fin t → Step) :
    truncate t (extendPrefix t p) = p := by
  funext i
  simp [truncate, extendPrefix, i.isLt]

@[simp] theorem prefixToHistory_length (t : ℕ) (p : Fin t → Step) :
    (prefixToHistory t p).length = 2 * t := by
  -- Reduce to `trajectoryToHistory_length` using an explicit extension trajectory.
  have hEq : prefixToHistory t p = trajectoryToHistory (extendPrefix t p) t := by
    simpa [truncate_extendPrefix] using (prefixToHistory_eq_trajectoryToHistory t (extendPrefix t p))
  simpa [hEq.symm] using (trajectoryToHistory_length (extendPrefix t p) t)

theorem prefixToHistory_wellFormed (t : ℕ) (p : Fin t → Step) :
    (prefixToHistory t p).wellFormed := by
  -- Reduce to `trajectoryToHistory_wellFormed`.
  have hEq : prefixToHistory t p = trajectoryToHistory (extendPrefix t p) t := by
    simpa [truncate_extendPrefix] using (prefixToHistory_eq_trajectoryToHistory t (extendPrefix t p))
  simpa [hEq.symm] using (trajectoryToHistory_wellFormed (extendPrefix t p) t)

theorem prefixToHistory_even (t : ℕ) (p : Fin t → Step) :
    Even (prefixToHistory t p).length := by
  -- `length = 2 * t`.
  rw [prefixToHistory_length]
  exact even_two_mul t

theorem historySteps_prefixToHistory (t : ℕ) (p : Fin t → Step) :
    historySteps (prefixToHistory t p) = t := by
  -- `historySteps h = h.length / 2`.
  simp [historySteps, prefixToHistory_length]

/-- A singleton cylinder at time `t` (specified by a prefix `p`) is the same as the `cylinderSet`
of the corresponding history `prefixToHistory t p`. -/
theorem truncate_preimage_singleton_eq_cylinderSet (t : ℕ) (p : Fin t → Step) :
    truncate t ⁻¹' ({p} : Set (Fin t → Step)) = cylinderSet (prefixToHistory t p) := by
  classical
  have hw : (prefixToHistory t p).wellFormed :=
    prefixToHistory_wellFormed t p
  have hsteps : historySteps (prefixToHistory t p) = t :=
    historySteps_prefixToHistory t p
  have h_set :
      ({p' : Fin t → Step | prefixToHistory t p' = prefixToHistory t p} : Set (Fin t → Step)) =
        ({p} : Set (Fin t → Step)) := by
    ext p'
    constructor
    · intro hp'
      have : historyToFinPrefix t (prefixToHistory t p') = historyToFinPrefix t (prefixToHistory t p) :=
        congrArg (historyToFinPrefix t) hp'
      simpa [historyToFinPrefix_prefixToHistory] using this
    · intro hp'
      simp [Set.mem_singleton_iff] at hp'
      subst hp'
      rfl
  have h_pre :
      truncate t ⁻¹' ({p} : Set (Fin t → Step)) = cylinderSetAt t (prefixToHistory t p) := by
    simp [cylinderSetAt_eq_preimage, h_set]
  have h_cyl :
      cylinderSetAt t (prefixToHistory t p) = cylinderSet (prefixToHistory t p) := by
    simpa [hsteps] using (cylinderSet_eq_cylinderSetAt (h := prefixToHistory t p) hw).symm
  exact h_pre.trans h_cyl

/-! ## The posterior process as an ℝ-valued adapted process -/

noncomputable abbrev ξ (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) : Measure Trajectory :=
  mixtureMeasureWithPolicy O M prior envs π h_stoch

/-- Real-valued posterior process (for martingale theory). -/
noncomputable def posteriorReal (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (ν_idx : EnvironmentIndex) :
    ℕ → Trajectory → ℝ :=
  fun t traj => (posteriorWeight O M prior envs ν_idx t traj).toReal

theorem posteriorReal_adapted (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (ν_idx : EnvironmentIndex) :
    MeasureTheory.StronglyAdapted trajectoryFiltration (posteriorReal O M prior envs ν_idx) := by
  intro t
  -- We prove measurability by “depends only on the first t steps”.
  have h_meas :
      @Measurable Trajectory ℝ (sigmaAlgebraUpTo t) _ (posteriorReal O M prior envs ν_idx t) := by
    refine (measurable_wrt_filtration_iff (f := posteriorReal O M prior envs ν_idx t) t).2 ?_
    intro traj₁ traj₂ hprefix
    have hEq :
        posteriorWeight O M prior envs ν_idx t traj₁ =
          posteriorWeight O M prior envs ν_idx t traj₂ :=
      posteriorWeight_adapted O M prior envs ν_idx t traj₁ traj₂ hprefix
    simpa [posteriorReal] using congrArg ENNReal.toReal hEq
  -- Convert measurability to strong measurability in the filtration σ-algebra.
  apply Measurable.stronglyMeasurable
  change @Measurable Trajectory ℝ (sigmaAlgebraUpTo t) _ (posteriorReal O M prior envs ν_idx t)
  exact h_meas

/-! ## A simple bound: posterior weights are ≤ 1 -/

theorem bayesianPosteriorWeight_le_one (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (ν_idx : EnvironmentIndex) (h : History) :
    bayesianPosteriorWeight O M prior envs ν_idx h ≤ 1 := by
  classical
  set numerator : ℝ≥0∞ := prior.weight ν_idx * historyProbability (envs ν_idx) h
  set denom : ℝ≥0∞ := mixtureProbability O M prior envs h
  by_cases hden : denom = 0
  · -- posterior falls back to the prior
    simp [bayesianPosteriorWeight, denom, hden]
    have hle : prior.weight ν_idx ≤ ∑' i, prior.weight i := ENNReal.le_tsum ν_idx
    exact le_trans hle prior.tsum_le_one
  · have hden_ne0 : denom ≠ 0 := hden
    have hden_le_one : denom ≤ 1 := by
      have h_term : ∀ i : EnvironmentIndex,
          prior.weight i * historyProbability (envs i) h ≤ prior.weight i := by
        intro i
        have h_prob : historyProbability (envs i) h ≤ 1 := historyProbability_le_one (envs i) h
        simpa [mul_one] using (mul_le_mul_right h_prob (prior.weight i))
      have h_le : denom ≤ ∑' i, prior.weight i := by
        simpa [denom, mixtureProbability] using (ENNReal.tsum_le_tsum h_term)
      exact le_trans h_le prior.tsum_le_one
    have hden_ne_top : denom ≠ ∞ := (lt_of_le_of_lt hden_le_one ENNReal.one_lt_top).ne_top
    have h_num_le : numerator ≤ denom := by
      simpa [numerator, denom, mixtureProbability] using ENNReal.le_tsum ν_idx
    have hdiv_le : numerator / denom ≤ (1 : ℝ≥0∞) := by
      exact (ENNReal.div_le_iff hden_ne0 hden_ne_top).2 (by simpa [one_mul] using h_num_le)
    simpa [bayesianPosteriorWeight, numerator, denom, hden] using hdiv_le

theorem posteriorReal_le_one (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (ν_idx : EnvironmentIndex) (t : ℕ) (traj : Trajectory) :
    posteriorReal O M prior envs ν_idx t traj ≤ 1 := by
  -- Reduce to the corresponding history and use monotonicity of `ENNReal.toReal`.
  have hle :
      posteriorWeight O M prior envs ν_idx t traj ≤ (1 : ℝ≥0∞) := by
    simpa [posteriorWeight] using
      bayesianPosteriorWeight_le_one (O := O) (M := M) (prior := prior) (envs := envs)
        (ν_idx := ν_idx) (h := trajectoryToHistory traj t)
  have hmono :
      (posteriorWeight O M prior envs ν_idx t traj).toReal ≤ (1 : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono (by simp) hle
  simpa [posteriorReal] using hmono

/-! ## Martingale proof via set-integral characterization -/

theorem posteriorReal_integrable (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (ν_idx : EnvironmentIndex) :
    ∀ t, Integrable (posteriorReal O M prior envs ν_idx t) (ξ O M prior envs π h_stoch) := by
  intro t
  have hadp := posteriorReal_adapted (O := O) (M := M) (prior := prior) (envs := envs) (ν_idx := ν_idx)
  have hmeas :
      AEStronglyMeasurable (posteriorReal O M prior envs ν_idx t) (ξ O M prior envs π h_stoch) := by
    -- `σ(t) ≤ m0`, so adaptedness upgrades to strong measurability in the ambient measurable space.
    have hsm :
        StronglyMeasurable (posteriorReal O M prior envs ν_idx t) :=
      (hadp t).mono (sigmaAlgebraUpTo_le t)
    exact hsm.aestronglyMeasurable
  have hbound :
      ∀ᵐ traj ∂(ξ O M prior envs π h_stoch),
        ‖posteriorReal O M prior envs ν_idx t traj‖ ≤ (1 : ℝ) := by
    refine Filter.Eventually.of_forall (fun traj => ?_)
    have h0 : 0 ≤ posteriorReal O M prior envs ν_idx t traj := ENNReal.toReal_nonneg
    have h1 : posteriorReal O M prior envs ν_idx t traj ≤ 1 :=
      posteriorReal_le_one (O := O) (M := M) (prior := prior) (envs := envs) (ν_idx := ν_idx) t traj
    -- Since the value is nonnegative, `‖x‖ = x`.
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  -- Bounded by an integrable constant on a finite measure space.
  have : Integrable (fun _ : Trajectory => (1 : ℝ)) (ξ O M prior envs π h_stoch) := by
    simp
  exact this.mono' hmeas hbound

/-! ## Main theorem: the posterior is a martingale under `ξ^π` -/

theorem posteriorReal_martingale (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (ν_idx : EnvironmentIndex) :
    MeasureTheory.Martingale
        (posteriorReal O M prior envs ν_idx)
        trajectoryFiltration
        (ξ O M prior envs π h_stoch) := by
  -- We use the finite-measure characterization `martingale_of_setIntegral_eq_succ`.
  refine MeasureTheory.martingale_of_setIntegral_eq_succ
      (μ := ξ O M prior envs π h_stoch) (𝒢 := trajectoryFiltration)
      (posteriorReal_adapted (O := O) (M := M) (prior := prior) (envs := envs) (ν_idx := ν_idx))
      (posteriorReal_integrable (O := O) (M := M) (prior := prior) (envs := envs) (π := π)
        (h_stoch := h_stoch) (ν_idx := ν_idx)) ?_
  intro t s hs
  classical
  let μξ : Measure Trajectory := ξ O M prior envs π h_stoch
  let μν : Measure Trajectory := environmentMeasureWithPolicy (envs ν_idx) π (h_stoch ν_idx)

  -- Any `σ(t)`-measurable set is a preimage under `truncate t`.
  have hs_sigma : @MeasurableSet Trajectory (sigmaAlgebraUpTo t) s := by
    change @MeasurableSet Trajectory (sigmaAlgebraUpTo t) s at hs
    exact hs
  rcases (by
      simpa [sigmaAlgebraUpTo, MeasurableSpace.measurableSet_comap] using hs_sigma) with
    ⟨w, _hw, hw_eq⟩
  have hs_eq : s = truncate t ⁻¹' w := hw_eq.symm
  -- Reduce to the case `s = truncate t ⁻¹' w`.
  subst hs_eq

  -- Since the prefix space is finite, the event decomposes into a finite disjoint union of atoms.
  letI : DecidablePred (fun p : Fin t → Step => p ∈ w) := Classical.decPred _
  let W : Finset (Fin t → Step) := Finset.univ.filter (fun p => p ∈ w)
  have h_union :
      truncate t ⁻¹' w =
        ⋃ p ∈ W, truncate t ⁻¹' ({p} : Set (Fin t → Step)) := by
    ext traj
    constructor
    · intro htraj
      have hw' : truncate t traj ∈ w := htraj
      refine (Set.mem_iUnion).2 ?_
      refine ⟨truncate t traj, ?_⟩
      refine (Set.mem_iUnion).2 ?_
      refine ⟨?_, ?_⟩
      · simp [W, Finset.mem_filter, hw']
      · simp [Set.mem_preimage, Set.mem_singleton_iff]
    · intro htraj
      rcases (Set.mem_iUnion.1 htraj) with ⟨p, hp⟩
      rcases (Set.mem_iUnion.1 hp) with ⟨hpW, hpAtom⟩
      have hpw : p ∈ w := by
        simpa [W, Finset.mem_filter] using hpW
      have htrunc : truncate t traj = p := by
        simpa [Set.mem_preimage, Set.mem_singleton_iff] using hpAtom
      simpa [htrunc] using hpw

  -- Atom sets: `truncate t = p` for a fixed prefix `p`.
  let atom : (Fin t → Step) → Set Trajectory :=
    fun p => truncate t ⁻¹' ({p} : Set (Fin t → Step))
  have h_atom_meas : ∀ p ∈ W, MeasurableSet (atom p) := by
    intro p _hpW
    simpa [atom] using (truncate_measurable t) (measurableSet_singleton p)
  have h_atom_disj : Set.Pairwise (↑W) (fun p₁ p₂ => Disjoint (atom p₁) (atom p₂)) := by
    intro p₁ hp₁ p₂ hp₂ hp_ne
    refine Set.disjoint_left.2 ?_
    intro traj h₁ h₂
    have ht₁ : truncate t traj = p₁ := by
      simpa [atom, Set.mem_preimage, Set.mem_singleton_iff] using h₁
    have ht₂ : truncate t traj = p₂ := by
      simpa [atom, Set.mem_preimage, Set.mem_singleton_iff] using h₂
    exact hp_ne (by simpa [ht₁] using ht₂)

  have h_integrable_t : ∀ p ∈ W, IntegrableOn (posteriorReal O M prior envs ν_idx t) (atom p) μξ := by
    intro _p _hpW
    exact (posteriorReal_integrable (O := O) (M := M) (prior := prior) (envs := envs) (π := π)
      (h_stoch := h_stoch) (ν_idx := ν_idx) t).integrableOn
  have h_integrable_succ :
      ∀ p ∈ W, IntegrableOn (posteriorReal O M prior envs ν_idx (t + 1)) (atom p) μξ := by
    intro _p _hpW
    exact (posteriorReal_integrable (O := O) (M := M) (prior := prior) (envs := envs) (π := π)
      (h_stoch := h_stoch) (ν_idx := ν_idx) (t + 1)).integrableOn

  -- Core atom equality: on each prefix-atom, the set integral matches between `t` and `t+1`.
  have h_atom_eq :
      ∀ p ∈ W,
        (∫ ω in atom p, posteriorReal O M prior envs ν_idx t ω ∂μξ) =
          ∫ ω in atom p, posteriorReal O M prior envs ν_idx (t + 1) ω ∂μξ := by
    intro p _hpW
    set h : History := prefixToHistory t p
    have h_wf : h.wellFormed := by
      simpa [h] using prefixToHistory_wellFormed t p
    have h_complete : Even h.length := by
      exact prefixToHistory_even t p
    have h_steps : historySteps h = t := by
      simpa [h] using historySteps_prefixToHistory t p

    -- Rewrite the atom as a cylinder set.
    have h_atom_cyl : atom p = cylinderSet h := by
      simpa [atom, h] using (truncate_preimage_singleton_eq_cylinderSet t p)

    -- (1) Time `t`: the posterior is constant on `atom p`.
    have h_atom_meas' : MeasurableSet (atom p) := by
      simpa [atom] using (truncate_measurable t) (measurableSet_singleton p)
    have hEqOn_t :
        Set.EqOn (posteriorReal O M prior envs ν_idx t)
          (fun _ => (bayesianPosteriorWeight O M prior envs ν_idx h).toReal) (atom p) := by
      intro traj htraj
      have htrunc : truncate t traj = p := by
        simpa [atom, Set.mem_preimage, Set.mem_singleton_iff] using htraj
      have ht : trajectoryToHistory traj t = h := by
        have := (prefixToHistory_eq_trajectoryToHistory t traj).symm
        simpa [h, htrunc] using this
      simp [posteriorReal, posteriorWeight, ht]

    have hInt_t :
        (∫ ω in atom p, posteriorReal O M prior envs ν_idx t ω ∂μξ) =
          μξ.real (atom p) * (bayesianPosteriorWeight O M prior envs ν_idx h).toReal := by
      rw [MeasureTheory.setIntegral_congr_fun h_atom_meas' hEqOn_t]
      simp [smul_eq_mul]

    have hCancel_t :
        bayesianPosteriorWeight O M prior envs ν_idx h * μξ (cylinderSet h) =
          prior.weight ν_idx * μν (cylinderSet h) := by
      simpa [μξ, μν, ξ] using
        (bayesianPosteriorWeight_mul_mixtureMeasureWithPolicy_cylinderSet (O := O) (M := M) (prior := prior)
          (envs := envs) (π := π) (h_stoch := h_stoch) (ν_idx := ν_idx) (h := h) (h_wf := h_wf)
          (h_complete := h_complete))

    have hInt_t' :
        (∫ ω in atom p, posteriorReal O M prior envs ν_idx t ω ∂μξ) =
          (prior.weight ν_idx).toReal * μν.real (atom p) := by
      have hCancel_t_real := congrArg ENNReal.toReal hCancel_t
      -- Convert the constant integral into a `toReal` product and cancel using `hCancel_t`.
      calc
        (∫ ω in atom p, posteriorReal O M prior envs ν_idx t ω ∂μξ)
            = μξ.real (atom p) * (bayesianPosteriorWeight O M prior envs ν_idx h).toReal := hInt_t
        _ = ((bayesianPosteriorWeight O M prior envs ν_idx h) * μξ (atom p)).toReal := by
              simp [MeasureTheory.measureReal_def, ENNReal.toReal_mul, mul_comm]
        _ = ((prior.weight ν_idx) * μν (cylinderSet h)).toReal := by
              simpa [h_atom_cyl] using hCancel_t_real
        _ = (prior.weight ν_idx).toReal * μν.real (atom p) := by
              simp [MeasureTheory.measureReal_def, ENNReal.toReal_mul, h_atom_cyl]

    -- (2) Time `t+1`: decompose the atom into one-step extension cylinders.
    let extSet : Step → Set Trajectory :=
      fun st => cylinderSet (h ++ [HistElem.act st.action, HistElem.per st.percept])
    have h_ext_meas : ∀ st, MeasurableSet (extSet st) := by
      intro st
      simpa [extSet] using cylinderSet_measurable (h ++ [HistElem.act st.action, HistElem.per st.percept])
    have h_ext_disj : Pairwise (fun st₁ st₂ => Disjoint (extSet st₁) (extSet st₂)) := by
      intro st₁ st₂ hne
      refine Set.disjoint_left.2 ?_
      intro traj h₁ h₂
      have h₁' :
          traj ∈ cylinderSet h ∩ {traj | traj (historySteps h) = Step.mk st₁.action st₁.percept} := by
        simpa [extSet, cylinderSet_append_eq_inter (pfx := h) (a := st₁.action) (x := st₁.percept) h_wf h_complete]
          using h₁
      have h₂' :
          traj ∈ cylinderSet h ∩ {traj | traj (historySteps h) = Step.mk st₂.action st₂.percept} := by
        simpa [extSet, cylinderSet_append_eq_inter (pfx := h) (a := st₂.action) (x := st₂.percept) h_wf h_complete]
          using h₂
      have hmk : (Step.mk st₁.action st₁.percept) = Step.mk st₂.action st₂.percept := by
        -- Both sets constrain the same `traj (historySteps h)` value.
        have h1 : Step.mk st₁.action st₁.percept = traj (historySteps h) := by
          simpa using h₁'.2.symm
        have h2 : traj (historySteps h) = Step.mk st₂.action st₂.percept := by
          simpa using h₂'.2
        exact h1.trans h2
      have : st₁ = st₂ := by
        have hη₁ : Step.mk st₁.action st₁.percept = st₁ := by
          cases st₁
          rfl
        have hη₂ : Step.mk st₂.action st₂.percept = st₂ := by
          cases st₂
          rfl
        calc
          st₁ = Step.mk st₁.action st₁.percept := by simp [hη₁]
          _ = Step.mk st₂.action st₂.percept := hmk
          _ = st₂ := hη₂
      exact hne this

    have h_ext_union : (⋃ st : Step, extSet st) = cylinderSet h := by
      ext traj
      constructor
      · intro hmem
        rcases (Set.mem_iUnion.1 hmem) with ⟨st, hst⟩
        have :
            traj ∈ cylinderSet h ∩ {traj | traj (historySteps h) = Step.mk st.action st.percept} := by
          simpa [extSet, cylinderSet_append_eq_inter (pfx := h) (a := st.action) (x := st.percept) h_wf h_complete]
            using hst
        exact this.1
      · intro hmem
        refine (Set.mem_iUnion).2 ?_
        refine ⟨traj (historySteps h), ?_⟩
        have :
            traj ∈ cylinderSet h ∩ {traj | traj (historySteps h) = traj (historySteps h)} := by
          exact ⟨hmem, by simp⟩
        simpa [extSet, cylinderSet_append_eq_inter (pfx := h)
          (a := (traj (historySteps h)).action) (x := (traj (historySteps h)).percept) h_wf h_complete] using this

    have h_ext_integrable :
        ∀ st, IntegrableOn (posteriorReal O M prior envs ν_idx (t + 1)) (extSet st) μξ := by
      intro _st
      exact (posteriorReal_integrable (O := O) (M := M) (prior := prior) (envs := envs) (π := π)
        (h_stoch := h_stoch) (ν_idx := ν_idx) (t + 1)).integrableOn

    have h_ext_int :
        ∀ st,
          (∫ ω in extSet st, posteriorReal O M prior envs ν_idx (t + 1) ω ∂μξ) =
            (prior.weight ν_idx).toReal * μν.real (extSet st) := by
      intro st
      set h' : History := h ++ [HistElem.act st.action, HistElem.per st.percept]
      have h'_wf : h'.wellFormed := by
        simpa [h'] using wellFormed_append_pair' h st.action st.percept h_wf h_complete
      have h'_complete : Even h'.length := by
        have : h'.length = h.length + 2 := by simp [h']
        simpa [this] using h_complete.add (by decide : Even 2)
      have h'_meas : MeasurableSet (extSet st) := h_ext_meas st
      have hEqOn_succ :
          Set.EqOn (posteriorReal O M prior envs ν_idx (t + 1))
            (fun _ => (bayesianPosteriorWeight O M prior envs ν_idx h').toReal) (extSet st) := by
        intro traj htraj
        have hstep : trajectoryToHistory traj (t + 1) = h' := by
          have ht : trajectoryToHistory traj (historySteps h') = h' := by
            have : traj ∈ cylinderSetAt (historySteps h') h' := by
              have : traj ∈ cylinderSet h' := by
                simpa [extSet, h'] using htraj
              simpa [cylinderSet_eq_cylinderSetAt' h' h'_wf] using this
            simpa [cylinderSetAt] using this
          have hsteps' : historySteps h' = t + 1 := by
            have h_len_div : h.length / 2 = t := by
              simpa [historySteps] using h_steps
            -- `historySteps` is `length / 2`, and `h'` appends two elements.
            simp [h', historySteps, List.length_append, h_len_div, Nat.add_div_right, show 0 < 2 by norm_num]
          simpa [hsteps'] using ht
        simp [posteriorReal, posteriorWeight, h', hstep]
      have hInt_succ :
          (∫ ω in extSet st, posteriorReal O M prior envs ν_idx (t + 1) ω ∂μξ) =
            μξ.real (extSet st) * (bayesianPosteriorWeight O M prior envs ν_idx h').toReal := by
        rw [MeasureTheory.setIntegral_congr_fun h'_meas hEqOn_succ]
        simp [smul_eq_mul]
      have hCancel_succ :
          bayesianPosteriorWeight O M prior envs ν_idx h' * μξ (cylinderSet h') =
            prior.weight ν_idx * μν (cylinderSet h') := by
        simpa [μξ, μν, ξ] using
          (bayesianPosteriorWeight_mul_mixtureMeasureWithPolicy_cylinderSet (O := O) (M := M) (prior := prior)
            (envs := envs) (π := π) (h_stoch := h_stoch) (ν_idx := ν_idx) (h := h') (h_wf := h'_wf)
            (h_complete := h'_complete))
      have hCancel_succ_real := congrArg ENNReal.toReal hCancel_succ
      -- Convert to the desired `prior.toReal * μν.real` form.
      calc
        (∫ ω in extSet st, posteriorReal O M prior envs ν_idx (t + 1) ω ∂μξ)
            = μξ.real (extSet st) * (bayesianPosteriorWeight O M prior envs ν_idx h').toReal := hInt_succ
        _ = ((bayesianPosteriorWeight O M prior envs ν_idx h') * μξ (cylinderSet h')).toReal := by
              simp [MeasureTheory.measureReal_def, ENNReal.toReal_mul, h', extSet, mul_comm]
        _ = ((prior.weight ν_idx) * μν (cylinderSet h')).toReal := by
              simpa [h', extSet] using hCancel_succ_real
        _ = (prior.weight ν_idx).toReal * μν.real (extSet st) := by
              simp [MeasureTheory.measureReal_def, ENNReal.toReal_mul, h', extSet]

    have hInt_succ_total :
        (∫ ω in atom p, posteriorReal O M prior envs ν_idx (t + 1) ω ∂μξ) =
          (prior.weight ν_idx).toReal * μν.real (atom p) := by
      -- Rewrite `atom p` as a cylinder and decompose into extensions.
      have h_decomp :
          (∫ ω in cylinderSet h, posteriorReal O M prior envs ν_idx (t + 1) ω ∂μξ) =
            ∑ st : Step, ∫ ω in extSet st, posteriorReal O M prior envs ν_idx (t + 1) ω ∂μξ := by
        rw [← h_ext_union]
        exact MeasureTheory.integral_iUnion_fintype (μ := μξ)
          (fun st => h_ext_meas st) h_ext_disj h_ext_integrable
      -- Convert each summand via `h_ext_int`, then collapse the measures using `measureReal_iUnion_fintype`.
      have hμν_sum :
          (∑ st : Step, μν.real (extSet st)) = μν.real (cylinderSet h) := by
        haveI : MeasureTheory.IsProbabilityMeasure μν :=
          environmentMeasureWithPolicy_isProbability (μ := envs ν_idx) (π := π) (h_stoch := h_stoch ν_idx)
        haveI : MeasureTheory.IsFiniteMeasure μν := inferInstance
        have h_ne_top : ∀ st : Step, μν (extSet st) ≠ (⊤ : ℝ≥0∞) := by
          intro st
          exact measure_ne_top μν (extSet st)
        have hμν_eq :=
          MeasureTheory.measureReal_iUnion_fintype (μ := μν) (f := extSet) h_ext_disj h_ext_meas (h' := h_ne_top)
        simpa [h_ext_union] using hμν_eq.symm
      calc
        (∫ ω in atom p, posteriorReal O M prior envs ν_idx (t + 1) ω ∂μξ)
            = ∫ ω in cylinderSet h, posteriorReal O M prior envs ν_idx (t + 1) ω ∂μξ := by
                  simp [h_atom_cyl]
        _ = ∑ st : Step, ∫ ω in extSet st, posteriorReal O M prior envs ν_idx (t + 1) ω ∂μξ := h_decomp
        _ = ∑ st : Step, (prior.weight ν_idx).toReal * μν.real (extSet st) := by
              refine Finset.sum_congr rfl ?_
              intro st _hst
              simpa using h_ext_int st
        _ = (prior.weight ν_idx).toReal * ∑ st : Step, μν.real (extSet st) := by
              -- factor out the constant
              simpa using
                (Finset.mul_sum (s := (Finset.univ : Finset Step))
                  (a := (prior.weight ν_idx).toReal) (f := fun st => μν.real (extSet st))).symm
        _ = (prior.weight ν_idx).toReal * μν.real (cylinderSet h) := by
              simp [hμν_sum]
        _ = (prior.weight ν_idx).toReal * μν.real (atom p) := by
              simp [h_atom_cyl]

    -- Combine both sides on this atom.
    simp [hInt_t', hInt_succ_total]

  -- Now sum the atom equalities over the finite decomposition of `truncate t ⁻¹' w`.
  rw [h_union]
  -- Convert both integrals to finite sums over atoms.
  rw [MeasureTheory.integral_biUnion_finset (μ := μξ) (f := posteriorReal O M prior envs ν_idx t)
        (t := W) (s := fun p => atom p) h_atom_meas h_atom_disj h_integrable_t]
  rw [MeasureTheory.integral_biUnion_finset (μ := μξ) (f := posteriorReal O M prior envs ν_idx (t + 1))
        (t := W) (s := fun p => atom p) h_atom_meas h_atom_disj h_integrable_succ]
  refine Finset.sum_congr rfl ?_
  intro p hpW
  exact h_atom_eq p hpW

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale
