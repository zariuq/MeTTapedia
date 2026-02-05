import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Topology.Algebra.Module.Basic
import Mettapedia.Logic.MarkovDeFinettiHardRepresentability
import Mettapedia.Logic.MarkovDeFinettiHardEmpirical
import Mettapedia.Logic.MarkovDeFinettiRecurrence
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti (Hard Direction) — Finite Moment Functional Setup

This file sets up the **finite constraint functional** for the Markov de Finetti hard direction.
It does **not** solve the Diaconis–Freedman core; instead it packages the finite constraints as
an explicit continuous map into a finite product space, so the remaining existence step can be
stated cleanly.

The goal is to reduce `finite_constraints_nonempty` to a single statement:

> the constraint vector `wμ` lies in the image of the continuous map
>   `π ↦ (∫ Wnn n e dπ)` for the finite set of indices `u`.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

open MeasureTheory

namespace MarkovDeFinettiHard

variable {k : ℕ}

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence

/-! ## Finite constraint vectors -/

/-- The constraint vector `wμ` restricted to a finite index set `u`. -/
def constraintVec (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    (Subtype (fun p : Nat × MarkovState k => p ∈ (u : Set (Nat × MarkovState k))) → ENNReal) :=
  fun p => wμ (k := k) μ p.1.1 p.1.2

/-- The evaluation vector of a candidate mixing measure `π` on the same finite index set `u`. -/
def evalVec (_μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    ProbabilityMeasure (MarkovParam k) →
      (Subtype (fun p : Nat × MarkovState k => p ∈ (u : Set (Nat × MarkovState k))) → ENNReal) :=
  fun π p => ∫⁻ θ, Wnn (k := k) p.1.1 p.1.2 θ ∂π

lemma evalVec_apply (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k))
    (π : ProbabilityMeasure (MarkovParam k))
    (p : Subtype (fun p : Nat × MarkovState k => p ∈ (u : Set (Nat × MarkovState k)))) :
    evalVec (k := k) μ u π p = ∫⁻ θ, Wnn (k := k) p.1.1 p.1.2 θ ∂π := rfl

/-! ## Constraint sets vs evaluation vectors -/

lemma mem_constraintSet_iff_evalVec_eq
    (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k))
    (π : ProbabilityMeasure (MarkovParam k)) :
    π ∈ (⋂ p ∈ u, constraintSet (k := k) μ p.1 p.2)
      ↔ evalVec (k := k) μ u π = constraintVec (k := k) μ u := by
  classical
  constructor
  · intro h
    funext p
    have hp : π ∈ constraintSet (k := k) μ p.1.1 p.1.2 := by
      have h' : π ∈ ⋂ p ∈ u, constraintSet (k := k) μ p.1 p.2 := h
      exact Set.mem_iInter₂.1 h' p.1 p.property
    simpa [constraintSet, evalVec, constraintVec] using hp.symm
  · intro h
    -- Show membership in every constraint set.
    refine Set.mem_iInter₂.2 ?_
    intro p hp
    have := congrArg (fun f => f ⟨p, hp⟩) h
    -- Expand definitions.
    simpa [constraintSet, evalVec, constraintVec] using this.symm

lemma finite_constraints_nonempty_iff
    (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    (⋂ p ∈ u, constraintSet (k := k) μ p.1 p.2).Nonempty
      ↔ ∃ π : ProbabilityMeasure (MarkovParam k),
          evalVec (k := k) μ u π = constraintVec (k := k) μ u := by
  constructor
  · intro h
    rcases h with ⟨π, hπ⟩
    refine ⟨π, ?_⟩
    exact (mem_constraintSet_iff_evalVec_eq (k := k) μ u π).1 hπ
  · rintro ⟨π, hπ⟩
    refine ⟨π, ?_⟩
    exact (mem_constraintSet_iff_evalVec_eq (k := k) μ u π).2 hπ

/-! ## Continuity of the finite evaluation map -/

lemma continuous_evalVec (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    Continuous (evalVec (k := k) μ u) := by
  classical
  -- Continuity of a finite product of continuous maps.
  -- `fun π => (fun p => ∫ Wnn p dπ)` is continuous because each component is continuous.
  -- We use `continuous_pi` for the finite index set `u`.
  refine continuous_pi ?_
  intro p
  -- Each component is the `Wnn`-integral, which is continuous on `ProbabilityMeasure`.
  simpa [evalVec] using (continuous_lintegral_Wnn (k := k) p.1.1 p.1.2)

/-! ## Moment polytope and compactness -/

/-- The finite **moment polytope** for index set `u`: image of `evalVec`. -/
def momentPolytope (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    Set (Subtype (fun p : Nat × MarkovState k => p ∈ (u : Set (Nat × MarkovState k))) → ENNReal) :=
  Set.range (evalVec (k := k) μ u)

lemma constraintVec_mem_momentPolytope_iff
    (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    constraintVec (k := k) μ u ∈ momentPolytope (k := k) μ u
      ↔ ∃ π : ProbabilityMeasure (MarkovParam k),
          evalVec (k := k) μ u π = constraintVec (k := k) μ u := by
  rfl

lemma isCompact_momentPolytope (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    IsCompact (momentPolytope (k := k) μ u) := by
  -- Continuous image of a compact space.
  have hcont : Continuous (evalVec (k := k) μ u) := continuous_evalVec (k := k) μ u
  have hcompact : IsCompact (Set.univ : Set (ProbabilityMeasure (MarkovParam k))) := isCompact_univ
  -- `Set.range` is the image of `Set.univ`.
  simpa [momentPolytope, Set.image_univ] using hcompact.image hcont

/-! ## Empirical approximation sequence (structure only) -/

/-- Empirical evaluation vector at horizon `n`, using the Laplace-smoothed empirical parameters. -/
def empiricalVec (hk : 0 < k) (μ : PrefixMeasure (Fin k))
    (u : Finset (Nat × MarkovState k)) (n : ℕ) :
    (Subtype (fun p : Nat × MarkovState k => p ∈ (u : Set (Nat × MarkovState k))) → ENNReal) :=
  evalVec (k := k) μ u (empiricalMeasure (k := k) hk μ n)

/-! ### Expanding empirical `lintegral`s into explicit mixtures over evidence states -/

lemma measurable_empiricalParam (hk : 0 < k) :
    Measurable (empiricalParam (k := k) hk : MarkovState k → MarkovParam k) := by
  -- `MarkovState k` has the discrete sigma-algebra in `MarkovDeFinettiHardEmpirical.lean`,
  -- so every function out of it is measurable.
  simp [Measurable]

/-- An empirical `Wnn`-integral is a `tsum` over evidence states. -/
lemma lintegral_Wnn_empiricalMeasure_eq_tsum
    (hk : 0 < k) (μ : PrefixMeasure (Fin k)) (N n : ℕ) (e : MarkovState k) :
    (∫⁻ θ, Wnn (k := k) n e θ ∂(empiricalMeasure (k := k) hk μ N)) =
      ∑' s : MarkovState k,
        (Wnn (k := k) n e (empiricalParam (k := k) hk s) : ENNReal) *
          statePMF (k := k) μ N s := by
  classical
  -- Unfold the underlying discrete measure and pull back along the `PMF.map`.
  have hmeas :
      Measurable (empiricalParam (k := k) hk : MarkovState k → MarkovParam k) :=
    measurable_empiricalParam (k := k) hk
  have hmap :
      (empiricalPMF (k := k) hk μ N).toMeasure =
        (statePMF (k := k) μ N).toMeasure.map (empiricalParam (k := k) hk) := by
    simpa [empiricalPMF] using
      (PMF.toMeasure_map (p := statePMF (k := k) μ N) (f := empiricalParam (k := k) hk) hmeas).symm
  have hW_meas :
      Measurable (fun θ : MarkovParam k => (Wnn (k := k) n e θ : ENNReal)) := by
    have hcont : Continuous (fun θ : MarkovParam k => Wnn (k := k) n e θ) :=
      continuous_Wnn (k := k) n e
    exact measurable_coe_nnreal_ennreal.comp hcont.measurable
  -- Rewrite `empiricalMeasure` as a mapped `statePMF` measure, then expand the discrete integral.
  -- The mapping step uses `lintegral_map`; the discrete expansion uses `lintegral_countable'`.
  -- Finally, `PMF.toMeasure` agrees with the PMF weights on singletons.
  have hsingleton (s : MarkovState k) :
      (statePMF (k := k) μ N).toMeasure ({s} : Set (MarkovState k)) =
        statePMF (k := k) μ N s := by
    simpa using
      (PMF.toMeasure_apply_singleton (p := statePMF (k := k) μ N) s (by simp))
  -- Start from the LHS and unfold to the PMF-to-measure form.
  change (∫⁻ θ, Wnn (k := k) n e θ ∂((empiricalPMF (k := k) hk μ N).toMeasure)) = _
  rw [hmap]
  -- Pull back the integral along the measurable map `empiricalParam`.
  rw [MeasureTheory.lintegral_map hW_meas hmeas]
  -- Now expand the integral on the countable discrete type `MarkovState k`.
  rw [MeasureTheory.lintegral_countable' (μ := (statePMF (k := k) μ N).toMeasure)
    (f := fun s : MarkovState k => (Wnn (k := k) n e (empiricalParam (k := k) hk s) : ENNReal))]
  -- Simplify singleton masses.
  refine tsum_congr ?_
  intro s
  simp [hsingleton s]

lemma lintegral_Wnn_empiricalMeasure_eq_sum
    (hk : 0 < k) (μ : PrefixMeasure (Fin k)) (N n : ℕ) (e : MarkovState k) :
    (∫⁻ θ, Wnn (k := k) n e θ ∂(empiricalMeasure (k := k) hk μ N)) =
      (stateFinset k N).sum (fun s =>
        (Wnn (k := k) n e (empiricalParam (k := k) hk s) : ENNReal) *
          statePMF (k := k) μ N s) := by
  classical
  -- Start from the `tsum` form and restrict to the finite support of `statePMF`.
  have htsum₀ :=
    lintegral_Wnn_empiricalMeasure_eq_tsum (k := k) hk (μ := μ) (N := N) (n := n) (e := e)
  -- Work with the simp-normal form (using `W` and `wμ`) to avoid fighting simp later.
  have htsum :
      (∫⁻ θ, W (k := k) n e θ ∂(empiricalMeasure (k := k) hk μ N)) =
        ∑' s : MarkovState k,
          W (k := k) n e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s := by
    simpa [statePMF_apply, coe_Wnn, mul_assoc] using htsum₀
  -- Outside `stateFinset k N`, the PMF weight is `0`, so the `tsum` is a finite sum.
  have hzero :
      ∀ s : MarkovState k,
        s ∉ stateFinset k N →
          W (k := k) n e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s = 0 := by
    intro s hs
    have hwt : wμ (k := k) μ N s = 0 :=
      wμ_eq_zero_of_not_mem_stateFinset (k := k) (μ := μ) (n := N) (e := s) hs
    simp [hwt]
  -- Rewrite the `tsum` as a `Finset.sum`.
  have hsum :
      (∑' s : MarkovState k,
          W (k := k) n e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s) =
        (stateFinset k N).sum (fun s =>
          W (k := k) n e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s) := by
    simpa using (tsum_eq_sum (s := stateFinset k N) hzero)
  -- Convert back to `Wnn`/`statePMF` in the final statement.
  -- (This is a definitional rewrite using `coe_Wnn` and `statePMF_apply`.)
  have :
      (∫⁻ θ, W (k := k) n e θ ∂(empiricalMeasure (k := k) hk μ N)) =
        (stateFinset k N).sum (fun s =>
          W (k := k) n e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s) := by
    simpa [hsum] using htsum
  simpa [statePMF_apply, coe_Wnn, mul_assoc] using this

/-! ## Horizon-0 computations -/

lemma prefixState_zero (N : ℕ) (xs : Traj k N) :
    prefixState (k := k) (n := 0) (N := N) (Nat.zero_le N) xs =
      ⟨xs 0, (0 : TransCounts k), xs 0⟩ := by
  classical
  unfold prefixState stateOfTraj trajPrefix
  ext <;> simp [MarkovExchangeabilityBridge.countsOfFn, MarkovExchangeability.transCount]

lemma countsOfFn_zero (xs : Traj k 0) : MarkovExchangeabilityBridge.countsOfFn (k := k) xs = (0 : TransCounts k) := by
  ext a b
  simp [MarkovExchangeabilityBridge.countsOfFn, MarkovExchangeability.transCount]

lemma markovState_counts_zero_of_mem_stateFinset0 (e : MarkovState k) (he0 : e ∈ stateFinset k 0) :
    e.counts = (0 : TransCounts k) := by
  classical
  rcases Finset.mem_image.1 he0 with ⟨xs0, hx0, hx0e⟩
  have hcounts : MarkovExchangeabilityBridge.countsOfFn (k := k) xs0 = e.counts := by
    simpa [stateOfTraj] using congrArg MarkovState.counts hx0e
  simpa [countsOfFn_zero (k := k) xs0] using hcounts.symm

lemma markovState_last_eq_start_of_mem_stateFinset0 (e : MarkovState k) (he0 : e ∈ stateFinset k 0) :
    e.last = e.start := by
  classical
  rcases Finset.mem_image.1 he0 with ⟨xs0, hx0, hx0e⟩
  have hstart : xs0 0 = e.start := by
    simpa [stateOfTraj] using congrArg MarkovState.start hx0e
  have hlast : xs0 (Fin.last 0) = e.last := by
    simpa [stateOfTraj] using congrArg MarkovState.last hx0e
  have hse : e.start = e.last := by
    simpa [hstart] using hlast
  exact hse.symm

lemma initProb_empiricalParam (hk : 0 < k) (s : MarkovState k) (a : Fin k) :
    initProb (k := k) (empiricalParam (k := k) hk s) a = (if a = s.start then 1 else 0) := by
  classical
  by_cases h : a = s.start
  · subst h
    have hm : s.start ∈ Set.singleton s.start := Set.mem_singleton _
    simp [initProb, empiricalParam, Set.indicator, hm]
  · have hm : s.start ∉ Set.singleton a := by
        intro hs
        have : s.start = a := hs
        exact h this.symm
    simp [initProb, empiricalParam, Set.indicator, hm, h]

lemma W_zero_empiricalParam_eq_indicator
    (hk : 0 < k) (e s : MarkovState k) (he0 : e ∈ stateFinset k 0) :
    W (k := k) 0 e (empiricalParam (k := k) hk s) = (if s.start = e.start then 1 else 0) := by
  classical
  -- For n=0, the fiber has exactly one trajectory with start = e.start.
  let xs0 : Traj k 0 := fun _ => e.start
  have hxs0 : stateOfTraj (k := k) xs0 = e := by
    have he_counts : e.counts = (0 : TransCounts k) :=
      markovState_counts_zero_of_mem_stateFinset0 (k := k) e he0
    have he_last : e.last = e.start :=
      markovState_last_eq_start_of_mem_stateFinset0 (k := k) e he0
    ext <;> simp [stateOfTraj, xs0, he_counts, he_last, MarkovExchangeabilityBridge.countsOfFn,
      MarkovExchangeability.transCount]
  -- show filter set is singleton {xs0}
  have hfilter :
      (trajFinset k 0).filter (fun xs => stateOfTraj (k := k) xs = e) = {xs0} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    refine ⟨?mem, ?uniq⟩
    · -- xs0 is in filter
      simp [trajFinset, hxs0]
    · intro xs hx
      -- show xs = xs0
      have hx' : stateOfTraj (k := k) xs = e := (Finset.mem_filter.1 hx).2
      -- compare starts
      have hxstart : xs 0 = e.start := by
        simpa [stateOfTraj] using congrArg MarkovState.start hx'
      -- Traj k 0 has only one index
      funext i
      have : i = 0 := Fin.eq_zero i
      simp [xs0, this, hxstart]
  -- reduce to wordProb of [e.start]
  have hsum :
      W (k := k) 0 e (empiricalParam (k := k) hk s) =
        wordProb (k := k) (empiricalParam (k := k) hk s) [e.start] := by
    simp [W, hfilter, trajToList, xs0]
  -- compute wordProb for length-1 list
  have hword :
      wordProb (k := k) (empiricalParam (k := k) hk s) [e.start] =
        (initProb (k := k) (empiricalParam (k := k) hk s) e.start : ENNReal) := by
    simp [wordProb, wordProbNN, wordProbAux]
  -- combine
  by_cases hstart : s.start = e.start
  · simp [hsum, hword, initProb_empiricalParam, hstart]
  · have h' : ¬ e.start = s.start := by
        intro hs
        exact hstart (hs.symm)
    simp [hsum, hword, initProb_empiricalParam, hstart, h']

lemma prefixCoeff_zero_eq_indicator
    (N : ℕ) (e s : MarkovState k) (he0 : e ∈ stateFinset k 0) (hs : s ∈ stateFinset k N) :
    prefixCoeff (k := k) (h := Nat.zero_le N) e s = (if s.start = e.start then 1 else 0) := by
  classical
  have hcard : (fiber k N s).card ≠ 0 :=
    fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := s) hs
  -- Express e in the canonical horizon-0 form.
  have he_counts : e.counts = (0 : TransCounts k) :=
    markovState_counts_zero_of_mem_stateFinset0 (k := k) e he0
  have he_last : e.last = e.start :=
    markovState_last_eq_start_of_mem_stateFinset0 (k := k) e he0
  have he_form : e = ⟨e.start, (0 : TransCounts k), e.start⟩ := by
    ext <;> simp [he_counts, he_last]
  by_cases hstart : s.start = e.start
  · -- prefixFiber = fiber
    have hprefix :
        prefixFiber (k := k) (h := Nat.zero_le N) e s = fiber k N s := by
      ext xs
      constructor
      · intro hx
        exact (Finset.mem_filter.1 hx).1
      · intro hx
        -- show prefixState 0 xs = e
        have hxstate : stateOfTraj (k := k) xs = s := (Finset.mem_filter.1 hx).2
        have hxs0 : xs 0 = s.start := by
          simpa [stateOfTraj] using congrArg MarkovState.start hxstate
        have hpref :
            prefixState (k := k) (n := 0) (N := N) (Nat.zero_le N) xs =
              ⟨xs 0, (0 : TransCounts k), xs 0⟩ :=
          prefixState_zero (k := k) (N := N) xs
        have : prefixState (k := k) (n := 0) (N := N) (Nat.zero_le N) xs = e := by
          rw [hpref, he_form]
          ext <;> simp [hxs0, hstart]
        exact Finset.mem_filter.2 ⟨hx, this⟩
    have hcard' : ((fiber k N s).card : ENNReal) ≠ 0 := by
      exact_mod_cast hcard
    have htop : ((fiber k N s).card : ENNReal) ≠ ⊤ := by
      simp
    have hcalc :
        prefixCoeff (k := k) (h := Nat.zero_le N) e s = 1 := by
      calc
        prefixCoeff (k := k) (h := Nat.zero_le N) e s =
            ((prefixFiber (k := k) (h := Nat.zero_le N) e s).card : ENNReal) /
              ((fiber k N s).card : ENNReal) := by
                simp [prefixCoeff, hcard]
        _ = ((fiber k N s).card : ENNReal) / ((fiber k N s).card : ENNReal) := by
              simp [hprefix]
        _ = 1 := by
              simpa using (ENNReal.div_self hcard' htop)
    simpa [hstart] using hcalc
  · -- prefixFiber = ∅
    have hprefix :
        prefixFiber (k := k) (h := Nat.zero_le N) e s = ∅ := by
      ext xs
      constructor
      · intro hx
        have hxstate : stateOfTraj (k := k) xs = s := (Finset.mem_filter.1 (Finset.mem_filter.1 hx).1).2
        have hxs0 : xs 0 = s.start := by
          simpa [stateOfTraj] using congrArg MarkovState.start hxstate
        have hpref :
            prefixState (k := k) (n := 0) (N := N) (Nat.zero_le N) xs =
              ⟨xs 0, (0 : TransCounts k), xs 0⟩ :=
          prefixState_zero (k := k) (N := N) xs
        have : prefixState (k := k) (n := 0) (N := N) (Nat.zero_le N) xs = e := (Finset.mem_filter.1 hx).2
        -- contradiction with start mismatch
        have hstartEq : (prefixState (k := k) (n := 0) (N := N) (Nat.zero_le N) xs).start = e.start :=
          congrArg MarkovState.start this
        have : xs 0 = e.start := by
          simpa [hpref] using hstartEq
        exact (hstart (by simpa [hxs0] using this)).elim
      · intro hx
        simp at hx
    have hcalc :
        prefixCoeff (k := k) (h := Nat.zero_le N) e s = 0 := by
      calc
        prefixCoeff (k := k) (h := Nat.zero_le N) e s =
            ((prefixFiber (k := k) (h := Nat.zero_le N) e s).card : ENNReal) /
              ((fiber k N s).card : ENNReal) := by
                simp [prefixCoeff, hcard]
        _ = 0 := by
              simp [hprefix]
    simpa [hstart] using hcalc

/-!
The core analytic step is a per-coordinate convergence statement.  We isolate it as a single lemma
so that higher-level compactness arguments remain sorry-free.

This is the genuine Diaconis–Freedman content: empirical evidence mixtures (built from the horizon
`N` evidence distribution) approximate the true evidence weights for any fixed `n,e`.
-/
/-!
## Curriculum breadcrumbs for the hard step

The succ-case proof should follow this pattern:

1. Use `lintegral_Wnn_empiricalMeasure_eq_sum` to rewrite the LHS as a finite sum
   over `stateFinset k N` with coefficients `wμ μ N s`.
2. Use the tower identity for evidence polynomials:
   `W_eq_sum_prefixCoeff_mul_W` (already proven in `MarkovDeFinettiEvidenceBasis.lean`).
3. Use the tower identity for evidence weights:
   `wμ_eq_sum_prefixCoeff_mul_wμ` (same file).
4. Prove the approximation lemma (Diaconis–Freedman core):
   empirical parameters map `s ↦ empiricalParam s` makes
   `W (n+1) e (empiricalParam s)` close to `prefixCoeff e s` uniformly as `N → ∞`
   under `MarkovRecurrentPrefixMeasure`.
5. Conclude with a dominated/finite sum convergence argument.

Everything else is already wired into the moment-polytope framework.
-/

theorem empiricalWnn_tendsto_wμ_succ
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (n : ℕ) (e : MarkovState k) :
    Filter.Tendsto
        (fun N =>
          ∫⁻ θ, Wnn (k := k) (Nat.succ n) e θ ∂(empiricalMeasure (k := k) hk μ N))
        Filter.atTop
        (nhds (wμ (k := k) μ (Nat.succ n) e)) := by
  -- Step 1: empirical integral as a finite sum over evidence states.
  have hsum :
      ∀ N : ℕ,
        (∫⁻ θ, Wnn (k := k) (Nat.succ n) e θ ∂(empiricalMeasure (k := k) hk μ N)) =
          ∑ s ∈ stateFinset k N,
            W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s := by
    intro N
    simpa using
      (lintegral_Wnn_empiricalMeasure_eq_sum (k := k) hk (μ := μ) (N := N)
        (n := Nat.succ n) (e := e))

  -- Step 2: tower identity for `wμ (n+1) e` (for large `N`).
  -- For every `N ≥ n+1`,
  --   wμ (n+1) e = ∑ s∈stateFinset k N, prefixCoeff (h := hN) e s * wμ N s.
  -- (This is `wμ_eq_sum_prefixCoeff_mul_wμ`.)

  -- Step 3: weighted‑difference form (the approximation lemma).
  -- Define the weighted real difference, guarded by `Nat.succ n ≤ N`.
  let weightedDiff : ℕ → ℝ :=
    fun N =>
      if hN : Nat.succ n ≤ N then
        ∑ s ∈ stateFinset k N,
          ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
            - (prefixCoeff (k := k) (h := hN) e s).toReal) *
            (wμ (k := k) μ N s).toReal
      else
        0

  -- TODO (Diaconis–Freedman 1980): show `weightedDiff N → 0` as `N → ∞`
  -- under `MarkovRecurrentPrefixMeasure`. This is the genuine approximation estimate:
  --   W (n+1) e (empiricalParam s) → prefixCoeff e s in weighted sum.
  have happrox : Filter.Tendsto weightedDiff Filter.atTop (nhds 0) := by
    sorry

  -- Step 4: conclude the original `ENNReal` convergence from `happrox`
  -- using the rewrite in Step 1 and the tower identity in Step 2.
  -- (Conversion from ENNReal to ℝ is routine once the approximation is established.)
  sorry

theorem empiricalWnn_tendsto_wμ
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (n : ℕ) (e : MarkovState k) :
    Filter.Tendsto
        (fun N =>
          ∫⁻ θ, Wnn (k := k) n e θ ∂(empiricalMeasure (k := k) hk μ N))
        Filter.atTop
        (nhds (wμ (k := k) μ n e)) := by
  classical
  -- TODO (Diaconis–Freedman 1980): This is the single remaining hard lemma in the Markov hard
  -- direction. Everything else (moment polytope, compactness, closed constraints) is already
  -- wired so that proving this lemma completes `markovDeFinetti_hard`.
  --
  -- Until this lemma is proven, all downstream results depending on Markov de Finetti should
  -- treat this as the *only* gap.
  cases n with
  | zero =>
      -- Show the sequence is constant in `N`.
      have hconst :
          ∀ N : ℕ,
            (∫⁻ θ, Wnn (k := k) 0 e θ ∂(empiricalMeasure (k := k) hk μ N)) =
              wμ (k := k) μ 0 e := by
        intro N
        -- Expand the empirical integral into a finite sum over evidence states at horizon `N`.
        have hsum :=
          lintegral_Wnn_empiricalMeasure_eq_sum (k := k) hk (μ := μ) (N := N) (n := 0) (e := e)
        -- Rewrite the empirical sum using `W` instead of `Wnn`.
        have hsum' :
            (∫⁻ θ, W (k := k) 0 e θ ∂(empiricalMeasure (k := k) hk μ N)) =
              (stateFinset k N).sum (fun s =>
                W (k := k) 0 e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s) := by
          simpa [coe_Wnn, statePMF_apply, mul_assoc] using hsum
        -- Now compute the sum using the explicit horizon-0 formulas.
        by_cases he0 : e ∈ stateFinset k 0
        · -- `e` is a valid horizon-0 state.
          have hpoint :
              (stateFinset k N).sum (fun s =>
                  W (k := k) 0 e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s) =
                ∑ s ∈ stateFinset k N, prefixCoeff (k := k) (h := Nat.zero_le N) e s * wμ (k := k) μ N s := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            simp [W_zero_empiricalParam_eq_indicator (k := k) (hk := hk) (e := e) (s := s) he0,
              prefixCoeff_zero_eq_indicator (k := k) (N := N) (e := e) (s := s) he0 hs]
          -- Regroup `wμ 0 e` via the tower identity at horizon `N`.
          have hwμ :=
            wμ_eq_sum_prefixCoeff_mul_wμ (k := k) (μ := μ) hμ (h := Nat.zero_le N) (e := e)
          have hsum'' :
              (∫⁻ θ, W (k := k) 0 e θ ∂(empiricalMeasure (k := k) hk μ N)) =
                ∑ s ∈ stateFinset k N, prefixCoeff (k := k) (h := Nat.zero_le N) e s * wμ (k := k) μ N s := by
            simpa [hpoint] using hsum'
          -- The right-hand side is exactly `wμ 0 e`.
          have hwμ' :
              (∑ s ∈ stateFinset k N, prefixCoeff (k := k) (h := Nat.zero_le N) e s * wμ (k := k) μ N s) =
                wμ (k := k) μ 0 e := by
            simpa using hwμ.symm
          -- finish
          simpa [coe_Wnn] using (hsum''.trans hwμ')
        · -- `e` is not realizable at horizon 0.
          have hW0 :
              (stateFinset k N).sum (fun s =>
                  W (k := k) 0 e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro s hs
            have hfilter :
                (trajFinset k 0).filter (fun xs => stateOfTraj (k := k) xs = e) = ∅ := by
              apply Finset.filter_eq_empty_iff.2
              intro xs hx hx'
              -- show `stateOfTraj xs ≠ e`
              have : e ∈ stateFinset k 0 := by
                simpa [hx'] using (stateOfTraj_mem_stateFinset (k := k) (xs := xs))
              exact he0 this
            simp [W, hfilter]
          have hw0 : wμ (k := k) μ 0 e = 0 :=
            wμ_eq_zero_of_not_mem_stateFinset (k := k) (μ := μ) (n := 0) (e := e) he0
          calc
            (∫⁻ θ, Wnn (k := k) 0 e θ ∂(empiricalMeasure (k := k) hk μ N))
                = (∫⁻ θ, W (k := k) 0 e θ ∂(empiricalMeasure (k := k) hk μ N)) := by
                    simp [coe_Wnn]
            _ = 0 := by simpa [hW0] using hsum'
            _ = wμ (k := k) μ 0 e := by simp [hw0]
      -- Now use `hconst` to conclude.
      have hconst_fun :
          (fun N : ℕ =>
              ∫⁻ θ, Wnn (k := k) 0 e θ ∂(empiricalMeasure (k := k) hk μ N)) =
            (fun _ : ℕ => wμ (k := k) μ 0 e) := by
        funext N
        exact hconst N
      rw [hconst_fun]
      exact (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => wμ (k := k) μ 0 e) Filter.atTop (nhds (wμ (k := k) μ 0 e)))
  | succ n =>
      -- Defer the genuine Diaconis–Freedman core to a dedicated lemma.
      exact empiricalWnn_tendsto_wμ_succ (k := k) (hk := hk) (μ := μ) hμ hrec n e
  /- Old (broken) proof attempt kept temporarily while we refactor:
  -- The `n = 0` case is exact: both sides reduce to the distribution of the initial state.
  -- The genuinely hard Diaconis–Freedman content starts at `n+1`.
  cases n with
  | zero =>
      -- Show the sequence is constant in `N`.
      have hconst :
          ∀ N : ℕ,
            (∫⁻ θ, Wnn (k := k) 0 e θ ∂(empiricalMeasure (k := k) hk μ N)) =
              wμ (k := k) μ 0 e := by
        intro N
        -- Expand the empirical integral into a finite sum over evidence states at horizon `N`.
        have hsum :=
          lintegral_Wnn_empiricalMeasure_eq_sum (k := k) hk (μ := μ) (N := N) (n := 0) (e := e)
        -- Regroup `wμ 0 e` via the tower identity at horizon `N`.
        have hwμ :=
          wμ_eq_sum_prefixCoeff_mul_wμ (k := k) (μ := μ) hμ (h := Nat.zero_le N) (e := e)
        -- Reduce to showing `W 0 e (empiricalParam s) = prefixCoeff 0≤N e s` for each state `s`.
        -- For `n = 0`, the prefix evidence state is determined by the start symbol.
        -- We work pointwise under the finite sum.
        -- Rewrite the empirical sum using `W` instead of `Wnn`.
        have hsum' :
            (∫⁻ θ, W (k := k) 0 e θ ∂(empiricalMeasure (k := k) hk μ N)) =
              (stateFinset k N).sum (fun s =>
                W (k := k) 0 e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s) := by
          -- `hsum` is already in the `Wnn` / `statePMF` form; unfold those definitions.
          -- Convert `Wnn` to `W` pointwise.
          simpa [coe_Wnn, statePMF_apply, mul_assoc] using hsum
        -- Convert the goal into the `W`-sum form.
        -- We can now use `hwμ` once we show the coefficient equality pointwise.
        -- This is a purely finite, combinatorial computation.
        have hpoint :
            (stateFinset k N).sum (fun s =>
                W (k := k) 0 e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s) =
              ∑ s ∈ stateFinset k N, prefixCoeff (k := k) (h := Nat.zero_le N) e s * wμ (k := k) μ N s := by
          -- Replace each summand using the explicit `n=0` evaluation.
          refine Finset.sum_congr rfl ?_
          intro s hs
          -- In a length-`0` trajectory, the evidence state is determined by the start symbol.
          -- `W 0 e` under `empiricalParam s` is `1` iff the start symbol matches.
          -- The same criterion decides whether `prefixCoeff` is `1` or `0`.
          by_cases he0 : e ∈ stateFinset k 0
          · -- When `e` is a valid horizon-0 state, it must be `⟨e.start, 0, e.start⟩`.
            have hlast : e.last = e.start := by
              -- Any state in `stateFinset k 0` comes from a length-1 trajectory, hence `last = start`.
              rcases Finset.mem_image.1 he0 with ⟨xs, -, rfl⟩
              simp [stateOfTraj]
            have hcounts : e.counts = 0 := by
              rcases Finset.mem_image.1 he0 with ⟨xs, -, rfl⟩
              ext a b
              -- With `n = 0`, there are no transitions.
              simp [stateOfTraj, MarkovExchangeabilityBridge.countsOfFn, MarkovExchangeabilityBridge.transCount]
            have he_form : e = ⟨e.start, (0 : TransCounts k), e.start⟩ := by
              ext <;> simp [hlast, hcounts]
            -- Now compute `W 0 e (empiricalParam s)` explicitly.
            -- There is exactly one length-1 trajectory with state `e`, namely the constant trajectory at `e.start`.
            have hW :
                W (k := k) 0 e (empiricalParam (k := k) hk s) =
                  if s.start = e.start then 1 else 0 := by
              -- Unfold `W` and simplify the finite sum.
              -- The filter picks out the unique trajectory with start `e.start`.
              classical
              subst he_form
              -- `Traj k 0` is `Fin 1 → Fin k`; enumerate by its value at `0`.
              -- `stateOfTraj` for such a trajectory is `⟨a, 0, a⟩`.
              -- Under `empiricalParam s`, `wordProb` of `[a]` is `1` iff `a = s.start`.
              -- All other terms vanish.
              simp [W, empiricalParam, wordProb, wordProbNN, initProb, stepProb, stateOfTraj]
            -- Compute `prefixCoeff` in the `n=0` case: it is `1` iff `s.start = e.start`.
            have hC :
                prefixCoeff (k := k) (h := Nat.zero_le N) e s =
                  if s.start = e.start then 1 else 0 := by
              classical
              -- If `s` is realizable at horizon `N`, its fiber is nonempty, and the prefix state is constant.
              have hsN : s ∈ stateFinset k N := hs
              have hcard : (fiber k N s).card ≠ 0 :=
                fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := s) hsN
              have hcard' : (fiber k N s).card = 0 := by
                exact (hcard rfl).elim
              -- Since `n=0`, `prefixState` depends only on the start symbol; so `prefixFiber` is either
              -- the full fiber or empty.
              by_cases hstart : s.start = e.start
              · -- In this case, every element of the fiber has prefix state `e`.
                have hpf : prefixFiber (k := k) (h := Nat.zero_le N) e s = fiber k N s := by
                  classical
                  ext xs
                  constructor
                  · intro hx
                    exact (Finset.mem_filter.1 hx).1
                  · intro hx
                    refine Finset.mem_filter.2 ?_
                    refine ⟨hx, ?_⟩
                    -- Compute the `0`-prefix evidence state.
                    -- `prefixState` is the evidence of the length-1 prefix, i.e. `⟨start, 0, start⟩`.
                    -- In the fiber, `start = s.start = e.start`.
                    have hxstart : xs 0 = s.start := by
                      have hxst : stateOfTraj (k := k) xs = s := (Finset.mem_filter.1 hx).2
                      simpa [stateOfTraj] using congrArg MarkovState.start hxst
                    -- Conclude `prefixState ... xs = e` by extensionality.
                    ext <;> simp [prefixState, stateOfTraj, hxstart, hstart]
                -- Now `prefixCoeff` is `card(fiber)/card(fiber)=1`.
                simp [prefixCoeff, hcard, hpf, hstart]
              · -- Otherwise the prefix fiber is empty, so the coefficient is `0`.
                have hpf : prefixFiber (k := k) (h := Nat.zero_le N) e s = ∅ := by
                  classical
                  ext xs
                  constructor
                  · intro hx
                    have hxstart : xs 0 = s.start := by
                      have hxst : stateOfTraj (k := k) xs = s := (Finset.mem_filter.1 (Finset.mem_filter.1 hx).1).2
                      simpa [stateOfTraj] using congrArg MarkovState.start hxst
                    -- Contradiction: prefix state's start must be `s.start`, but `e.start` differs.
                    have : prefixState (k := k) (n := 0) (N := N) (Nat.zero_le N) xs ≠ e := by
                      intro hpe
                      have := congrArg MarkovState.start hpe
                      simpa [prefixState, stateOfTraj, hxstart] using this
                    exact (this (Finset.mem_filter.1 hx).2).elim
                  · intro hx
                    exact (Finset.notMem_empty xs hx).elim
                simp [prefixCoeff, hcard, hpf, hstart]
            -- Combine the explicit computations.
            simp [hW, hC]
          · -- If `e` is not a valid horizon-0 state, both `wμ 0 e` and `W 0 e` are zero.
            have hw0 : wμ (k := k) μ 0 e = 0 :=
              wμ_eq_zero_of_not_mem_stateFinset (k := k) (μ := μ) (n := 0) (e := e) he0
            -- `W 0 e` is also identically zero when the fiber is empty.
            have hW0 : W (k := k) 0 e (empiricalParam (k := k) hk s) = 0 := by
              classical
              -- The filter in `W` is empty since `e` is not realized at horizon `0`.
              -- (Any membership would witness `e ∈ stateFinset k 0`.)
              have : (trajFinset k 0).filter (fun xs => stateOfTraj (k := k) xs = e) = ∅ := by
                classical
                refine Finset.filter_eq_empty_iff.2 ?_
                intro xs hx
                exact he0 (Finset.mem_image.2 ⟨xs, by simp [trajFinset], hx⟩)
              simp [W, this]
            -- The corresponding `prefixCoeff` is also zero by the previous lemma.
            have hC0 : prefixCoeff (k := k) (h := Nat.zero_le N) e s = 0 :=
              prefixCoeff_eq_zero_of_not_mem_stateFinset (k := k) (h := Nat.zero_le N) (e := e) (eN := s) he0
            simp [hW0, hC0]
        -- Finish the constant identity.
        -- Put together `hsum'`, `hpoint`, and the tower identity `hwμ`.
        calc
          (∫⁻ θ, Wnn (k := k) 0 e θ ∂(empiricalMeasure (k := k) hk μ N))
              = (∫⁻ θ, W (k := k) 0 e θ ∂(empiricalMeasure (k := k) hk μ N)) := by
                    simpa [coe_Wnn]
          _ = (stateFinset k N).sum (fun s =>
                W (k := k) 0 e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s) := hsum'
          _ = ∑ s ∈ stateFinset k N, prefixCoeff (k := k) (h := Nat.zero_le N) e s * wμ (k := k) μ N s := hpoint
          _ = wμ (k := k) μ 0 e := by
                simpa [hwμ]
      -- Conclude by `tendsto_const_nhds`.
      have : (fun N =>
          ∫⁻ θ, Wnn (k := k) 0 e θ ∂(empiricalMeasure (k := k) hk μ N))
            = fun _ : ℕ => wμ (k := k) μ 0 e := by
        funext N
        exact hconst N
      simpa [this] using (Filter.tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => wμ (k := k) μ 0 e) Filter.atTop (nhds (wμ (k := k) μ 0 e)))
  | succ n =>
      -- TODO (Diaconis–Freedman 1980): Markov-exchangeable + recurrent implies that the empirical
      -- mixing measures built from horizon-`N` evidence converge on every fixed evidence polynomial.
      --
      -- The helper lemma `lintegral_Wnn_empiricalMeasure_eq_sum` rewrites the LHS as a finite sum:
      --   `∑ s in stateFinset k N, Wnn (n+1) e (empiricalParam s) * wμ μ N s`.
      --
      -- Completing this proof requires a combinatorial / probabilistic estimate relating the
      -- conditional law of a length-`(n+1)` prefix given a horizon-`N` Markov summary to the Markov chain
      -- with (Laplace-smoothed) empirical transitions derived from that summary.
      --
      -- This is the genuine Diaconis–Freedman heart, and is the only remaining missing piece in
      -- the Markov hard direction.
      sorry
  -/

lemma empiricalVec_mem_momentPolytope (hk : 0 < k) (μ : PrefixMeasure (Fin k))
    (u : Finset (Nat × MarkovState k)) (n : ℕ) :
    empiricalVec (k := k) hk μ u n ∈ momentPolytope (k := k) μ u := by
  refine ⟨empiricalMeasure (k := k) hk μ n, rfl⟩

lemma constraintVec_mem_closure_momentPolytope_of_tendsto
    (hk : 0 < k) (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k))
    (hlim :
      Filter.Tendsto (fun n => empiricalVec (k := k) hk μ u n) Filter.atTop
        (nhds (constraintVec (k := k) μ u))) :
    constraintVec (k := k) μ u ∈ closure (momentPolytope (k := k) μ u) := by
  -- If a sequence in a set tends to `x`, then `x` is in the closure.
  refine mem_closure_of_tendsto hlim ?_
  exact Filter.Eventually.of_forall (fun n => empiricalVec_mem_momentPolytope (k := k) hk μ u n)

/-!
The core analytic step: show that the empirical evaluation vectors converge to the constraint
vector. This is the genuine Diaconis–Freedman content for Markov exchangeability.
-/
theorem empiricalVec_tendsto_constraintVec
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (u : Finset (Nat × MarkovState k)) :
    ∃ hk : 0 < k,
      Filter.Tendsto (fun n => empiricalVec (k := k) hk μ u n) Filter.atTop
        (nhds (constraintVec (k := k) μ u)) := by
  classical
  -- `MarkovRecurrentPrefixMeasure` is impossible when `k = 0`, so we can extract `0 < k`.
  have hk : 0 < k := by
    cases k with
    | zero =>
        rcases hrec with ⟨P, hP, -, -⟩
        have huniv : (Set.univ : Set (ℕ → Fin 0)) = ∅ := by
          ext ω
          -- `ℕ → Fin 0` is empty since `Fin 0` is empty and `ℕ` is nonempty.
          haveI : IsEmpty (ℕ → Fin 0) := by infer_instance
          exact (isEmptyElim ω)
        have : (P Set.univ) = 0 := by simp [huniv]
        have : (0 : ENNReal) = 1 := by
          simpa [this] using (hP.measure_univ : P Set.univ = 1)
        exact (zero_ne_one this).elim
    | succ k' =>
        exact Nat.succ_pos k'
  refine ⟨hk, ?_⟩
  -- Convergence in the product space is coordinatewise.
  rw [tendsto_pi_nhds]
  intro p
  -- Reduce to the per-coordinate Diaconis–Freedman convergence lemma.
  simpa [empiricalVec, evalVec, constraintVec] using
    empiricalWnn_tendsto_wμ (k := k) (hk := hk) (μ := μ) hμ hrec p.1.1 p.1.2

/-! ## Affine closure under two-point mixtures (convexity lemma) -/

-- A two-point mixture of probability measures with ENNReal weights.
def mixProb (a b : ENNReal) (h : a + b = 1)
    (pi1 pi2 : ProbabilityMeasure (MarkovParam k)) : ProbabilityMeasure (MarkovParam k) :=
  ⟨a • (pi1 : Measure (MarkovParam k)) + b • (pi2 : Measure (MarkovParam k)), by
      -- Probability measure: total mass is `a + b = 1`.
      have h1 :
          (a • (pi1 : Measure (MarkovParam k)) + b • (pi2 : Measure (MarkovParam k))) Set.univ = 1 := by
        -- Use linearity of measures on `univ`.
        simp [Measure.add_apply, Measure.smul_apply, h]
      exact IsProbabilityMeasure.mk h1⟩

lemma evalVec_mix (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k))
    (a b : ENNReal) (h : a + b = 1)
    (pi1 pi2 : ProbabilityMeasure (MarkovParam k)) :
    evalVec (k := k) μ u (mixProb (k := k) a b h pi1 pi2)
      = fun p => a * evalVec (k := k) μ u pi1 p + b * evalVec (k := k) μ u pi2 p := by
  classical
  funext p
  -- Expand definitions and use linearity of the `lintegral`.
  simp [evalVec, mixProb, lintegral_add_measure, lintegral_smul_measure]

lemma momentPolytope_closed_under_mix
    (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k))
    (a b : ENNReal) (h : a + b = 1)
    {x y :
      Subtype (fun p : Nat × MarkovState k => p ∈ (u : Set (Nat × MarkovState k))) → ENNReal}
    (hx : x ∈ momentPolytope (k := k) μ u)
    (hy : y ∈ momentPolytope (k := k) μ u) :
    (fun p => a * x p + b * y p) ∈ momentPolytope (k := k) μ u := by
  rcases hx with ⟨pi1, rfl⟩
  rcases hy with ⟨pi2, rfl⟩
  refine ⟨mixProb (k := k) a b h pi1 pi2, ?_⟩
  -- Use linearity of `evalVec` under mixtures.
  simp [evalVec_mix (k := k) (μ := μ) (u := u) a b h]

/-! ## Core finite satisfiability lemma (Diaconis–Freedman) -/

/--
The **finite satisfiability core**: for any finite index set `u`, the constraint vector `wμ`
lies in the moment polytope (the image of `evalVec`).

This is the precise finite-dimensional content of the Diaconis–Freedman hard direction.
It is isolated here as a single lemma so the rest of the proof can proceed by compactness.
-/
theorem constraintVec_mem_momentPolytope
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (u : Finset (Nat × MarkovState k)) :
    constraintVec (k := k) μ u ∈ momentPolytope (k := k) μ u := by
  -- Reduce to the empirical approximation limit + closedness of the moment polytope.
  rcases empiricalVec_tendsto_constraintVec (k := k) (μ := μ) hμ hrec u with ⟨hk, hlim⟩
  have hclosure :
      constraintVec (k := k) μ u ∈ closure (momentPolytope (k := k) μ u) :=
    constraintVec_mem_closure_momentPolytope_of_tendsto (k := k) hk μ u hlim
  have hclosed : IsClosed (momentPolytope (k := k) μ u) :=
    (isCompact_momentPolytope (k := k) μ u).isClosed
  simpa [hclosed.closure_eq] using hclosure

end MarkovDeFinettiHard

end Mettapedia.Logic
