import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Topology.Algebra.Module.Basic
import Mettapedia.Logic.MarkovDeFinettiHardRepresentability
import Mettapedia.Logic.MarkovDeFinettiHardEmpirical
import Mettapedia.Logic.MarkovDeFinettiHardGoodStateBound
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

private theorem empiricalWnn_tendsto_wμ_succ_of_weightedDiff
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (n : ℕ) (e : MarkovState k)
    (happrox :
      Filter.Tendsto (weightedDiff (k := k) hk μ n e) Filter.atTop (nhds 0)) :
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

  -- Step 4: conclude the original `ENNReal` convergence from `happrox`
  -- using the rewrite in Step 1 and the tower identity in Step 2.
  -- (Conversion from ENNReal to ℝ is routine once the approximation is established.)
  have hdiff_eventually :
      Filter.Eventually
        (fun N =>
          ((∫⁻ θ, Wnn (k := k) (Nat.succ n) e θ ∂(empiricalMeasure (k := k) hk μ N)).toReal
            - (wμ (k := k) μ (Nat.succ n) e).toReal)
            = weightedDiff (k := k) hk μ n e N)
        Filter.atTop := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨Nat.succ n, ?_⟩
    intro N hN
    -- Rewrite both terms as finite sums.
    have hsumN := hsum N
    have hwμN :=
      wμ_eq_sum_prefixCoeff_mul_wμ (k := k) (μ := μ) hμ (h := hN) (e := e)
    -- Bounds to justify `toReal_sum`.
    have hW_le_one :
        ∀ θ : MarkovParam k, W (k := k) (Nat.succ n) e θ ≤ 1 := by
      intro θ
      by_cases he : e ∈ stateFinset k (Nat.succ n)
      · have hsumW :=
          sum_W_eq_one' (k := k) (n := Nat.succ n) (θ := θ)
        have hle :
            W (k := k) (Nat.succ n) e θ ≤
              ∑ eN ∈ stateFinset k (Nat.succ n), W (k := k) (Nat.succ n) eN θ := by
          refine Finset.single_le_sum (f := fun eN =>
            W (k := k) (Nat.succ n) eN θ) ?_ he
          intro eN hmem
          exact W_nonneg (k := k) (n := Nat.succ n) (e := eN) (θ := θ)
        simpa [hsumW] using hle
      · -- No realizable trajectories: the evidence weight is zero.
        have hfilter :
            (trajFinset k (Nat.succ n)).filter
              (fun xs => stateOfTraj (k := k) xs = e) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro xs hxs hxe
          have : e ∈ stateFinset k (Nat.succ n) := by
            simpa [hxe] using (stateOfTraj_mem_stateFinset (k := k) (xs := xs))
          exact he this
        simp [W, hfilter]
    have hwμ_le_one :
        ∀ N : ℕ, ∀ s : MarkovState k, wμ (k := k) μ N s ≤ 1 := by
      intro N s
      by_cases hs : s ∈ stateFinset k N
      · have hsum := sum_wμ_eq_one' (k := k) (μ := μ) N
        have hle :
            wμ (k := k) μ N s ≤
              ∑ e ∈ stateFinset k N, wμ (k := k) μ N e := by
          refine Finset.single_le_sum (f := fun e =>
            wμ (k := k) μ N e) ?_ hs
          intro e he
          exact wμ_nonneg (k := k) (μ := μ) (n := N) (e := e)
        simpa [hsum] using hle
      · have hw0 :
            wμ (k := k) μ N s = 0 :=
          wμ_eq_zero_of_not_mem_stateFinset (k := k) (μ := μ) (n := N) (e := s) hs
        simp [hw0]
    have hsum_toReal_W :
        (∑ s ∈ stateFinset k N,
            W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) *
              wμ (k := k) μ N s).toReal =
          ∑ s ∈ stateFinset k N,
            (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal *
              (wμ (k := k) μ N s).toReal := by
      classical
      refine (ENNReal.toReal_sum ?_).trans ?_
      · intro s hs
        apply ENNReal.mul_ne_top
        · exact ne_of_lt (lt_of_le_of_lt (hW_le_one _)
            ENNReal.one_lt_top)
        · exact ne_of_lt (lt_of_le_of_lt (hwμ_le_one N s)
            ENNReal.one_lt_top)
      · simp [ENNReal.toReal_mul]
    have hsum_toReal_pref :
        (∑ s ∈ stateFinset k N,
            prefixCoeff (k := k) (h := hN) e s * wμ (k := k) μ N s).toReal =
          ∑ s ∈ stateFinset k N,
            (prefixCoeff (k := k) (h := hN) e s).toReal *
              (wμ (k := k) μ N s).toReal := by
      classical
      refine (ENNReal.toReal_sum ?_).trans ?_
      · intro s hs
        apply ENNReal.mul_ne_top
        · -- `prefixCoeff ≤ 1`
          have hle' :
              prefixCoeff (k := k) (h := hN) e s ≤ 1 := by
            by_cases he : e ∈ stateFinset k (Nat.succ n)
            · have hsum :=
                sum_prefixCoeff_eq_one_of_mem_stateFinset (k := k) (h := hN) (eN := s) hs
              have hle :
                  prefixCoeff (k := k) (h := hN) e s ≤
                    ∑ e' ∈ stateFinset k (Nat.succ n),
                      prefixCoeff (k := k) (h := hN) e' s := by
                refine Finset.single_le_sum (f := fun e' =>
                  prefixCoeff (k := k) (h := hN) e' s) ?_ he
                intro e' he'
                by_cases hcard : (fiber k N s).card = 0
                · simp [prefixCoeff, hcard]
                · simp [prefixCoeff, hcard]
              simpa [hsum] using hle
            · have hzero :
                  prefixCoeff (k := k) (h := hN) e s = 0 := by
                simpa [prefixCoeff, he] using
                  (prefixCoeff_eq_zero_of_not_mem_stateFinset (k := k)
                    (h := hN) (e := e) (eN := s) he)
              simp [hzero]
          exact ne_of_lt (lt_of_le_of_lt hle' ENNReal.one_lt_top)
        · exact ne_of_lt (lt_of_le_of_lt (hwμ_le_one N s) ENNReal.one_lt_top)
      · simp [ENNReal.toReal_mul]
    calc
      ((∫⁻ θ, Wnn (k := k) (Nat.succ n) e θ ∂(empiricalMeasure (k := k) hk μ N)).toReal
          - (wμ (k := k) μ (Nat.succ n) e).toReal)
          =
          (∑ s ∈ stateFinset k N,
              W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s).toReal
            - (∑ s ∈ stateFinset k N,
                prefixCoeff (k := k) (h := hN) e s * wμ (k := k) μ N s).toReal := by
                rw [hsumN, hwμN]
      _ =
          ∑ s ∈ stateFinset k N,
            ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
              - (prefixCoeff (k := k) (h := hN) e s).toReal) *
              (wμ (k := k) μ N s).toReal := by
        -- distribute the difference inside the finite sum
        classical
        -- use `sub_mul` and `sum_sub_distrib` in reverse
        simp [hsum_toReal_W, hsum_toReal_pref, sub_mul, Finset.sum_sub_distrib]
      _ = weightedDiff (k := k) hk μ n e N := by
        simp [weightedDiff, weightedDiffCore, hN]
  have hdiff_tendsto :
      Filter.Tendsto
        (fun N =>
          ((∫⁻ θ, Wnn (k := k) (Nat.succ n) e θ ∂(empiricalMeasure (k := k) hk μ N)).toReal
            - (wμ (k := k) μ (Nat.succ n) e).toReal))
        Filter.atTop (nhds 0) := by
    refine (Filter.Tendsto.congr' (Filter.EventuallyEq.symm hdiff_eventually) ?_)
    simpa using happrox
  have htoReal :
      Filter.Tendsto
        (fun N =>
          (∫⁻ θ, Wnn (k := k) (Nat.succ n) e θ ∂(empiricalMeasure (k := k) hk μ N)).toReal)
        Filter.atTop
        (nhds ((wμ (k := k) μ (Nat.succ n) e).toReal)) := by
    -- `f - c → 0` implies `f → c`
    have htoReal' :=
      (Filter.tendsto_sub_const_iff
          (b := (wμ (k := k) μ (Nat.succ n) e).toReal)
          (c := (wμ (k := k) μ (Nat.succ n) e).toReal)
          (f := fun N =>
            (∫⁻ θ, Wnn (k := k) (Nat.succ n) e θ ∂(empiricalMeasure (k := k) hk μ N)).toReal)).1
        (by simpa using hdiff_tendsto)
    exact htoReal'
  -- Lift the real convergence back to `ENNReal`.
  refine (ENNReal.tendsto_toReal_iff
    (hf := ?_) (hx := ?_)).1 htoReal
  · intro N
    -- local bounds (reused from the weighted-difference step)
    have hW_le_one' :
        ∀ θ : MarkovParam k, W (k := k) (Nat.succ n) e θ ≤ 1 := by
      intro θ
      by_cases he : e ∈ stateFinset k (Nat.succ n)
      · have hsumW :=
          sum_W_eq_one' (k := k) (n := Nat.succ n) (θ := θ)
        have hle :
            W (k := k) (Nat.succ n) e θ ≤
              ∑ eN ∈ stateFinset k (Nat.succ n), W (k := k) (Nat.succ n) eN θ := by
          refine Finset.single_le_sum (f := fun eN =>
            W (k := k) (Nat.succ n) eN θ) ?_ he
          intro eN hmem
          exact W_nonneg (k := k) (n := Nat.succ n) (e := eN) (θ := θ)
        simpa [hsumW] using hle
      · have hfilter :
            (trajFinset k (Nat.succ n)).filter
              (fun xs => stateOfTraj (k := k) xs = e) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro xs hxs hxe
          have : e ∈ stateFinset k (Nat.succ n) := by
            simpa [hxe] using (stateOfTraj_mem_stateFinset (k := k) (xs := xs))
          exact he this
        simp [W, hfilter]
    have hwμ_le_one' :
        ∀ s : MarkovState k, wμ (k := k) μ N s ≤ 1 := by
      intro s
      by_cases hs : s ∈ stateFinset k N
      · have hsum := sum_wμ_eq_one' (k := k) (μ := μ) N
        have hle :
            wμ (k := k) μ N s ≤
              ∑ e ∈ stateFinset k N, wμ (k := k) μ N e := by
          refine Finset.single_le_sum (f := fun e =>
            wμ (k := k) μ N e) ?_ hs
          intro e he
          exact wμ_nonneg (k := k) (μ := μ) (n := N) (e := e)
        simpa [hsum] using hle
      · have hw0 :
            wμ (k := k) μ N s = 0 :=
          wμ_eq_zero_of_not_mem_stateFinset (k := k) (μ := μ) (n := N) (e := s) hs
        simp [hw0]
    have hle :
        (∫⁻ θ, Wnn (k := k) (Nat.succ n) e θ ∂(empiricalMeasure (k := k) hk μ N)) ≤ 1 := by
      -- Use the finite-sum representation and `W ≤ 1`.
      have hle_sum :
          ∑ s ∈ stateFinset k N,
              W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s
            ≤ ∑ s ∈ stateFinset k N, wμ (k := k) μ N s := by
        refine Finset.sum_le_sum ?_
        intro s hs
        have hWle : W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) ≤ 1 := by
          exact hW_le_one' _
        have hwμle : wμ (k := k) μ N s ≤ 1 := hwμ_le_one' s
        -- `W ≤ 1` gives `W * wμ ≤ wμ`
        have hmul :=
          mul_le_mul_of_nonneg_right hWle
            (wμ_nonneg (k := k) (μ := μ) (n := N) (e := s))
        simpa [one_mul] using hmul
      have hsum_wμ := sum_wμ_eq_one' (k := k) (μ := μ) N
      have hsumN := hsum N
      calc
        (∫⁻ θ, Wnn (k := k) (Nat.succ n) e θ ∂(empiricalMeasure (k := k) hk μ N))
            = ∑ s ∈ stateFinset k N,
                W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) * wμ (k := k) μ N s := by
                  rw [hsumN]
        _ ≤ ∑ s ∈ stateFinset k N, wμ (k := k) μ N s := hle_sum
        _ = 1 := by simp [hsum_wμ]
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  · have hwμ_le : wμ (k := k) μ (Nat.succ n) e ≤ 1 := by
        -- simple bound from the total mass
        by_cases he : e ∈ stateFinset k (Nat.succ n)
        · have hsum := sum_wμ_eq_one' (k := k) (μ := μ) (Nat.succ n)
          have hle :
              wμ (k := k) μ (Nat.succ n) e ≤
                ∑ e' ∈ stateFinset k (Nat.succ n), wμ (k := k) μ (Nat.succ n) e' := by
            refine Finset.single_le_sum (f := fun e' =>
              wμ (k := k) μ (Nat.succ n) e') ?_ he
            intro e' he'
            exact wμ_nonneg (k := k) (μ := μ) (n := Nat.succ n) (e := e')
          simpa [hsum] using hle
        · have hw0 :
              wμ (k := k) μ (Nat.succ n) e = 0 :=
            wμ_eq_zero_of_not_mem_stateFinset (k := k) (μ := μ) (n := Nat.succ n) (e := e) he
          simp [hw0]
    exact ne_of_lt (lt_of_le_of_lt hwμ_le ENNReal.one_lt_top)


theorem empiricalWnn_tendsto_wμ_succ
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (n : ℕ) (e : MarkovState k)
    (hcore : HasExcursionBiapproxCore (k := k) hk n e) :
    Filter.Tendsto
        (fun N =>
          ∫⁻ θ, Wnn (k := k) (Nat.succ n) e θ ∂(empiricalMeasure (k := k) hk μ N))
        Filter.atTop
        (nhds (wμ (k := k) μ (Nat.succ n) e)) := by
  have happrox :
      Filter.Tendsto (weightedDiff (k := k) hk μ n e) Filter.atTop (nhds 0) := by
    simpa using
      (weightedDiff_tendsto_zero (k := k) hk (μ := μ) hμ hrec n e hcore)
  exact empiricalWnn_tendsto_wμ_succ_of_weightedDiff
    (k := k) (hk := hk) (μ := μ) hμ n e happrox

theorem empiricalWnn_tendsto_wμ_succ_of_residualRate
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (n : ℕ) (e : MarkovState k)
    (C : ℝ) (hC : 0 ≤ C)
    (hrate : HasExcursionResidualBoundRate (k := k) hk n e C) :
    Filter.Tendsto
        (fun N =>
          ∫⁻ θ, Wnn (k := k) (Nat.succ n) e θ ∂(empiricalMeasure (k := k) hk μ N))
        Filter.atTop
        (nhds (wμ (k := k) μ (Nat.succ n) e)) := by
  have happrox :
      Filter.Tendsto (weightedDiff (k := k) hk μ n e) Filter.atTop (nhds 0) := by
    simpa using
      (weightedDiff_tendsto_zero_of_residualRate
        (k := k) (hk := hk) (μ := μ) hμ hrec n e C hC hrate)
  exact empiricalWnn_tendsto_wμ_succ_of_weightedDiff
    (k := k) (hk := hk) (μ := μ) hμ n e happrox

theorem empiricalWnn_tendsto_wμ
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hcoreAll : ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e)
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
      exact empiricalWnn_tendsto_wμ_succ
        (k := k) (hk := hk) (μ := μ) hμ hrec n e (hcoreAll n e)
  -- (Legacy proof attempt removed — the `| succ n` case is now handled by
  --  `empiricalWnn_tendsto_wμ_succ` via `weightedDiff_tendsto_zero`.)


theorem empiricalWnn_tendsto_wμ_of_residualRate
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hrateAll : ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C)
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
      rcases hrateAll n e with ⟨C, hC, hrate⟩
      exact empiricalWnn_tendsto_wμ_succ_of_residualRate
        (k := k) (hk := hk) (μ := μ) hμ hrec n e C hC hrate
  -- (Legacy proof attempt removed — the `| succ n` case is now handled by
  --  `empiricalWnn_tendsto_wμ_succ` via `weightedDiff_tendsto_zero`.)



theorem empiricalWnn_tendsto_wμ_of_splitRates
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hsplitAll : ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cw Cpc : ℝ,
        0 ≤ Cw ∧ 0 ≤ Cpc ∧
        HasCanonicalWRSmoothingRate (k := k) hk n e Cw ∧
        HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc)
    (n : ℕ) (e : MarkovState k) :
    Filter.Tendsto
        (fun N =>
          ∫⁻ θ, Wnn (k := k) n e θ ∂(empiricalMeasure (k := k) hk μ N))
        Filter.atTop
        (nhds (wμ (k := k) μ n e)) := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_splitRatesAll_fixed
      (k := k) (hk := hk) hsplitAll
  exact empiricalWnn_tendsto_wμ_of_residualRate
    (k := k) (hk := hk) (μ := μ) hμ hrec hrateAll n e



theorem empiricalWnn_tendsto_wμ_of_exactSurrogateWORTransport
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hWORAll : ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cpc : ℝ, 0 ≤ Cpc ∧
        HasCanonicalWORTransportRate (k := k) hk n e 0 Cpc)
    (n : ℕ) (e : MarkovState k) :
    Filter.Tendsto
        (fun N =>
          ∫⁻ θ, Wnn (k := k) n e θ ∂(empiricalMeasure (k := k) hk μ N))
        Filter.atTop
        (nhds (wμ (k := k) μ n e)) := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_exactSurrogateWORTransportAll_fixed
      (k := k) (hk := hk) hWORAll
  exact empiricalWnn_tendsto_wμ_of_residualRate
    (k := k) (hk := hk) (μ := μ) hμ hrec hrateAll n e


theorem empiricalWnn_tendsto_wμ_of_biapproxCore_exactSurrogate
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hcoreAll : ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e)
    (n : ℕ) (e : MarkovState k) :
    Filter.Tendsto
        (fun N =>
          ∫⁻ θ, Wnn (k := k) n e θ ∂(empiricalMeasure (k := k) hk μ N))
        Filter.atTop
        (nhds (wμ (k := k) μ n e)) := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_biapproxCoreAll_exactSurrogate_fixed
      (k := k) (hk := hk) hcoreAll
  exact empiricalWnn_tendsto_wμ_of_residualRate
    (k := k) (hk := hk) (μ := μ) hμ hrec hrateAll n e

theorem empiricalWnn_tendsto_wμ_of_explicitPatternSurrogateRate
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hpatternAll : ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧
        HasPatternSurrogateResidualAlignmentRate (k := k) hk n e C)
    (n : ℕ) (e : MarkovState k) :
    Filter.Tendsto
        (fun N =>
          ∫⁻ θ, Wnn (k := k) n e θ ∂(empiricalMeasure (k := k) hk μ N))
        Filter.atTop
        (nhds (wμ (k := k) μ n e)) := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_explicitPatternSurrogateRateAll_fixed
      (k := k) (hk := hk) hpatternAll
  exact empiricalWnn_tendsto_wμ_of_residualRate
    (k := k) (hk := hk) (μ := μ) hμ hrec hrateAll n e

theorem empiricalWnn_tendsto_wμ_via_residualRateBridge
    (hk : 0 < k)
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hcoreAll : ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e)
    (n : ℕ) (e : MarkovState k) :
    Filter.Tendsto
        (fun N =>
          ∫⁻ θ, Wnn (k := k) n e θ ∂(empiricalMeasure (k := k) hk μ N))
        Filter.atTop
        (nhds (wμ (k := k) μ n e)) := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_biapproxCoreAll_fixed
      (k := k) (hk := hk) hcoreAll
  exact empiricalWnn_tendsto_wμ_of_residualRate
    (k := k) (hk := hk) (μ := μ) hμ hrec hrateAll n e

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
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e)
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
    empiricalWnn_tendsto_wμ
      (k := k) (hk := hk) (μ := μ) hμ hrec (hcoreAll hk) p.1.1 p.1.2


theorem empiricalVec_tendsto_constraintVec_of_residualRate
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hrateAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C)
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
    empiricalWnn_tendsto_wμ_of_residualRate
      (k := k) (hk := hk) (μ := μ) hμ hrec (hrateAll hk) p.1.1 p.1.2



theorem empiricalVec_tendsto_constraintVec_of_splitRates
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hsplitAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cw Cpc : ℝ,
        0 ≤ Cw ∧ 0 ≤ Cpc ∧
        HasCanonicalWRSmoothingRate (k := k) hk n e Cw ∧
        HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc)
    (u : Finset (Nat × MarkovState k)) :
    ∃ hk : 0 < k,
      Filter.Tendsto (fun n => empiricalVec (k := k) hk μ u n) Filter.atTop
        (nhds (constraintVec (k := k) μ u)) := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_splitRatesAll
      (k := k) hsplitAll
  exact empiricalVec_tendsto_constraintVec_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll u



theorem empiricalVec_tendsto_constraintVec_of_exactSurrogateWORTransport
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hWORAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cpc : ℝ, 0 ≤ Cpc ∧
        HasCanonicalWORTransportRate (k := k) hk n e 0 Cpc)
    (u : Finset (Nat × MarkovState k)) :
    ∃ hk : 0 < k,
      Filter.Tendsto (fun n => empiricalVec (k := k) hk μ u n) Filter.atTop
        (nhds (constraintVec (k := k) μ u)) := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_exactSurrogateWORTransportAll
      (k := k) hWORAll
  exact empiricalVec_tendsto_constraintVec_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll u


theorem empiricalVec_tendsto_constraintVec_of_biapproxCore_exactSurrogate
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e)
    (u : Finset (Nat × MarkovState k)) :
    ∃ hk : 0 < k,
      Filter.Tendsto (fun n => empiricalVec (k := k) hk μ u n) Filter.atTop
        (nhds (constraintVec (k := k) μ u)) := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_biapproxCoreAll_exactSurrogate
      (k := k) hcoreAll
  exact empiricalVec_tendsto_constraintVec_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll u

theorem empiricalVec_tendsto_constraintVec_of_explicitPatternSurrogateRate
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hpatternAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧
        HasPatternSurrogateResidualAlignmentRate (k := k) hk n e C)
    (u : Finset (Nat × MarkovState k)) :
    ∃ hk : 0 < k,
      Filter.Tendsto (fun n => empiricalVec (k := k) hk μ u n) Filter.atTop
        (nhds (constraintVec (k := k) μ u)) := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_explicitPatternSurrogateRateAll
      (k := k) hpatternAll
  exact empiricalVec_tendsto_constraintVec_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll u

theorem empiricalVec_tendsto_constraintVec_via_residualRateBridge
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e)
    (u : Finset (Nat × MarkovState k)) :
    ∃ hk : 0 < k,
      Filter.Tendsto (fun n => empiricalVec (k := k) hk μ u n) Filter.atTop
        (nhds (constraintVec (k := k) μ u)) := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_biapproxCoreAll
      (k := k) hcoreAll
  exact empiricalVec_tendsto_constraintVec_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll u

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
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e)
    (u : Finset (Nat × MarkovState k)) :
    constraintVec (k := k) μ u ∈ momentPolytope (k := k) μ u := by
  -- Reduce to the empirical approximation limit + closedness of the moment polytope.
  rcases empiricalVec_tendsto_constraintVec
      (k := k) (μ := μ) hμ hrec hcoreAll u with ⟨hk, hlim⟩
  have hclosure :
      constraintVec (k := k) μ u ∈ closure (momentPolytope (k := k) μ u) :=
    constraintVec_mem_closure_momentPolytope_of_tendsto (k := k) hk μ u hlim
  have hclosed : IsClosed (momentPolytope (k := k) μ u) :=
    (isCompact_momentPolytope (k := k) μ u).isClosed
  simpa [hclosed.closure_eq] using hclosure

theorem constraintVec_mem_momentPolytope_of_residualRate
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hrateAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C)
    (u : Finset (Nat × MarkovState k)) :
    constraintVec (k := k) μ u ∈ momentPolytope (k := k) μ u := by
  -- Reduce to the empirical approximation limit + closedness of the moment polytope.
  rcases empiricalVec_tendsto_constraintVec_of_residualRate
      (k := k) (μ := μ) hμ hrec hrateAll u with ⟨hk, hlim⟩
  have hclosure :
      constraintVec (k := k) μ u ∈ closure (momentPolytope (k := k) μ u) :=
    constraintVec_mem_closure_momentPolytope_of_tendsto (k := k) hk μ u hlim
  have hclosed : IsClosed (momentPolytope (k := k) μ u) :=
    (isCompact_momentPolytope (k := k) μ u).isClosed
  simpa [hclosed.closure_eq] using hclosure


theorem constraintVec_mem_momentPolytope_of_splitRates
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hsplitAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cw Cpc : ℝ,
        0 ≤ Cw ∧ 0 ≤ Cpc ∧
        HasCanonicalWRSmoothingRate (k := k) hk n e Cw ∧
        HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc)
    (u : Finset (Nat × MarkovState k)) :
    constraintVec (k := k) μ u ∈ momentPolytope (k := k) μ u := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_splitRatesAll
      (k := k) hsplitAll
  exact constraintVec_mem_momentPolytope_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll u


theorem constraintVec_mem_momentPolytope_of_exactSurrogateWORTransport
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hWORAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cpc : ℝ, 0 ≤ Cpc ∧
        HasCanonicalWORTransportRate (k := k) hk n e 0 Cpc)
    (u : Finset (Nat × MarkovState k)) :
    constraintVec (k := k) μ u ∈ momentPolytope (k := k) μ u := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_exactSurrogateWORTransportAll
      (k := k) hWORAll
  exact constraintVec_mem_momentPolytope_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll u


theorem constraintVec_mem_momentPolytope_of_biapproxCore_exactSurrogate
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e)
    (u : Finset (Nat × MarkovState k)) :
    constraintVec (k := k) μ u ∈ momentPolytope (k := k) μ u := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_biapproxCoreAll_exactSurrogate
      (k := k) hcoreAll
  exact constraintVec_mem_momentPolytope_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll u

theorem constraintVec_mem_momentPolytope_of_explicitPatternSurrogateRate
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hpatternAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧
        HasPatternSurrogateResidualAlignmentRate (k := k) hk n e C)
    (u : Finset (Nat × MarkovState k)) :
    constraintVec (k := k) μ u ∈ momentPolytope (k := k) μ u := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_explicitPatternSurrogateRateAll
      (k := k) hpatternAll
  exact constraintVec_mem_momentPolytope_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll u

theorem constraintVec_mem_momentPolytope_via_residualRateBridge
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e)
    (u : Finset (Nat × MarkovState k)) :
    constraintVec (k := k) μ u ∈ momentPolytope (k := k) μ u := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_biapproxCoreAll
      (k := k) hcoreAll
  exact constraintVec_mem_momentPolytope_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll u


end MarkovDeFinettiHard

end Mettapedia.Logic
