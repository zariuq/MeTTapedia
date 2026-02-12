import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mettapedia.Logic.MarkovDeFinetti
import Mettapedia.Logic.MarkovDeFinettiHardBase
import Mettapedia.Logic.MarkovDeFinettiEvidenceBasis
import Mettapedia.Logic.MarkovDeFinettiHardRepresentability
import Mettapedia.Logic.MarkovDeFinettiHardFinite
import Mettapedia.Logic.MarkovDeFinettiRecurrence
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti (Hard Direction)

`Mettapedia.Logic.MarkovDeFinetti` proves the **easy direction**:

* a fixed (time-homogeneous) Markov chain gives a Markov-exchangeable `PrefixMeasure`, and
* mixtures preserve Markov exchangeability.

This file isolates the remaining mathematical content of the classical theorem of
Diaconis–Freedman (1980):

> Markov exchangeability ⇒ mixture of Markov chains.

The shared analytic infrastructure (compact parameter space, cylinder kernel, Stone–Weierstrass
setup) lives in `Mettapedia.Logic.MarkovDeFinettiHardBase`.

The intended proof route is the same pattern as the i.i.d. development in `HausdorffMoment.lean`:

1. construct a positive, normalized linear functional on a dense subalgebra of `C(K,ℝ)`,
2. apply Riesz–Markov–Kakutani on the compact space `K := MarkovParam k`,
3. show the resulting mixing measure reproduces the original cylinder probabilities.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators
open scoped NNReal ENNReal

open MeasureTheory

namespace MarkovDeFinettiHard

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence

variable {k : ℕ}

/-!
## Evidence constraints vs per-word mixture constraints

`MarkovDeFinettiEvidenceBasis.lean` defines, for each horizon `n`:

* `wμ μ n e`  : the total mass of the evidence class `e` under the prefix measure `μ`,
* `W n e θ`   : the corresponding evidence polynomial under parameter `θ`.

The “hard direction” of Markov de Finetti can be split cleanly into:

1. **(Representability)** Construct a probability measure `pi` on `MarkovParam k` such that
   `wμ μ n e = ∫⁻ θ, W n e θ ∂pi` for all evidence classes `(n,e)`.
2. **(Regrouping)** Show that such a `pi` implies the desired per-word mixture formula
   `μ xs = ∫⁻ θ, wordProb θ xs ∂pi`.

This file proves (2) and leaves (1) as the single remaining “Diaconis–Freedman” step.
-/

namespace EvidenceConstraints

open FiniteAlphabet

/-- Evidence-level constraints for a candidate mixing measure `pi`. -/
def Holds (μ : PrefixMeasure (Fin k)) (pi : Measure (MarkovParam k)) : Prop :=
  ∀ n : ℕ, ∀ e : MarkovState k, wμ (k := k) μ n e = ∫⁻ θ, W (k := k) n e θ ∂pi

end EvidenceConstraints

open EvidenceConstraints

namespace EvidenceToWords

open FiniteAlphabet

/-!
### Constant-on-fiber lemmas

`wμ` and `W` are defined by summing over a fiber of trajectories with the same `MarkovState`.
To turn evidence constraints into per-word constraints, we need to know that both:

* `μ (trajToList xs)` and
* `wordProb θ (trajToList xs)`

are constant on each evidence fiber.
-/

private lemma evidenceOf_eq_of_stateOfTraj_eq {n : ℕ} {xs ys : Traj k n}
    (h : stateOfTraj (k := k) xs = stateOfTraj (k := k) ys) :
    MarkovExchangeability.evidenceOf (α := Fin k) (n := n) xs =
      MarkovExchangeability.evidenceOf (α := Fin k) (n := n) ys := by
  -- `evidenceOf` only records `start` and transition counts.
  apply MarkovExchangeability.MarkovEvidence.ext
  · simpa [MarkovExchangeability.evidenceOf] using congrArg MarkovState.start h
  · funext a b
    -- `stateOfTraj.counts` is `countsOfFn`, i.e. `transCount`.
    have hcounts :
        (MarkovExchangeabilityBridge.countsOfFn (k := k) xs).counts a b =
          (MarkovExchangeabilityBridge.countsOfFn (k := k) ys).counts a b := by
      simpa using congrArg (fun e : MarkovState k => e.counts.counts a b) h
    simpa [MarkovExchangeability.evidenceOf, MarkovExchangeabilityBridge.countsOfFn] using hcounts

lemma mu_const_on_state_fiber
    (μ : PrefixMeasure (Fin k)) (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    {n : ℕ} {xs ys : Traj k n} (h : stateOfTraj (k := k) xs = stateOfTraj (k := k) ys) :
    μ (trajToList (k := k) xs) = μ (trajToList (k := k) ys) := by
  -- Reduce to the `evidenceOf` equality expected by `hμ`.
  have he : MarkovExchangeability.evidenceOf (α := Fin k) (n := n) xs =
      MarkovExchangeability.evidenceOf (α := Fin k) (n := n) ys :=
    evidenceOf_eq_of_stateOfTraj_eq (k := k) h
  -- `hμ` is stated on `List.ofFn`.
  simpa [trajToList] using hμ n xs ys he

lemma wordProb_const_on_state_fiber
    {n : ℕ} {xs ys : Traj k n} (θ : MarkovParam k)
    (h : stateOfTraj (k := k) xs = stateOfTraj (k := k) ys) :
    wordProb (k := k) θ (trajToList (k := k) xs) =
      wordProb (k := k) θ (trajToList (k := k) ys) := by
  -- `wordProb θ` is itself a Markov-exchangeable prefix measure (easy direction).
  -- We reuse the `MarkovDeFinetti.MarkovChain` proof by building a Markov chain from `θ`.
  classical
  let M : MarkovDeFinetti.MarkovChain k :=
    { init := fun a => (θ.init : Measure (Fin k)) (Set.singleton a)
      trans := fun a b => (θ.trans a : Measure (Fin k)) (Set.singleton b)
      init_sum := by
        classical
        -- Singletons partition the space under a probability measure:
        -- `∑ a, μ {a} = μ univ = 1`.
        have hsum :
            (∑ a ∈ (Finset.univ : Finset (Fin k)),
                (θ.init : Measure (Fin k)) (Set.singleton a)) =
              (θ.init : Measure (Fin k)) (Finset.univ : Finset (Fin k)) :=
          MeasureTheory.sum_measure_singleton (μ := (θ.init : Measure (Fin k)))
            (s := (Finset.univ : Finset (Fin k)))
        calc
          (∑ a : Fin k, (θ.init : Measure (Fin k)) (Set.singleton a))
              = ∑ a ∈ (Finset.univ : Finset (Fin k)),
                  (θ.init : Measure (Fin k)) (Set.singleton a) := by
                    simp
          _ = (θ.init : Measure (Fin k)) (Set.univ : Set (Fin k)) := by
                simpa using hsum
          _ = 1 := by
                simp
      trans_sum := by
        intro a
        classical
        have hsum :
            (∑ b ∈ (Finset.univ : Finset (Fin k)),
                (θ.trans a : Measure (Fin k)) (Set.singleton b)) =
              (θ.trans a : Measure (Fin k)) (Finset.univ : Finset (Fin k)) :=
          MeasureTheory.sum_measure_singleton (μ := (θ.trans a : Measure (Fin k)))
            (s := (Finset.univ : Finset (Fin k)))
        calc
          (∑ b : Fin k, (θ.trans a : Measure (Fin k)) (Set.singleton b))
              = ∑ b ∈ (Finset.univ : Finset (Fin k)),
                  (θ.trans a : Measure (Fin k)) (Set.singleton b) := by
                    simp
          _ = (θ.trans a : Measure (Fin k)) (Set.univ : Set (Fin k)) := by
                simpa using hsum
          _ = 1 := by
                simp }
  have hM :
      MarkovExchangeablePrefixMeasure (k := k) M.prefixMeasure :=
    MarkovDeFinetti.MarkovChain.prefixMeasure_markovExchangeable (k := k) (M := M)
  have he : MarkovExchangeability.evidenceOf (α := Fin k) (n := n) xs =
      MarkovExchangeability.evidenceOf (α := Fin k) (n := n) ys :=
    evidenceOf_eq_of_stateOfTraj_eq (k := k) h
  -- Identify `wordProb` with `M.prefixMeasure`.
  have hword : ∀ zs : List (Fin k), wordProb (k := k) θ zs = M.prefixMeasure zs := by
    intro zs
    -- First show that the NNReal recursion (`wordProbAux`) matches the ENNReal recursion
    -- (`MarkovChain.prefixAux`) after coercion.
    have hstep (a b : Fin k) :
        (stepProb (k := k) θ a b : ENNReal) = M.trans a b := by
      -- `stepProb` is `toNNReal` of the underlying measure; since all measures are finite, the
      -- coercion back to `ENNReal` agrees with the underlying value.
      have hne_top : ((θ.trans a : Measure (Fin k)) (Set.singleton b)) ≠ (⊤ : ENNReal) := by
        -- Bounded by `measure_univ = 1`.
        have hle : (θ.trans a : Measure (Fin k)) (Set.singleton b) ≤
            (θ.trans a : Measure (Fin k)) (Set.univ : Set (Fin k)) :=
          measure_mono (show (Set.singleton b : Set (Fin k)) ⊆ Set.univ from Set.subset_univ _)
        have hle' : (θ.trans a : Measure (Fin k)) (Set.singleton b) ≤ (1 : ENNReal) := by
          simpa [((θ.trans a).prop.measure_univ : (θ.trans a : Measure (Fin k)) Set.univ = 1)] using hle
        exact ne_top_of_le_ne_top (by simp) hle'
      -- Unfold `stepProb` and apply `ENNReal.coe_toNNReal`.
      change
        (↑(((θ.trans a : Measure (Fin k)) (Set.singleton b)).toNNReal) :
            ENNReal) = (θ.trans a : Measure (Fin k)) (Set.singleton b)
      exact ENNReal.coe_toNNReal hne_top
    have hinit (a : Fin k) :
        (initProb (k := k) θ a : ENNReal) = M.init a := by
      have hne_top : ((θ.init : Measure (Fin k)) (Set.singleton a)) ≠ (⊤ : ENNReal) := by
        have hle : (θ.init : Measure (Fin k)) (Set.singleton a) ≤
            (θ.init : Measure (Fin k)) (Set.univ : Set (Fin k)) :=
          measure_mono (show (Set.singleton a : Set (Fin k)) ⊆ Set.univ from Set.subset_univ _)
        have hle' : (θ.init : Measure (Fin k)) (Set.singleton a) ≤ (1 : ENNReal) := by
          simpa [θ.init.prop.measure_univ] using hle
        exact ne_top_of_le_ne_top (by simp) hle'
      change
        (↑(((θ.init : Measure (Fin k)) (Set.singleton a)).toNNReal) :
            ENNReal) = (θ.init : Measure (Fin k)) (Set.singleton a)
      exact ENNReal.coe_toNNReal hne_top
    have haux :
        ∀ (prev : Fin k) (zs : List (Fin k)),
          (wordProbAux (k := k) θ prev zs : ENNReal) = M.prefixAux prev zs := by
      intro prev zs
      induction zs generalizing prev with
      | nil =>
          simp [wordProbAux, MarkovDeFinetti.MarkovChain.prefixAux]
      | cons b zs ih =>
          simp [wordProbAux, MarkovDeFinetti.MarkovChain.prefixAux, hstep, ih]
    cases zs with
    | nil =>
        simp [wordProb, wordProbNN, MarkovDeFinetti.MarkovChain.prefixMeasure,
          MarkovDeFinetti.MarkovChain.prefixProb]
    | cons a zs =>
        -- Use the NNReal recursion + the compatibility lemmas `hinit`/`haux`.
        simp [wordProb, wordProbNN, MarkovDeFinetti.MarkovChain.prefixMeasure,
          MarkovDeFinetti.MarkovChain.prefixProb, hinit, haux]
  -- Apply Markov exchangeability to the `ofFn` trajectories.
  simpa [trajToList, hword] using hM n xs ys he

/-!
### Evidence constraints imply the per-word mixture formula
-/

theorem wordProb_of_evidence_constraints
    (μ : PrefixMeasure (Fin k)) (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (pi : Measure (MarkovParam k)) (hpi : IsProbabilityMeasure pi)
    (hE : Holds (k := k) μ pi) :
    ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  classical
  intro xs
  cases xs with
  | nil =>
      -- Both sides are 1 by the prefix-measure root axiom.
      -- `μ [] = 1` and `wordProb θ [] = 1`, hence the integral is `1` under a probability measure.
      have hμ0 : μ ([] : List (Fin k)) = 1 := by simpa using μ.root_eq_one'
      have hpi0 : (∫⁻ θ, wordProb (k := k) θ ([] : List (Fin k)) ∂pi) = 1 := by
        -- `∫⁻ θ, 1 ∂pi = 1 * pi univ = 1`.
        have hconst :
            (∫⁻ _θ : MarkovParam k, (1 : ENNReal) ∂pi) =
              (1 : ENNReal) * pi (Set.univ : Set (MarkovParam k)) :=
          lintegral_const (μ := pi) (c := (1 : ENNReal))
        calc
          (∫⁻ θ, wordProb (k := k) θ ([] : List (Fin k)) ∂pi)
              = ∫⁻ _θ : MarkovParam k, (1 : ENNReal) ∂pi := by
                  simp [wordProb, wordProbNN]
          _ = (1 : ENNReal) * pi (Set.univ : Set (MarkovParam k)) := hconst
          _ = 1 := by simp [hpi.measure_univ]
      simp [hμ0, hpi0]
  | cons a xs =>
      let n : ℕ := xs.length
      -- Encode the word as a trajectory of length `n+1`.
      let xsFn : Traj k n := fun i =>
        (a :: xs).get (Fin.cast (by simp [n]) i)
      have hxFn : trajToList (k := k) xsFn = a :: xs := by
        -- `trajToList` is `List.ofFn`, and `xsFn` is `List.get` up to a cast on `Fin`.
        have hlen : (a :: xs).length = n + 1 := by simp [n]
        have hcast :
            List.ofFn xsFn = List.ofFn (List.get (a :: xs)) := by
          -- `ofFn_congr` rewrites the domain cast in the other direction.
          simpa [xsFn] using
            (List.ofFn_congr (α := Fin k) (h := hlen) (f := List.get (a :: xs))).symm
        have hget : List.ofFn (List.get (a :: xs)) = (a :: xs) :=
          List.ofFn_get (a :: xs)
        calc
          trajToList (k := k) xsFn = List.ofFn xsFn := rfl
          _ = List.ofFn (List.get (a :: xs)) := hcast
          _ = a :: xs := hget
      let e : MarkovState k := stateOfTraj (k := k) xsFn
      have hEv : wμ (k := k) μ n e = ∫⁻ θ, W (k := k) n e θ ∂pi := hE n e
      -- Fiber of evidence class `e`.
      let fiber : Finset (Traj k n) :=
        (trajFinset k n).filter (fun ys => stateOfTraj (k := k) ys = e)
      have hx_mem_fiber : xsFn ∈ fiber := by
        have hx : stateOfTraj (k := k) xsFn = e := rfl
        simp [fiber, trajFinset, hx]
      have hcard_pos : 0 < fiber.card := Finset.card_pos.2 ⟨xsFn, hx_mem_fiber⟩
      -- Rewrite `wμ` as `card * μ(rep)`.
      have hwμ :
          wμ (k := k) μ n e = (fiber.card : ENNReal) * μ (trajToList (k := k) xsFn) := by
        -- Unfold `wμ` and rewrite the filter as `fiber`.
        simp [wμ, fiber]
        -- Replace the filtered sum by a sum over `fiber` (definitional).
        have hterm :
            ∀ ys, ys ∈ fiber → μ (trajToList (k := k) ys) = μ (trajToList (k := k) xsFn) := by
          intro ys hys
          have hstate : stateOfTraj (k := k) ys = stateOfTraj (k := k) xsFn := by
            have : stateOfTraj (k := k) ys = e := (Finset.mem_filter.1 hys).2
            simpa [e] using this.trans rfl.symm
          exact mu_const_on_state_fiber (k := k) (μ := μ) hμ hstate
        calc
          (∑ ys ∈ fiber, μ (trajToList (k := k) ys))
              = ∑ ys ∈ fiber, μ (trajToList (k := k) xsFn) := by
                  refine Finset.sum_congr rfl ?_
                  intro ys hys
                  simp [hterm ys (by simpa using hys)]
          _ = (fiber.card : ENNReal) * μ (trajToList (k := k) xsFn) := by
                simp [Finset.sum_const, mul_comm]
      -- Rewrite `W` as `card * wordProb(rep)`.
      have hW :
          ∀ θ, W (k := k) n e θ =
            (fiber.card : ENNReal) * wordProb (k := k) θ (trajToList (k := k) xsFn) := by
        intro θ
        -- Unfold `W` and rewrite the filter as `fiber`.
        simp [W, fiber]
        have hterm :
            ∀ ys, ys ∈ fiber →
              wordProb (k := k) θ (trajToList (k := k) ys) =
                wordProb (k := k) θ (trajToList (k := k) xsFn) := by
          intro ys hys
          have hstate : stateOfTraj (k := k) ys = stateOfTraj (k := k) xsFn := by
            have : stateOfTraj (k := k) ys = e := (Finset.mem_filter.1 hys).2
            simpa [e] using this.trans rfl.symm
          exact wordProb_const_on_state_fiber (k := k) (θ := θ) hstate
        calc
          (∑ ys ∈ fiber, wordProb (k := k) θ (trajToList (k := k) ys))
              = ∑ ys ∈ fiber, wordProb (k := k) θ (trajToList (k := k) xsFn) := by
                  refine Finset.sum_congr rfl ?_
                  intro ys hys
                  simp [hterm ys (by simpa using hys)]
          _ = (fiber.card : ENNReal) * wordProb (k := k) θ (trajToList (k := k) xsFn) := by
                simp [Finset.sum_const, mul_comm]
      -- Plug rewrites into the evidence constraint, pull out the constant, and cancel.
      have hmul :
          (fiber.card : ENNReal) * μ (trajToList (k := k) xsFn) =
            ∫⁻ θ, (fiber.card : ENNReal) * wordProb (k := k) θ (trajToList (k := k) xsFn) ∂pi := by
        simpa [hwμ, hW] using hEv
      have hlin :
          ∫⁻ θ, (fiber.card : ENNReal) * wordProb (k := k) θ (trajToList (k := k) xsFn) ∂pi =
            (fiber.card : ENNReal) * ∫⁻ θ, wordProb (k := k) θ (trajToList (k := k) xsFn) ∂pi := by
        -- `lintegral_const_mul` is stated for `r * f`; our integrand is `card * wordProb`.
        simpa using
          (lintegral_const_mul (μ := pi) (r := (fiber.card : ENNReal))
            (f := fun θ => wordProb (k := k) θ (trajToList (k := k) xsFn))
            (hf := measurable_wordProb (k := k) (xs := trajToList (k := k) xsFn)))
      have hmul' :
          (fiber.card : ENNReal) * μ (trajToList (k := k) xsFn) =
            (fiber.card : ENNReal) * ∫⁻ θ, wordProb (k := k) θ (trajToList (k := k) xsFn) ∂pi := by
        simpa [hlin] using hmul
      have hcard_ne0 : (fiber.card : ENNReal) ≠ 0 := by
        exact_mod_cast (ne_of_gt hcard_pos)
      have hcard_ne_top : (fiber.card : ENNReal) ≠ (⊤ : ENNReal) := by
        simp
      -- Cancel the positive finite factor by multiplying by its inverse on the left.
      have hcancel' :
          μ (trajToList (k := k) xsFn) =
            ∫⁻ θ, wordProb (k := k) θ (trajToList (k := k) xsFn) ∂pi := by
        have := congrArg (fun t => (fiber.card : ENNReal)⁻¹ * t) hmul'
        simpa [mul_assoc, ENNReal.inv_mul_cancel_left hcard_ne0 hcard_ne_top] using this
      simpa [hxFn] using hcancel'

end EvidenceToWords

/-!
## Target theorem (Diaconis–Freedman, hard direction)

Diaconis–Freedman (1980) show that **Markov exchangeability alone is not sufficient** for a
mixture-of-Markov-chains representation without an additional **recurrence** assumption.

We therefore state the theorem with an explicit recurrence hypothesis on the prefix measure
(see `MarkovDeFinettiRecurrence.MarkovRecurrentPrefixMeasure`). This hypothesis is **not**
derived here; it is an external assumption to be proven in a separate development, not an axiom.

The mixture is stated using `lintegral` (`∫⁻`) since our prefix measures live in `ENNReal`.
-/

theorem markovDeFinetti_hard
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      MarkovDeFinettiHard.HasExcursionBiapproxCore (k := k) hk n e) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  classical
  -- The deep step: construct a mixing measure `pi` matching the evidence basis at every horizon.
  have hPi :
      ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧ Holds (k := k) μ pi := by
    -- Reduce to compactness: it suffices to show that every *finite* set of constraints is
    -- satisfiable. The compactness lemma is proved in `MarkovDeFinettiHardRepresentability.lean`.
    have hfin :
        ∀ u : Finset (ℕ × MarkovState k),
          (⋂ p ∈ u, constraintSet (k := k) μ p.1 p.2).Nonempty :=
      finite_constraints_nonempty (k := k) (μ := μ) hμ hrec hcoreAll
    rcases
        (exists_probabilityMeasure_of_finite_constraints (k := k) (μ := μ) hfin)
      with ⟨π, hπ⟩
    refine ⟨(π : Measure (MarkovParam k)), by infer_instance, ?_⟩
    intro n e
    -- Convert the `Wnn`-constraint into the `W`-constraint expected by `Holds`.
    have hWnn : wμ (k := k) μ n e = ∫⁻ θ, Wnn (k := k) n e θ ∂π := hπ n e
    -- `Wnn` coerces to `W` pointwise.
    simpa [coe_Wnn] using hWnn
  rcases hPi with ⟨pi, hpi, hE⟩
  refine ⟨pi, hpi, ?_⟩
  -- Regrouping step: evidence constraints imply the per-word mixture formula.
  exact EvidenceToWords.wordProb_of_evidence_constraints (k := k) (μ := μ) hμ pi hpi hE


theorem markovDeFinetti_hard_of_residualRate
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hrateAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧
        MarkovDeFinettiHard.HasExcursionResidualBoundRate (k := k) hk n e C) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  classical
  have hPi :
      ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧ Holds (k := k) μ pi := by
    have hfin :
        ∀ u : Finset (ℕ × MarkovState k),
          (⋂ p ∈ u, constraintSet (k := k) μ p.1 p.2).Nonempty :=
      finite_constraints_nonempty_of_residualRate (k := k) (μ := μ) hμ hrec hrateAll
    rcases
        (exists_probabilityMeasure_of_finite_constraints (k := k) (μ := μ) hfin)
      with ⟨π, hπ⟩
    refine ⟨(π : Measure (MarkovParam k)), by infer_instance, ?_⟩
    intro n e
    have hWnn : wμ (k := k) μ n e = ∫⁻ θ, Wnn (k := k) n e θ ∂π := hπ n e
    simpa [coe_Wnn] using hWnn
  rcases hPi with ⟨pi, hpi, hE⟩
  refine ⟨pi, hpi, ?_⟩
  exact EvidenceToWords.wordProb_of_evidence_constraints (k := k) (μ := μ) hμ pi hpi hE



theorem markovDeFinetti_hard_of_splitRates
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hsplitAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cw Cpc : ℝ,
        0 ≤ Cw ∧ 0 ≤ Cpc ∧
        MarkovDeFinettiHard.HasCanonicalWRSmoothingRate (k := k) hk n e Cw ∧
        MarkovDeFinettiHard.HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  have hrateAll :=
    MarkovDeFinettiHard.hasExcursionResidualBoundRateAll_of_splitRatesAll
      (k := k) hsplitAll
  exact markovDeFinetti_hard_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll

theorem markovDeFinetti_hard_via_residualRateBridge
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      MarkovDeFinettiHard.HasExcursionBiapproxCore (k := k) hk n e) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  have hrateAll :=
    MarkovDeFinettiHard.hasExcursionResidualBoundRateAll_of_biapproxCoreAll
      (k := k) hcoreAll
  exact markovDeFinetti_hard_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll

end MarkovDeFinettiHard

end Mettapedia.Logic
