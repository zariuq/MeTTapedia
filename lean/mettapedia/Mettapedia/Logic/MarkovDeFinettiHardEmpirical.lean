import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.Dirac
import Mettapedia.Logic.MarkovDeFinettiEvidenceBasis
import Mettapedia.Logic.UniversalPrediction.MarkovDirichletPredictor

/-!
# Markov de Finetti (Hard Direction) — Empirical Evidence Measures

This file introduces a small, concrete piece of the hard direction: the **finite
probability distribution over evidence states** at horizon `n`, induced by a
prefix measure `μ`.

This is a stepping stone toward constructing mixing measures on `MarkovParam k`
from evidence partitions.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHard

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.EvidenceDirichlet

variable {k : ℕ}

/-- Discrete sigma-algebra on the finite evidence state space. -/
instance : MeasurableSpace (MarkovState k) := ⊤

/-- Finite PMF on evidence states at horizon `n`, induced by a prefix measure `μ`. -/
def statePMF (μ : PrefixMeasure (Fin k)) (n : ℕ) : PMF (MarkovState k) :=
  PMF.ofFinset (fun e => wμ (k := k) μ n e) (stateFinset k n)
    (sum_wμ_eq_one' (k := k) (μ := μ) n)
    (wμ_eq_zero_of_not_mem_stateFinset (k := k) (μ := μ) n)

/-- The corresponding probability measure on evidence states. -/
def stateProbMeasure (μ : PrefixMeasure (Fin k)) (n : ℕ) :
    MeasureTheory.ProbabilityMeasure (MarkovState k) :=
  ⟨(statePMF (k := k) μ n).toMeasure, by infer_instance⟩

@[simp] lemma statePMF_apply (μ : PrefixMeasure (Fin k)) (n : ℕ) (e : MarkovState k) :
    statePMF (k := k) μ n e = wμ (k := k) μ n e := by
  rfl

/-! ## Empirical Markov parameters (Laplace-smoothed) -/

/-! ## Laplace-smoothed empirical transition probabilities -/

/-- Laplace-smoothed row probability for transition `prev → next`. -/
def empiricalStepProb (_hk : 0 < k) (c : TransCounts k) (prev next : Fin k) : ℝ :=
  let prior : DirichletParams k := DirichletParams.uniformPrior
  ((c.counts prev next : ℝ) + prior.priorParams next) /
    ((c.rowTotal prev : ℝ) + prior.totalConcentration)

private lemma empiricalStepProb_nonneg (hk : 0 < k) (c : TransCounts k) (prev next : Fin k) :
    0 ≤ empiricalStepProb (k := k) hk c prev next := by
  unfold empiricalStepProb
  -- numerator and denominator are nonnegative, denominator positive
  have hnum : 0 ≤ (c.counts prev next : ℝ) + (DirichletParams.uniformPrior (k := k)).priorParams next := by
    have h1 : 0 ≤ (c.counts prev next : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have h2 : 0 ≤ (DirichletParams.uniformPrior (k := k)).priorParams next := by
      -- uniform prior params are positive
      simp [DirichletParams.uniformPrior, DirichletParams.uniform]
    linarith
  have hden_pos : 0 < (c.rowTotal prev : ℝ) + (DirichletParams.uniformPrior (k := k)).totalConcentration := by
    have hrow : 0 ≤ (c.rowTotal prev : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hprior : 0 < (DirichletParams.uniformPrior (k := k)).totalConcentration := by
      -- totalConcentration = sum of positive entries
      simpa [DirichletParams.uniformPrior, DirichletParams.uniform] using
        (DirichletParams.totalConcentration_pos (k := k) (p := DirichletParams.uniformPrior) hk)
    linarith
  exact div_nonneg hnum (le_of_lt hden_pos)

private lemma empiricalStepProb_sum (hk : 0 < k) (c : TransCounts k) (prev : Fin k) :
    (∑ j : Fin k, empiricalStepProb (k := k) hk c prev j) = 1 := by
  classical
  unfold empiricalStepProb
  -- expand sums in numerator and denominator
  have hrow :
      (c.rowTotal prev : ℝ) = ∑ j : Fin k, (c.counts prev j : ℝ) := by
    unfold TransCounts.rowTotal
    -- cast of Nat sum
    simp
  have hprior :
      (DirichletParams.uniformPrior (k := k)).totalConcentration =
        ∑ j : Fin k, (DirichletParams.uniformPrior (k := k)).priorParams j := by
    unfold DirichletParams.totalConcentration
    simp
  -- use linearity of sums
  have hden :
      (c.rowTotal prev : ℝ) + (DirichletParams.uniformPrior (k := k)).totalConcentration =
        ∑ j : Fin k, ((c.counts prev j : ℝ) + (DirichletParams.uniformPrior (k := k)).priorParams j) := by
    -- combine the two sums
    simp [hrow, hprior, Finset.sum_add_distrib]
  -- sum of fractions with common denominator
  have hden_pos : 0 < (c.rowTotal prev : ℝ) + (DirichletParams.uniformPrior (k := k)).totalConcentration := by
    have hrow0 : 0 ≤ (c.rowTotal prev : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hprior0 : 0 < (DirichletParams.uniformPrior (k := k)).totalConcentration := by
      simpa [DirichletParams.uniformPrior, DirichletParams.uniform] using
        (DirichletParams.totalConcentration_pos (k := k) (p := DirichletParams.uniformPrior) hk)
    linarith
  have hden_ne : (c.rowTotal prev : ℝ) + (DirichletParams.uniformPrior (k := k)).totalConcentration ≠ 0 := by
    linarith [hden_pos]
  -- now compute the sum
  -- set shorthand
  let D : ℝ := (c.rowTotal prev : ℝ) + (DirichletParams.uniformPrior (k := k)).totalConcentration
  have hden' : D ≠ 0 := by simpa [D] using hden_ne
  have hden_eq : D = ∑ j : Fin k, ((c.counts prev j : ℝ) + (DirichletParams.uniformPrior (k := k)).priorParams j) := by
    simp [D, hden]
  calc
    (∑ j : Fin k,
        ((c.counts prev j : ℝ) + (DirichletParams.uniformPrior (k := k)).priorParams j) / D)
        = (∑ j : Fin k,
            ((c.counts prev j : ℝ) + (DirichletParams.uniformPrior (k := k)).priorParams j) * (1 / D)) := by
            simp [div_eq_mul_inv]
    _ = (∑ j : Fin k,
            ((c.counts prev j : ℝ) + (DirichletParams.uniformPrior (k := k)).priorParams j)) * (1 / D) := by
            simp [Finset.sum_mul]
    _ = (∑ j : Fin k,
            ((c.counts prev j : ℝ) + (DirichletParams.uniformPrior (k := k)).priorParams j)) / D := by
            simp [div_eq_mul_inv]
    _ = 1 := by
            -- numerator equals denominator
            have hnum_ne :
                (∑ j : Fin k,
                  ((c.counts prev j : ℝ) + (DirichletParams.uniformPrior (k := k)).priorParams j)) ≠ 0 := by
              simpa [hden_eq] using hden'
            simp [hden_eq, hnum_ne]

/-- PMF for a single transition row, using Laplace smoothing. -/
def empiricalRowPMF (hk : 0 < k) (c : TransCounts k) (prev : Fin k) : PMF (Fin k) :=
  PMF.ofFinset
    (fun j => ENNReal.ofReal (empiricalStepProb (k := k) hk c prev j))
    (Finset.univ)
    (by
      -- sum of probabilities = 1 (in ℝ)
      have hsum : (∑ j : Fin k, empiricalStepProb (k := k) hk c prev j) = 1 :=
        empiricalStepProb_sum (k := k) hk c prev
      -- convert to ENNReal using nonnegativity
      have hsum' :
          ENNReal.ofReal (∑ j : Fin k, empiricalStepProb (k := k) hk c prev j) =
            (∑ j : Fin k, ENNReal.ofReal (empiricalStepProb (k := k) hk c prev j)) := by
        simpa using
          (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
            (f := fun j => empiricalStepProb (k := k) hk c prev j)
            (by intro j hj; exact empiricalStepProb_nonneg (k := k) hk c prev j))
      -- finish
      simpa [hsum] using hsum'.symm
    )
    (by
      intro j hj
      -- outside `Finset.univ` never happens
      exact (hj (Finset.mem_univ j)).elim)

/-- Empirical transition measure for a fixed row. -/
def empiricalRowMeasure (hk : 0 < k) (c : TransCounts k) (prev : Fin k) :
    MeasureTheory.ProbabilityMeasure (Fin k) :=
  ⟨(empiricalRowPMF (k := k) hk c prev).toMeasure, by infer_instance⟩

/-! ## Empirical Markov parameters from evidence states -/

/-- Empirical Markov parameter from a Markov evidence state. -/
def empiricalParam (hk : 0 < k) (e : MarkovState k) : MarkovParam k :=
  ⟨
    -- initial distribution: point mass at start
    ⟨MeasureTheory.Measure.dirac e.start, by infer_instance⟩,
    -- transition rows from counts
    fun a => empiricalRowMeasure (k := k) hk e.counts a
  ⟩

/-! ## Empirical mixing measure on `MarkovParam k` -/

/-- Pushforward PMF on `MarkovParam k` obtained by mapping `empiricalParam` over the
evidence-state PMF at horizon `n`. -/
def empiricalPMF (hk : 0 < k) (μ : PrefixMeasure (Fin k)) (n : ℕ) : PMF (MarkovParam k) :=
  PMF.map (empiricalParam (k := k) hk) (statePMF (k := k) μ n)

/-- The corresponding probability measure on `MarkovParam k`. -/
def empiricalMeasure (hk : 0 < k) (μ : PrefixMeasure (Fin k)) (n : ℕ) :
    MeasureTheory.ProbabilityMeasure (MarkovParam k) :=
  ⟨(empiricalPMF (k := k) hk μ n).toMeasure, by infer_instance⟩


end MarkovDeFinettiHard

end Mettapedia.Logic
