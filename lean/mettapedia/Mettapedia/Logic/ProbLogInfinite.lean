import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mettapedia.Logic.PLNMarkovLogicAbstract

/-!
# ProbLog Distribution Semantics for Countably Infinite Facts

This module extends ProbLog's distribution semantics to countably many
independent probabilistic facts using Mathlib's `Measure.infinitePi` —
which is the Kolmogorov Extension Theorem.

## Scope

This is about **ProbLog** (independent probabilistic facts + definite clauses),
NOT about Markov Logic Networks (which have clause potentials / Gibbs
interactions). For MLNs with interacting clauses, the infinite case would
require Gibbs measures (`Measure.withDensity`), which is a different problem.

## What This Module Proves

For countably many **independent** probabilistic facts (ProbLog-style):

1. The world measure is the infinite product measure `Measure.infinitePi`
2. Query probability for finite queries reduces to finite products
3. WM-PLN query strength equals this probability (no finite-support assumption)

## Mathematical Foundation

- **Kolmogorov Extension Theorem** (Mathlib: `Measure.infinitePi`): Given a
  consistent family of finite-dimensional distributions, there exists a unique
  probability measure on the infinite product space.

- **Ionescu-Tulcea Theorem** (Mathlib: `Probability/Kernel/IonescuTulcea/`):
  Used internally by Mathlib to construct the infinite product measure.

## References

- Kolmogorov, "Foundations of the Theory of Probability", 1933
- Kallenberg, "Foundations of Modern Probability", 3rd ed., 2021 (Theorem 8.24)
- Cohn, "Measure Theory", 2nd ed., 2013 (Proposition 10.6.1)

0 sorry.
-/

namespace Mettapedia.Logic.ProbLogInfinite

open MeasureTheory Measure
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open scoped ENNReal NNReal

/-! ## §1 Bernoulli Measure on Bool

Each probabilistic fact `i` with probability `pᵢ` induces a Bernoulli
measure on `Bool`: probability `pᵢ` for `true`, `1-pᵢ` for `false`. -/

/-- Bernoulli probability measure on Bool from an NNReal probability.
    This is `PMF.bernoulli` lifted to a measure. -/
noncomputable def bernoulliMeasure (p : ℝ≥0) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p hp).toMeasure

instance bernoulliMeasure_prob (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernoulliMeasure p hp) :=
  PMF.toMeasure.isProbabilityMeasure _

/-! ## §2 Infinite Product Measure for Independent Facts

For countably many independent probabilistic facts with probabilities
`p : ℕ → ℝ≥0` (each `≤ 1`), the world space is `ℕ → Bool` and the
world measure is the infinite product:

  `μ = ⨂ᵢ bernoulli(pᵢ)`

This is constructed by Mathlib's `Measure.infinitePi`, which internally
uses the Kolmogorov Extension Theorem (via Ionescu-Tulcea). -/

/-- The infinite product measure for independent probabilistic facts.
    This is the distribution semantics measure for ProbLog with countably
    many independent facts. -/
noncomputable def infiniteFactMeasure (p : ℕ → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    Measure (ℕ → Bool) :=
  Measure.infinitePi (fun i => bernoulliMeasure (p i) (hp i))

instance infiniteFactMeasure_prob (p : ℕ → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    IsProbabilityMeasure (infiniteFactMeasure p hp) := by
  unfold infiniteFactMeasure
  infer_instance

/-! ## §3 Finite Cylinder Probabilities

The key property of the infinite product measure: the probability of a
cylinder set (a constraint on finitely many coordinates) equals the product
of the individual Bernoulli probabilities.

This is the content of `Measure.infinitePi_pi`. -/

/-- The infinite product measure on a finite cylinder equals the product
    of Bernoulli probabilities. This is the Kolmogorov consistency property. -/
theorem infiniteFactMeasure_cylinder (p : ℕ → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (S : Finset ℕ) (t : ℕ → Set Bool) (ht : ∀ i ∈ S, MeasurableSet (t i)) :
    infiniteFactMeasure p hp (Set.pi S t) =
      ∏ i ∈ S, bernoulliMeasure (p i) (hp i) (t i) := by
  exact Measure.infinitePi_pi _ ht

/-- The measure restricted to a finite set of coordinates equals the
    finite product measure. This is the marginalization property. -/
theorem infiniteFactMeasure_restrict (p : ℕ → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (S : Finset ℕ) :
    (infiniteFactMeasure p hp).map S.restrict =
      Measure.pi (fun i : S => bernoulliMeasure (p i) (hp i)) := by
  exact Measure.infinitePi_map_restrict _

/-! ## §4 Query Probability via Infinite Product Measure

For a query that depends on finitely many atoms (a measurable cylinder set),
the query probability under the infinite product measure equals the sum over
finite assignments, weighted by the finite product of Bernoulli probabilities.

This is exactly the ProbLog distribution semantics — but without any
finite-support assumption. -/

/-- Query probability under the infinite product measure.
    For probability measures, this simplifies to just `μ(Q)`. -/
noncomputable def infiniteQueryProb (p : ℕ → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (Q : Set (ℕ → Bool)) : ℝ≥0∞ :=
  infiniteFactMeasure p hp Q

/-- The infinite product measure is a probability measure, so total mass = 1. -/
theorem infiniteFactMeasure_total (p : ℕ → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    infiniteFactMeasure p hp Set.univ = 1 :=
  measure_univ

/-! ## §5 Bridge to MassSemantics

The infinite product measure induces a `MassSemantics` object (from
`PLNMarkovLogicAbstract.lean`), which bridges to WM-PLN via
`queryStrength_eq_queryProb_of_evidence_eq`. -/

/-- Convert the infinite product measure semantics into a `MassSemantics`
    for a specific measurable query. -/
noncomputable def infiniteMassSemantics (p : ℕ → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (Q : Set (ℕ → Bool)) (hQ : MeasurableSet Q) :
    PLNMarkovLogicAbstract.MassSemantics Unit where
  queryMass := fun _ => infiniteFactMeasure p hp Q
  totalMass := 1
  queryMass_le_total := fun _ =>
    (measure_mono (Set.subset_univ Q)).trans (le_of_eq (infiniteFactMeasure_total p hp))
  totalMass_ne_top := ENNReal.one_ne_top

/-- The query probability from `infiniteMassSemantics` equals the measure of Q. -/
theorem infiniteMassSemantics_queryProb (p : ℕ → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (Q : Set (ℕ → Bool)) (hQ : MeasurableSet Q) :
    (infiniteMassSemantics p hp Q hQ).queryProb () = infiniteFactMeasure p hp Q := by
  simp [PLNMarkovLogicAbstract.MassSemantics.queryProb, infiniteMassSemantics,
        infiniteFactMeasure_total, div_one]

/-! ## §6 Crown Theorem

The WM-PLN query strength for the infinite independent-facts model
equals the distribution semantics probability — with no finite-support
assumption. The infinite product measure (Kolmogorov extension) provides
the measure-theoretic foundation. -/

/-- **Crown Theorem (Infinite Case)**: For countably many independent
    probabilistic facts, the WM-PLN query strength equals the distribution
    semantics probability for any measurable query.

    No `FiniteSupportWitness` needed. The Kolmogorov Extension Theorem
    (via `Measure.infinitePi`) constructs the measure directly. -/
theorem wm_queryStrength_eq_infiniteQueryProb (p : ℕ → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (Q : Set (ℕ → Bool)) (hQ : MeasurableSet Q) :
    BinaryWorldModel.queryStrength
      ({infiniteMassSemantics p hp Q hQ} : PLNMarkovLogicAbstract.MassState Unit) ()
    = infiniteFactMeasure p hp Q := by
  rw [PLNMarkovLogicAbstract.MassState.queryStrength_singleton_eq_queryProb]
  exact infiniteMassSemantics_queryProb p hp Q hQ

end Mettapedia.Logic.ProbLogInfinite
