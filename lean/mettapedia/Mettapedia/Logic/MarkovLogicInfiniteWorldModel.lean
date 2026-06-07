import Mettapedia.Logic.MarkovLogicAbstract
import Mettapedia.Logic.MarkovLogicInfiniteUniqueness

/-!
# The Gibbs-to-World-Model Bridge for Infinite Markov Logic Networks

This module closes the semantic gap between two independently developed
formalizations:

  (A) **Infinite MLN measure theory.** A `ClassicalInfiniteGroundMLNSpec`
      over a countable atom set admits at least one DLR/Gibbs probability
      measure on the infinite Boolean product `InfiniteWorld Atom`
      (proved in `MarkovLogicInfiniteExistence`), and at most one such
      measure when the uniform Dobrushin contraction condition holds
      (proved in `MarkovLogicInfiniteUniqueness`).

  (B) **The PLN World Model calculus.** A `MassSemantics` object packages
      query-mass and total-mass data into `BinaryEvidence`, which in turn
      instantiates a `BinaryWorldModel` with `queryStrength`, `queryConfidence`,
      and simple truth-value views (developed in `MarkovLogicAbstract`).

The bridge is elementary once the right abstraction is chosen: a probability
measure has total mass 1, so the `MassSemantics` record is immediate.  The
resulting pipeline reads:

```text
ClassicalInfiniteGroundMLNSpec M
      │  (DLR existence)
      ▼
ProbabilityMeasure μ on InfiniteWorld Atom
      │  infiniteMLNMassSemantics
      ▼
MassSemantics (ConstraintQuery Atom)
    queryMass q  =  μ { ω | ω satisfies q }
    totalMass    =  1
      │  evidenceOfMasses
      ▼
BinaryEvidence  ⟨ μ(q) ,  1 − μ(q) ⟩
      │  toStrength
      ▼
queryStrength  =  μ(q)
```

The final identity `queryStrength = μ(q)` is trivial yet load-bearing: it says
that the probabilistic semantics of an infinite relational knowledge base
is faithfully reflected in the algebraic WM/PLN truth-value calculus.

## Uniqueness and specification-determined semantics

Under the uniform Dobrushin condition (Dobrushin 1968; Georgii, *Gibbs Measures
and Phase Transitions*, Theorem 8.7), the DLR measure is unique.  Therefore
`infiniteMLN_queryStrength_unique_of_uniform` guarantees that the query
strength depends only on the MLN specification `M` — not on the particular
Gibbs measure selected.  This is the rigorous counterpart of the informal
assumption in Singla and Domingos (2006) that an MLN "defines a probability
distribution" rather than merely constraining a family of distributions.

**Positive example.**  An unbounded chain of agents, each influencing only
nearest neighbours with weights bounded by a global constant, satisfies the
Dobrushin condition.  Its belief probabilities are uniquely determined, and
the WM bridge provides a single, well-defined truth value for any finite query.

**Negative example (phase transitions).**  Without the contraction bound,
an infinite Ising-type MLN at low temperature admits coexisting `+` and `−`
Gibbs measures with distinct singleton marginals.  The bridge still works for
each measure individually, but different measures yield different query
strengths.  The uniqueness theorem is genuinely conditional; no general
uniqueness claim is made or could be made.

## References

- R. L. Dobrushin, *The description of a random field by means of conditional
  probabilities and conditions of its regularity*, Theor. Probab. Appl. 13
  (1968), 197--224.
- H.-O. Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., de Gruyter,
  2011, Theorem 8.7.
- P. Singla and M. Domingos, *Discriminative training of Markov logic networks*,
  AAAI 2005; *Entity resolution with Markov logic*, ICDM 2006.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteWorldModel

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open MeasureTheory
open scoped ENNReal

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- The cylinder event for a finite constraint query `q`:
    the set of all infinite Boolean worlds that satisfy every atom–value
    constraint in `q`.  This is measurable as a finite intersection of
    coordinate-projection preimages. -/
def infiniteQueryEvent
    (q : ConstraintQuery Atom) :
    Set (InfiniteWorld Atom) :=
  {ω | satisfiesConstraints ω q}

omit [DecidableEq Atom] in
/-- Infinite finite-constraint query events are measurable cylinder events. -/
theorem measurableSet_infiniteQueryEvent
    (q : ConstraintQuery Atom) :
    MeasurableSet (infiniteQueryEvent (Atom := Atom) q) := by
  classical
  induction q with
  | nil =>
      simp [infiniteQueryEvent, satisfiesConstraints]
  | cons c cs ih =>
      have hc :
          MeasurableSet {ω : InfiniteWorld Atom | ω c.1 = c.2} := by
        simpa using
          (measurableSet_eq_fun (measurable_pi_apply c.1) measurable_const)
      have htail :
          MeasurableSet {ω : InfiniteWorld Atom | satisfiesConstraints ω cs} := by
        simpa [infiniteQueryEvent] using ih
      have hset :
          infiniteQueryEvent (Atom := Atom) (c :: cs) =
            ({ω : InfiniteWorld Atom | ω c.1 = c.2} ∩
              {ω : InfiniteWorld Atom | satisfiesConstraints ω cs}) := by
        ext ω
        simp [infiniteQueryEvent, satisfiesConstraints]
      rw [hset]
      exact hc.inter htail

/-- **Mass semantics induced by a DLR measure.**

    Every probability measure `μ` on `InfiniteWorld Atom` gives rise to a
    `MassSemantics` with `totalMass = 1` and `queryMass q = μ(infiniteQueryEvent q)`.
    The DLR hypothesis `hμ` is carried but not consumed; it witnesses that `μ`
    arose from the Gibbs specification of `M`, justifying the semantic
    interpretation as an MLN query probability.

    This is the infinite analogue of `compiledMassSemantics` used in the
    finite-support bridge (`MarkovLogicWorldModel`). -/
noncomputable def infiniteMLNMassSemantics
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : ProbabilityMeasure (InfiniteWorld Atom))
    (_hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom))) :
    MassSemantics (ConstraintQuery Atom) where
  queryMass q := (μ : Measure (InfiniteWorld Atom)) (infiniteQueryEvent q)
  totalMass := 1
  queryMass_le_total q := by
    calc (μ : Measure (InfiniteWorld Atom)) (infiniteQueryEvent q)
        ≤ (μ : Measure (InfiniteWorld Atom)) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := by exact_mod_cast MeasureTheory.measure_univ (μ := (μ : Measure (InfiniteWorld Atom)))
  totalMass_ne_top := ENNReal.one_ne_top

/-- The mass-semantics query probability is exactly the measure of the
measurable finite-cylinder query event. -/
theorem infiniteMLNMassSemantics_queryProb_eq_measure_infiniteQueryEvent
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom) :
    (infiniteMLNMassSemantics M μ hμ).queryProb q =
      (μ : Measure (InfiniteWorld Atom)) (infiniteQueryEvent q) := by
  simp [MassSemantics.queryProb, infiniteMLNMassSemantics]

/-- **WM query strength equals Gibbs probability.**

    For a singleton `MassState` built from the infinite-MLN mass semantics,
    the `BinaryWorldModel.queryStrength` coincides with `queryProb`, which
    in turn equals `μ(infiniteQueryEvent q) / 1 = μ(infiniteQueryEvent q)`.

    The proof composes `MassState.queryStrength_singleton_eq_queryProb`
    (from `MarkovLogicAbstract`) with no further work — the types carry
    the content. -/
theorem infiniteMLN_queryStrength_eq_gibbsProb
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom) :
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M μ hμ} : MassState (ConstraintQuery Atom)) q =
    (infiniteMLNMassSemantics M μ hμ).queryProb q := by
  exact MassState.queryStrength_singleton_eq_queryProb _ q

/-- **Uniqueness: the bridge is specification-determined under Dobrushin.**

    When `M.PaperUniformSmallTotalInfluence` holds — i.e., the Dobrushin
    interdependence matrix has spectral radius strictly less than 1 — the
    DLR measure for `M` is unique.  Consequently the `queryProb` produced
    by `infiniteMLNMassSemantics` is independent of which DLR witness is
    supplied.

    Concretely: if `μ` and `ν` both satisfy `FixedRegionCylinderDLR` for `M`,
    then `μ = ν` (by `paperUniformSmallTotalInfluence_implies_paperUniqueMeasure`),
    and the query probabilities coincide. -/
theorem infiniteMLN_queryStrength_unique_of_uniform
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (hν : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom) :
    (infiniteMLNMassSemantics M μ hμ).queryProb q =
    (infiniteMLNMassSemantics M ν hν).queryProb q := by
  have hmeq : (μ : Measure (InfiniteWorld Atom)) = (ν : Measure (InfiniteWorld Atom)) :=
    M.paperUniformSmallTotalInfluence_implies_paperUniqueMeasure hM μ ν hμ hν
  simp only [MassSemantics.queryProb, infiniteMLNMassSemantics]
  rw [hmeq]

end Mettapedia.Logic.MarkovLogicInfiniteWorldModel
