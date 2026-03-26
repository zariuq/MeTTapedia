import Mettapedia.Logic.MarkovLogicOntologyGrowth

/-!
# Individuated Subsystems of Infinite MLNs

This module packages the boundary-stability and ontology-growth theorems
into the language of **individuation** (Simondon 1958, Weinbaum & Veitas 2015).

An `IndividuatedSubsystem` is a finite region Γ of an infinite MLN whose
interaction neighborhood is fully contained within Γ itself.  Such a
subsystem has three formal properties that together constitute a rigorous
analogue of Weinbaum's "open-ended intelligence" coherence condition:

1. **Query stability.**  Any query supported on the subsystem's core has
   answer-discrepancy that decays geometrically with shell depth.  Two
   admissible DLR completions disagree by at most `2|Γ| · C^n` after
   `n` interaction shells.

2. **Ontology robustness.**  Adding or modifying clauses outside the
   subsystem's interaction-closed region does not change the subsystem's
   query answers — not approximately, but exactly.

3. **WM-PLN bridge.**  The subsystem's truth values
   (`queryStrength = μ(q)`) are specification-determined under the
   Dobrushin budget: they depend only on the MLN, not on the choice of
   Gibbs measure.

Together these say: an individuated subsystem has a **stable identity**
(its query answers) that **persists under perturbation** (ontology growth)
and is **uniquely determined** (Dobrushin uniqueness).

**Positive example.**  A cluster of medical concepts with bounded
cross-cluster influence forms an individuated subsystem.  Adding new
social-network concepts far away does not change any medical query.

**Negative example.**  If a newly added concept injects a clause into the
medical cluster's interaction neighborhood, individuation breaks.  And if
the total incoming influence exceeds the Dobrushin budget, the uniqueness
guarantee is lost.

## What this does NOT formalize

- The **process** of a subsystem emerging (dynamic individuation).
- Weinbaum's SAI score or self-transcendence constraint.
- The agent's capacity to identify and maintain its own boundary
  (meta-individuation).

These remain future directions.  The present module formalizes the
**static criterion**: when a subsystem IS individuated, not how it
BECOMES individuated.

## References

- G. Simondon, *Du mode d'existence des objets techniques*, 1958.
- D. R. Weinbaum & V. Veitas, *Open Ended Intelligence: The individuation
  of intelligent agents*, arXiv:1505.06366, 2015.
- V. Veitas & D. R. Weinbaum, *Living Cognitive Society: A `digital'
  world of views*, 2015.
- H.-O. Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., 2011.
-/

namespace Mettapedia.Logic.MarkovLogicIndividuation

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

-- ═══════════════════════════════════════════════════════════════════════════
-- The individuated subsystem structure
-- ═══════════════════════════════════════════════════════════════════════════

/-- An **individuated subsystem** of an infinite MLN: a finite region Γ
    whose full interaction neighborhood is contained within itself.

    Mathematically: `InteractionClosed M Γ` means every atom in Γ has
    all its interacting neighbors also in Γ.  Philosophically: the
    subsystem's internal dynamics are self-contained — its queries are
    determined by its own clauses, not by the exterior. -/
structure IndividuatedSubsystem
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) where
  /-- The core region: the subsystem's "identity." -/
  core : Region Atom
  /-- The core is nonempty (a subsystem must contain at least one atom). -/
  core_nonempty : core.Nonempty
  /-- The core is interaction-closed: all interaction neighborhoods stay
      within the core.  This is the formal individuation condition. -/
  interaction_closed : InteractionClosed M core

/-- The **influence radius** of an individuated subsystem at depth `n`:
    the `n`-th iterated expansion of the core region.  At depth `n`,
    the subsystem's boundary influence is bounded by `C^n`. -/
noncomputable def IndividuatedSubsystem.influenceRadius
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : IndividuatedSubsystem M) (n : ℕ) : Region Atom :=
  M.iterExpandRegion S.core n

-- ═══════════════════════════════════════════════════════════════════════════
-- Theorem 1: Query stability (boundary insensitivity)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Query stability**: any local query on an individuated subsystem has
    answer-discrepancy that decays geometrically with shell depth.

    Two admissible DLR completions of the same specification disagree on
    a query `q` supported on `S.core` by at most `2 · |S.core| · C^n`.

    This is the formal content of "the subsystem's identity is stable":
    different boundary conditions at infinity barely affect local answers. -/
theorem IndividuatedSubsystem.queryDiscrepancy_le_geometric
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : IndividuatedSubsystem M)
    (hM : M.PaperUniformSmallTotalInfluence)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (hν : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)))
    {Δ : Region Atom} (hΔ : Δ = S.core)
    (q : LocalConstraintQuery Atom Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ n : ℕ,
        M.finiteRegionLocalQueryDiscrepancy μ ν Δ q ≤
          2 * (Δ.card : ℝ) * C ^ n := by
  subst hΔ
  exact finiteRegionLocalQueryDiscrepancy_le_geometric_of_uniformSmallTotalInfluence
    M hM μ ν hμ hν S.core q

-- ═══════════════════════════════════════════════════════════════════════════
-- Theorem 2: Ontology robustness (cross-specification invariance)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Ontology robustness**: if a second specification agrees with the first
    on all clauses touching the subsystem's core, and both satisfy the
    Dobrushin budget, then both specifications assign exactly the same
    probability to every query supported on the core.

    This is the formal content of "adding new concepts far away does not
    change the subsystem's answers." -/
theorem IndividuatedSubsystem.queryProb_invariant_under_extension
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : IndividuatedSubsystem M₁)
    (hagree : SpecAgreesOnRegion M₁ M₂ S.core)
    (hclosed₂ : InteractionClosed M₂ S.core)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.core) :
    (infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q =
    (infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q :=
  queryProb_eq_of_specAgreesOnRegion hagree S.interaction_closed hclosed₂
    hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂ q hq

-- ═══════════════════════════════════════════════════════════════════════════
-- Theorem 3: WM bridge uniqueness (specification-determined truth values)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **WM bridge uniqueness**: under the Dobrushin budget, the subsystem's
    WM query strength is uniquely determined by the specification alone.

    Any two DLR measures yield the same `queryProb` for every query
    supported on the subsystem's core.  This means the subsystem's
    truth values are an intrinsic property of the specification, not
    an artifact of which Gibbs measure was selected. -/
theorem IndividuatedSubsystem.wmQueryStrength_unique
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : IndividuatedSubsystem M)
    (hM : M.PaperUniformSmallTotalInfluence)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (hν : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom) :
    (infiniteMLNMassSemantics M μ hμ).queryProb q =
    (infiniteMLNMassSemantics M ν hν).queryProb q :=
  infiniteMLN_queryStrength_unique_of_uniform M hM μ ν hμ hν q

-- ═══════════════════════════════════════════════════════════════════════════
-- Capstone: WM queryStrength stable under ontology extension
-- ═══════════════════════════════════════════════════════════════════════════

open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract.MassState

/-- **Capstone theorem: WM query strength is stable under ontology extension.**

    If an individuated subsystem's core is protected (specs agree on it,
    both satisfy Dobrushin), then the `BinaryWorldModel.queryStrength` —
    the PLN/WM truth value — is exactly the same for both specs.

    This is the full semantic chain:
    infinite MLN → DLR measure → MassSemantics → BinaryEvidence → queryStrength,
    and the queryStrength at the end is invariant under distant ontology growth.

    This is the theorem GPT-5.4 Pro identified as the "most beautiful use
    of the WM layer": the WM side is not a passive probability wrapper
    but the final semantic interface whose stability is guaranteed. -/
theorem IndividuatedSubsystem.wmStrength_stable_under_extension
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : IndividuatedSubsystem M₁)
    (hagree : SpecAgreesOnRegion M₁ M₂ S.core)
    (hclosed₂ : InteractionClosed M₂ S.core)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.core) :
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M₁ μ₁ hμ₁} : MassState (ConstraintQuery Atom)) q =
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M₂ μ₂ hμ₂} : MassState (ConstraintQuery Atom)) q := by
  simp only [MassState.queryStrength_singleton_eq_queryProb]
  exact S.queryProb_invariant_under_extension hagree hclosed₂
    hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂ q hq

end Mettapedia.Logic.MarkovLogicIndividuation
