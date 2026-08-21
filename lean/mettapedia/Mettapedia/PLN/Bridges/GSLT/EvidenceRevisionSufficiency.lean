import Mettapedia.PLN.Bridges.GSLT.EvidenceResolutionAlgebra

/-!
# Dynamic sufficiency of PLN evidence

A scalar resolution grade can be sufficient for the next scheduling choice
without being sufficient for the next learning update.  This file states the
distinction as a commuting-square law.

For a state readout `observe : State → Value`, revision descends to `Value`
only when there is a value-level update making every square commute:

```
State  --revise observation-->  State
  |                              |
observe                        observe
  |                              |
  v                              v
Value  --update observation-->  Value
```

The kernel of any such readout must be stable under revision.  Unit-prior PLN
propensity fails this necessary condition: `concentratedEvidence` and
`mixedEvidence` have the same present propensity, but one additional positive
observation gives them different next propensities.  Consequently no learner
whose complete epistemic state is that scalar can implement PLN revision.

The theorem is deliberately relative to the declared propensity readout.  It
does not claim that a real number cannot set-theoretically encode a pair.  The
positive result is that the native two-coordinate sufficient statistic
`BinaryEvidence` is closed under revision, while the scheduler projection is
not.  Raw additive revision retains its existing independent-evidence scope;
provenance admissibility is handled by the stamped-witness bridge.
-/

namespace Mettapedia.PLN.Bridges.GSLT.EvidenceRevisionSufficiency

open scoped ENNReal

open Mettapedia.PLN.Bridges.GSLT.EvidenceCostReadout
open Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler
open Mettapedia.PLN.Bridges.GSLT.GuidanceOptimization
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision

noncomputable section

universe uState uObservation uValue

/-- A state transition driven by an observation, together with the value seen
by a controller. -/
structure RevisionObservation
    (State : Type uState) (Observation : Type uObservation)
    (Value : Type uValue) where
  revise : State → Observation → State
  observe : State → Value

namespace RevisionObservation

/-- Revision is visible entirely at the readout level when one value-level
update makes the state-level revision square commute for every state and
observation. -/
def FactorsThrough {State : Type uState} {Observation : Type uObservation}
    {Value : Type uValue}
    (system : RevisionObservation State Observation Value) : Prop :=
  ∃ update : Value → Observation → Value,
    ∀ state observation,
      update (system.observe state) observation =
        system.observe (system.revise state observation)

/-- A necessary quotient condition for value-level revision: states identified
by the readout must remain identified after receiving the same observation. -/
def KernelStable {State : Type uState} {Observation : Type uObservation}
    {Value : Type uValue}
    (system : RevisionObservation State Observation Value) : Prop :=
  ∀ left right observation,
    system.observe left = system.observe right →
      system.observe (system.revise left observation) =
        system.observe (system.revise right observation)

/-- Every readout through which revision factors has a revision-stable kernel. -/
theorem kernelStable_of_factorsThrough
    {State : Type uState} {Observation : Type uObservation}
    {Value : Type uValue}
    (system : RevisionObservation State Observation Value)
    (factors : system.FactorsThrough) : system.KernelStable := by
  obtain ⟨update, commutes⟩ := factors
  intro left right observation sameValue
  calc
    system.observe (system.revise left observation) =
        update (system.observe left) observation :=
      (commutes left observation).symm
    _ = update (system.observe right) observation := by rw [sameValue]
    _ = system.observe (system.revise right observation) :=
      commutes right observation

/-- A collision that is separated by one common observation rules out every
possible value-level revision operation. -/
theorem not_factorsThrough_of_collision
    {State : Type uState} {Observation : Type uObservation}
    {Value : Type uValue}
    (system : RevisionObservation State Observation Value)
    {left right : State} {observation : Observation}
    (collision : system.observe left = system.observe right)
    (separation :
      system.observe (system.revise left observation) ≠
        system.observe (system.revise right observation)) :
    ¬ system.FactorsThrough := by
  intro factors
  exact separation
    (kernelStable_of_factorsThrough system factors left right observation
      collision)

end RevisionObservation

/-! ## The PLN mortal-scientist witness -/

/-- Full binary evidence with raw independent-evidence revision and unit-prior
propensity as the controller-visible value. -/
def propensityRevisionSystem :
    RevisionObservation BinaryEvidence BinaryEvidence ℝ≥0∞ where
  revise := revision
  observe := propensity 1

/-- The propensity quotient is not stable under PLN revision.  Thus equal
present execution rates do not imply equal rates after a shared observation. -/
theorem propensity_kernel_not_revisionStable :
    ¬ propensityRevisionSystem.KernelStable := by
  intro stable
  exact revised_propensity_separates_collision
    (stable concentratedEvidence mixedEvidence positiveObservation
      propensity_collision)

/-- **Dynamic insufficiency of scalar propensity.**  There is no update on the
current propensity and incoming evidence alone that reproduces PLN revision for
all evidence states. -/
theorem no_propensity_only_revision :
    ¬ ∃ update : ℝ≥0∞ → BinaryEvidence → ℝ≥0∞,
      ∀ state observation,
        update (propensity 1 state) observation =
          propensity 1 (revision state observation) := by
  exact RevisionObservation.not_factorsThrough_of_collision
    propensityRevisionSystem propensity_collision
      revised_propensity_separates_collision

/-- Even when the only possible next observation is one positive occurrence,
no autonomous update of the scalar propensity can be correct for every state. -/
theorem no_propensity_only_positive_update :
    ¬ ∃ update : ℝ≥0∞ → ℝ≥0∞,
      ∀ state,
        update (propensity 1 state) =
          propensity 1 (revision state positiveObservation) := by
  rintro ⟨update, commutes⟩
  apply revised_propensity_separates_collision
  calc
    propensity 1 (revision concentratedEvidence positiveObservation) =
        update (propensity 1 concentratedEvidence) :=
      (commutes concentratedEvidence).symm
    _ = update (propensity 1 mixedEvidence) := by rw [propensity_collision]
    _ = propensity 1 (revision mixedEvidence positiveObservation) :=
      commutes mixedEvidence

/-- Full evidence itself is a dynamically sufficient observation state:
revision is performed once on the sufficient statistics, before any lossy
scheduler readout. -/
def evidenceRevisionSystem :
    RevisionObservation BinaryEvidence BinaryEvidence BinaryEvidence where
  revise := revision
  observe := id

theorem evidence_revision_factorsThrough :
    evidenceRevisionSystem.FactorsThrough := by
  exact ⟨revision, fun _ _ => rfl⟩

/-- The two colliding scheduler grades retain different confidence coordinates:
the one-observation state has confidence `1/2`, while the three-observation
state has confidence `3/4`. -/
theorem confidence_separates_propensity_collision :
    BinaryEvidence.toConfidence 1 concentratedEvidence ≠
      BinaryEvidence.toConfidence 1 mixedEvidence := by
  intro equal
  have realEqual := congrArg ENNReal.toReal equal
  norm_num [BinaryEvidence.toConfidence, BinaryEvidence.total,
    concentratedEvidence, mixedEvidence, ENNReal.toReal_div] at realEqual

/-- The concrete rates in the counterexample.  Both beliefs presently fund the
same Gillespie-style rate `1/2`; after one positive observation the correct
rates are respectively `2/3` and `3/5`. -/
theorem mortalScientist_exact_rate_update :
    propensity 1 concentratedEvidence = (1 : ℝ≥0∞) / 2 ∧
    propensity 1 mixedEvidence = (1 : ℝ≥0∞) / 2 ∧
    propensity 1 (revision concentratedEvidence positiveObservation) =
      (2 : ℝ≥0∞) / 3 ∧
    propensity 1 (revision mixedEvidence positiveObservation) =
      (3 : ℝ≥0∞) / 5 := by
  have concentratedRate :
      propensity 1 concentratedEvidence = (1 : ℝ≥0∞) / 2 := by
    norm_num [propensity, ScoreFusion.binaryEvidenceFusedQuality,
      BinaryEvidence.total, concentratedEvidence]
  refine ⟨concentratedRate, propensity_collision.symm.trans concentratedRate,
    ?_, ?_⟩
  · norm_num [propensity, ScoreFusion.binaryEvidenceFusedQuality,
      BinaryEvidence.total, revision, BinaryEvidence.hplus_def,
      concentratedEvidence, positiveObservation]
  · norm_num [propensity, ScoreFusion.binaryEvidenceFusedQuality,
      BinaryEvidence.total, revision, BinaryEvidence.hplus_def,
      mixedEvidence, positiveObservation]

/-- One theorem packages the mortal-scientist counterexample: the two beliefs
license the same present stochastic rate, their retained confidence differs,
and the same next positive observation forces different future rates. -/
theorem mortalScientist_needs_retained_evidence :
    propensity 1 concentratedEvidence = propensity 1 mixedEvidence ∧
    BinaryEvidence.toConfidence 1 concentratedEvidence ≠
      BinaryEvidence.toConfidence 1 mixedEvidence ∧
    propensity 1 (revision concentratedEvidence positiveObservation) ≠
      propensity 1 (revision mixedEvidence positiveObservation) ∧
    ¬ ∃ update : ℝ≥0∞ → ℝ≥0∞,
      ∀ state,
        update (propensity 1 state) =
          propensity 1 (revision state positiveObservation) :=
  ⟨propensity_collision, confidence_separates_propensity_collision,
    revised_propensity_separates_collision,
    no_propensity_only_positive_update⟩

#print axioms RevisionObservation.kernelStable_of_factorsThrough
#print axioms RevisionObservation.not_factorsThrough_of_collision
#print axioms propensity_kernel_not_revisionStable
#print axioms no_propensity_only_revision
#print axioms no_propensity_only_positive_update
#print axioms evidence_revision_factorsThrough
#print axioms confidence_separates_propensity_collision
#print axioms mortalScientist_exact_rate_update
#print axioms mortalScientist_needs_retained_evidence

end

end Mettapedia.PLN.Bridges.GSLT.EvidenceRevisionSufficiency
