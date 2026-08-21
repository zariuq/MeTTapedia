import Mettapedia.GSLT.Dynamics.ObservationDiscipline
import Mettapedia.PLN.Bridges.GSLT.EvidenceCostReadout

/-!
# PLN evidence as an observation discipline

Full binary evidence is retained in the witness container.  Propensity is a
declared value readout from that container, while work/span is an independent
observation of the same operational events.  The product discipline retains
both axes; no blended scalar is treated as their semantic carrier.
-/

namespace Mettapedia.PLN.Bridges.GSLT.ObservationDiscipline

open scoped ENNReal

open Mettapedia.Algebra
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.Dynamics.WorkSpanObservation
open Mettapedia.PLN.Bridges.GSLT.EvidenceCostReadout
open Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler
open Mettapedia.PLN.Evidence.EvidenceQuantale

noncomputable section

universe uEvent

/-- Accumulate occurrence evidence in its native additive carrier. -/
def evidenceValuation {Event : Type uEvent}
    (evidence : Event -> BinaryEvidence) : Valuation Event :=
  additive evidence

/-- Full evidence is both the retained container and the identity readout. -/
def evidenceDiscipline {Event : Type uEvent}
    (evidence : Event -> BinaryEvidence) :
    Mettapedia.GSLT.Dynamics.ObservationDiscipline Event :=
  Mettapedia.GSLT.Dynamics.ObservationDiscipline.ofValuation
    (evidenceValuation evidence)

/-- Propensity changes only the value dial; its witness container remains
full revisable evidence. -/
def propensityDiscipline {Event : Type uEvent}
    (prior : ℝ≥0∞) (evidence : Event -> BinaryEvidence) :
    Mettapedia.GSLT.Dynamics.ObservationDiscipline Event :=
  (evidenceDiscipline evidence).mapValue (propensity prior)

@[simp] theorem propensity_readout {Event : Type uEvent}
    (prior : ℝ≥0∞) (evidence : Event -> BinaryEvidence)
    (value : BinaryEvidence) :
    (propensityDiscipline prior evidence).readout value =
      propensity prior value :=
  rfl

/-- The evidence and propensity disciplines use definitionally the same
witness collector. -/
theorem propensity_collection_eq_evidence_collection {Event : Type uEvent}
    (prior : ℝ≥0∞) (evidence : Event -> BinaryEvidence) :
    (propensityDiscipline prior evidence).collection =
      (evidenceDiscipline evidence).collection :=
  rfl

/-- Unit-prior propensity is a lossy readout of its retained evidence. -/
theorem propensity_isLossy {Event : Type uEvent}
    (evidence : Event -> BinaryEvidence) :
    (propensityDiscipline 1 evidence).Lossy := by
  apply Mettapedia.GSLT.Dynamics.ObservationDiscipline.lossy_of_collision
    (first := concentratedEvidence) (second := mixedEvidence)
  · exact concentratedEvidence_ne_mixedEvidence
  · exact propensity_collision

/-- No decoder from scalar propensity reconstructs the full evidence
container. -/
theorem no_evidence_reconstruction_from_discipline_propensity
    {Event : Type uEvent} (evidence : Event -> BinaryEvidence) :
    ¬ ∃ recover : ℝ≥0∞ -> BinaryEvidence,
      Function.LeftInverse recover
        (propensityDiscipline 1 evidence).readout :=
  Mettapedia.GSLT.Dynamics.ObservationDiscipline.no_reconstruction_of_lossy
    (propensityDiscipline 1 evidence) (propensity_isLossy evidence)

/-! ## Evidence and resource observations of one event family -/

/-- One operational occurrence with separate epistemic and resource data. -/
structure ObservedEvent where
  evidence : BinaryEvidence
  resources : WorkSpan

/-- The product retains evidence and work/span as separate coordinates. -/
def evidenceAndResources :
    Mettapedia.GSLT.Dynamics.ObservationDiscipline ObservedEvent :=
  (evidenceDiscipline ObservedEvent.evidence).prod
    (discipline ObservedEvent.resources)

def concentratedCheap : ObservedEvent :=
  ⟨concentratedEvidence, ⟨1, 1⟩⟩

def mixedCheap : ObservedEvent :=
  ⟨mixedEvidence, ⟨1, 1⟩⟩

@[simp] theorem concentratedCheap_observe :
    evidenceAndResources.observe [concentratedCheap] =
      some (concentratedEvidence, (⟨1, 1⟩ : WorkSpan)) := by
  simp [evidenceAndResources, evidenceDiscipline, evidenceValuation,
    Mettapedia.GSLT.Dynamics.ObservationDiscipline.observe,
    Mettapedia.GSLT.Dynamics.ObservationDiscipline.prod,
    Mettapedia.GSLT.Dynamics.ObservationDiscipline.ofValuation,
    Mettapedia.GSLT.Dynamics.WitnessCollector.ofValuation,
    Mettapedia.GSLT.Dynamics.WitnessCollector.prod,
    WorkSpanObservation.discipline, WorkSpanObservation.valuation,
    WorkSpanObservation.sequentialAlgebra, concentratedCheap]
  rw [(additivePartialMonoid BinaryEvidence).op_unit concentratedEvidence]
  rfl

@[simp] theorem mixedCheap_observe :
    evidenceAndResources.observe [mixedCheap] =
      some (mixedEvidence, (⟨1, 1⟩ : WorkSpan)) := by
  simp [evidenceAndResources, evidenceDiscipline, evidenceValuation,
    Mettapedia.GSLT.Dynamics.ObservationDiscipline.observe,
    Mettapedia.GSLT.Dynamics.ObservationDiscipline.prod,
    Mettapedia.GSLT.Dynamics.ObservationDiscipline.ofValuation,
    Mettapedia.GSLT.Dynamics.WitnessCollector.ofValuation,
    Mettapedia.GSLT.Dynamics.WitnessCollector.prod,
    WorkSpanObservation.discipline, WorkSpanObservation.valuation,
    WorkSpanObservation.sequentialAlgebra, mixedCheap]
  rw [(additivePartialMonoid BinaryEvidence).op_unit mixedEvidence]
  rfl

/-- Equal work/span does not identify distinct evidence. -/
theorem same_resources_different_evidence :
    concentratedCheap.resources = mixedCheap.resources ∧
      concentratedCheap.evidence ≠ mixedCheap.evidence :=
  ⟨rfl, concentratedEvidence_ne_mixedEvidence⟩

/-- The product observation preserves the epistemic distinction even when
the resource coordinate is equal. -/
theorem combined_observation_distinguishes_evidence :
    evidenceAndResources.observe [concentratedCheap] ≠
      evidenceAndResources.observe [mixedCheap] := by
  rw [concentratedCheap_observe, mixedCheap_observe]
  intro equal
  exact concentratedEvidence_ne_mixedEvidence
    (congrArg (fun value => value.map Prod.fst) equal |> Option.some.inj)

end

end Mettapedia.PLN.Bridges.GSLT.ObservationDiscipline
