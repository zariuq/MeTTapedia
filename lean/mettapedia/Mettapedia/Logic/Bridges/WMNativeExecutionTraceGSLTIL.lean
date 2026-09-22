import Mettapedia.Logic.Bridges.WMNativeCapabilityComputation
import Mettapedia.OSLF.Framework.WMCalculusOccurrenceTrace

/-!
# Authored WM execution traces in the relational internal language

The extensional syntax-to-capability relation has a unique checked semantic
request and therefore forgets operational multiplicity. This module refines
its first leg by an actual Type-valued execution trace. The resulting
GSLT-IL chain retains the reduced typed request, each contextual rule
occurrence, the interpreted semantic request, and the supported answer
receipt. Erasing those traces returns exactly the old relation's support,
but not an equivalence of evidence fibres: distinct executions remain
distinct data.
-/


set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.WMNativeExecutionTraceGSLTIL

open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.RelationPresentation
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusOccurrenceTrace
open Mettapedia.OSLF.Framework.WMCalculusNativeContextExample
open Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL
open Mettapedia.Logic.Bridges.WMNativeCapabilityComputation

abbrev TermRequest := WMTerm .state × WMTerm .query

/-- The first GSLT-IL leg retains a contextual execution independently in
each typed component of a request. -/
def executionRelation : Mettapedia.GSLT.RelationPresentation.Rel TermRequest TermRequest where
  evidence source target :=
    WMTrace source.1 target.1 × WMTrace source.2 target.2

/-- Exact support of the execution relation is the pair of authored
contextual reachability claims. -/
theorem executionRelation_support_iff (source target : TermRequest) :
    Nonempty (executionRelation.evidence source target) ↔
      Mettapedia.OSLF.Framework.WMCalculusContextEncoding.WMContextStepStar
        source.1 target.1 ∧
      Mettapedia.OSLF.Framework.WMCalculusContextEncoding.WMContextStepStar
        source.2 target.2 := by
  constructor
  · rintro ⟨stateTrace, queryTrace⟩
    exact ⟨stateTrace.erase, queryTrace.erase⟩
  · rintro ⟨stateSteps, querySteps⟩
    obtain ⟨stateTrace⟩ := trace_support_iff.mpr stateSteps
    obtain ⟨queryTrace⟩ := trace_support_iff.mpr querySteps
    exact ⟨stateTrace, queryTrace⟩

/-- The chained relation retains both operational paths, the reduced term
request, and the complete semantic capability receipt. -/
def tracedCapabilityChain {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    Mettapedia.GSLT.RelationPresentation.Rel TermRequest V :=
  Mettapedia.GSLT.RelationPresentation.Rel.Chain executionRelation (termCapabilityChain capability)

/-- Forget the actual execution while preserving the checked answer at the
source request. The inverse is not asserted: the source may have many traces. -/
def forgetExecution {State Query V : Type}
    {R : WMReading State Query V} (laws : R.CoreLaws)
    (capability : WMCapability R)
    (source : TermRequest) (answer : V)
    (witness : (tracedCapabilityChain capability).evidence source answer) :
    (termCapabilityChain capability).evidence source answer :=
  (chainEvidenceEquivOfPairSteps capability laws
    witness.2.1.1.erase witness.2.1.2.erase answer).symm witness.2.2

/-- The trace-aware chain and the extensional chain admit exactly the same
answers. The forward map forgets genuine occurrence identity; the reverse
direction chooses the zero-step execution, not an inverse on witnesses. -/
theorem tracedCapabilityChain_support_iff {State Query V : Type}
    {R : WMReading State Query V} (laws : R.CoreLaws)
    (capability : WMCapability R)
    (source : TermRequest) (answer : V) :
    Nonempty ((tracedCapabilityChain capability).evidence source answer) ↔
      Nonempty ((termCapabilityChain capability).evidence source answer) := by
  constructor
  · rintro ⟨witness⟩
    exact ⟨forgetExecution laws capability source answer witness⟩
  · rintro ⟨receipt⟩
    exact ⟨⟨source, (WMTrace.refl, WMTrace.refl), receipt⟩⟩

/-- The trace-aware syntax-to-answer relation has an answer precisely for
supported source requests; execution adds evidence, not extra admission. -/
theorem tracedCapabilityChain_has_answer_iff {State Query V : Type}
    {R : WMReading State Query V} (laws : R.CoreLaws)
    (capability : WMCapability R) (source : TermRequest) :
    Nonempty (Sigma fun answer =>
      (tracedCapabilityChain capability).evidence source answer) ↔
        capability.supports (R.denote source.1) (R.denote source.2) := by
  constructor
  · rintro ⟨⟨answer, witness⟩⟩
    exact (termCapabilityChain_has_answer_iff capability source).1
      ⟨⟨answer, forgetExecution laws capability source answer witness⟩⟩
  · intro supported
    obtain ⟨⟨answer, receipt⟩⟩ :=
      (termCapabilityChain_has_answer_iff capability source).2 supported
    exact ⟨⟨answer, ⟨source, (WMTrace.refl, WMTrace.refl), receipt⟩⟩⟩

/-- A total Boolean query capability. Its GSLT-IL trace relation will still
not be functionally representable because executions are proof-relevant. -/
def totalBooleanCapability : WMCapability booleanReading where
  supports := fun _ _ => True
  respectsAgree := by
    intro first second query agree
    exact Iff.rfl

theorem totalBooleanCapability_all_supported (request : Bool × Unit) :
    totalBooleanCapability.supports request.1 request.2 :=
  trivial

private def specimenState : WMTerm .state :=
  .revise (.state "on") (.state "off")
private def specimenQuery : WMTerm .query := .query "available"
private def specimenRequest : TermRequest := (specimenState, specimenQuery)
private def specimenAnswer : Bool :=
  booleanReading.extract (booleanReading.denote specimenState)
    (booleanReading.denote specimenQuery)

private def specimenReceipt :
    (termCapabilityChain totalBooleanCapability).evidence
      specimenRequest specimenAnswer :=
  ⟨(booleanReading.denote specimenState,
      booleanReading.denote specimenQuery),
    ⟨rfl⟩, ⟨trivial, rfl⟩⟩

/-- A zero-step execution carrying the checked Boolean answer. -/
def zeroStepWitness :
    (tracedCapabilityChain totalBooleanCapability).evidence
      specimenRequest specimenAnswer :=
  ⟨specimenRequest, (WMTrace.refl, WMTrace.refl), specimenReceipt⟩

/-- Two genuine, opposite revision-rule occurrences return to the same
request and yield the same checked answer. -/
def roundtripWitness :
    (tracedCapabilityChain totalBooleanCapability).evidence
      specimenRequest specimenAnswer :=
  ⟨specimenRequest,
    (revisionCommRoundtrip (.state "on") (.state "off"), WMTrace.refl),
    specimenReceipt⟩

/-- Trace erasure loses information even when every request is supported
and the checked answer is unchanged. -/
theorem zeroStep_ne_roundtrip : zeroStepWitness ≠ roundtripWitness := by
  intro equal
  have lengthEqual := congrArg
    (fun witness : (tracedCapabilityChain totalBooleanCapability).evidence
      specimenRequest specimenAnswer => witness.2.1.1.length) equal
  change (0 : Nat) = 2 at lengthEqual
  omega

/-- The relation cannot be compiled as a function in proof-relevant GSLT-IL,
despite total support and a single extensional answer per request. A
functional readout must explicitly forget execution evidence first. -/
theorem tracedTotalBoolean_not_representable :
    ¬ Nonempty (Mettapedia.GSLT.RelationPresentation.Rel.Representation
      (tracedCapabilityChain totalBooleanCapability)) := by
  rintro ⟨representation⟩
  have fibreSubsingleton : Subsingleton
      ((tracedCapabilityChain totalBooleanCapability).evidence
        specimenRequest specimenAnswer) :=
    Mettapedia.GSLT.LooseRelationEquipment.Representation.fibreSubsingleton
      representation.deterministic specimenRequest specimenAnswer
  exact zeroStep_ne_roundtrip
    (fibreSubsingleton.allEq zeroStepWitness roundtripWitness)

end Mettapedia.Logic.Bridges.WMNativeExecutionTraceGSLTIL
