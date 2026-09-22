import Mettapedia.Logic.Bridges.WMNativeExecutionTraceGSLTIL
import Mettapedia.OSLF.Framework.WMCalculusExecutableTrace

/-!
# Premise-aware WM execution receipts in GSLT-IL

This first relational leg records finite engine occurrences, including the
fuel and each rule/alternative index. The second leg is the existing typed
world-model capability and checked answer receipt. On support, the composite
agrees with the typed-event chain and with the extensional capability chain;
the proof-relevant evidence fibres are not asserted to be equivalent.
-/


set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.WMExecutableTraceGSLTIL

open Mettapedia.GSLT.RelationPresentation
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusExecutableTrace
open Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL
open Mettapedia.Logic.Bridges.WMNativeCapabilityComputation
open Mettapedia.Logic.Bridges.WMNativeExecutionTraceGSLTIL

/-- The first GSLT-IL leg retains one numbered, premise-aware engine trace
for each typed component of the request. -/
def executableRelation : Mettapedia.GSLT.RelationPresentation.Rel TermRequest TermRequest where
  evidence source target :=
    ExecutableWMTrace source.1 target.1 ×
      ExecutableWMTrace source.2 target.2

/-- Machine-indexed and typed-constructor execution relations admit exactly
the same endpoint pairs, without identifying their evidence fibres. -/
theorem executableRelation_typed_support_iff (source target : TermRequest) :
    Nonempty (executableRelation.evidence source target) ↔
      Nonempty (executionRelation.evidence source target) := by
  constructor
  · rintro ⟨stateTrace, queryTrace⟩
    obtain ⟨stateTyped⟩ :=
      (executableTrace_typedTrace_support_iff source.1 target.1).mp
        ⟨stateTrace⟩
    obtain ⟨queryTyped⟩ :=
      (executableTrace_typedTrace_support_iff source.2 target.2).mp
        ⟨queryTrace⟩
    exact ⟨stateTyped, queryTyped⟩
  · rintro ⟨stateTrace, queryTrace⟩
    obtain ⟨stateMachine⟩ :=
      (executableTrace_typedTrace_support_iff source.1 target.1).mpr
        ⟨stateTrace⟩
    obtain ⟨queryMachine⟩ :=
      (executableTrace_typedTrace_support_iff source.2 target.2).mpr
        ⟨queryTrace⟩
    exact ⟨stateMachine, queryMachine⟩

/-- A WM answer relation that keeps the actual finite compiler occurrences,
the reduced term request, the interpreted semantic request, and the checked
capability answer. -/
def executableCapabilityChain {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    Mettapedia.GSLT.RelationPresentation.Rel TermRequest V :=
  Mettapedia.GSLT.RelationPresentation.Rel.Chain executableRelation (termCapabilityChain capability)

/-- Forget the finite machine trace while retaining the checked answer at
the original term request. This is a many-to-one erasure in general. -/
def forgetExecutable {State Query V : Type}
    {R : WMReading State Query V} (laws : R.CoreLaws)
    (capability : WMCapability R) (source : TermRequest) (answer : V)
    (witness : (executableCapabilityChain capability).evidence source answer) :
    (termCapabilityChain capability).evidence source answer :=
  (chainEvidenceEquivOfPairSteps capability laws
    witness.2.1.1.erase witness.2.1.2.erase answer).symm witness.2.2

/-- Executable provenance adds no new answer values and loses none, assuming
the WM core laws. The reverse direction chooses two zero-step traces. -/
theorem executableCapabilityChain_support_iff {State Query V : Type}
    {R : WMReading State Query V} (laws : R.CoreLaws)
    (capability : WMCapability R) (source : TermRequest) (answer : V) :
    Nonempty ((executableCapabilityChain capability).evidence source answer) ↔
      Nonempty ((termCapabilityChain capability).evidence source answer) := by
  constructor
  · rintro ⟨witness⟩
    exact ⟨forgetExecutable laws capability source answer witness⟩
  · rintro ⟨receipt⟩
    exact ⟨⟨source, (ExecutableWMTrace.refl, ExecutableWMTrace.refl), receipt⟩⟩

/-- The executable and typed-event GSLT-IL composites have the same answer
support; their occurrence records remain distinct data. -/
theorem executableCapabilityChain_typed_support_iff {State Query V : Type}
    {R : WMReading State Query V} (laws : R.CoreLaws)
    (capability : WMCapability R) (source : TermRequest) (answer : V) :
    Nonempty ((executableCapabilityChain capability).evidence source answer) ↔
      Nonempty ((tracedCapabilityChain capability).evidence source answer) :=
  (executableCapabilityChain_support_iff laws capability source answer).trans
    (tracedCapabilityChain_support_iff laws capability source answer).symm

/-- An executable, checked answer exists precisely for a supported source
request, despite the extra machine provenance. -/
theorem executableCapabilityChain_has_answer_iff {State Query V : Type}
    {R : WMReading State Query V} (laws : R.CoreLaws)
    (capability : WMCapability R) (source : TermRequest) :
    Nonempty (Sigma fun answer =>
      (executableCapabilityChain capability).evidence source answer) ↔
        capability.supports (R.denote source.1) (R.denote source.2) := by
  constructor
  · rintro ⟨⟨answer, witness⟩⟩
    exact (termCapabilityChain_has_answer_iff capability source).1
      ⟨⟨answer, forgetExecutable laws capability source answer witness⟩⟩
  · intro supported
    obtain ⟨⟨answer, receipt⟩⟩ :=
      (termCapabilityChain_has_answer_iff capability source).2 supported
    exact ⟨⟨answer,
      ⟨source, (ExecutableWMTrace.refl, ExecutableWMTrace.refl), receipt⟩⟩⟩

end Mettapedia.Logic.Bridges.WMExecutableTraceGSLTIL
