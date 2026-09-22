import Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyGSLTIL
import Mettapedia.Logic.Bridges.WMExecutableTraceGSLTIL

/-!
# Execution evidence versus observable dependent answer families

The observable CwF answer family is exactly reached by both typed-event and
numbered-engine GSLT-IL chains: each chain forgets to a checked receipt,
and every checked receipt has a zero-step execution witness. The forgetting
is not an equivalence of proof-relevant fibres. A concrete pair of distinct
typed executions maps to one and the same observable receipt.

This separates semantic dependent transport from retention of machine or
rule-occurrence history, while connecting them by explicit maps.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.RevisionedFamilies.ExecutionFamilyBoundary

open Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyGSLTIL
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusOccurrenceTrace
open Mettapedia.OSLF.Framework.WMCalculusExecutableTrace
open Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL
open Mettapedia.Logic.Bridges.WMNativeExecutionTraceGSLTIL
open Mettapedia.Logic.Bridges.WMExecutableTraceGSLTIL

variable {State Query V : Type} {R : WMReading State Query V}

/-- The observable receipt retains only proposition-valued support and
checked-answer fields, hence has no hidden execution multiplicity. -/
theorem observableReceipt_subsingleton (capability : WMCapability R)
    (request : observableRequestContext R) (answer : V) :
    Subsingleton (observableReceiptFamily capability answer request) := by
  constructor
  intro first second
  cases first
  cases second
  rfl

/-- Forget typed constructor-position traces to Prime's observable
dependent receipt, keeping the actual checked answer. -/
def traceToObservableReceipt (laws : R.CoreLaws)
    (capability : WMCapability R) (source : TermRequest) (answer : V) :
    (tracedCapabilityChain capability).evidence source answer →
      observableReceiptFamily capability answer
        (classOf R (R.denote source.1), R.denote source.2) :=
  fun witness =>
    (termChainReceiptEquiv capability source answer)
      (forgetExecution laws capability source answer witness)

/-- Every observable dependent receipt is reached by a zero-step typed
execution chain. This is surjectivity, not an equivalence of evidence types. -/
theorem traceToObservableReceipt_surjective (laws : R.CoreLaws)
    (capability : WMCapability R) (source : TermRequest) (answer : V) :
    Function.Surjective
      (traceToObservableReceipt laws capability source answer) := by
  intro receipt
  refine ⟨⟨source, (WMTrace.refl, WMTrace.refl),
    (termChainReceiptEquiv capability source answer).symm receipt⟩, ?_⟩
  exact (observableReceipt_subsingleton capability _ answer).allEq _ _

/-- The actual premise-aware engine occurrence chain has the same exact
observable receipt image, but retains its fuel and alternative indices. -/
def executableToObservableReceipt (laws : R.CoreLaws)
    (capability : WMCapability R) (source : TermRequest) (answer : V) :
    (executableCapabilityChain capability).evidence source answer →
      observableReceiptFamily capability answer
        (classOf R (R.denote source.1), R.denote source.2) :=
  fun witness =>
    (termChainReceiptEquiv capability source answer)
      (forgetExecutable laws capability source answer witness)

/-- A checked observable receipt is also realized by the finite engine's
zero-step trace. No functional representation of arbitrary trace fibres is
inferred from this surjection. -/
theorem executableToObservableReceipt_surjective (laws : R.CoreLaws)
    (capability : WMCapability R) (source : TermRequest) (answer : V) :
    Function.Surjective
      (executableToObservableReceipt laws capability source answer) := by
  intro receipt
  refine ⟨⟨source, (ExecutableWMTrace.refl, ExecutableWMTrace.refl),
    (termChainReceiptEquiv capability source answer).symm receipt⟩, ?_⟩
  exact (observableReceipt_subsingleton capability _ answer).allEq _ _

/-- Two genuinely different typed executions reach one CwF receipt fibre.
The quotient's dependent equality has not erased history inside the
operational relation; erasure happens only at this explicit map. -/
theorem distinct_traces_same_observable_receipt :
    zeroStepWitness ≠ roundtripWitness ∧
      traceToObservableReceipt
          Mettapedia.OSLF.Framework.WMCalculusNativeContextExample.booleanReading_coreLaws
          totalBooleanCapability _ _ zeroStepWitness =
        traceToObservableReceipt
          Mettapedia.OSLF.Framework.WMCalculusNativeContextExample.booleanReading_coreLaws
          totalBooleanCapability _ _ roundtripWitness := by
  refine ⟨zeroStep_ne_roundtrip, ?_⟩
  exact (observableReceipt_subsingleton totalBooleanCapability _ _).allEq _ _

end Mettapedia.TypeTheory.Models.RevisionedFamilies.ExecutionFamilyBoundary
