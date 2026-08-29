import Mettapedia.Languages.MeTTa.Prime.NativeTypedQuotation
import Mettapedia.Languages.MeTTa.Prime.NativeAgentInteractionExample
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionCost

/-!
# A MeTTa-authored, Lean-certified Prime interaction protocol

This example closes the first source-to-kernel dock across four previously
separate layers:

1. both endpoints are authored with explicit PeTTa syntax;
2. `native%` infers their MeTTa Native types and retains typing derivations;
3. the authorized revision indexes the exact interaction computation;
4. the retained occurrence path yields its work/span and provenance.

Typing remains an accelerator.  The typed endpoint plans erase to the same
raw native terms, and the raw runner never receives a checker argument.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeTypedProtocolExample

open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.Languages.MeTTa.MeTTaInteraction
open Mettapedia.Languages.MeTTa.MeTTaInteraction.Canary
open Mettapedia.Languages.MeTTa.MeTTaInteractionBind.Canary
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan
open Mettapedia.Languages.MeTTa.Prime.NativeAgentInteractionExample
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionCost
open Mettapedia.Languages.MeTTa.Prime.NativeTypedQuotation
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

/-! ## Authored and intrinsically typed endpoints -/

def authoredSource : ClosedTyping :=
  native% petta "(native:pattern (interaction-a))"

def authoredTarget : ClosedTyping :=
  native% petta "(native:pattern (interaction-b))"

@[simp] theorem authoredSource_term :
    authoredSource.term = (.pattern a : StagedReflectiveTm 0 0) :=
  rfl

@[simp] theorem authoredTarget_term :
    authoredTarget.term = (.pattern b : StagedReflectiveTm 0 0) :=
  rfl

@[simp] theorem authoredSource_type : authoredSource.type = .u0 :=
  rfl

@[simp] theorem authoredTarget_type : authoredTarget.type = .u0 :=
  rfl

abbrev NativeTypedPlan :=
  TypedPlan (StagedReflectiveTm 0 0) (StagedReflectiveTm 0 0)
    NativeCanary.ClosedNativeTyping

def authoredSourcePlan : NativeTypedPlan where
  term := authoredSource.term
  type := authoredSource.type
  typing := authoredSource.typing

def authoredTargetPlan : NativeTypedPlan where
  term := authoredTarget.term
  type := authoredTarget.type
  typing := authoredTarget.typing

/-! ## Revision-indexed exact interaction -/

/-- The authorized catalog occurrence inhabits the computation indexed by
the two authored native endpoints and the proof-carrying current revision. -/
def authoredComputation :
    familiesCwF.Tm PrimeContext
      (siteComputationTy currentRevision.revision
        authoredSource.term authoredTarget.term) := by
  simpa [currentRevision] using cheapNative

/-- The exact occurrence path retained by the computation. -/
def authoredPath :
    familiesCwF.Tm PrimeContext
      (interactionComputationTy
        (presentation model authorityWorld currentRevision.revision) a b) :=
  fun _ =>
    .cons (site := cheap) cheapEvent
      (.nil (presentation := presentation model authorityWorld false) b)

/-- The proof-carrying revision is not metadata: selecting the other
revision removes the endpoint computation. -/
theorem wrong_revision_has_no_authored_computation :
    ¬ Nonempty
      ((siteComputationTy true authoredSource.term authoredTarget.term)
        PUnit.unit) := by
  simpa using true_revision_has_no_a_to_b_computation

/-! ## Cost and provenance readouts -/

/-- One exact catalog occurrence contributes one unit of work and one unit
of chronological span. -/
theorem authoredComputation_workSpan :
    pathWorkSpan authoredPath PUnit.unit = ⟨1, 1⟩ :=
  rfl

/-- Endpoint typing does not erase which rule occurrence fired or its cost. -/
theorem authoredComputation_cost_and_provenance :
    EventPath.grade (presentation model authorityWorld false)
      costAndNameValuation (authoredPath PUnit.unit) =
        some (1, ["cheap"]) :=
  rfl

/-! ## Accelerator-never-gatekeeper control -/

/-- Erasing the typed plan gives the exact authored raw term. -/
theorem authoredSourcePlan_erases :
    (Plan.typed (Key := PUnit) (Obligation := PUnit)
      authoredSourcePlan).erase = authoredSource.term :=
  rfl

/-- Ordinary execution of the typed plan is just raw endpoint lowering. -/
theorem authoredSourcePlan_runs_raw :
    (Plan.typed (Key := PUnit) (Obligation := PUnit)
      authoredSourcePlan).run (siteInterpretation false).lower? = some a :=
  rfl

/-- Negative control: the native dependent protocol term itself does not
become a rho endpoint merely because its application can produce typed
runtime values. -/
theorem dependentReceipt_is_not_rho_endpoint :
    (siteInterpretation false).lower? dependentReceiptTyping.term = none :=
  rfl

#print axioms authoredComputation_workSpan
#print axioms authoredComputation_cost_and_provenance
#print axioms wrong_revision_has_no_authored_computation
#print axioms authoredSourcePlan_runs_raw
#print axioms dependentReceipt_is_not_rho_endpoint

end Mettapedia.Languages.MeTTa.Prime.NativeTypedProtocolExample
