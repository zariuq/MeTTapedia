import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedFrameControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferenceValueControls

/-!
# Wrong source origins, arguments and physical spaces cannot pass the bridge

The routing refusal holds for every actual completed returned update. A fuel
cutoff is not interpreted as refutation. Source-origin and argument refusals
also evaluate the original activation path, before any proof projection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedRefusalControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (a definition)
open InferenceSchemaActivation (judgment)
open InferenceRequestExecution (Occurrence)
open ContextualFrameUpdate
open ScopedInferenceValues (Ready base encode)
open InferenceScopedExecutionControls
  (locals captures readyRequest readyA readyB readyRule requestOccurrence outputOccurrence
    state selection scopes retained templates nativeRule canonical_readback)
open InferenceScopedFrameControls (extra)

local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq (ScopedInferenceValues.Head × List Nat))

theorem unknown_source_refuses :
    (InferenceScopedActivation.activate definition ⟨"uninstalled"⟩ []).isNone = true := by decide +kernel

theorem wrong_input_vector_refuses :
    (InferenceScopedActivation.activate definition ⟨"ab"⟩ [a]).isNone = true := by decide +kernel

def publicA : Ready := ⟨(.requests, judgment a), rfl⟩
def publicOccurrence : Occurrence := (1, publicA.val)

def wrongLabel (occurrence : Occurrence) : Ready :=
  if occurrence.1 = 0 then readyRequest else if occurrence.1 = 1 then publicA else readyB

def wrongState : Configuration Ready Occurrence := ⟨[], {requestOccurrence, publicOccurrence}⟩
def wrongSelection : Selection Occurrence := ⟨[requestOccurrence], [publicOccurrence], [outputOccurrence]⟩
def occupied : Finset Nat :=
  InferenceScopedInventory.reserve locals captures scopes ∅ wrongLabel wrongState retained templates extra
def nativeRows := ContextualRigidActivation.rows locals captures encode wrongLabel
def nativeBefore := ContextualRigidActivation.withFrame captures encode extra wrongState
def nativeOutputs := ContextualRigidActivation.outputs locals captures encode wrongLabel
def problem := ContextualActivatedStep.problem locals captures occupied wrongSelection nativeRule nativeRows nativeBefore

/-- A public value with the exact expected payload still cannot solve a
protected premise equation, even while a real caller-frame binding is solved. -/
theorem no_completed_wrong_space (fuel : Nat)
    (update : Update (ContextualResidual.observeProblem problem))
    (returned : ContextualTransportedActivation.FromRun locals captures fuel occupied wrongSelection
      nativeRule nativeRows nativeBefore nativeOutputs update) : False := by
  have reflected := ContextualRigidActivation.completed_equations locals captures encode
    ScopedInferenceValues.encode_injective occupied wrongSelection readyRule wrongLabel wrongState
    extra update returned.empty
  have mismatched : (readyA, publicA) ∈ wrongSelection.problem wrongLabel readyRule wrongState := by
    simp [Selection.problem, Selection.equations, wrongSelection, wrongState,
      readyRule, wrongLabel, publicOccurrence]
  have same := reflected (readyA, publicA) mismatched
  have locations := congrArg (fun value : Ready => value.val.1) same
  cases locations

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedRefusalControls
