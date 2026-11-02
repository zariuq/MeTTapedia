import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseApplication

/-!
# Source-domain and completion controls for a supplied mixed case

The positive application uses all five fields and all three IHs. Swapping
equal-carrier inputs does not preserve their dependent source domains. An
accepted prefix remains a function awaiting its final IH.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseControls

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open IndexedContainerNativeVectorMethodReading
open IndexedContainerNativeVectorCaseApplication
local infixr:60 " ⇒ " => HOL.Ty.arr

private abbrev context := IndexedContainerNativeVectorCaseContext.context
private abbrev carrier := IndexedContainerNativeVectorCaseContext.carrier
private abbrev methodCarrier := IndexedContainerNativeVectorCaseContext.methodCarrier

def swappedDirect : VariablePositions carrier := [⟨W, afterIH⟩, ⟨W, bundleIndex⟩, ⟨W, beforeIH⟩]
def missingBundle : VariablePositions carrier := [⟨W, beforeIH⟩, ⟨W, afterIH⟩]
def swappedPayload : VariablePositions carrier :=
  [⟨N, lengthIndex⟩, ⟨E, tagIndex⟩, ⟨E, beforeIndex⟩, ⟨V, vectorIndex⟩, ⟨E, afterIndex⟩]

variable (roots : List (HOL.ClosedFormula Const))

theorem swapped_direct_refused :
    SuppliedArguments.readVariables? roots context swappedDirect expectedResidual residualCarrier = none := by rfl

theorem missing_bundle_refused :
    SuppliedArguments.readVariables? roots context missingBundle expectedResidual residualCarrier = none := by rfl

theorem swapped_payload_refused : SuppliedArguments.readVariables? roots context swappedPayload
    (context.source.lookup methodIndex.toFin) methodCarrier = none := by rfl

theorem changed_carrier_refused : SuppliedArguments.readVariables? roots context fieldPositions
    (context.source.lookup methodIndex.toFin) (E ⇒ residualCarrier) = none := by rfl

def prefixPositions : VariablePositions carrier := [⟨W, beforeIH⟩, ⟨W, bundleIndex⟩]
def prefixTarget : CTm Tower.Head carrier.length := .pi (.app (.var 10) (.var 3)) (expectedConclusion.rename wk)

theorem prefix_shape : VariablesSupply context prefixPositions expectedResidual residualCarrier prefixTarget (W ⇒ W) := by
  refine VariablesSupply.step (context := context) beforeIH (by rfl) ?_
  refine VariablesSupply.step (context := context) bundleIndex (by rfl) ?_
  convert VariablesSupply.done (context := context) prefixTarget (W ⇒ W) using 1
  decide +kernel

def receivedPrefix := SuppliedArguments.readVariables? roots context prefixPositions expectedResidual residualCarrier
theorem prefix_accepted : (receivedPrefix roots).isSome = true := SuppliedArguments.readVariables?_complete prefix_shape

theorem prefix_keeps_final_input : ((receivedPrefix roots).get (prefix_accepted roots)).resultCarrier = (W ⇒ W) :=
  (VariablesSupply.unique ((receivedPrefix roots).get (prefix_accepted roots)).shape prefix_shape).2

theorem prefix_is_not_a_completed_value : ((receivedPrefix roots).get (prefix_accepted roots)).resultCarrier ≠ W := by
  rw [prefix_keeps_final_input]
  decide +kernel

#print axioms swapped_payload_refused
#print axioms prefix_is_not_a_completed_value

end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseControls
