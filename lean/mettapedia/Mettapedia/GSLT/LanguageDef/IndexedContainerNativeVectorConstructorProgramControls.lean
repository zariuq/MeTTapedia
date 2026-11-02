import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorCaseTransport
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorEvidenceModel

/-!
# Computed constructor and independent-source controls

The existing array/All model supplies nontrivial Boolean elements. A raw
operation returning true and an independently supplied source constructor
returning false distinguish implementation substitution from an assumed
equation. Retained beta computation still evaluates the implemented source
application to the raw result. This countermodel concerns the unconditional
constructor equation, not satisfaction of the complete source field context.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorProgramControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V W)
open IndexedContainerNativeVectorLogicalRow (fieldCarrier)
open IndexedContainerNativeVectorEvidenceModel (model full elementSelection arraySelection)
open IndexedContainerNativeVectorConstructorCaseTransport
open IndexedContainerNativeVectorConstructorProgram (RawConstructor)

def raw : Term Const fieldCarrier RawConstructor := .lam (.lam (.lam (.const (.parameter 20 E))))
def bottom : Term Const fieldCarrier E := .const (.parameter 21 E)
def values : model.Valuation fieldCarrier := fun {type} _ => IndexedContainerNativeVectorEvidenceModel.defaultValue type
def implemented := replacement elementSelection arraySelection raw bottom
def result := value elementSelection arraySelection raw bottom

theorem raw_result_true : model.denote result values = ULift.up true := rfl
theorem source_result_false : model.denote IndexedContainerNativeVectorLogicalRow.constructorCode values = ULift.up false := rfl

theorem arbitrary_source_equation_refused :
    model.denote IndexedContainerNativeVectorLogicalRow.constructorCode values ≠ model.denote result values := by
  rw [source_result_false,raw_result_true]
  intro same
  have impossible : (false : Bool) = true := congrArg ULift.down same
  cases impossible

theorem implemented_result_true : model.denote
    (IndexedContainerNativeVectorConstructorProgram.applySource implemented length before tag vector after) values = ULift.up true := by
  let proof := IndexedContainerNativeVectorConstructorProgram.computation (Δ := [])
    elementSelection arraySelection payload raw bottom length before tag vector after
  have equality := Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial)
    (show Soundness.SatisfiesHyps model values [] from fun _ absent => False.elim (List.not_mem_nil absent))
  have same := (model.eqv_iff_eq_of_fullDomains full _ _).mp equality
  exact same.trans raw_result_true

theorem original_constructor_is_replaced :
    images implemented IndexedContainerNativeVectorLogicalRow.constructorIndex = implemented := images_constructor implemented

theorem original_motive_is_retained :
    images implemented IndexedContainerNativeVectorLogicalRow.motiveIndex =
      .var IndexedContainerNativeVectorLogicalRow.motiveIndex := images_other implemented _ (by decide +kernel)

theorem original_length_is_retained :
    images implemented IndexedContainerNativeVectorLogicalRow.lengthIndex =
      .var IndexedContainerNativeVectorLogicalRow.lengthIndex := images_other implemented _ (by decide +kernel)

#print axioms arbitrary_source_equation_refused
#print axioms implemented_result_true
#print axioms original_motive_is_retained
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorProgramControls
