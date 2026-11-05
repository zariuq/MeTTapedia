import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeWitnessControls
import Mettapedia.Logic.HOL.VectorTabulationPrograms

/-!
# Both tabulation programs in the same compatible Native4 world

The input array contains the two distinct values of the actual derived
family, followed by canonical bottom padding. Both separately selected
programs reconstruct the original indexed two-element Vector in order.
Their different recursion result types and four retained premises remain
explicit. No unindexed length reflection or cost comparison is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeTabulationControls

open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedVectorTreeNativeWitnessModel
open IndexedVectorTreeNativeWitnessControls
  (family solvedValue zeroBranchValue tailVector sourceVector vectorProof originalVectorGuard originalVectorProof)

noncomputable section

def shiftedChoiceFormula : ClosedFormula Native.Const := SelectionProofs.principle shiftedSelection
def shiftedRecursionFormula : ClosedFormula Native.Const := NaturalRecursionProofs.statement
  Native.original.zero Native.original.successor (VectorTabulation.Shifted.Result arrays.toSignature)
def offsetChoiceFormula : ClosedFormula Native.Const := SelectionProofs.principle offsetSelection
def offsetRecursionFormula : ClosedFormula Native.Const := NaturalRecursionProofs.statement
  Native.original.zero Native.original.successor (VectorTabulation.Offset.Result arrays.toSignature)
def additional : List (ClosedFormula Native.Const) :=
  [shiftedChoiceFormula,shiftedRecursionFormula,offsetChoiceFormula,offsetRecursionFormula]
def hypotheses : List (ClosedFormula Native.Const) := additional ++ IndexedVectorTreeNativeWitnessControls.delta

def shiftedChoice : ProofSyntax Native.Const hypotheses shiftedChoiceFormula := .hyp ⟨0,by simp [hypotheses,additional]⟩
def shiftedRecursion : ProofSyntax Native.Const hypotheses shiftedRecursionFormula := .hyp ⟨1,by simp [hypotheses,additional]⟩
def offsetChoice : ProofSyntax Native.Const hypotheses offsetChoiceFormula := .hyp ⟨2,by simp [hypotheses,additional]⟩
def offsetRecursion : ProofSyntax Native.Const hypotheses offsetRecursionFormula := .hyp ⟨3,by simp [hypotheses,additional]⟩

def liftProof {formula : ClosedFormula Native.Const}
    (proof : ProofSyntax Native.Const IndexedVectorTreeNativeWitnessControls.delta formula) :
    ProofSyntax Native.Const hypotheses formula := proof.mono (ProofSyntax.OccurrenceMap.appendLeft additional _)

def arrayPremises : arrays.ComputationPremises hypotheses :=
  ((((premises.prepend IndexedVectorTreeNativeWitnessControls.fieldHyp).prepend offsetRecursionFormula).prepend
    offsetChoiceFormula).prepend shiftedRecursionFormula).prepend shiftedChoiceFormula

theorem hypotheses_realizable : Soundness.SatisfiesHyps model values hypotheses := by
  intro formula member
  rcases List.mem_append.mp member with extra | inherited
  · simp only [additional,List.mem_cons,List.not_mem_nil,or_false] at extra
    rcases extra with rfl | rfl | rfl | rfl
    · exact (model.models_iff_denote_closed _ values).mp shifted_selection_holds
    · exact (model.models_iff_denote_closed _ values).mp (recursion_holds _)
    · exact (model.models_iff_denote_closed _ values).mp offset_selection_holds
    · exact (model.models_iff_denote_closed _ values).mp (recursion_holds _)
  · exact IndexedVectorTreeNativeWitnessControls.delta_realizable formula inherited

theorem sound {formula : ClosedFormula Native.Const} (proof : ProofSyntax Native.Const hypotheses formula) :
    (model.denote formula values).down :=
  Soundness.extDerivation_sound proof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) hypotheses_realizable

def sourceArray : ClosedTerm Native.Const (Native.N ⇒ Native.E) := arrays.single (numeral 2) sourceVector bottom

def firstLookup : ProofSyntax Native.Const hypotheses
    (IndexedVectorPositions.lookup arrays.toSignature (numeral 2) sourceVector Native.original.zero solvedValue) :=
  IndexedVectorPositions.here arrays.toSignature one solvedValue tailVector
def secondLookup : ProofSyntax Native.Const hypotheses
    (IndexedVectorPositions.lookup arrays.toSignature (numeral 2) sourceVector one zeroBranchValue) :=
  IndexedVectorPositions.there arrays.toSignature one solvedValue tailVector Native.original.zero zeroBranchValue
    (IndexedVectorPositions.here arrays.toSignature Native.original.zero zeroBranchValue arrays.nil)

def firstArrayValue : ProofSyntax Native.Const hypotheses (.eq (.app sourceArray Native.original.zero) solvedValue) :=
  arrays.singleAtLookup (numeral 2) sourceVector bottom Native.original.zero solvedValue arrayPremises firstLookup
def secondArrayValue : ProofSyntax Native.Const hypotheses (.eq (.app sourceArray one) zeroBranchValue) :=
  arrays.singleAtLookup (numeral 2) sourceVector bottom one zeroBranchValue arrayPremises secondLookup
def arrayPadding : ProofSyntax Native.Const hypotheses (.eq (.app sourceArray (numeral 2)) bottom) :=
  arrays.singleAtEnd family (numeral 2) sourceVector bottom arrayPremises (liftProof vectorProof)

private def consCongr (length : ClosedTerm Native.Const Native.N)
    {first second : ClosedTerm Native.Const Native.E} {tailFirst tailSecond : ClosedTerm Native.Const Native.V}
    (heads : ProofSyntax Native.Const hypotheses (.eq first second))
    (tails : ProofSyntax Native.Const hypotheses (.eq tailFirst tailSecond)) :
    ProofSyntax Native.Const hypotheses (.eq (arrays.toSignature.consValue length first tailFirst)
      (arrays.toSignature.consValue length second tailSecond)) :=
  .eqTrans (.eqApp tailFirst (.eqAppArg (.app Native.original.cons length) heads))
    (.eqAppArg (.app (.app Native.original.cons length) second) tails)

def shiftedValue := VectorTabulation.Shifted.tabulate arrays.toSignature shiftedSelection (numeral 2) sourceArray
def offsetValue := VectorTabulation.Offset.tabulate arrays.toSignature offsetSelection (numeral 2) sourceArray

private def shiftedHead : ProofSyntax Native.Const hypotheses
    (.eq (.app (VectorTabulation.Shifted.shift arrays.toSignature sourceArray) Native.original.zero) zeroBranchValue) :=
  .eqTrans (VectorTabulation.Shifted.shift_apply arrays.toSignature sourceArray Native.original.zero) secondArrayValue

private def shiftedTail : ProofSyntax Native.Const hypotheses
    (.eq (VectorTabulation.Shifted.tabulate arrays.toSignature shiftedSelection one
      (VectorTabulation.Shifted.shift arrays.toSignature sourceArray)) tailVector) :=
  .eqTrans (VectorTabulation.Shifted.atSuccessor arrays.toSignature shiftedSelection shiftedChoice shiftedRecursion
      Native.original.zero (VectorTabulation.Shifted.shift arrays.toSignature sourceArray))
    (consCongr Native.original.zero shiftedHead
      (VectorTabulation.Shifted.atZero arrays.toSignature shiftedSelection shiftedChoice shiftedRecursion _))

@[irreducible] def shiftedExact : ProofSyntax Native.Const hypotheses (.eq shiftedValue sourceVector) :=
  .eqTrans (VectorTabulation.Shifted.atSuccessor arrays.toSignature shiftedSelection shiftedChoice shiftedRecursion one sourceArray)
    (consCongr one firstArrayValue shiftedTail)

private def offsetTail : ProofSyntax Native.Const hypotheses
    (.eq (VectorTabulation.Offset.fromOffset arrays.toSignature offsetSelection one sourceArray one) tailVector) :=
  .eqTrans (VectorTabulation.Offset.atSuccessor arrays.toSignature offsetSelection offsetChoice offsetRecursion
      Native.original.zero sourceArray one)
    (consCongr Native.original.zero secondArrayValue
      (VectorTabulation.Offset.atZero arrays.toSignature offsetSelection offsetChoice offsetRecursion sourceArray (numeral 2)))

@[irreducible] def offsetExact : ProofSyntax Native.Const hypotheses (.eq offsetValue sourceVector) :=
  .eqTrans (VectorTabulation.Offset.atSuccessor arrays.toSignature offsetSelection offsetChoice offsetRecursion one sourceArray Native.original.zero)
    (consCongr one firstArrayValue offsetTail)

def shiftedGuard : ProofSyntax Native.Const hypotheses
    (.app (NativeVectorAll.Reading.vectorCode Native.original Native.selection family (numeral 2)) shiftedValue) :=
  .impE (.eqPropER (.eqAppArg (NativeVectorAll.Reading.vectorCode Native.original Native.selection family (numeral 2)) shiftedExact))
    (liftProof originalVectorProof)
def offsetGuard : ProofSyntax Native.Const hypotheses
    (.app (NativeVectorAll.Reading.vectorCode Native.original Native.selection family (numeral 2)) offsetValue) :=
  .impE (.eqPropER (.eqAppArg (NativeVectorAll.Reading.vectorCode Native.original Native.selection family (numeral 2)) offsetExact))
    (liftProof originalVectorProof)

theorem shifted_value_holds : model.denote shiftedValue values = model.denote sourceVector values :=
  model.eq_of_eqv_of_fullDomains full (sound shiftedExact)
theorem offset_value_holds : model.denote offsetValue values = model.denote sourceVector values :=
  model.eq_of_eqv_of_fullDomains full (sound offsetExact)
theorem both_routes_agree : model.denote shiftedValue values = model.denote offsetValue values :=
  shifted_value_holds.trans offset_value_holds.symm
theorem shifted_guard_holds :
    (model.denote (.app (NativeVectorAll.Reading.vectorCode Native.original Native.selection family (numeral 2)) shiftedValue) values).down :=
  sound shiftedGuard
theorem offset_guard_holds :
    (model.denote (.app (NativeVectorAll.Reading.vectorCode Native.original Native.selection family (numeral 2)) offsetValue) values).down :=
  sound offsetGuard

theorem shifted_order_holds :
    model.denote Native.original.head values (model.denote shiftedValue values) ≠
      model.denote Native.original.head values (model.denote Native.original.tail values (model.denote shiftedValue values)) := by
  have observed := IndexedVectorTreeNativeWitnessControls.actual_ordered_values_distinct
  exact shifted_value_holds ▸ observed
theorem offset_order_holds :
    model.denote Native.original.head values (model.denote offsetValue values) ≠
      model.denote Native.original.head values (model.denote Native.original.tail values (model.denote offsetValue values)) := by
  have observed := IndexedVectorTreeNativeWitnessControls.actual_ordered_values_distinct
  exact offset_value_holds ▸ observed

theorem first_inactive_slot_is_bottom : model.denote sourceArray values (model.denote (numeral 2) values) = model.denote bottom values :=
  model.eq_of_eqv_of_fullDomains full (sound arrayPadding)

#print axioms hypotheses_realizable
#print axioms shifted_value_holds
#print axioms offset_value_holds
#print axioms shifted_guard_holds
#print axioms offset_guard_holds
#print axioms shifted_order_holds
#print axioms offset_order_holds

end
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeTabulationControls
