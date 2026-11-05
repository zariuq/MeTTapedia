import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeWitnessModel
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeConstructorFunctions

/-!
# Nonempty actual-family inputs in the compatible Native4 world

The predicate is the actual derived stored family. A positive original
natural payload introduces a solved value, and a real zero-child branch
introduces a distinct value. An ordered Vector contains both. The supplied
case values below are selected for the particular motive `e ↦ F_C(e)`;
they do not constitute synthesis of methods for arbitrary motives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeWitnessControls

open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedVectorTreeNativeWitnessModel

noncomputable section

def family : ClosedTerm Native.Const (Native.E ⇒ .prop) :=
  IndexedVectorTreeStoredFamily.family input originalPredicate numbers Native.original.zero one
    Native.original.successor numeral bottom

def solvedFunction := IndexedVectorTreeConstructorFunctions.solved input originalPredicate numbers
  Native.original.zero one numeral bottom
def branchFunction := IndexedVectorTreeConstructorFunctions.Native.branch Native.original elementSelection arraySelection
  input originalPredicate numbers one numeral bottom
def solvedFunctionGuard := IndexedVectorTreeConstructorFunctions.solvedGuard input originalPredicate numbers
  Native.original.zero one Native.original.successor numeral bottom
def branchFunctionGuard := IndexedVectorTreeConstructorFunctions.Native.branchGuard Native.original Native.selection
  input originalPredicate numbers one numeral bottom

def solvedFunctionProof : ProofSyntax Native.Const assumptions
    (.app solvedFunctionGuard solvedFunction) :=
  IndexedVectorTreeConstructorFunctions.solvedMember input originalPredicate numbers Native.original.zero one
    Native.original.successor numeral bottom

def branchFunctionProof : ProofSyntax Native.Const assumptions
    (.app branchFunctionGuard branchFunction) :=
  IndexedVectorTreeConstructorFunctions.Native.branchMember Native.original Native.selection elementSelection arraySelection
    input originalPredicate numbers one numeral bottom numericRecognition premises arithmetic

theorem solved_function_guard_holds :
    (model.denote (.app solvedFunctionGuard solvedFunction) values).down := by
  exact Soundness.extDerivation_sound solvedFunctionProof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable
theorem branch_function_guard_holds : (model.denote (.app branchFunctionGuard branchFunction) values).down :=
  Soundness.extDerivation_sound branchFunctionProof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable

def fieldHyp : ClosedFormula Native.Const := .app originalPredicate one
def delta : List (ClosedFormula Native.Const) := fieldHyp :: assumptions
theorem delta_realizable : Soundness.SatisfiesHyps model values delta := by
  intro formula present
  rcases List.mem_cons.mp present with rfl | inherited
  · change (0 : Nat) < 1
    decide
  · exact assumptions_realizable formula inherited

theorem sound {formula : ClosedFormula Native.Const} (proof : ProofSyntax Native.Const delta formula) :
    (model.denote formula values).down :=
  Soundness.extDerivation_sound proof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) delta_realizable

def solvedValue := IndexedVectorTreeStoredFamilySolved.value input originalPredicate numbers
  Native.original.zero one numeral bottom (.app input.encode one)
def solvedProof : ProofSyntax Native.Const delta (.app family solvedValue) :=
  IndexedVectorTreeStoredFamilySolved.fromAnswer input originalPredicate numbers Native.original.zero one
    Native.original.successor numeral bottom one (.hyp (Δ := delta) ⟨0,by simp [delta]⟩)

def numberMember (n : ClosedTerm Native.Const Native.N) : ProofSyntax Native.Const delta (.app numbers n) :=
  .impE (.eqPropER (.beta n .top)) .topI

def zeroBranchValue := IndexedVectorTreeStoredFamilyBranch.value arrays input originalPredicate numbers one numeral bottom
  Native.original.zero arrays.nil
def zeroBranchProof : ProofSyntax Native.Const delta (.app family zeroBranchValue) :=
  IndexedVectorTreeStoredFamilyBranch.member arrays input originalPredicate numbers one numeral bottom
    Native.original.zero arrays.nil (numberMember _) (premises.prepend fieldHyp) (arithmetic.prepend fieldHyp)
    (arrays.toSignature.nil_member family)

theorem solved_member_holds : (model.denote (.app family solvedValue) values).down := sound solvedProof
theorem branch_member_holds : (model.denote (.app family zeroBranchValue) values).down := sound zeroBranchProof
theorem family_nonempty : ∃ value : Ty.denote model.Carrier Native.E, (model.denote family values value).down :=
  ⟨model.denote solvedValue values,solved_member_holds⟩

theorem solved_not_bottom : model.denote solvedValue values ≠ bottomValue := by
  exact RecursiveSpaceSemantics.construct_ne_bottom filler _ _ _
theorem branch_not_bottom : model.denote zeroBranchValue values ≠ bottomValue := by
  exact RecursiveSpaceSemantics.construct_ne_bottom filler _ _ _
theorem constructor_values_distinct : model.denote solvedValue values ≠ model.denote zeroBranchValue values := by
  intro same
  have tags := (RecursiveSpaceSemantics.construct_injective filler _ _ _ _ _ _).mp same
  have impossible : (0 : Nat) = 1 := tags.1
  cases impossible

def tailVector : ClosedTerm Native.Const Native.V :=
  arrays.toSignature.consValue Native.original.zero zeroBranchValue arrays.nil
def tailProof : ProofSyntax Native.Const delta (arrays.toSignature.member family one tailVector) :=
  arrays.toSignature.cons_member family Native.original.zero zeroBranchValue arrays.nil zeroBranchProof
    (arrays.toSignature.nil_member family)
def sourceVector : ClosedTerm Native.Const Native.V := arrays.toSignature.consValue one solvedValue tailVector
def vectorProof : ProofSyntax Native.Const delta (arrays.toSignature.member family (numeral 2) sourceVector) :=
  arrays.toSignature.cons_member family one solvedValue tailVector solvedProof tailProof

def originalVectorGuard : ClosedFormula Native.Const :=
  .app (NativeVectorAll.Reading.vectorCode Native.original Native.selection family (numeral 2)) sourceVector
def originalVectorProof : ProofSyntax Native.Const delta originalVectorGuard :=
  .impE (.eqPropER (IndexedVectorTreeNativeChildConditions.ReaderGuard.vector_beta Native.original Native.selection
    family (numeral 2) sourceVector)) vectorProof
theorem vector_guard_holds : (model.denote originalVectorGuard values).down := sound originalVectorProof

theorem first_position_holds : model.denote Native.original.head values (model.denote sourceVector values) =
    model.denote solvedValue values := rfl
theorem second_position_holds : model.denote Native.original.head values
    (model.denote Native.original.tail values (model.denote sourceVector values)) = model.denote zeroBranchValue values := rfl
theorem actual_ordered_values_distinct : model.denote Native.original.head values (model.denote sourceVector values) ≠
    model.denote Native.original.head values (model.denote Native.original.tail values (model.denote sourceVector values)) := by
  exact constructor_values_distinct

def motive : ClosedTerm Native.Const (Native.E ⇒ Native.W ⇒ .prop) :=
  .lam (.lam (.app (weaken (weaken family)) (.var (.vs .vz))))
def suppliedSolvedCase : ClosedTerm Native.Const (Native.E ⇒ Native.W) := .lam (weaken Native.witness)
def suppliedBranchCase : ClosedTerm Native.Const (Native.N ⇒ Native.V ⇒ Native.W ⇒ Native.W) :=
  .lam (.lam (.lam (weaken (weaken (weaken Native.witness)))))

def providerAssumptions : List (ClosedFormula Native.Const) :=
  [SelectionProofs.principle input.payloadSelection,SelectionProofs.principle input.fieldSelection,
   ConstructorProjections.fieldInjective input.raw]
theorem providers_realizable : Soundness.SatisfiesHyps model values providerAssumptions := by
  intro formula present
  simp only [providerAssumptions,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl
  · exact (model.models_iff_denote_closed _ values).mp payload_selection_holds
  · exact (model.models_iff_denote_closed _ values).mp field_selection_holds
  · exact (model.models_iff_denote_closed _ values).mp raw_injective_holds

def recoveryProof : ProofSyntax Native.Const providerAssumptions
    (ConstructorFieldRepresentation.leftInverse input.encode input.decode) :=
  input.roundtripLaw (.hyp ⟨0,by simp [providerAssumptions]⟩)
    (.hyp ⟨1,by simp [providerAssumptions]⟩) (.hyp ⟨2,by simp [providerAssumptions]⟩)
theorem field_roundtrip (field : Number) : model.denote input.decode values (model.denote input.encode values field) = field := by
  have actual := Soundness.extDerivation_sound recoveryProof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) providers_realizable
  exact actual field trivial

def zeroField : ClosedTerm Native.Const Native.E := .app input.encode Native.original.zero
theorem original_zero_payload_refused : ¬ (model.denote (.app (input.predicate originalPredicate) zeroField) values).down := by
  intro present
  obtain ⟨original,allowed,same⟩ :=
    (ConstructorPredicateRepresentation.lift_denote_full model full input.encode originalPredicate values _).mp present
  have recovered := (field_roundtrip original).symm.trans
    ((congrArg (model.denote input.decode values) same).trans (field_roundtrip (ULift.up 0)))
  change 0 < original.down at allowed
  have down := congrArg ULift.down recovered
  exact Nat.not_lt_zero 0 (Eq.mp (congrArg (fun n : Nat => 0 < n) down) allowed)

#print axioms delta_realizable
#print axioms solved_member_holds
#print axioms branch_member_holds
#print axioms family_nonempty
#print axioms constructor_values_distinct
#print axioms vector_guard_holds
#print axioms actual_ordered_values_distinct
#print axioms original_zero_payload_refused

end
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeWitnessControls
