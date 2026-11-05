import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeConstructorFunctions
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeChildConditionsControls

/-!
# Actual constructor functions in the restrictive function-vector profile

The functions are the retained lambda programs built from the original solved
and branch values. Their guarded products have actual admissible arguments:
an encoded true answer and an ordered two-child Vector. The original numeric,
shape and inactive-padding conditions remain observable.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeConstructorFunctionControls

open Mettapedia.Logic Mettapedia.Logic.HOL
open FiniteConstructorEncoding
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open FiniteConstructorFieldEmbeddingControls (Base N A E Number Space filler)
open IndexedVectorTreeFunctionVectorFixture
open IndexedVectorTreeNativeChildConditionsControls
  (family signature sourceField sourceMember solvedValue sourceVector originalVectorGuard)

def field : ClosedTerm Const E := .app given.encode sourceField
def solvedFunction := IndexedVectorTreeConstructorFunctions.solved given onlyTrue numbers zero one numeral bottom
def solvedFunctionGuard := IndexedVectorTreeConstructorFunctions.solvedGuard
  given onlyTrue numbers zero one successor numeral bottom
def branchFunction := IndexedVectorTreeConstructorFunctions.Native.branch original elementSelection arraySelection
  given onlyTrue numbers one numeral bottom
def branchFunctionGuard := IndexedVectorTreeConstructorFunctions.Native.branchGuard original readerSelection
  given onlyTrue numbers one numeral bottom

@[irreducible] def solvedMembership : ProofSyntax Const assumptions (.app solvedFunctionGuard solvedFunction) :=
  IndexedVectorTreeConstructorFunctions.solvedMember given onlyTrue numbers zero one successor numeral bottom
theorem solvedMembership_free : solvedMembership.FunctionExtensionalityFree := by
  unfold solvedMembership
  exact IndexedVectorTreeConstructorFunctions.solvedMember_free _ _ _ _ _ _ _ _

def numericRecognition : ProofSyntax Const assumptions
    (IndexedVectorTreeConstructorFunctions.Native.numberRecognition numbers) :=
  IndexedVectorTreeConstructorFunctions.Native.fullNumberRecognition
theorem numericRecognition_free : numericRecognition.FunctionExtensionalityFree :=
  IndexedVectorTreeConstructorFunctions.Native.fullNumberRecognition_free

@[irreducible] def branchMembership : ProofSyntax Const assumptions (.app branchFunctionGuard branchFunction) :=
  IndexedVectorTreeConstructorFunctions.Native.branchMember original readerSelection elementSelection arraySelection
    given onlyTrue numbers one numeral bottom numericRecognition premises arithmetic
theorem branchMembership_free : branchMembership.FunctionExtensionalityFree := by
  unfold branchMembership
  exact IndexedVectorTreeConstructorFunctions.Native.branchMember_free original readerSelection elementSelection arraySelection
    given onlyTrue numbers one numeral bottom numericRecognition premises arithmetic
    numericRecognition_free premises_free arithmetic_free

def solvedBeta : ProofSyntax Const assumptions (.eq (.app solvedFunction field) solvedValue) :=
  IndexedVectorTreeConstructorFunctions.solved_apply given onlyTrue numbers zero one numeral bottom field
theorem solvedBeta_free : solvedBeta.FunctionExtensionalityFree :=
  IndexedVectorTreeConstructorFunctions.solved_apply_free _ _ _ _ _ _ _ _

def branchBeta : ProofSyntax Const assumptions
    (.eq (.app (.app branchFunction (numeral 2)) sourceVector)
      IndexedVectorTreeNativeChildConditionsControls.nativeBranchValue) :=
  IndexedVectorTreeConstructorFunctions.Native.branch_apply original elementSelection arraySelection
    given onlyTrue numbers one numeral bottom (numeral 2) sourceVector
theorem branchBeta_free : branchBeta.FunctionExtensionalityFree :=
  IndexedVectorTreeConstructorFunctions.Native.branch_apply_free _ _ _ _ _ _ _ _ _ _ _

def fieldMember : ProofSyntax Const assumptions (.app (given.predicate onlyTrue) field) :=
  ConstructorPredicateRepresentation.introduce given.encode onlyTrue sourceField sourceMember
theorem fieldMember_free : fieldMember.FunctionExtensionalityFree :=
  ConstructorPredicateRepresentation.introduce_free _ _ _ _
    IndexedVectorTreeNativeChildConditionsControls.sourceMember_free

theorem solved_function_guard_holds : (model.denote (.app solvedFunctionGuard solvedFunction) values).down :=
  IndexedVectorTreeNativeChildConditionsControls.sound solvedMembership
theorem branch_function_guard_holds : (model.denote (.app branchFunctionGuard branchFunction) values).down :=
  IndexedVectorTreeNativeChildConditionsControls.sound branchMembership
theorem actual_solved_beta_value : model.denote solvedFunction values (model.denote field values) =
    model.denote solvedValue values :=
  model.eq_of_eqv_of_fullDomains full (IndexedVectorTreeNativeChildConditionsControls.sound solvedBeta)
theorem actual_branch_beta_value : model.denote branchFunction values (model.denote (numeral 2) values)
    (model.denote sourceVector values) = model.denote IndexedVectorTreeNativeChildConditionsControls.nativeBranchValue values :=
  model.eq_of_eqv_of_fullDomains full (IndexedVectorTreeNativeChildConditionsControls.sound branchBeta)

theorem solved_domain_nonempty : ∃ argument : Ty.denote model.Carrier E,
    (model.denote (given.predicate onlyTrue) values argument).down :=
  ⟨model.denote field values,IndexedVectorTreeNativeChildConditionsControls.sound fieldMember⟩

theorem branch_admissible_arguments_nonempty :
    ∃ length : ClosedTerm Const N, ∃ vector : ClosedTerm Const V,
      (model.denote (.app (PredicateProducts.full N) length) values).down ∧
      (model.denote (.app (NativeVectorAll.Reading.vectorCode original readerSelection family length) vector) values).down :=
  ⟨numeral 2,sourceVector,True.intro,
    IndexedVectorTreeNativeChildConditionsControls.source_vector_guard_holds⟩

def emptyVectorProof : ProofSyntax Const assumptions
    (.app (NativeVectorAll.Reading.vectorCode original readerSelection family zero) ops.nil) :=
  .impE (.eqPropER (IndexedVectorTreeNativeChildConditions.ReaderGuard.vector_beta original readerSelection
    family zero ops.nil)) (ops.toSignature.nil_member family)

theorem zero_length_argument_holds :
    (model.denote (.app (NativeVectorAll.Reading.vectorCode original readerSelection family zero) ops.nil) values).down :=
  IndexedVectorTreeNativeChildConditionsControls.sound emptyVectorProof

def zeroBranchBeta : ProofSyntax Const assumptions
    (.eq (.app (.app branchFunction zero) ops.nil)
      (IndexedVectorTreeStoredFamilyBranch.ReaderGuard.value original elementSelection arraySelection
        given onlyTrue numbers one numeral bottom zero ops.nil)) :=
  IndexedVectorTreeConstructorFunctions.Native.branch_apply original elementSelection arraySelection
    given onlyTrue numbers one numeral bottom zero ops.nil

private def storedBranchPayload (n : ClosedTerm Const N) :=
  encode (VectorTreeFieldEmbedding.storedSignature N E)
    (VectorTreeFieldEmbedding.branchOccurrence (number := N) (element := E)) (n,zero,PUnit.unit)
private def rawBranchPayload (n : ClosedTerm Const N) :=
  encode (VectorTreeFieldEmbedding.rawSignature N A)
    (VectorTreeFieldEmbedding.branchOccurrence (number := N) (element := A)) (n,zero,PUnit.unit)

private def lowerBranch (n : ClosedTerm Const N) : ProofSyntax Const assumptions
    (.eq (.app (VectorTreePayloadMaps.lowerProgram given) (storedBranchPayload n)) (rawBranchPayload n)) :=
  .eqTrans ((VectorTreePayloadMaps.lower given).program_beta (storedBranchPayload n))
    (.eqTrans ((VectorTreePayloadMaps.lower given).mapPayload_encode
      (VectorTreeFieldEmbedding.branchOccurrence (number := N) (element := E)) (n,zero,PUnit.unit))
      (encode_congr (VectorTreeFieldEmbedding.rawSignature N A)
        (VectorTreeFieldEmbedding.branchOccurrence (number := N) (element := A)) _ (n,zero,PUnit.unit)
        (fun index => FieldMaps.identity_at [N,N] (n,zero,PUnit.unit) index)))

private def rawBranchValue (n : ClosedTerm Const N) (vector : ClosedTerm Const V) :=
  ConstructorProjections.apply given.raw (numeral 1) (rawBranchPayload n) (ops.single n vector bottom)

private def branchRawComputation (n : ClosedTerm Const N) (vector : ClosedTerm Const V) :
    ProofSyntax Const assumptions (.eq
      (IndexedVectorTreeStoredFamilyBranch.ReaderGuard.value original elementSelection arraySelection
        given onlyTrue numbers one numeral bottom n vector) (rawBranchValue n vector)) :=
  .eqTrans (ConstructorArgumentMap.computation given.raw (VectorTreePayloadMaps.lowerProgram given)
      (numeral 1) (storedBranchPayload n) (ops.single n vector bottom))
    (.eqApp (ops.single n vector bottom) (.eqAppArg (.app given.raw (numeral 1)) (lowerBranch n)))

theorem branch_distinguishes_zero_and_two_children :
    model.denote branchFunction values (model.denote zero values) (model.denote ops.nil values) ≠
      model.denote branchFunction values (model.denote (numeral 2) values) (model.denote sourceVector values) := by
  intro same
  have atZero := model.eq_of_eqv_of_fullDomains full
    (IndexedVectorTreeNativeChildConditionsControls.sound zeroBranchBeta)
  change model.denote branchFunction values (model.denote zero values) (model.denote ops.nil values) =
    model.denote (IndexedVectorTreeStoredFamilyBranch.ReaderGuard.value original elementSelection arraySelection
      given onlyTrue numbers one numeral bottom zero ops.nil) values at atZero
  have actual := atZero.symm.trans (same.trans actual_branch_beta_value)
  have rawZero := model.eq_of_eqv_of_fullDomains full
    (IndexedVectorTreeNativeChildConditionsControls.sound (branchRawComputation zero ops.nil))
  have rawTwo := model.eq_of_eqv_of_fullDomains full
    (IndexedVectorTreeNativeChildConditionsControls.sound (branchRawComputation (numeral 2) sourceVector))
  have rawSame := rawZero.symm.trans (actual.trans rawTwo)
  have fields := (Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics.construct_injective filler _ _ _ _ _ _).mp rawSame
  let solvedObservation : FiniteConstructorFieldEmbeddingControls.Element → ULift.{1,0} Prop := fun _ => .up False
  let branchObservation : Number → Number → ULift.{1,0} Prop := fun n _ => .up (n.down = 0)
  have observed := congrFun (congrFun fields.2.1 solvedObservation) branchObservation
  change (ULift.up ((0 : Nat) = 0) : ULift.{1,0} Prop) = ULift.up ((2 : Nat) = 0) at observed
  have impossible : (2 : Nat) = 0 := Eq.mp (congrArg ULift.down observed) rfl
  cases impossible

def solvedApplicationMember : ProofSyntax Const assumptions (.app family (.app solvedFunction field)) :=
  .castIndices rfl (congrArg (fun predicate => Term.app predicate (.app solvedFunction field))
    (instantiate_weaken field family))
    (PredicateProducts.eliminate (given.predicate onlyTrue) (weaken family) solvedFunction field solvedMembership fieldMember)

theorem solved_application_member_holds : (model.denote (.app family (.app solvedFunction field)) values).down :=
  IndexedVectorTreeNativeChildConditionsControls.sound solvedApplicationMember
theorem branch_application_member_holds :
    (model.denote (.app family (.app (.app branchFunction (numeral 2)) sourceVector)) values).down := by
  change (model.denote family values
    (model.denote branchFunction values (model.denote (numeral 2) values) (model.denote sourceVector values))).down
  rw [actual_branch_beta_value]
  exact IndexedVectorTreeNativeChildConditionsControls.actual_branch_from_original_vector_holds

def falseField : ClosedTerm Const E := IndexedVectorTreeNativeChildConditionsControls.falseField
theorem wrong_source_argument_refused : ¬ (model.denote (.app (given.predicate onlyTrue) falseField) values).down :=
  IndexedVectorTreeNativeChildConditionsControls.original_false_field_refused
theorem wrong_source_argument_unprovable : ¬ Nonempty (ProofSyntax Const assumptions
    (.app (given.predicate onlyTrue) falseField)) := by
  rintro ⟨claimed⟩
  exact wrong_source_argument_refused (IndexedVectorTreeNativeChildConditionsControls.sound claimed)

theorem wrong_shape_code_refused :
    ¬ (model.denote IndexedVectorTreeNativeChildConditionsControls.wrongShapeGuard values).down :=
  IndexedVectorTreeNativeChildConditionsControls.wrong_shape_refused
theorem omitted_padding_refused :
    ¬ (model.denote IndexedVectorTreeNativeChildConditionsControls.forgedContract values).down :=
  IndexedVectorTreeNativeChildConditionsControls.omitted_padding_refused

def restrictedNumbers : ClosedTerm Const (N ⇒ .prop) := .lam (.eq (.var .vz) (weakenCtx [N] zero))
theorem restricted_numbers_nonempty :
    (model.denote (.app restrictedNumbers zero) values).down := rfl
theorem missing_total_numeric_recognition_refused :
    ¬ Nonempty (ProofSyntax Const assumptions
      (IndexedVectorTreeConstructorFunctions.Native.numberRecognition restrictedNumbers)) := by
  rintro ⟨claimed⟩
  have allNumbers := IndexedVectorTreeNativeChildConditionsControls.sound claimed
  have atOne := allNumbers (model.denote one values) (full _ _)
  change (ULift.up 1 : Number) = .up 0 at atOne
  have impossible := congrArg ULift.down atOne
  cases impossible

#print axioms solvedMembership_free
#print axioms branchMembership_free
#print axioms actual_solved_beta_value
#print axioms actual_branch_beta_value
#print axioms solved_domain_nonempty
#print axioms branch_admissible_arguments_nonempty
#print axioms branch_distinguishes_zero_and_two_children
#print axioms wrong_source_argument_unprovable
#print axioms missing_total_numeric_recognition_refused

end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeConstructorFunctionControls
