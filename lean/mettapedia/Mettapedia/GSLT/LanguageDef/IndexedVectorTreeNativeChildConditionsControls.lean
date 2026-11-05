import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeFunctionVectorFixture
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilySolved
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyBranch

/-!
# Nonempty actual-family controls for the complete child contract

A proved solved value and a proved one-child branch belong to the same
derived family with its original restrictive answer predicate. The source
Vector contains them in that order. Its actual reader guard produces the
full branch contract, including inactive padding. All displayed assumptions
hold in the recursive-space/function-vector model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeChildConditionsControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open FiniteConstructorEncoding IndexedConstructorGuards
open FiniteConstructorFieldEmbeddingControls (Base N A E Space filler)
open IndexedVectorTreeFunctionVectorFixture

attribute [local irreducible] IndexedVectorTreeNativeChildConditions.ReaderGuard.vector_beta

def family := IndexedVectorTreeStoredFamily.family given onlyTrue numbers zero one successor numeral bottom
def signature := IndexedVectorTreeStoredFamily.signature given onlyTrue numbers zero one successor numeral bottom
def sourceField : ClosedTerm Const A := .const (.old (.old (.answer true)))
def solvedValue := IndexedVectorTreeStoredFamilySolved.value given onlyTrue numbers zero one numeral bottom (.app given.encode sourceField)

def sourceMember : ProofSyntax Const assumptions (.app onlyTrue sourceField) :=
  .impE (.eqPropER (.beta sourceField (.eq (.var .vz) (.const (.old (.old (.answer true))))))) (.eqRefl sourceField)
theorem sourceMember_free : sourceMember.FunctionExtensionalityFree := by trivial

@[irreducible] def solvedProof : ProofSyntax Const assumptions (.app family solvedValue) :=
  IndexedVectorTreeStoredFamilySolved.fromAnswer given onlyTrue numbers zero one successor numeral bottom sourceField sourceMember
theorem solvedProof_free : solvedProof.FunctionExtensionalityFree := by
  unfold solvedProof
  exact IndexedVectorTreeStoredFamilySolved.fromAnswer_free given onlyTrue numbers zero one successor numeral bottom
    sourceField sourceMember sourceMember_free

def numberMember (n : ClosedTerm Const N) : ProofSyntax Const assumptions (.app numbers n) :=
  .impE (.eqPropER (.beta n .top)) .topI
theorem numberMember_free (n : ClosedTerm Const N) : (numberMember n).FunctionExtensionalityFree := by trivial

def oneVector : ClosedTerm Const V := ops.toSignature.consValue zero solvedValue ops.nil
@[irreducible] def oneVectorProof : ProofSyntax Const assumptions (ops.toSignature.member family one oneVector) :=
  ops.toSignature.cons_member family zero solvedValue ops.nil solvedProof (ops.toSignature.nil_member family)
theorem oneVectorProof_free : oneVectorProof.FunctionExtensionalityFree := by
  unfold oneVectorProof
  exact ops.toSignature.cons_member_free family zero solvedValue ops.nil solvedProof (ops.toSignature.nil_member family)
    solvedProof_free (ops.toSignature.nil_member_free _)

def branchValue : ClosedTerm Const E :=
  IndexedVectorTreeStoredFamilyBranch.value ops given onlyTrue numbers one numeral bottom one oneVector
@[irreducible] def branchProof : ProofSyntax Const assumptions (.app family branchValue) :=
  IndexedVectorTreeStoredFamilyBranch.member ops given onlyTrue numbers one numeral bottom one oneVector
    (numberMember one) premises arithmetic oneVectorProof
theorem branchProof_free : branchProof.FunctionExtensionalityFree := by
  unfold branchProof
  exact IndexedVectorTreeStoredFamilyBranch.member_free ops given onlyTrue numbers one numeral bottom one oneVector
    (numberMember one) premises arithmetic oneVectorProof (numberMember_free _) premises_free arithmetic_free oneVectorProof_free

def tailVector : ClosedTerm Const V := ops.toSignature.consValue zero branchValue ops.nil
@[irreducible] def tailVectorProof : ProofSyntax Const assumptions (ops.toSignature.member family one tailVector) :=
  ops.toSignature.cons_member family zero branchValue ops.nil branchProof (ops.toSignature.nil_member family)
theorem tailVectorProof_free : tailVectorProof.FunctionExtensionalityFree := by
  unfold tailVectorProof
  exact ops.toSignature.cons_member_free family zero branchValue ops.nil branchProof (ops.toSignature.nil_member family)
    branchProof_free (ops.toSignature.nil_member_free _)

def sourceVector : ClosedTerm Const V := ops.toSignature.consValue one solvedValue tailVector
@[irreducible] def vectorProof : ProofSyntax Const assumptions
    (ops.toSignature.member family (numeral 2) sourceVector) :=
  ops.toSignature.cons_member family one solvedValue tailVector solvedProof tailVectorProof
theorem vectorProof_free : vectorProof.FunctionExtensionalityFree := by
  unfold vectorProof
  exact ops.toSignature.cons_member_free family one solvedValue tailVector solvedProof tailVectorProof solvedProof_free tailVectorProof_free

def originalVectorGuard : ClosedFormula Const :=
  .app (NativeVectorAll.Reading.vectorCode original readerSelection family (numeral 2)) sourceVector
@[irreducible] def originalVectorProof : ProofSyntax Const assumptions originalVectorGuard :=
  .impE (.eqPropER (IndexedVectorTreeNativeChildConditions.ReaderGuard.vector_beta original readerSelection
    family (numeral 2) sourceVector)) vectorProof
theorem originalVectorProof_free : originalVectorProof.FunctionExtensionalityFree := by
  unfold originalVectorProof
  exact ⟨IndexedVectorTreeNativeChildConditions.ReaderGuard.vector_beta_free original readerSelection family (numeral 2) sourceVector,
    vectorProof_free⟩

def payload := IndexedVectorTreeBranchActivity.payload given onlyTrue numbers zero one numeral (numeral 2) zero
def children := ops.single (numeral 2) sourceVector bottom
def contract : ClosedFormula Const := signature.childConditions signature.least payload children

@[irreducible] def childProof : ProofSyntax Const assumptions contract :=
  IndexedVectorTreeNativeChildConditions.ReaderGuard.sourceChildConditions original readerSelection elementSelection arraySelection
    given onlyTrue numbers one numeral bottom (numeral 2) sourceVector (numberMember _) premises arithmetic originalVectorProof
theorem childProof_free : childProof.FunctionExtensionalityFree := by
  unfold childProof
  exact IndexedVectorTreeNativeChildConditions.ReaderGuard.sourceChildConditions_free original readerSelection elementSelection arraySelection
    given onlyTrue numbers one numeral bottom (numeral 2) sourceVector (numberMember _) premises arithmetic originalVectorProof
    (numberMember_free _) premises_free arithmetic_free originalVectorProof_free

def nativeBranchValue : ClosedTerm Const E :=
  IndexedVectorTreeStoredFamilyBranch.ReaderGuard.value original elementSelection arraySelection
    given onlyTrue numbers one numeral bottom (numeral 2) sourceVector
@[irreducible] def nativeBranchProof : ProofSyntax Const assumptions (.app family nativeBranchValue) :=
  IndexedVectorTreeStoredFamilyBranch.ReaderGuard.member original readerSelection elementSelection arraySelection
    given onlyTrue numbers one numeral bottom (numeral 2) sourceVector (numberMember _) premises arithmetic originalVectorProof
theorem nativeBranchProof_free : nativeBranchProof.FunctionExtensionalityFree := by
  unfold nativeBranchProof
  exact IndexedVectorTreeStoredFamilyBranch.ReaderGuard.member_free original readerSelection elementSelection arraySelection
    given onlyTrue numbers one numeral bottom (numeral 2) sourceVector (numberMember _) premises arithmetic originalVectorProof
    (numberMember_free _) premises_free arithmetic_free originalVectorProof_free

theorem sound {formula : ClosedFormula Const} (proof : ProofSyntax Const assumptions formula) :
    (model.denote formula values).down :=
  Soundness.extDerivation_sound proof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable

theorem solved_member_holds : (model.denote (.app family solvedValue) values).down := sound solvedProof
theorem branch_member_holds : (model.denote (.app family branchValue) values).down := sound branchProof
theorem source_vector_guard_holds : (model.denote originalVectorGuard values).down := sound originalVectorProof
theorem complete_child_contract_holds : (model.denote contract values).down := sound childProof
theorem actual_branch_from_original_vector_holds : (model.denote (.app family nativeBranchValue) values).down := sound nativeBranchProof

def firstLookup : ProofSyntax Const assumptions
    (IndexedVectorPositions.lookup ops.toSignature (numeral 2) sourceVector zero solvedValue) :=
  IndexedVectorPositions.here ops.toSignature one solvedValue tailVector
def secondLookup : ProofSyntax Const assumptions
    (IndexedVectorPositions.lookup ops.toSignature (numeral 2) sourceVector one branchValue) :=
  IndexedVectorPositions.there ops.toSignature one solvedValue tailVector zero branchValue
    (IndexedVectorPositions.here ops.toSignature zero branchValue ops.nil)

def firstValue : ProofSyntax Const assumptions (.eq (.app children zero) solvedValue) :=
  ops.singleAtLookup (numeral 2) sourceVector bottom zero solvedValue premises firstLookup
def secondValue : ProofSyntax Const assumptions (.eq (.app children one) branchValue) :=
  ops.singleAtLookup (numeral 2) sourceVector bottom one branchValue premises secondLookup
def endPadding : ProofSyntax Const assumptions (.eq (.app children (numeral 2)) bottom) :=
  ops.singleAtEnd family (numeral 2) sourceVector bottom premises vectorProof

theorem first_value_holds : model.denote children values (model.denote zero values) = model.denote solvedValue values :=
  model.eq_of_eqv_of_fullDomains full (sound firstValue)
theorem second_value_holds : model.denote children values (model.denote one values) = model.denote branchValue values :=
  model.eq_of_eqv_of_fullDomains full (sound secondValue)
theorem first_inactive_is_bottom : model.denote children values (model.denote (numeral 2) values) = model.denote bottom values :=
  model.eq_of_eqv_of_fullDomains full (sound endPadding)

theorem solved_not_bottom : model.denote solvedValue values ≠ model.denote bottom values := by
  intro same
  exact Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics.construct_ne_bottom filler _ _ _ same

theorem constructor_values_distinct : model.denote solvedValue values ≠ model.denote branchValue values := by
  intro same
  have tags := (Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics.construct_injective filler _ _ _ _ _ _).mp same
  exact Nat.noConfusion tags.1

theorem ordered_slots_distinct : model.denote children values (model.denote zero values) ≠
    model.denote children values (model.denote one values) := by
  rw [first_value_holds,second_value_holds]
  exact constructor_values_distinct

def falseField : ClosedTerm Const E := .app given.encode (.const (.old (.old (.answer false))))
theorem original_false_field_refused : ¬ (model.denote (.app (given.predicate onlyTrue) falseField) values).down :=
  VectorTreeSuccessorFixture.rejected_false

def wrongShapeGuard := IndexedVectorTreeBranchActivity.allowed given onlyTrue numbers zero one numeral (numeral 2) (numeral 2)

def wrongShapeConsequence : ProofSyntax Const assumptions (.imp wrongShapeGuard (.eq (numeral 2) zero)) := by
  apply ProofSyntax.impI
  have compiled : ProofSyntax Const (wrongShapeGuard :: assumptions)
      (applyArguments [N,N] (IndexedVectorTreeStoredFieldGuards.compiledConditions given onlyTrue numbers zero one ⟨1,by decide⟩)
        (numeral 2,numeral 2,PUnit.unit)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := wrongShapeGuard :: assumptions) 0)
    exact congrArg (fun condition => applyArguments [N,N] condition (numeral 2,numeral 2,PUnit.unit))
      (IndexedVectorTreeStoredFieldGuards.allowed_eq given onlyTrue numbers zero one numeral ⟨1,by decide⟩)
  exact .andEL (.andER (IndexedVectorTreeStoredFieldGuards.branchRead given onlyTrue numbers zero one (numeral 2) (numeral 2) compiled))

theorem wrong_shape_refused : ¬ (model.denote wrongShapeGuard values).down := by
  intro present
  have same := model.eq_of_eqv_of_fullDomains full ((sound wrongShapeConsequence) present)
  have impossible : (2 : Nat) = 0 := congrArg ULift.down same
  exact Nat.noConfusion impossible

def inactiveOne : ProofSyntax Const assumptions
    (.not (IndexedVectorTreeBranchActivity.activity given onlyTrue numbers zero one successor numeral one zero one)) := by
  apply ProofSyntax.notI
  have bounded := ProofSyntax.andER (IndexedVectorTreeBranchActivity.activityReadback
    given onlyTrue numbers zero one successor numeral one zero one
      (.hyp (Δ := IndexedVectorTreeBranchActivity.activity given onlyTrue numbers zero one successor numeral one zero one :: assumptions) 0))
  exact SuccessorOrder.lessZeroRefute successor zero zero ((arithmetic.prepend _).separation)
    (SuccessorOrder.lessSuccessorCancel successor zero zero ((arithmetic.prepend _).injectivity) bounded)

def forgedChildren : ClosedTerm Const V := ops.toSignature.consValue one solvedValue oneVector
def forgedPayload := IndexedVectorTreeBranchActivity.payload given onlyTrue numbers zero one numeral one zero
def forgedContract : ClosedFormula Const := signature.childConditions signature.least forgedPayload forgedChildren

theorem forged_extra_child (position : Ty.denote model.Carrier N) (same : position = model.denote one values) :
    model.denote forgedChildren values position = model.denote solvedValue values := by
  subst position
  rfl

theorem omitted_padding_refused : ¬ (model.denote forgedContract values).down := by
  intro present
  simp only [forgedContract,RecursiveSpacePredicate.Contextual.childConditions,HenkinModel.denote,PreModel.denote,
    Soundness.denote_weaken,PreModel.extend] at present
  have inactive := sound inactiveOne
  have padding := (present (model.denote one values) (full _ _)).2 inactive
  have same := model.eq_of_eqv_of_fullDomains full padding
  exact solved_not_bottom ((forged_extra_child _ rfl).symm.trans same)

theorem omitted_padding_unprovable : ¬ Nonempty (ProofSyntax Const assumptions forgedContract) := by
  rintro ⟨proof⟩
  exact omitted_padding_refused (sound proof)

#print axioms solvedProof_free
#print axioms branchProof_free
#print axioms childProof_free
#print axioms nativeBranchProof_free
#print axioms actual_branch_from_original_vector_holds
#print axioms complete_child_contract_holds
#print axioms ordered_slots_distinct
#print axioms omitted_padding_unprovable
#print axioms wrong_shape_refused
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeChildConditionsControls
