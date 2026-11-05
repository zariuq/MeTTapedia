import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseApplications
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseApplicationInputs
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllInterpretation

/-!
# Original case applications with a genuine nonempty All input

The control world is the same independent-payload Native4 interpretation.
Its actual two-element Vector is supplied with a retained two-level pair
of All evidence. The case guards are explicit, independently realized input
premises. The parent result is derived by applying those guards; it is not
an input premise. Existential use keeps the All witness local.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseApplicationsControls
open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.Languages.HOLLight
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open IndexedVectorTreeNativeWitnessModel
open IndexedVectorTreeNativeWitnessControls
  (family motive suppliedSolvedCase suppliedBranchCase solvedFunction branchFunction solvedValue zeroBranchValue
   tailVector sourceVector fieldHyp delta originalVectorGuard)
namespace SourceWitness
export IndexedVectorTreeNativeSourceWitnessControls
  (answer solvedCaseGuard branchCaseGuard solved_case_guard_holds branch_case_guard_holds)
end SourceWitness
namespace Applications
export IndexedVectorTreeSourceCaseApplications (solvedApply branchApply branchExists parentExists)
end Applications

noncomputable section

open IndexedVectorTreeSourceCaseApplicationInputs

def field : ClosedTerm Native.Const Native.E := .app input.encode one
def fieldGuard : ProofSyntax Native.Const hypotheses (.app SourceWitness.answer field) :=
  ConstructorPredicateRepresentation.introduce input.encode originalPredicate one
    (lift (.hyp (Δ := delta) ⟨0,by simp [delta]⟩))

@[irreducible] def solvedApplication : ProofSyntax Native.Const hypotheses
    (.app (.app motive (.app solvedFunction field)) (.app suppliedSolvedCase field)) :=
  Applications.solvedApply SourceWitness.answer motive solvedFunction suppliedSolvedCase field solvedCaseInput fieldGuard

@[irreducible] def branchApplication : ProofSyntax Native.Const hypotheses
    (.app (.app motive (.app (.app branchFunction (numeral 2)) sourceVector))
      (.app (.app (.app suppliedBranchCase (numeral 2)) sourceVector) evidence)) :=
  Applications.branchApply family motive branchFunction suppliedBranchCase (numeral 2) sourceVector evidence
    branchCaseInput vectorInput allInput

@[irreducible] def branchExistence : ProofSyntax Native.Const hypotheses
    (Applications.parentExists motive branchFunction (numeral 2) sourceVector) :=
  Applications.branchExists family motive branchFunction suppliedBranchCase (numeral 2) sourceVector
    branchCaseInput vectorInput allQuery

theorem actual_solved_application_holds : (model.denote
    (.app (.app motive (.app solvedFunction field)) (.app suppliedSolvedCase field)) values).down := sound solvedApplication
theorem actual_branch_application_holds : (model.denote
    (.app (.app motive (.app (.app branchFunction (numeral 2)) sourceVector))
      (.app (.app (.app suppliedBranchCase (numeral 2)) sourceVector) evidence)) values).down := sound branchApplication
theorem actual_parent_exists : (model.denote
    (Applications.parentExists motive branchFunction (numeral 2) sourceVector) values).down := sound branchExistence

theorem original_wrong_field_refused : ¬ Nonempty (ProofSyntax Native.Const hypotheses
    (.app SourceWitness.answer IndexedVectorTreeNativeWitnessControls.zeroField)) := by
  rintro ⟨proof⟩
  exact IndexedVectorTreeNativeWitnessControls.original_zero_payload_refused (sound proof)

private theorem cons_denote (length : ClosedTerm Native.Const Native.N)
    (head : ClosedTerm Native.Const Native.E) (tail : ClosedTerm Native.Const Native.V) (point : Space) :
    (model.denote (allPredicate (.app Native.original.successor length)
      (arrays.toSignature.consValue length head tail)) values point).down ↔
    ∃ first, model.adm Native.W first ∧ ∃ second, model.adm Native.W second ∧
      model.Eqv Native.W (PredicateSigma.pairValue model Native.pairs first second) point ∧
      (model.denote (.app motive head) values first).down ∧
      (model.denote (allPredicate length tail) values second).down := by
  have coded := NativeVectorAll.Interpretation.cons_denote Native.original Native.pairs Native.witness Native.selection
    family motive choice recursion model values (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) hypotheses_realizable length head tail arrayPremises.head arrayPremises.tail point (by trivial)
  have alignment := NativeVectorAll.Reading.arguments_equal Native.original Native.pairs Native.witness Native.selection
    (assumptions := hypotheses) family motive (.app Native.original.successor length) (.app Native.original.successor length)
    _ (arrays.toSignature.consValue length head tail) (.eqRefl _)
    ((NativeVectorAll.Reading.operations Native.original Native.selection).cons_apply family length head tail)
  exact (model.eqv_arr_apply (sound alignment) (by trivial : model.adm Native.W point)).symm.trans coded

theorem genuine_pair_not_bottom (first second : Space) :
    PredicateSigma.pairValue model Native.pairs first second ≠ bottomValue := by
  exact RecursiveSpaceSemantics.construct_ne_bottom filler _ _ _

private theorem pairImage_refused (query : Prop) (firstGuard secondGuard : Space → Prop)
    (shape : query ↔ ∃ first, model.adm Native.W first ∧ ∃ second, model.adm Native.W second ∧
      model.Eqv Native.W (PredicateSigma.pairValue model Native.pairs first second) bottomValue ∧
      firstGuard first ∧ secondGuard second) : ¬ query := by
  intro present
  obtain ⟨first,_,second,_,same,_,_⟩ := shape.mp present
  exact genuine_pair_not_bottom first second (model.eq_of_eqv_of_fullDomains full same)

private theorem wrong_evidence_at_bottom :
    ¬ (model.denote (allPredicate (.app Native.original.successor one)
      (arrays.toSignature.consValue one solvedValue tailVector)) values bottomValue).down :=
  pairImage_refused
    (model.denote (allPredicate (.app Native.original.successor one)
      (arrays.toSignature.consValue one solvedValue tailVector)) values bottomValue).down
    (fun first => (model.denote (.app motive solvedValue) values first).down)
    (fun second => (model.denote (allPredicate one tailVector) values second).down)
    (cons_denote one solvedValue tailVector bottomValue)

private theorem atWitness_refused (predicate : ClosedTerm Native.Const (Native.W ⇒ .prop))
    (atBottom : ¬ (model.denote predicate values bottomValue).down) :
    ¬ (model.denote (.app predicate Native.witness) values).down :=
  Eq.mpr (congrArg (fun point : Space => ¬ (model.denote predicate values point).down) witness_meaning) atBottom

theorem wrong_evidence_refused : ¬ (model.denote (.app (allPredicate (numeral 2) sourceVector) Native.witness) values).down :=
  atWitness_refused (allPredicate (numeral 2) sourceVector) wrong_evidence_at_bottom

theorem wrong_evidence_unprovable : ¬ Nonempty (ProofSyntax Native.Const hypotheses
    (.app (allPredicate (numeral 2) sourceVector) Native.witness)) := by
  rintro ⟨proof⟩
  exact wrong_evidence_refused (sound proof)

theorem empty_evidence_boundary : (model.denote (.app (allPredicate Native.original.zero arrays.nil) nilEvidence) values).down :=
  sound nilAll
theorem solvedApplication_free : solvedApplication.FunctionExtensionalityFree := by
  unfold solvedApplication
  exact IndexedVectorTreeSourceCaseApplications.solvedApply_free SourceWitness.answer motive solvedFunction
    suppliedSolvedCase field solvedCaseInput fieldGuard True.intro
    (ConstructorPredicateRepresentation.introduce_free input.encode originalPredicate one
      (lift (.hyp (Δ := delta) ⟨0,by simp [delta]⟩)) (by trivial))

theorem branchApplication_free : branchApplication.FunctionExtensionalityFree := by
  unfold branchApplication
  exact IndexedVectorTreeSourceCaseApplications.branchApply_free family motive branchFunction suppliedBranchCase
    (numeral 2) sourceVector evidence branchCaseInput vectorInput allInput True.intro True.intro allInput_free

theorem branchExistence_free : branchExistence.FunctionExtensionalityFree := by
  unfold branchExistence
  exact IndexedVectorTreeSourceCaseApplications.branchExists_free family motive branchFunction suppliedBranchCase
    (numeral 2) sourceVector branchCaseInput vectorInput allQuery True.intro True.intro allQuery_free
#print axioms allInput
#print axioms actual_all_input_holds
#print axioms actual_branch_application_holds
#print axioms actual_parent_exists
#print axioms original_wrong_field_refused
#print axioms genuine_pair_not_bottom
#print axioms wrong_evidence_unprovable
#print axioms allInput_free
#print axioms branchApplication_free
#print axioms branchExistence_free

end
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseApplicationsControls
