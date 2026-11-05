import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllExistence
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceWitnessControls

/-!
# Retained inputs for the original case applications

The control world is the same independent-payload Native4 interpretation.
Its actual two-element Vector is supplied with a retained two-level pair
of All evidence. Its case guards and prior child and Vector membership facts
are explicit, independently realized inputs. Neither an All guard nor the
parent result is assumed; both the All witness and its existential query
are constructed by retained proof programs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseApplicationInputs
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

noncomputable section

def solvedCaseLaw : ClosedFormula Native.Const := .app SourceWitness.solvedCaseGuard suppliedSolvedCase
def branchCaseLaw : ClosedFormula Native.Const := .app SourceWitness.branchCaseGuard suppliedBranchCase
def choiceLaw : ClosedFormula Native.Const := SelectionProofs.principle Native.selection
def recursionLaw : ClosedFormula Native.Const := NaturalRecursionProofs.statement
  Native.original.zero Native.original.successor (Native.V ⇒ Native.W ⇒ .prop)
def solvedChildLaw : ClosedFormula Native.Const := .app family solvedValue
def branchChildLaw : ClosedFormula Native.Const := .app family zeroBranchValue
def vectorLaw : ClosedFormula Native.Const := originalVectorGuard
def additional := [solvedCaseLaw,branchCaseLaw,choiceLaw,recursionLaw,solvedChildLaw,branchChildLaw,vectorLaw]
def hypotheses : List (ClosedFormula Native.Const) := additional ++ delta

def lift {formula : ClosedFormula Native.Const} (proof : ProofSyntax Native.Const delta formula) :
    ProofSyntax Native.Const hypotheses formula := proof.mono (ProofSyntax.OccurrenceMap.appendLeft additional delta)
def solvedCaseInput : ProofSyntax Native.Const hypotheses solvedCaseLaw := .hyp ⟨0,by simp [hypotheses,additional]⟩
def branchCaseInput : ProofSyntax Native.Const hypotheses branchCaseLaw := .hyp ⟨1,by simp [hypotheses,additional]⟩
def choice : ProofSyntax Native.Const hypotheses choiceLaw := .hyp ⟨2,by simp [hypotheses,additional]⟩
def recursion : ProofSyntax Native.Const hypotheses recursionLaw := .hyp ⟨3,by simp [hypotheses,additional]⟩
def solvedChildInput : ProofSyntax Native.Const hypotheses solvedChildLaw := .hyp ⟨4,by simp [hypotheses,additional]⟩
def branchChildInput : ProofSyntax Native.Const hypotheses branchChildLaw := .hyp ⟨5,by simp [hypotheses,additional]⟩
def vectorInput : ProofSyntax Native.Const hypotheses vectorLaw := .hyp ⟨6,by simp [hypotheses,additional]⟩
def arrayPremises : arrays.ComputationPremises hypotheses :=
  (((((((premises.prepend fieldHyp).prepend vectorLaw).prepend branchChildLaw).prepend solvedChildLaw).prepend
    recursionLaw).prepend choiceLaw).prepend branchCaseLaw).prepend solvedCaseLaw

theorem arrayPremises_free : arrayPremises.FunctionExtensionalityFree := by
  unfold arrayPremises
  apply VectorChildArrays.Operations.ComputationPremises.prepend_free
  apply VectorChildArrays.Operations.ComputationPremises.prepend_free
  apply VectorChildArrays.Operations.ComputationPremises.prepend_free
  apply VectorChildArrays.Operations.ComputationPremises.prepend_free
  apply VectorChildArrays.Operations.ComputationPremises.prepend_free
  apply VectorChildArrays.Operations.ComputationPremises.prepend_free
  apply VectorChildArrays.Operations.ComputationPremises.prepend_free
  exact premises.prepend_free fieldHyp premises_free

theorem lift_free {formula : ClosedFormula Native.Const} (proof : ProofSyntax Native.Const delta formula)
    (free : proof.FunctionExtensionalityFree) : (lift proof).FunctionExtensionalityFree :=
  (ProofSyntax.functionExtensionalityFree_mono _ _).mpr free

theorem hypotheses_realizable : Soundness.SatisfiesHyps model values hypotheses := by
  intro formula present
  rcases List.mem_append.mp present with extra | inherited
  · simp only [additional,List.mem_cons,List.not_mem_nil,or_false] at extra
    rcases extra with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact SourceWitness.solved_case_guard_holds
    · exact SourceWitness.branch_case_guard_holds
    · exact (model.models_iff_denote_closed _ values).mp reader_selection_holds
    · exact (model.models_iff_denote_closed _ values).mp (recursion_holds _)
    · exact IndexedVectorTreeNativeWitnessControls.solved_member_holds
    · exact IndexedVectorTreeNativeWitnessControls.branch_member_holds
    · exact IndexedVectorTreeNativeWitnessControls.vector_guard_holds
  · exact IndexedVectorTreeNativeWitnessControls.delta_realizable formula inherited

theorem sound {formula : ClosedFormula Native.Const} (proof : ProofSyntax Native.Const hypotheses formula) :
    (model.denote formula values).down :=
  Soundness.extDerivation_sound proof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) hypotheses_realizable

private def familyMotive (predicate : ClosedTerm Native.Const (Native.E ⇒ .prop)) :
    ClosedTerm Native.Const (Native.E ⇒ Native.W ⇒ .prop) :=
  .lam (.lam (.app (weaken (weaken predicate)) (.var (.vs .vz))))

private def familyMotive_beta {H : List (ClosedFormula Native.Const)}
    (predicate : ClosedTerm Native.Const (Native.E ⇒ .prop))
    (point : ClosedTerm Native.Const Native.E) (evidence : ClosedTerm Native.Const Native.W) :
    ProofSyntax Native.Const H (.eq (.app (.app (familyMotive predicate) point) evidence) (.app predicate point)) := by
  apply ProofSyntax.castIndices rfl ?_
    (CurriedGuardProgramProofs.beta2 (.app (weaken (weaken predicate)) (.var (.vs .vz))) point evidence)
  simp only [instantiate,HOL.subst,Subst.lift,Subst.single,subst_weaken,PredicateFixedPoint.subst_single_weaken]
  rw [← weaken,PredicateFixedPoint.subst_single_weaken]
  rfl

private theorem familyMotive_beta_free {H : List (ClosedFormula Native.Const)}
    (predicate : ClosedTerm Native.Const (Native.E ⇒ .prop))
    (point : ClosedTerm Native.Const Native.E) (evidence : ClosedTerm Native.Const Native.W) :
    (familyMotive_beta (H := H) predicate point evidence).FunctionExtensionalityFree := by
  unfold familyMotive_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

private def motiveOfMember {H : List (ClosedFormula Native.Const)}
    (predicate : ClosedTerm Native.Const (Native.E ⇒ .prop))
    (point : ClosedTerm Native.Const Native.E) (evidence : ClosedTerm Native.Const Native.W)
    (member : ProofSyntax Native.Const H (.app predicate point)) :
    ProofSyntax Native.Const H (.app (.app (familyMotive predicate) point) evidence) :=
  .impE (.eqPropER (familyMotive_beta predicate point evidence)) member

private theorem motiveOfMember_free {H : List (ClosedFormula Native.Const)}
    (predicate : ClosedTerm Native.Const (Native.E ⇒ .prop))
    (point : ClosedTerm Native.Const Native.E) (evidence : ClosedTerm Native.Const Native.W)
    (member : ProofSyntax Native.Const H (.app predicate point)) (free : member.FunctionExtensionalityFree) :
    (motiveOfMember predicate point evidence member).FunctionExtensionalityFree :=
  ⟨familyMotive_beta_free predicate point evidence,free⟩

def headEvidence : ClosedTerm Native.Const Native.W := Native.witness
def nilEvidence : ClosedTerm Native.Const Native.W :=
  .app (StructuralProfile.reflexivityCode Native.witness Native.N) Native.original.zero
def tailEvidence : ClosedTerm Native.Const Native.W := PredicateSigma.pair Native.pairs headEvidence nilEvidence
def evidence : ClosedTerm Native.Const Native.W := PredicateSigma.pair Native.pairs headEvidence tailEvidence

def solvedMotive : ProofSyntax Native.Const hypotheses (.app (.app motive solvedValue) headEvidence) :=
  motiveOfMember family solvedValue headEvidence solvedChildInput
def branchMotive : ProofSyntax Native.Const hypotheses (.app (.app motive zeroBranchValue) headEvidence) :=
  motiveOfMember family zeroBranchValue headEvidence branchChildInput

def allPredicate (length : ClosedTerm Native.Const Native.N) (vector : ClosedTerm Native.Const Native.V) :=
  NativeVectorAll.Reading.allCode Native.original Native.pairs Native.witness Native.selection family motive length vector

@[irreducible] def nilAll : ProofSyntax Native.Const hypotheses (.app (allPredicate Native.original.zero arrays.nil) nilEvidence) := by
  have coded := NativeVectorAll.Evidence.nil_value Native.original Native.pairs Native.witness Native.selection
    family motive choice recursion
  have alignment := NativeVectorAll.Reading.arguments_equal Native.original Native.pairs Native.witness Native.selection
    (assumptions := hypotheses) family motive Native.original.zero Native.original.zero _ arrays.nil (.eqRefl _)
    (NativeVectorComputationRows.GuardedFamily.nil_apply (NativeVectorAll.Reading.operations Native.original Native.selection) family)
  exact .impE (.eqPropEL (.eqApp nilEvidence alignment)) coded

@[irreducible] private def consAll (length : ClosedTerm Native.Const Native.N)
    (head : ClosedTerm Native.Const Native.E) (tail : ClosedTerm Native.Const Native.V)
    (headProof : ProofSyntax Native.Const hypotheses (.app (.app motive head) headEvidence))
    (tailProof : ProofSyntax Native.Const hypotheses (.app (allPredicate length tail) nilEvidence)) :
    ProofSyntax Native.Const hypotheses (.app (allPredicate (.app Native.original.successor length)
      (arrays.toSignature.consValue length head tail)) (PredicateSigma.pair Native.pairs headEvidence nilEvidence)) := by
  have coded := NativeVectorAll.Evidence.cons_value Native.original Native.pairs Native.witness Native.selection
    family motive choice recursion length head tail arrayPremises.head arrayPremises.tail
    headEvidence nilEvidence headProof tailProof
  have alignment := NativeVectorAll.Reading.arguments_equal Native.original Native.pairs Native.witness Native.selection
    (assumptions := hypotheses) family motive (.app Native.original.successor length) (.app Native.original.successor length)
    _ (arrays.toSignature.consValue length head tail) (.eqRefl _)
    ((NativeVectorAll.Reading.operations Native.original Native.selection).cons_apply family length head tail)
  exact .impE (.eqPropEL (.eqApp (PredicateSigma.pair Native.pairs headEvidence nilEvidence) alignment)) coded

def tailAll : ProofSyntax Native.Const hypotheses (.app (allPredicate one tailVector) tailEvidence) :=
  consAll Native.original.zero zeroBranchValue arrays.nil branchMotive nilAll

@[irreducible] def allInput : ProofSyntax Native.Const hypotheses (.app (allPredicate (numeral 2) sourceVector) evidence) := by
  have coded := NativeVectorAll.Evidence.cons_value Native.original Native.pairs Native.witness Native.selection
    family motive choice recursion one solvedValue tailVector arrayPremises.head arrayPremises.tail
    headEvidence tailEvidence solvedMotive tailAll
  have alignment := NativeVectorAll.Reading.arguments_equal Native.original Native.pairs Native.witness Native.selection
    (assumptions := hypotheses) family motive (numeral 2) (numeral 2) _ sourceVector (.eqRefl _)
    ((NativeVectorAll.Reading.operations Native.original Native.selection).cons_apply family one solvedValue tailVector)
  exact .impE (.eqPropEL (.eqApp evidence alignment)) coded

def allQuery : ProofSyntax Native.Const hypotheses
    (NativeVectorAll.Existence.query Native.original Native.pairs Native.witness Native.selection family motive (numeral 2) sourceVector) :=
  CurriedPredicates.existsValue_intro [] (allPredicate (numeral 2) sourceVector) PUnit.unit evidence allInput

theorem solvedMotive_free : solvedMotive.FunctionExtensionalityFree :=
  motiveOfMember_free family solvedValue headEvidence solvedChildInput True.intro
theorem branchMotive_free : branchMotive.FunctionExtensionalityFree :=
  motiveOfMember_free family zeroBranchValue headEvidence branchChildInput True.intro

theorem nilAll_free : nilAll.FunctionExtensionalityFree := by
  unfold nilAll
  constructor
  · apply NativeVectorAll.Reading.arguments_equal_free
    · trivial
    · trivial
  · apply NativeVectorAll.Evidence.nil_value_free <;> trivial

private theorem consAll_free (length : ClosedTerm Native.Const Native.N)
    (head : ClosedTerm Native.Const Native.E) (tail : ClosedTerm Native.Const Native.V)
    (headProof : ProofSyntax Native.Const hypotheses (.app (.app motive head) headEvidence))
    (tailProof : ProofSyntax Native.Const hypotheses (.app (allPredicate length tail) nilEvidence))
    (headFree : headProof.FunctionExtensionalityFree) (tailFree : tailProof.FunctionExtensionalityFree) :
    (consAll length head tail headProof tailProof).FunctionExtensionalityFree := by
  unfold consAll
  constructor
  · apply NativeVectorAll.Reading.arguments_equal_free
    · trivial
    · trivial
  · apply NativeVectorAll.Evidence.cons_value_free
    · trivial
    · trivial
    · exact arrayPremises_free.2.2.2.2.1
    · exact arrayPremises_free.2.2.2.2.2
    · exact headFree
    · exact tailFree

theorem tailAll_free : tailAll.FunctionExtensionalityFree :=
  consAll_free _ _ _ _ _ branchMotive_free nilAll_free

theorem allInput_free : allInput.FunctionExtensionalityFree := by
  unfold allInput
  constructor
  · apply NativeVectorAll.Reading.arguments_equal_free
    · trivial
    · trivial
  · apply NativeVectorAll.Evidence.cons_value_free
    · trivial
    · trivial
    · exact arrayPremises_free.2.2.2.2.1
    · exact arrayPremises_free.2.2.2.2.2
    · exact solvedMotive_free
    · exact tailAll_free

theorem allQuery_free : allQuery.FunctionExtensionalityFree := by
  apply CurriedPredicates.existsValue_intro_free
  exact allInput_free
theorem actual_all_input_holds : (model.denote (.app (allPredicate (numeral 2) sourceVector) evidence) values).down := sound allInput

#print axioms allInput
#print axioms allInput_free
#print axioms allQuery_free
#print axioms hypotheses_realizable

end
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseApplicationInputs
