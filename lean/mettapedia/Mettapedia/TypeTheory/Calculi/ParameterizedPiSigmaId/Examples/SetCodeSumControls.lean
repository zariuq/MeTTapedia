import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeSumProofs
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeControls

/-!
# A dependent-pair source control and a wrong-fibre countermodel

The fibre compares its new index with an ambient variable. The second
projection is typed at the first projection's fibre. Substituting the second
projection instead is false in a model satisfying the receiver's set laws
and the original context guard.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeSumControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open TowerInterpretation CodedHOL
open SetComprehensionProofs
open HOL.Embedding

namespace Source
abbrev church := SetCodeControls.Source.church
def context : CCtx Nat 1 := .snoc .nil (.head 2)
def domain : CTm Nat 1 := .head 2
def left : CTm Nat 1 := .var 0
def family : CTm Nat 2 := .id (.head 2) (.var 0) (.var 1)
def right : CTm Nat 1 := .refl left
def pair : CTm Nat 1 := .pair left right
def sumType : CTm Nat 1 := .sigma domain family

theorem left_typed : CTyped church context left domain := .var 0
theorem family_typed : CTyped church (.snoc context domain) family (.head 3) :=
  .idForm (.headType rfl) (by change 0 < 3; decide) (.var 0) (.var 1)
theorem sum_typed : CTyped church context sumType (.head 3) :=
  .sigmaForm (.headType rfl) (by change 0 < 3; decide) family_typed (by change 0 < 3; decide) rfl
theorem right_typed : CTyped church context right (CTm.inst0 left family) := .reflIntro left_typed
theorem pair_typed : CTyped church context pair sumType :=
  .pairIntro sum_typed (by change 0 < 3; decide) left_typed right_typed
theorem first_typed : CTyped church context (.fst pair) domain := .fstElim pair_typed
theorem second_typed : CTyped church context (.snd pair) (CTm.inst0 (.fst pair) family) := .sndElim pair_typed
theorem first_beta : CDerivable church (.equality context (.fst pair) left domain) :=
  .betaFst sum_typed (by change 0 < 3; decide) left_typed right_typed
theorem second_beta : CDerivable church (.equality context (.snd pair) right (CTm.inst0 left family)) :=
  .betaSnd sum_typed (by change 0 < 3; decide) left_typed right_typed
end Source

abbrev Constants := SetCode.PrimitiveSymbol Nat
abbrev core : Core Constants := SetCode.core
abbrev epsilon : ClosedTerm Constants (SelectionProofs.Selection object) := SetCode.epsilon
abbrev basis : List (Formula Constants [object]) := weakenHyps (σ := object) SetCodeControls.basis
def sets : SetTraceProofs.Laws core epsilon basis := SetCodeControls.sets.weaken object
theorem sets_free : sets.Free := SetCodeControls.sets.weaken_free object SetCodeControls.sets_free
def bound : Fin 1 → Term (CodedHOL.Symbol Nat) [object] object := fun _ => .var .vz

def leftReceipt : ProofSyntax Constants basis (SetCode.expand (judgmentAt (.typing Source.context Source.left Source.domain) bound)) :=
  SetCode.ContextProofs.variableJudgment Source.context 0 bound
def rightReceipt : ProofSyntax Constants basis (SetCode.expand
    (judgmentAt (.typing Source.context Source.right (CTm.inst0 Source.left Source.family)) bound)) :=
  SetCode.TypingProofs.reflexivityJudgment Source.context Source.domain Source.left bound sets.pairing.power sets.pairing.separation
def pairReceipt : ProofSyntax Constants basis (SetCode.expand (judgmentAt (.typing Source.context Source.pair Source.sumType) bound)) :=
  SetCode.SumProofs.pairJudgment Source.context Source.left Source.right Source.domain Source.family bound sets leftReceipt rightReceipt
def firstReceipt := SetCode.SumProofs.firstJudgment Source.context Source.pair Source.domain Source.family bound sets pairReceipt
def secondReceipt := SetCode.SumProofs.secondJudgment Source.context Source.pair Source.domain Source.family bound sets pairReceipt
def firstBetaReceipt := SetCode.SumProofs.firstBetaJudgment Source.context Source.left Source.right Source.domain bound sets.pairing leftReceipt
def secondBetaReceipt := SetCode.SumProofs.secondBetaJudgment Source.context Source.left Source.right Source.family bound sets.pairing rightReceipt

theorem leftReceipt_free : leftReceipt.FunctionExtensionalityFree := SetCode.ContextProofs.variableJudgment_free Source.context 0 bound
theorem rightReceipt_free : rightReceipt.FunctionExtensionalityFree :=
  SetCode.TypingProofs.reflexivityJudgment_free Source.context Source.domain Source.left bound _ _
    sets_free.pairing.power sets_free.pairing.separation
theorem pairReceipt_free : pairReceipt.FunctionExtensionalityFree :=
  SetCode.SumProofs.pairJudgment_free Source.context Source.left Source.right Source.domain Source.family bound sets _ _
    sets_free leftReceipt_free rightReceipt_free
theorem firstReceipt_free : firstReceipt.FunctionExtensionalityFree :=
  SetCode.SumProofs.firstJudgment_free Source.context Source.pair Source.domain Source.family bound sets pairReceipt sets_free pairReceipt_free
theorem secondReceipt_free : secondReceipt.FunctionExtensionalityFree :=
  SetCode.SumProofs.secondJudgment_free Source.context Source.pair Source.domain Source.family bound sets pairReceipt sets_free pairReceipt_free
theorem firstBetaReceipt_free : firstBetaReceipt.FunctionExtensionalityFree :=
  SetCode.SumProofs.firstBetaJudgment_free Source.context Source.left Source.right Source.domain bound sets.pairing leftReceipt
    sets_free.pairing leftReceipt_free
theorem secondBetaReceipt_free : secondBetaReceipt.FunctionExtensionalityFree :=
  SetCode.SumProofs.secondBetaJudgment_free Source.context Source.left Source.right Source.family bound sets.pairing rightReceipt
    sets_free.pairing rightReceipt_free

noncomputable def heads (name : Nat) : ZFSet.{0} := if name = 2 then ZFSet.powerset (ZFSet.powerset ∅) else ∅
def constants (_ : DeclName) : ZFSet.{0} := ∅
noncomputable abbrev actualModel := SetCode.model heads constants
noncomputable def emptyValuation : actualModel.Valuation [] := fun index => nomatch index
noncomputable def valuation : actualModel.Valuation [object] :=
  actualModel.extend (σ := object) emptyValuation (ZFSet.powerset (∅ : ZFSet.{0}))

theorem basis_valid : Soundness.SatisfiesHyps actualModel valuation basis := by
  have same : basis = (ZFSetTraceProofInterpretation.basis [object]).map
      (HOL.mapConst (SetCode.PrimitiveSymbol.set (Head := Nat))) := rfl
  intro formula present
  rw [same] at present
  obtain ⟨original,admitted,rfl⟩ := List.mem_map.mp present
  rw [SetCode.denote_choiceMap]
  exact ZFSetTraceProofInterpretation.basis_valid.{0} valuation original admitted

theorem receipt_valid {formula : Formula Constants [object]} (received : ProofSyntax Constants basis formula) :
    (actualModel.denote formula valuation).down :=
  Soundness.extDerivation_sound received.erase
    (actualModel.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ _; trivial) basis_valid

theorem actual_pair : (actualModel.denote (SetCode.expand
    (judgmentAt (.typing Source.context Source.pair Source.sumType) bound)) valuation).down := receipt_valid pairReceipt
theorem actual_first : (actualModel.denote (SetCode.expand
    (judgmentAt (.typing Source.context (.fst Source.pair) Source.domain) bound)) valuation).down := receipt_valid firstReceipt
theorem actual_second : (actualModel.denote (SetCode.expand
    (judgmentAt (.typing Source.context (.snd Source.pair) (CTm.inst0 (.fst Source.pair) Source.family)) bound)) valuation).down :=
  receipt_valid secondReceipt
theorem actual_first_beta : (actualModel.denote (SetCode.expand
    (judgmentAt (.equality Source.context (.fst Source.pair) Source.left Source.domain) bound)) valuation).down :=
  receipt_valid firstBetaReceipt
theorem actual_second_beta : (actualModel.denote (SetCode.expand
    (judgmentAt (.equality Source.context (.snd Source.pair) Source.right (CTm.inst0 Source.left Source.family)) bound)) valuation).down :=
  receipt_valid secondBetaReceipt

def wrongStatement : CStatement Nat :=
  .typing Source.context (.snd Source.pair) (CTm.inst0 (.snd Source.pair) Source.family)

theorem context_valid : ((CodedHOL.model heads constants).denote (contextAt Source.context bound) valuation).down := by
  apply (CodedHOL.denote_contextAt heads constants Source.context bound valuation).mpr
  intro index
  have zero : index = 0 := Subsingleton.elim _ _
  subst index
  change ZFSet.powerset (∅ : ZFSet.{0}) ∈ ZFSet.powerset (ZFSet.powerset ∅)
  exact ZFSet.mem_powerset.mpr (fun _ present => present)

theorem wrong_fibre_false : ¬ (actualModel.denote (SetCode.expand (judgmentAt wrongStatement bound)) valuation).down := by
  intro alleged
  have expanded := SetCode.denote_expand heads constants (judgmentAt wrongStatement bound) valuation
  have original := (congrArg ULift.down expanded).mp alleged
  change ((CodedHOL.model heads constants).denote (contextAt Source.context bound) valuation).down →
    ((CodedHOL.model heads constants).denote (statementAt wrongStatement bound) valuation).down at original
  have wrong := (CodedHOL.denote_statementAt heads constants wrongStatement bound valuation).mp (original context_valid)
  change Mettapedia.SetTheory.ZFSetOrderedPair.second (ZFSet.pair (ZFSet.powerset (∅ : ZFSet.{0})) ∅) ∈
    ZFSetTraceProofDecoding.truthCode
      (Mettapedia.SetTheory.ZFSetOrderedPair.second (ZFSet.pair (ZFSet.powerset (∅ : ZFSet.{0})) ∅) = ZFSet.powerset ∅) at wrong
  rw [Mettapedia.SetTheory.ZFSetOrderedPair.second_pair] at wrong
  have impossible := (ZFSetTraceProofDecoding.mem_truthCode _ _).mp wrong
  have present : (∅ : ZFSet.{0}) ∈ ZFSet.powerset ∅ := ZFSet.mem_powerset.mpr (by simp)
  rw [← impossible.2] at present
  exact ZFSet.notMem_empty _ present

theorem no_wrong_fibre : ¬ Nonempty (ProofSyntax Constants basis (SetCode.expand (judgmentAt wrongStatement bound))) := by
  rintro ⟨proof⟩
  exact wrong_fibre_false (receipt_valid proof)

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeSumControls
