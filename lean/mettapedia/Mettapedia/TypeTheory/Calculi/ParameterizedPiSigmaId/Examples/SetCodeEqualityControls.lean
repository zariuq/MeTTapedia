import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeEqualityProofs
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeSumControls

/-!
# Explicit source type conversion through pair computation

A context contains a type and one of its elements. Pair computation gives a
different type expression with the same code. The conversion producers carry
both typing and typed equality across that equation. Reflexive equality alone
does not supply the membership part of a typed equality judgment.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeEqualityControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open TowerInterpretation CodedHOL
open SetComprehensionProofs
open HOL.Embedding

namespace Source
abbrev church := SetCodeControls.Source.church
def context : CCtx Nat 2 := .snoc (.snoc .nil (.head 2)) (.var 0)
def value : CTm Nat 2 := .var 0
def before : CTm Nat 2 := .var 1
def after : CTm Nat 2 := .fst (.pair before before)
theorem value_typed : CTyped church context value before := .var 0
theorem before_typed : CTyped church context before (.head 2) := .var 1
theorem computed_type : CDerivable church (.equality context after before (.head 2)) := by
  have formation : CTyped church context (.sigma (.head 2) (.head 2)) (.head 3) :=
    .sigmaForm (.headType rfl) (by change 0 < 3; decide) (.headType rfl) (by change 0 < 3; decide) rfl
  exact .betaFst formation (by change 0 < 3; decide) before_typed before_typed
theorem type_equality : CDerivable church (.equality context before after (.head 2)) := .symm computed_type
theorem type_roundtrip : CDerivable church (.equality context after after (.head 2)) := .trans computed_type type_equality
theorem converted : CTyped church context value after := .conv value_typed type_equality (by change 0 < 2; decide)
theorem reflexive : CDerivable church (.equality context value value before) := .refl value_typed
theorem converted_equality : CDerivable church (.equality context value value after) :=
  .convEq reflexive type_equality (by change 0 < 2; decide)
end Source

abbrev Constants := SetCode.PrimitiveSymbol Nat
abbrev core : Core Constants := SetCode.core
abbrev epsilon : ClosedTerm Constants (SelectionProofs.Selection object) := SetCode.epsilon
abbrev basis : List (Formula Constants [object,object]) := weakenHyps (σ := object) SetCodeSumControls.basis
def sets : SetTraceProofs.Laws core epsilon basis := SetCodeSumControls.sets.weaken object
theorem sets_free : sets.Free := SetCodeSumControls.sets.weaken_free object SetCodeSumControls.sets_free
def bound : Fin 2 → Term (CodedHOL.Symbol Nat) [object,object] object :=
  Fin.cases (.var .vz) (fun _ => .var (.vs .vz))

def valueReceipt := SetCode.ContextProofs.variableJudgment (Δ := basis) Source.context 0 bound
def beforeReceipt := SetCode.ContextProofs.variableJudgment (Δ := basis) Source.context 1 bound
def typeBetaReceipt := SetCode.SumProofs.firstBetaJudgment Source.context Source.before Source.before (.head 2) bound sets.pairing beforeReceipt
def typeReceipt := SetCode.EqualityProofs.symmetryJudgment Source.context Source.after Source.before (.head 2) bound typeBetaReceipt
def roundtripReceipt := SetCode.EqualityProofs.transitivityJudgment Source.context Source.after Source.before Source.after (.head 2)
  bound typeBetaReceipt typeReceipt
def convertedReceipt := SetCode.EqualityProofs.conversionJudgment Source.context Source.value Source.before Source.after (.head 2)
  bound valueReceipt typeReceipt
def reflexiveReceipt := SetCode.EqualityProofs.reflexiveJudgment Source.context Source.value Source.before bound valueReceipt
def convertedEqualityReceipt := SetCode.EqualityProofs.equalityConversionJudgment Source.context Source.value Source.value
  Source.before Source.after (.head 2) bound reflexiveReceipt typeReceipt

theorem valueReceipt_free : valueReceipt.FunctionExtensionalityFree := SetCode.ContextProofs.variableJudgment_free Source.context 0 bound
theorem beforeReceipt_free : beforeReceipt.FunctionExtensionalityFree := SetCode.ContextProofs.variableJudgment_free Source.context 1 bound
theorem typeBetaReceipt_free : typeBetaReceipt.FunctionExtensionalityFree :=
  SetCode.SumProofs.firstBetaJudgment_free Source.context Source.before Source.before (.head 2) bound sets.pairing beforeReceipt
    sets_free.pairing beforeReceipt_free
theorem typeReceipt_free : typeReceipt.FunctionExtensionalityFree :=
  SetCode.EqualityProofs.symmetryJudgment_free Source.context Source.after Source.before (.head 2) bound typeBetaReceipt typeBetaReceipt_free
theorem roundtripReceipt_free : roundtripReceipt.FunctionExtensionalityFree :=
  SetCode.EqualityProofs.transitivityJudgment_free Source.context Source.after Source.before Source.after (.head 2)
    bound typeBetaReceipt typeReceipt typeBetaReceipt_free typeReceipt_free
theorem convertedReceipt_free : convertedReceipt.FunctionExtensionalityFree :=
  SetCode.EqualityProofs.conversionJudgment_free Source.context Source.value Source.before Source.after (.head 2)
    bound valueReceipt typeReceipt valueReceipt_free typeReceipt_free
theorem reflexiveReceipt_free : reflexiveReceipt.FunctionExtensionalityFree :=
  SetCode.EqualityProofs.reflexiveJudgment_free Source.context Source.value Source.before bound valueReceipt valueReceipt_free
theorem convertedEqualityReceipt_free : convertedEqualityReceipt.FunctionExtensionalityFree :=
  SetCode.EqualityProofs.equalityConversionJudgment_free Source.context Source.value Source.value Source.before Source.after (.head 2)
    bound reflexiveReceipt typeReceipt reflexiveReceipt_free typeReceipt_free

noncomputable abbrev actualModel := SetCodeSumControls.actualModel
noncomputable def valuation : actualModel.Valuation [object,object] :=
  actualModel.extend (σ := object) SetCodeSumControls.valuation (∅ : ZFSet.{0})

theorem basis_valid : Soundness.SatisfiesHyps actualModel valuation basis := by
  have same : basis = (ZFSetTraceProofInterpretation.basis [object,object]).map
      (HOL.mapConst (SetCode.PrimitiveSymbol.set (Head := Nat))) := rfl
  intro formula present
  rw [same] at present
  obtain ⟨original,admitted,rfl⟩ := List.mem_map.mp present
  rw [SetCode.denote_choiceMap]
  exact ZFSetTraceProofInterpretation.basis_valid.{0} valuation original admitted

theorem receipt_valid {formula : Formula Constants [object,object]} (received : ProofSyntax Constants basis formula) :
    (actualModel.denote formula valuation).down :=
  Soundness.extDerivation_sound received.erase
    (actualModel.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ _; trivial) basis_valid

theorem actual_symmetry : (actualModel.denote (SetCode.expand
    (judgmentAt (.equality Source.context Source.before Source.after (.head 2)) bound)) valuation).down := receipt_valid typeReceipt
theorem actual_transitivity : (actualModel.denote (SetCode.expand
    (judgmentAt (.equality Source.context Source.after Source.after (.head 2)) bound)) valuation).down := receipt_valid roundtripReceipt
theorem actual_conversion : (actualModel.denote (SetCode.expand
    (judgmentAt (.typing Source.context Source.value Source.after) bound)) valuation).down := receipt_valid convertedReceipt
theorem actual_reflexivity : (actualModel.denote (SetCode.expand
    (judgmentAt (.equality Source.context Source.value Source.value Source.before) bound)) valuation).down := receipt_valid reflexiveReceipt
theorem actual_equality_conversion : (actualModel.denote (SetCode.expand
    (judgmentAt (.equality Source.context Source.value Source.value Source.after) bound)) valuation).down := receipt_valid convertedEqualityReceipt

def wrongStatement : CStatement Nat := .equality Source.context Source.value Source.value (.head 0)

theorem context_valid : ((CodedHOL.model SetCodeSumControls.heads SetCodeSumControls.constants).denote
    (contextAt Source.context bound) valuation).down := by
  apply (CodedHOL.denote_contextAt SetCodeSumControls.heads SetCodeSumControls.constants Source.context bound valuation).mpr
  intro index
  refine Fin.cases ?_ (fun older => ?_) index
  · change (∅ : ZFSet.{0}) ∈ ZFSet.powerset ∅
    exact ZFSet.mem_powerset.mpr (by simp)
  · have zero : older = 0 := Subsingleton.elim _ _
    subst older
    change ZFSet.powerset (∅ : ZFSet.{0}) ∈ ZFSet.powerset (ZFSet.powerset ∅)
    exact ZFSet.mem_powerset.mpr (fun _ present => present)

theorem equation_without_membership :
    (actualModel.denote (.eq (SetCode.AbstractionProofs.code Source.value bound)
      (SetCode.AbstractionProofs.code Source.value bound)) valuation).down := rfl

theorem missing_membership_false : ¬ (actualModel.denote (SetCode.expand (judgmentAt wrongStatement bound)) valuation).down := by
  intro alleged
  have expanded := SetCode.denote_expand SetCodeSumControls.heads SetCodeSumControls.constants (judgmentAt wrongStatement bound) valuation
  have original := (congrArg ULift.down expanded).mp alleged
  change ((CodedHOL.model SetCodeSumControls.heads SetCodeSumControls.constants).denote (contextAt Source.context bound) valuation).down →
    ((CodedHOL.model SetCodeSumControls.heads SetCodeSumControls.constants).denote (statementAt wrongStatement bound) valuation).down at original
  have wrong := (CodedHOL.denote_statementAt SetCodeSumControls.heads SetCodeSumControls.constants wrongStatement bound valuation).mp
    (original context_valid)
  exact ZFSet.notMem_empty (∅ : ZFSet.{0}) wrong.2

theorem no_missing_membership : ¬ Nonempty (ProofSyntax Constants basis (SetCode.expand (judgmentAt wrongStatement bound))) := by
  rintro ⟨proof⟩
  exact missing_membership_false (receipt_valid proof)

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeEqualityControls
