import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeSubtypingProofs
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeEqualityControls

/-!
# Source subtyping through a computed domain and a dependent fibre

The source context contains a type A and an element of A. A computed domain
first(pair(A,A)) replaces A, while the fibre compares its index with the
ambient element. The source derivations and their retained target receipts
use the same contexts, expressions and displayed result types.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeSubtypingControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open TowerInterpretation CodedHOL
open SetComprehensionProofs

namespace Source
abbrev church := SetCodeEqualityControls.Source.church
abbrev context := SetCodeEqualityControls.Source.context
abbrev before := SetCodeEqualityControls.Source.before
abbrev after := SetCodeEqualityControls.Source.after
abbrev value := SetCodeEqualityControls.Source.value

theorem domain_included : CBelow church context before after :=
  .subEqual SetCodeEqualityControls.Source.type_equality (by change 0 < 2; decide)
theorem domain_reverse : CBelow church context after before :=
  .subEqual SetCodeEqualityControls.Source.computed_type (by change 0 < 2; decide)
theorem domain_roundtrip : CBelow church context before before := .subTrans domain_included domain_reverse
theorem typed_up : CTyped church context value after := .sub SetCodeEqualityControls.Source.value_typed domain_included
theorem equality_up : CEqual church context value value after := .subEq SetCodeEqualityControls.Source.reflexive domain_included

def fibre : CTm Nat 3 := .id (.var 2) (.var 0) (.var 1)
def beforeSum : CTm Nat 2 := .sigma before fibre
def afterSum : CTm Nat 2 := .sigma after fibre

theorem computed_type {n : Nat} {ctx : CCtx Nat n} {point : CTm Nat n}
    (typed : CTyped church ctx point (.head 2)) : CEqual church ctx (.fst (.pair point point)) point (.head 2) := by
  have formation : CTyped church ctx (.sigma (.head 2) (.head 2)) (.head 3) :=
    .sigmaForm (.headType rfl) (by change 0 < 3; decide) (.headType rfl) (by change 0 < 3; decide) rfl
  exact .betaFst formation (by change 0 < 3; decide) typed typed

theorem after_typed : CTyped church context after (.head 2) := by
  have formation : CTyped church context (.sigma (.head 2) (.head 2)) (.head 3) :=
    .sigmaForm (.headType rfl) (by change 0 < 3; decide) (.headType rfl) (by change 0 < 3; decide) rfl
  exact .fstElim (.pairIntro formation (by change 0 < 3; decide)
    SetCodeEqualityControls.Source.before_typed SetCodeEqualityControls.Source.before_typed)

theorem fibre_before_typed : CTyped church (.snoc context before) fibre (.head 2) :=
  .idForm (.var 2) (by change 0 < 2; decide) (.var 0) (.var 1)
theorem fibre_after_typed : CTyped church (.snoc context after) fibre (.head 2) := by
  have opened : CTyped church (.snoc context after) (.var 0) (.var 2) :=
    .conv (.var 0) (computed_type (.var 2)) (by change 0 < 2; decide)
  exact .idForm (.var 2) (by change 0 < 2; decide) opened (.var 1)

theorem before_sum_typed : CTyped church context beforeSum (.head 2) :=
  .sigmaForm SetCodeEqualityControls.Source.before_typed (by change 0 < 2; decide)
    fibre_before_typed (by change 0 < 2; decide) rfl
theorem after_sum_typed : CTyped church context afterSum (.head 2) :=
  .sigmaForm after_typed (by change 0 < 2; decide) fibre_after_typed (by change 0 < 2; decide) rfl
theorem fibres_included : CBelow church (.snoc context before) fibre fibre :=
  .subEqual (.refl fibre_before_typed) (by change 0 < 2; decide)
theorem sum_included : CBelow church context beforeSum afterSum :=
  .subSigma before_sum_typed (by change 0 < 2; decide) after_sum_typed (by change 0 < 2; decide)
    domain_included fibres_included
end Source

abbrev Constants := SetCodeEqualityControls.Constants
abbrev core : Core Constants := SetCodeEqualityControls.core
abbrev epsilon : ClosedTerm Constants (SelectionProofs.Selection object) := SetCodeEqualityControls.epsilon
abbrev basis : List (Formula Constants [object,object]) := SetCodeEqualityControls.basis
abbrev bound : Fin 2 → Term (CodedHOL.Symbol Nat) [object,object] object := SetCodeEqualityControls.bound
abbrev sets : SetTraceProofs.Laws core epsilon basis := SetCodeEqualityControls.sets

def domainReceipt := SetCode.SubtypingProofs.fromEqualityJudgment Source.context Source.before Source.after (.head 2)
  bound SetCodeEqualityControls.typeReceipt
def reverseReceipt := SetCode.SubtypingProofs.fromEqualityJudgment Source.context Source.after Source.before (.head 2)
  bound SetCodeEqualityControls.typeBetaReceipt
def roundtripReceipt := SetCode.SubtypingProofs.transitivityJudgment Source.context Source.before Source.after Source.before
  bound domainReceipt reverseReceipt
def typedUpReceipt := SetCode.SubtypingProofs.typingJudgment Source.context Source.value Source.before Source.after
  bound SetCodeEqualityControls.valueReceipt domainReceipt
def equalityUpReceipt := SetCode.SubtypingProofs.equalityJudgment Source.context Source.value Source.value Source.before Source.after
  bound SetCodeEqualityControls.reflexiveReceipt domainReceipt

def fibreReceipt : ProofSyntax Constants (weakenHyps (σ := object) basis)
    (SetCode.expand (judgmentAt (.sub (.snoc Source.context Source.before) Source.fibre Source.fibre)
      (AnnotatedCodedReading.lift bound))) :=
  SetCode.SubtypingProofs.closeSub (.snoc Source.context Source.before) Source.fibre Source.fibre (AnnotatedCodedReading.lift bound)
    (SetInclusionProofs.reflexive core _)
def sumReceipt := SetCode.SubtypingProofs.sumJudgment Source.context Source.before Source.after Source.fibre Source.fibre
  bound sets domainReceipt fibreReceipt

theorem domainReceipt_free : domainReceipt.FunctionExtensionalityFree :=
  SetCode.SubtypingProofs.fromEqualityJudgment_free Source.context Source.before Source.after (.head 2) bound
    SetCodeEqualityControls.typeReceipt SetCodeEqualityControls.typeReceipt_free
theorem reverseReceipt_free : reverseReceipt.FunctionExtensionalityFree :=
  SetCode.SubtypingProofs.fromEqualityJudgment_free Source.context Source.after Source.before (.head 2) bound
    SetCodeEqualityControls.typeBetaReceipt SetCodeEqualityControls.typeBetaReceipt_free
theorem roundtripReceipt_free : roundtripReceipt.FunctionExtensionalityFree :=
  SetCode.SubtypingProofs.transitivityJudgment_free Source.context Source.before Source.after Source.before bound
    domainReceipt reverseReceipt domainReceipt_free reverseReceipt_free
theorem typedUpReceipt_free : typedUpReceipt.FunctionExtensionalityFree :=
  SetCode.SubtypingProofs.typingJudgment_free Source.context Source.value Source.before Source.after bound
    SetCodeEqualityControls.valueReceipt domainReceipt SetCodeEqualityControls.valueReceipt_free domainReceipt_free
theorem equalityUpReceipt_free : equalityUpReceipt.FunctionExtensionalityFree :=
  SetCode.SubtypingProofs.equalityJudgment_free Source.context Source.value Source.value Source.before Source.after bound
    SetCodeEqualityControls.reflexiveReceipt domainReceipt SetCodeEqualityControls.reflexiveReceipt_free domainReceipt_free
theorem fibreReceipt_free : fibreReceipt.FunctionExtensionalityFree :=
  SetCode.SubtypingProofs.closeSub_free (.snoc Source.context Source.before) Source.fibre Source.fibre
    (AnnotatedCodedReading.lift bound) _ (SetInclusionProofs.reflexive_free core _)
theorem sumReceipt_free : sumReceipt.FunctionExtensionalityFree :=
  SetCode.SubtypingProofs.sumJudgment_free Source.context Source.before Source.after Source.fibre Source.fibre bound sets
    domainReceipt fibreReceipt SetCodeEqualityControls.sets_free domainReceipt_free fibreReceipt_free

noncomputable abbrev actualModel := SetCodeEqualityControls.actualModel
noncomputable abbrev valuation : actualModel.Valuation [object,object] := SetCodeEqualityControls.valuation
theorem actual_domain : (actualModel.denote (SetCode.expand
    (judgmentAt (.sub Source.context Source.before Source.after) bound)) valuation).down :=
  SetCodeEqualityControls.receipt_valid domainReceipt
theorem actual_roundtrip : (actualModel.denote (SetCode.expand
    (judgmentAt (.sub Source.context Source.before Source.before) bound)) valuation).down :=
  SetCodeEqualityControls.receipt_valid roundtripReceipt
theorem actual_typed_up : (actualModel.denote (SetCode.expand
    (judgmentAt (.typing Source.context Source.value Source.after) bound)) valuation).down :=
  SetCodeEqualityControls.receipt_valid typedUpReceipt
theorem actual_equality_up : (actualModel.denote (SetCode.expand
    (judgmentAt (.equality Source.context Source.value Source.value Source.after) bound)) valuation).down :=
  SetCodeEqualityControls.receipt_valid equalityUpReceipt
theorem actual_sum : (actualModel.denote (SetCode.expand
    (judgmentAt (.sub Source.context Source.beforeSum Source.afterSum) bound)) valuation).down :=
  SetCodeEqualityControls.receipt_valid sumReceipt

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeSubtypingControls
