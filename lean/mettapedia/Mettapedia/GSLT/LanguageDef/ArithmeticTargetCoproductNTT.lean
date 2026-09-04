import Mettapedia.GSLT.LanguageDef.ArithmeticTargetCoproduct
import Mettapedia.GSLT.LanguageDef.StructuralCoproductOperational
import Mettapedia.GSLT.LanguageDef.RadixDigitNTT
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory

/-!
# Operational and native-type gates for the arithmetic target coproduct

The combined arithmetic target is exercised through the premise-aware
contextual engine, not only through its combinedLanguage rows.  A single explicit
relation environment supplies inhabited ExternalCallMachine and
RadixDigitMachine transitions.  Exact component-versus-coproduct fibres and
the generated spatial/modal structure are checked on both sides.
-/

namespace Mettapedia.GSLT.LanguageDef.ArithmeticTargetCoproductNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralCoproduct
open Mettapedia.GSLT.LanguageDef.ArithmeticTargetCoproduct
open Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics
open Mettapedia.GSLT.LanguageDef.StructuralCoproductOperational

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

private def externalNatZero : Pattern := a "external-call:nat-zero"
private def externalLabelZero : Pattern :=
  a "external-call:label" [externalNatZero]
private def externalFuelZero : Pattern := a "external-call:fuel-zero"
private def externalFuelOne : Pattern :=
  a "external-call:fuel-succ" [externalFuelZero]
private def externalReceiptNil : Pattern := a "external-call:receipt-nil"
private def externalStoreNil : Pattern := a "external-call:store-nil"
private def externalReturnDeclined : Pattern :=
  a "external-call:return-declined"
private def externalInstructionNil : Pattern :=
  a "external-call:instruction-nil"
private def externalNil : Pattern := a "external-call:external-nil"
private def externalProgram : Pattern :=
  a "external-call:program"
    [a "external-call:instruction-cons"
      [externalReturnDeclined, externalInstructionNil],
     externalNil, externalLabelZero]
private def externalStepLimitFault : Pattern :=
  a "external-call:fault" [a "external-call:step-limit"]
private def externalStart : Pattern :=
  ExternalCallMachine.run externalProgram externalLabelZero externalStoreNil
    externalFuelOne externalReceiptNil
private def externalDone : Pattern :=
  ExternalCallMachine.halted (a "external-call:outcome-declined")
    (ExternalCallMachine.stepReceipt externalLabelZero externalReceiptNil)

private def radixProgram : Pattern := a "radix-digit:demo-program"
private def radixPcZero : Pattern := a "radix-digit:demo-pc-zero"
private def radixPcOne : Pattern := a "radix-digit:demo-pc-one"
private def radixBuffers : Pattern := a "radix-digit:demo-buffers"
private def radixRegisters : Pattern := a "radix-digit:demo-registers"
private def radixFuelZero : Pattern := a "radix-digit:demo-fuel-zero"
private def radixFuelOne : Pattern := a "radix-digit:demo-fuel-one"
private def radixReceiptNil : Pattern := a "radix-digit:demo-receipt-nil"
private def radixInstruction : Pattern :=
  a "radix-digit:jump" [radixPcOne]
private def radixReceiptAfter : Pattern :=
  a "radix-digit:receipt-cons"
    [a "radix-digit:execute-event" [radixPcZero], radixReceiptNil]
private def radixPrimitiveResult : Pattern :=
  a "radix-digit:result-next"
    [radixBuffers, radixRegisters, radixPcOne, radixReceiptAfter]
private def radixStart : Pattern :=
  RadixDigitLanguageDef.run radixProgram radixPcZero radixBuffers
    radixRegisters radixFuelOne radixReceiptNil
private def radixNext : Pattern :=
  RadixDigitLanguageDef.run radixProgram radixPcOne radixBuffers
    radixRegisters radixFuelZero radixReceiptAfter

private def mapExternalRows (rows : List (List Pattern)) : List (List Pattern) :=
  rows.map (List.map (mapPattern externalSymbols))

private def mapRadixRows (rows : List (List Pattern)) : List (List Pattern) :=
  rows.map (List.map (mapPattern radixSymbols))

/-- One explicit primitive-relation catalog for the composed operational
theory.  Relation tags select the owning component; returned tuples inhabit
that component's tagged pattern image. -/
def combinedDemoRelationEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == externalSymbols.relation "ExternalCallConsumeFuel" then
      mapExternalRows [[externalFuelOne, externalFuelZero]]
    else if relation ==
        externalSymbols.relation "ExternalCallFetchInstruction" then
      mapExternalRows
        [[externalProgram, externalLabelZero, externalReturnDeclined]]
    else if relation ==
        externalSymbols.relation "ExternalCallStepLimitFault" then
      mapExternalRows [[externalStepLimitFault]]
    else if relation == radixSymbols.relation "RadixDigitConsumeFuel" then
      mapRadixRows [[radixFuelOne, radixFuelZero]]
    else if relation == radixSymbols.relation "RadixDigitFetch" then
      mapRadixRows [[radixProgram, radixPcZero, radixInstruction]]
    else if relation ==
        radixSymbols.relation "RadixDigitExecuteInstruction" then
      mapRadixRows
        [[radixInstruction, radixBuffers, radixRegisters,
          radixReceiptAfter, radixPrimitiveResult]]
    else
      []

private noncomputable def externalInverseSymbols : LanguageDefSymbolMap where
  sort := Function.invFun externalSymbols.sort
  constructor := Function.invFun externalSymbols.constructor
  relation := Function.invFun externalSymbols.relation
  equation := Function.invFun externalSymbols.equation
  rewrite := Function.invFun externalSymbols.rewrite

private noncomputable def radixInverseSymbols : LanguageDefSymbolMap where
  sort := Function.invFun radixSymbols.sort
  constructor := Function.invFun radixSymbols.constructor
  relation := Function.invFun radixSymbols.relation
  equation := Function.invFun radixSymbols.equation
  rewrite := Function.invFun radixSymbols.rewrite

private theorem external_inverse_comp :
    externalSymbols.comp externalInverseSymbols = LanguageDefSymbolMap.id := by
  apply LanguageDefSymbolMap.ext
  · funext name
    exact Function.leftInverse_invFun
      compatibility.leftSymbolsInjective.sort name
  · funext name
    exact Function.leftInverse_invFun
      compatibility.leftSymbolsInjective.constructor name
  · funext name
    exact Function.leftInverse_invFun
      compatibility.leftSymbolsInjective.relation name
  · funext name
    exact Function.leftInverse_invFun
      compatibility.leftSymbolsInjective.equation name
  · funext name
    exact Function.leftInverse_invFun
      compatibility.leftSymbolsInjective.rewrite name

private theorem radix_inverse_comp :
    radixSymbols.comp radixInverseSymbols = LanguageDefSymbolMap.id := by
  apply LanguageDefSymbolMap.ext
  · funext name
    exact Function.leftInverse_invFun
      compatibility.rightSymbolsInjective.sort name
  · funext name
    exact Function.leftInverse_invFun
      compatibility.rightSymbolsInjective.constructor name
  · funext name
    exact Function.leftInverse_invFun
      compatibility.rightSymbolsInjective.relation name
  · funext name
    exact Function.leftInverse_invFun
      compatibility.rightSymbolsInjective.equation name
  · funext name
    exact Function.leftInverse_invFun
      compatibility.rightSymbolsInjective.rewrite name

@[simp] private theorem external_inverse_pattern (pattern : Pattern) :
    mapPattern externalInverseSymbols (mapPattern externalSymbols pattern) =
      pattern := by
  rw [← mapPattern_comp, external_inverse_comp, mapPattern_id]

@[simp] private theorem radix_inverse_pattern (pattern : Pattern) :
    mapPattern radixInverseSymbols (mapPattern radixSymbols pattern) = pattern := by
  rw [← mapPattern_comp, radix_inverse_comp, mapPattern_id]

@[simp] private theorem external_inverse_bindings (bindings : Bindings) :
    mapBindings externalInverseSymbols (mapBindings externalSymbols bindings) =
      bindings := by
  induction bindings with
  | nil => rfl
  | cons entry bindings inductionHypothesis =>
      rcases entry with ⟨name, value⟩
      change
        (name, mapPattern externalInverseSymbols
          (mapPattern externalSymbols value)) ::
            mapBindings externalInverseSymbols
              (mapBindings externalSymbols bindings) =
          (name, value) :: bindings
      rw [external_inverse_pattern, inductionHypothesis]

@[simp] private theorem radix_inverse_bindings (bindings : Bindings) :
    mapBindings radixInverseSymbols (mapBindings radixSymbols bindings) =
      bindings := by
  induction bindings with
  | nil => rfl
  | cons entry bindings inductionHypothesis =>
      rcases entry with ⟨name, value⟩
      change
        (name, mapPattern radixInverseSymbols
          (mapPattern radixSymbols value)) ::
            mapBindings radixInverseSymbols
              (mapBindings radixSymbols bindings) =
          (name, value) :: bindings
      rw [radix_inverse_pattern, inductionHypothesis]

@[simp] private theorem external_inverse_patterns (patterns : List Pattern) :
    patterns.map
        (mapPattern externalInverseSymbols ∘ mapPattern externalSymbols) =
      patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [Function.comp_apply, inductionHypothesis]

@[simp] private theorem radix_inverse_patterns (patterns : List Pattern) :
    patterns.map (mapPattern radixInverseSymbols ∘ mapPattern radixSymbols) =
      patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [Function.comp_apply, inductionHypothesis]

@[simp] private theorem external_inverse_premise (premise : Premise) :
    mapPremise externalInverseSymbols (mapPremise externalSymbols premise) =
      premise := by
  rw [← mapPremise_comp, external_inverse_comp, mapPremise_id]

@[simp] private theorem radix_inverse_premise (premise : Premise) :
    mapPremise radixInverseSymbols (mapPremise radixSymbols premise) = premise := by
  rw [← mapPremise_comp, radix_inverse_comp, mapPremise_id]

@[simp] private theorem external_inverse_relation (relation : String) :
    externalInverseSymbols.relation (externalSymbols.relation relation) =
      relation :=
  Function.leftInverse_invFun
    compatibility.leftSymbolsInjective.relation relation

@[simp] private theorem radix_inverse_relation (relation : String) :
    radixInverseSymbols.relation (radixSymbols.relation relation) = relation :=
  Function.leftInverse_invFun
    compatibility.rightSymbolsInjective.relation relation

/-- One premise evaluator for the combined operational theory.  Tagged
relation symbols dispatch to their owning source evaluator; results return in
the same tagged pattern image.  Other premise forms are rejected here because
neither component authors them. -/
noncomputable def combinedOperationalBase : BasePremiseEvaluator :=
  fun _target bindings premise =>
    match premise with
    | .relationQuery relation _arguments =>
        if relation.startsWith "E:" then
          (engineBasePremises ExternalCallMachine.externalCallDemoRelationEnv
            ExternalCallMachine.externalCallLanguage
            (mapBindings externalInverseSymbols bindings)
            (mapPremise externalInverseSymbols premise)).map
              (mapBindings externalSymbols)
        else if relation.startsWith "R:" then
          (engineBasePremises RadixDigitNTT.demoRelationEnv
            RadixDigitLanguageDef.language
            (mapBindings radixInverseSymbols bindings)
            (mapPremise radixInverseSymbols premise)).map
              (mapBindings radixSymbols)
        else
          []
    | _ => []

private theorem external_relation_commutes
    (relation : String) (arguments : List Pattern)
    (tagged : (externalSymbols.relation relation).startsWith "E:" = true) :
    PremiseEvaluatorCommutesAt externalSymbols
      ExternalCallMachine.externalCallLanguage validatedCombinedLanguage.language
      (engineBasePremises ExternalCallMachine.externalCallDemoRelationEnv)
      combinedOperationalBase (.relationQuery relation arguments) := by
  intro bindings
  simp only [combinedOperationalBase, mapPremise]
  rw [if_pos tagged]
  rw [external_inverse_bindings]
  simp only [external_inverse_relation, List.map_map,
    external_inverse_patterns]

private theorem radix_relation_commutes
    (relation : String) (arguments : List Pattern)
    (tagged : (radixSymbols.relation relation).startsWith "R:" = true) :
    PremiseEvaluatorCommutesAt radixSymbols RadixDigitLanguageDef.language
      validatedCombinedLanguage.language (engineBasePremises RadixDigitNTT.demoRelationEnv)
      combinedOperationalBase (.relationQuery relation arguments) := by
  intro bindings
  simp only [combinedOperationalBase, mapPremise]
  have externalFalse :
      (radixSymbols.relation relation).startsWith "E:" = false := by
    change ("R:" ++ relation).startsWith "E:" = false
    simp
  rw [if_neg (by exact Bool.eq_false_iff.mp externalFalse), if_pos tagged]
  rw [radix_inverse_bindings]
  simp only [radix_inverse_relation, List.map_map, radix_inverse_patterns]

private theorem external_relation_tagged (relation : String) :
    (externalSymbols.relation relation).startsWith "E:" = true := by
  change ("E:" ++ relation).startsWith "E:" = true
  simp

private theorem radix_relation_tagged (relation : String) :
    (radixSymbols.relation relation).startsWith "R:" = true := by
  change ("R:" ++ relation).startsWith "R:" = true
  simp

/-- Every primitive premise authored by ExternalCallMachine commutes with the
single combined evaluator. -/
theorem external_rule_premises_commute :
    RulePremiseEvaluatorsCommute externalSymbols
      ExternalCallMachine.externalCallLanguage validatedCombinedLanguage.language
      (engineBasePremises ExternalCallMachine.externalCallDemoRelationEnv)
      combinedOperationalBase := by
  intro rule ruleMembership premise premiseMembership
  have relationForm : ∃ relation arguments,
      premise = .relationQuery relation arguments := by
    change rule ∈ ExternalCallMachine.externalCallLanguageTransitions at ruleMembership
    simp only [ExternalCallMachine.externalCallLanguageTransitions,
      List.mem_cons, List.mem_nil_iff, or_false] at ruleMembership
    rcases ruleMembership with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [ExternalCallMachine.fuelExhaustedRule,
        ExternalCallMachine.branchZeroTransition,
        ExternalCallMachine.branchNonzeroTransition,
        ExternalCallMachine.callValueTransition,
        ExternalCallMachine.callLanguageFaultTransition,
        ExternalCallMachine.callEngineFaultTransition,
        ExternalCallMachine.callResourceFaultTransition,
        ExternalCallMachine.returnValueTransition,
        ExternalCallMachine.returnDeclinedTransition,
        ExternalCallMachine.returnLanguageFaultTransition,
        ExternalCallMachine.returnEngineFaultTransition,
        ExternalCallMachine.returnResourceFaultTransition,
        ExternalCallMachine.branchRule, ExternalCallMachine.callRule,
        ExternalCallMachine.returnFaultRule,
        ExternalCallMachine.consumeFuel, ExternalCallMachine.fetch,
        ExternalCallMachine.query, List.mem_cons, List.mem_nil_iff,
        or_false] at premiseMembership
    all_goals aesop
  obtain ⟨relation, arguments, rfl⟩ := relationForm
  exact external_relation_commutes relation arguments
    (external_relation_tagged relation)

/-- Every primitive premise authored by RadixDigitMachine commutes with the
same combined evaluator. -/
theorem radix_rule_premises_commute :
    RulePremiseEvaluatorsCommute radixSymbols RadixDigitLanguageDef.language
      validatedCombinedLanguage.language (engineBasePremises RadixDigitNTT.demoRelationEnv)
      combinedOperationalBase := by
  intro rule ruleMembership premise premiseMembership
  have relationForm : ∃ relation arguments,
      premise = .relationQuery relation arguments := by
    change rule ∈ RadixDigitLanguageDef.transitions at ruleMembership
    simp only [RadixDigitLanguageDef.transitions, List.mem_cons,
      List.mem_nil_iff, or_false] at ruleMembership
    rcases ruleMembership with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [RadixDigitLanguageDef.fuelExhaustedTransition,
        RadixDigitLanguageDef.missingProgramCounterTransition,
        RadixDigitLanguageDef.nextTransition,
        RadixDigitLanguageDef.valueTransition,
        RadixDigitLanguageDef.languageFaultTransition,
        RadixDigitLanguageDef.engineFaultTransition,
        RadixDigitLanguageDef.resourceFaultTransition,
        RadixDigitLanguageDef.faultTransition,
        RadixDigitLanguageDef.fetchedPremises,
        RadixDigitLanguageDef.query, List.mem_cons, List.mem_nil_iff,
        or_false] at premiseMembership
    all_goals aesop
  obtain ⟨relation, arguments, rfl⟩ := relationForm
  exact radix_relation_commutes relation arguments
    (radix_relation_tagged relation)

/-- Universal premise-aware contextual conservativity of ExternalCallMachine
inside the composed operational theory. -/
theorem external_contextual_exact (fuel : Nat) (term : Pattern) :
    rewriteAt combinedOperationalBase validatedCombinedLanguage.language fuel
        (mapPattern externalSymbols term) =
      (rewriteAt
        (engineBasePremises ExternalCallMachine.externalCallDemoRelationEnv)
        ExternalCallMachine.externalCallLanguage fuel term).map
          (mapPattern externalSymbols) :=
  StructuralCoproductOperational.Compatibility.left_rewriteAt_exact_onRules
    compatibility
    (engineBasePremises ExternalCallMachine.externalCallDemoRelationEnv)
    combinedOperationalBase external_rule_premises_commute fuel term

/-- Universal premise-aware contextual conservativity of RadixDigitMachine
inside the same composed operational theory. -/
theorem radix_contextual_exact (fuel : Nat) (term : Pattern) :
    rewriteAt combinedOperationalBase validatedCombinedLanguage.language fuel
        (mapPattern radixSymbols term) =
      (rewriteAt (engineBasePremises RadixDigitNTT.demoRelationEnv)
        RadixDigitLanguageDef.language fuel term).map
          (mapPattern radixSymbols) :=
  StructuralCoproductOperational.Compatibility.right_rewriteAt_exact_onRules
    compatibility (engineBasePremises RadixDigitNTT.demoRelationEnv)
    combinedOperationalBase radix_rule_premises_commute fuel term

/-- Inhabited ExternalCall witness obtained through the universal operational
coproduct theorem, including the exact ordered receipt. -/
theorem external_operational_step_exact :
    rewriteAt combinedOperationalBase validatedCombinedLanguage.language 1
        (mapPattern externalSymbols externalStart) =
      [mapPattern externalSymbols externalDone] := by
  rw [external_contextual_exact]
  exact congrArg (List.map (mapPattern externalSymbols))
    ExternalCallMachine.decline_step_exact

/-- Inhabited RadixDigit witness obtained through the universal operational
coproduct theorem, including the exact ordered receipt. -/
theorem radix_operational_step_exact :
    rewriteAt combinedOperationalBase validatedCombinedLanguage.language 1
        (mapPattern radixSymbols radixStart) =
      [mapPattern radixSymbols radixNext] := by
  rw [radix_contextual_exact]
  exact congrArg (List.map (mapPattern radixSymbols))
    RadixDigitNTT.jump_step_exact

/-- The ExternalCall component has the same exact, ordered operational fibre
inside the composed language under the combined primitive catalog. -/
theorem external_contextual_fibre_exact :
    rewriteAt (engineBasePremises combinedDemoRelationEnv)
        validatedCombinedLanguage.language 1 (mapPattern externalSymbols externalStart) =
      (rewriteAt
        (engineBasePremises ExternalCallMachine.externalCallDemoRelationEnv)
        ExternalCallMachine.externalCallLanguage 1 externalStart).map
          (mapPattern externalSymbols) := by
  decide +kernel

/-- The concrete ExternalCall fibre is inhabited and preserves its receipt. -/
theorem external_contextual_step_exact :
    rewriteAt (engineBasePremises combinedDemoRelationEnv)
        validatedCombinedLanguage.language 1 (mapPattern externalSymbols externalStart) =
      [mapPattern externalSymbols externalDone] := by
  decide +kernel

/-- The RadixDigit component has the same exact, ordered operational fibre
inside the composed language under the combined primitive catalog. -/
theorem radix_contextual_fibre_exact :
    rewriteAt (engineBasePremises combinedDemoRelationEnv)
        validatedCombinedLanguage.language 1 (mapPattern radixSymbols radixStart) =
      (rewriteAt
        (engineBasePremises RadixDigitNTT.demoRelationEnv)
        RadixDigitLanguageDef.language 1 radixStart).map
          (mapPattern radixSymbols) := by
  decide +kernel

/-- The concrete RadixDigit fibre is inhabited and preserves its receipt. -/
theorem radix_contextual_step_exact :
    rewriteAt (engineBasePremises combinedDemoRelationEnv)
        validatedCombinedLanguage.language 1 (mapPattern radixSymbols radixStart) =
      [mapPattern radixSymbols radixNext] := by
  decide +kernel

/-- A terminal ExternalCall configuration cannot gain a RadixDigit step in
the coproduct. -/
theorem external_terminal_remains_normal :
    rewriteAt (engineBasePremises combinedDemoRelationEnv)
        validatedCombinedLanguage.language 1 (mapPattern externalSymbols externalDone) = [] := by
  decide +kernel

/-- OSLF synthesized for the ExternalCall configuration fibre of the composed
language. -/
def externalOSLF :=
  langOSLFUsing combinedDemoRelationEnv validatedCombinedLanguage.language
    (externalSymbols.sort "Config")

/-- OSLF synthesized for the RadixDigit configuration fibre of the composed
language. -/
def radixOSLF :=
  langOSLFUsing combinedDemoRelationEnv validatedCombinedLanguage.language
    (radixSymbols.sort "Config")

theorem external_galois :
    GaloisConnection
      (langDiamondUsing combinedDemoRelationEnv validatedCombinedLanguage.language)
      (langBoxUsing combinedDemoRelationEnv validatedCombinedLanguage.language) :=
  langGaloisUsing combinedDemoRelationEnv validatedCombinedLanguage.language

theorem radix_galois :
    GaloisConnection
      (langDiamondUsing combinedDemoRelationEnv validatedCombinedLanguage.language)
      (langBoxUsing combinedDemoRelationEnv validatedCombinedLanguage.language) :=
  langGaloisUsing combinedDemoRelationEnv validatedCombinedLanguage.language

/-- The generated native spatial structure retains the ExternalCall integer
carrier crossing. -/
theorem external_integer_crossing :
    (externalSymbols.constructor "external-call:exact-integer",
      externalSymbols.sort "Integer", externalSymbols.sort "Value") ∈
        unaryCrossings validatedCombinedLanguage.language := by
  decide +kernel

/-- The generated native spatial structure retains the RadixDigit jump
constructor crossing. -/
theorem radix_jump_crossing :
    (radixSymbols.constructor "radix-digit:jump", radixSymbols.sort "Nat",
      radixSymbols.sort "Instruction") ∈ unaryCrossings validatedCombinedLanguage.language := by
  decide +kernel

/-- Negative native-type control: component tagging cannot invent a crossing
from ExternalCall stores directly to RadixDigit outcomes. -/
theorem no_cross_component_store_outcome :
    (externalSymbols.constructor "external-call:invented-store-outcome",
      externalSymbols.sort "Store", radixSymbols.sort "Outcome") ∉
        unaryCrossings validatedCombinedLanguage.language := by
  decide +kernel

#print axioms external_contextual_fibre_exact
#print axioms radix_contextual_fibre_exact
#print axioms external_rule_premises_commute
#print axioms radix_rule_premises_commute
#print axioms external_contextual_exact
#print axioms radix_contextual_exact
#print axioms external_operational_step_exact
#print axioms radix_operational_step_exact
#print axioms external_contextual_step_exact
#print axioms radix_contextual_step_exact
#print axioms external_galois
#print axioms external_integer_crossing
#print axioms no_cross_component_store_outcome

end Mettapedia.GSLT.LanguageDef.ArithmeticTargetCoproductNTT
