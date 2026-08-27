import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# External-call operational GSLT and native-type diagnostics

This is the theorem-side presentation of a guarded external-call machine. Its
machine configurations, five completion classes, ordered receipt events, fuel
boundary, and external-call boundary are authored independently of any C
structure, interpreter, emitter, compiler, or linked library.
-/

namespace Mettapedia.GSLT.LanguageDef.ExternalCallMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory

def ctor (label category : String)
    (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := policy
}

def typed (entries : List (String × String)) :
    List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

def v (name : String) : Pattern := .fvar name
def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments
def query (relation : String) (arguments : List Pattern) : Premise :=
  .relationQuery relation arguments

def run (program pc store fuel receipt : Pattern) : Pattern :=
  a "external-call:run" [program, pc, store, fuel, receipt]

def halted (outcome receipt : Pattern) : Pattern :=
  a "external-call:halted" [outcome, receipt]

def stepReceipt (pc receipt : Pattern) : Pattern :=
  a "external-call:receipt-cons" [a "external-call:step-event" [pc], receipt]

def externalReceipt (external outcome pc receipt : Pattern) : Pattern :=
  a "external-call:receipt-cons"
    [a "external-call:external-event" [external, outcome], stepReceipt pc receipt]

def commonContext : List (String × TypeExpr) :=
  typed [
    ("program", "Program"), ("pc", "Label"), ("store", "Store"),
    ("fuel", "Fuel"), ("nextFuel", "Fuel"), ("receipt", "Receipt")]

def consumeFuel : Premise :=
  query "ExternalCallConsumeFuel" [v "fuel", v "nextFuel"]

def fetch (instruction : Pattern) : Premise :=
  query "ExternalCallFetchInstruction" [v "program", v "pc", instruction]

def branchRule (name test target : String) : RewriteRule := {
  name := name
  typeContext := commonContext ++ typed [
    ("slot", "SlotId"), ("value", "Value"),
    ("ifZero", "Label"), ("ifNonzero", "Label")]
  premises := [
    consumeFuel,
    fetch (a "external-call:branch-zero" [v "slot", v "ifZero", v "ifNonzero"]),
    query "ExternalCallReadSlot" [v "store", v "slot", v "value"],
    query test [v "value"]]
  left := run (v "program") (v "pc") (v "store") (v "fuel") (v "receipt")
  right := run (v "program") (v target) (v "store") (v "nextFuel")
    (stepReceipt (v "pc") (v "receipt"))
}

def callRule (name target : String) (valueCase : Bool)
    (externalOutcome storeAfter : Pattern) : RewriteRule := {
  name := name
  typeContext :=
    if valueCase then
      typed [
        ("program", "Program"), ("pc", "Label"), ("store", "Store"),
        ("nextStore", "Store"), ("fuel", "Fuel"),
        ("nextFuel", "Fuel"), ("receipt", "Receipt"),
        ("external", "ExternalId"), ("ifValue", "Label"),
        ("ifLanguageFault", "Label"), ("ifEngineFault", "Label"),
        ("ifResourceFault", "Label")]
    else
      commonContext ++ typed [
        ("external", "ExternalId"), ("fault", "Fault"),
        ("ifValue", "Label"), ("ifLanguageFault", "Label"),
        ("ifEngineFault", "Label"), ("ifResourceFault", "Label")]
  premises := [
    consumeFuel,
    fetch (a "external-call:call-binary"
      [v "external", v "ifValue", v "ifLanguageFault",
       v "ifEngineFault", v "ifResourceFault"]),
    query "ExternalCallCallBinaryExternal"
      [v "program", v "external", v "store", externalOutcome]]
  left := run (v "program") (v "pc") (v "store") (v "fuel") (v "receipt")
  right := run (v "program") (v target) storeAfter (v "nextFuel")
    (externalReceipt (v "external") externalOutcome (v "pc") (v "receipt"))
}

def returnFaultRule (name instruction outcome : String) : RewriteRule := {
  name := name
  typeContext := commonContext ++ typed [("fault", "Fault")]
  premises := [consumeFuel, fetch (a instruction [v "fault"])]
  left := run (v "program") (v "pc") (v "store") (v "fuel") (v "receipt")
  right := halted (a outcome [v "fault"])
    (stepReceipt (v "pc") (v "receipt"))
}

/-! ## Named authored transitions

Each operational edge has a stable theorem-side identity.  Besides making
the presentation easier to inspect, these names let compiler proofs select
one authored edge without unfolding and re-evaluating the whole rule list.
Their order below remains the canonical operational order.
-/

def fuelExhaustedRule : RewriteRule := {
  name := "external-call:fuel-exhausted"
  typeContext := typed [
    ("program", "Program"), ("pc", "Label"), ("store", "Store"),
    ("receipt", "Receipt"), ("fault", "Fault")]
  premises := [query "ExternalCallStepLimitFault" [v "fault"]]
  left := run (v "program") (v "pc") (v "store")
    (a "external-call:fuel-zero") (v "receipt")
  right := halted (a "external-call:outcome-resource-fault" [v "fault"])
    (a "external-call:receipt-cons"
      [a "external-call:fuel-exhausted-event" [v "pc"], v "receipt"])
}

def branchZeroTransition : RewriteRule :=
  branchRule "external-call:branch-zero" "ExternalCallIsZero" "ifZero"

def branchNonzeroTransition : RewriteRule :=
  branchRule "external-call:branch-nonzero" "ExternalCallIsNonzero" "ifNonzero"

def callValueTransition : RewriteRule :=
  callRule "external-call:call-value" "ifValue" true
    (a "external-call:external-value" [v "nextStore"]) (v "nextStore")

def callLanguageFaultTransition : RewriteRule :=
  callRule "external-call:call-language-fault" "ifLanguageFault" false
    (a "external-call:external-language-fault" [v "fault"]) (v "store")

def callEngineFaultTransition : RewriteRule :=
  callRule "external-call:call-engine-fault" "ifEngineFault" false
    (a "external-call:external-engine-fault" [v "fault"]) (v "store")

def callResourceFaultTransition : RewriteRule :=
  callRule "external-call:call-resource-fault" "ifResourceFault" false
    (a "external-call:external-resource-fault" [v "fault"]) (v "store")

def returnValueTransition : RewriteRule := {
  name := "external-call:return-value"
  typeContext := commonContext ++ typed [
    ("slot", "SlotId"), ("value", "Value")]
  premises := [
    consumeFuel, fetch (a "external-call:return-value" [v "slot"]),
    query "ExternalCallReadSlot" [v "store", v "slot", v "value"]]
  left := run (v "program") (v "pc") (v "store") (v "fuel") (v "receipt")
  right := halted (a "external-call:outcome-value" [v "value"])
    (stepReceipt (v "pc") (v "receipt"))
}

def returnDeclinedTransition : RewriteRule := {
  name := "external-call:return-declined"
  typeContext := commonContext
  premises := [consumeFuel, fetch (a "external-call:return-declined")]
  left := run (v "program") (v "pc") (v "store") (v "fuel") (v "receipt")
  right := halted (a "external-call:outcome-declined")
    (stepReceipt (v "pc") (v "receipt"))
}

def returnLanguageFaultTransition : RewriteRule :=
  returnFaultRule "external-call:return-language-fault"
    "external-call:return-language-fault" "external-call:outcome-language-fault"

def returnEngineFaultTransition : RewriteRule :=
  returnFaultRule "external-call:return-engine-fault"
    "external-call:return-engine-fault" "external-call:outcome-engine-fault"

def returnResourceFaultTransition : RewriteRule :=
  returnFaultRule "external-call:return-resource-fault"
    "external-call:return-resource-fault" "external-call:outcome-resource-fault"

def externalCallLanguageTransitions : List RewriteRule := [
  fuelExhaustedRule,
  branchZeroTransition,
  branchNonzeroTransition,
  callValueTransition,
  callLanguageFaultTransition,
  callEngineFaultTransition,
  callResourceFaultTransition,
  returnValueTransition,
  returnDeclinedTransition,
  returnLanguageFaultTransition,
  returnEngineFaultTransition,
  returnResourceFaultTransition
]

/-- Every ExternalCall transition consults only explicit relation facts.  In particular,
none of the target rules hides a recursive invocation of the ExternalCall evaluator in a
premise. -/
theorem externalCallLanguageTransitions_noncontextual :
    ∀ rule, rule ∈ externalCallLanguageTransitions →
      NoncontextualPremises rule.premises := by
  intro rule ruleMember
  simp only [externalCallLanguageTransitions, List.mem_cons, List.mem_nil_iff,
    or_false] at ruleMember
  rcases ruleMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [fuelExhaustedRule, branchZeroTransition,
      branchNonzeroTransition, callValueTransition,
      callLanguageFaultTransition, callEngineFaultTransition,
      callResourceFaultTransition, returnValueTransition,
      returnDeclinedTransition, returnLanguageFaultTransition,
      returnEngineFaultTransition, returnResourceFaultTransition,
      branchRule, callRule, returnFaultRule, consumeFuel, fetch, query]
  all_goals repeat' constructor

/-- The authored external-call operational target. -/
def externalCallLanguage : LanguageDef := {
  name := "ExternalCallMachine"
  types := [
    { name := "Integer", carrier := .builtinInt },
    { name := "String", carrier := .builtinString },
    "Nat", "SlotId", "Label", "ExternalId", "Value", "Slot", "Store",
    "Instruction", "InstructionList", "ExternalDecl", "ExternalList",
    "Program", "Fuel", "Fault", "ExternalOutcome", "Outcome", "Event",
    "Receipt", "Config"]
  terms := [
    ctor "external-call:nat-zero" "Nat" [],
    ctor "external-call:nat-succ" "Nat" [("prior", "Nat")],
    ctor "external-call:slot-id" "SlotId" [("index", "Nat")],
    ctor "external-call:label" "Label" [("index", "Nat")],
    ctor "external-call:external-id" "ExternalId" [("index", "Nat")],
    ctor "external-call:exact-integer" "Value" [("value", "Integer")],
    ctor "external-call:slot-empty" "Slot" [],
    ctor "external-call:slot-value" "Slot" [("value", "Value")],
    ctor "external-call:store-nil" "Store" [],
    ctor "external-call:store-cons" "Store" [("slot", "Slot"), ("rest", "Store")],
    ctor "external-call:branch-zero" "Instruction"
      [("slot", "SlotId"), ("ifZero", "Label"), ("ifNonzero", "Label")],
    ctor "external-call:call-binary" "Instruction"
      [("external", "ExternalId"), ("ifValue", "Label"),
       ("ifLanguageFault", "Label"), ("ifEngineFault", "Label"),
       ("ifResourceFault", "Label")],
    ctor "external-call:return-value" "Instruction" [("slot", "SlotId")],
    ctor "external-call:return-declined" "Instruction" [],
    ctor "external-call:return-language-fault" "Instruction" [("fault", "Fault")],
    ctor "external-call:return-engine-fault" "Instruction" [("fault", "Fault")],
    ctor "external-call:return-resource-fault" "Instruction" [("fault", "Fault")],
    ctor "external-call:instruction-nil" "InstructionList" [],
    ctor "external-call:instruction-cons" "InstructionList"
      [("instruction", "Instruction"), ("rest", "InstructionList")],
    ctor "external-call:binary-external" "ExternalDecl"
      [("external", "ExternalId"), ("linkName", "String"),
       ("firstInput", "SlotId"), ("secondInput", "SlotId"),
       ("output", "SlotId")],
    ctor "external-call:external-nil" "ExternalList" [],
    ctor "external-call:external-cons" "ExternalList"
      [("external", "ExternalDecl"), ("rest", "ExternalList")],
    ctor "external-call:program" "Program"
      [("instructions", "InstructionList"), ("externals", "ExternalList"),
       ("entry", "Label")],
    ctor "external-call:fuel-infinite" "Fuel" [],
    ctor "external-call:fuel-zero" "Fuel" [],
    ctor "external-call:fuel-succ" "Fuel" [("prior", "Fuel")],
    ctor "external-call:fault" "Fault" [("name", "String")],
    ctor "external-call:external-value" "ExternalOutcome" [("store", "Store")],
    ctor "external-call:external-language-fault" "ExternalOutcome" [("fault", "Fault")],
    ctor "external-call:external-engine-fault" "ExternalOutcome" [("fault", "Fault")],
    ctor "external-call:external-resource-fault" "ExternalOutcome" [("fault", "Fault")],
    ctor "external-call:outcome-value" "Outcome" [("value", "Value")],
    ctor "external-call:outcome-declined" "Outcome" [],
    ctor "external-call:outcome-language-fault" "Outcome" [("fault", "Fault")],
    ctor "external-call:outcome-engine-fault" "Outcome" [("fault", "Fault")],
    ctor "external-call:outcome-resource-fault" "Outcome" [("fault", "Fault")],
    ctor "external-call:step-event" "Event" [("at", "Label")],
    ctor "external-call:external-event" "Event"
      [("external", "ExternalId"), ("outcome", "ExternalOutcome")],
    ctor "external-call:fuel-exhausted-event" "Event" [("at", "Label")],
    ctor "external-call:receipt-nil" "Receipt" [],
    ctor "external-call:receipt-cons" "Receipt"
      [("event", "Event"), ("prior", "Receipt")],
    ctor "external-call:run" "Config"
      [("program", "Program"), ("pc", "Label"), ("store", "Store"),
       ("fuel", "Fuel"), ("receipt", "Receipt")] (some .rewrite),
    ctor "external-call:halted" "Config"
      [("outcome", "Outcome"), ("receipt", "Receipt")]
  ]
  equations := []
  rewrites := externalCallLanguageTransitions
}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem externalCallLanguage_rewrites_validate :
    ∀ rewrite ∈ externalCallLanguage.rewrites,
      LanguageDef.validateRewrite externalCallLanguage rewrite = [] := by
  intro rewrite membership
  change rewrite ∈ externalCallLanguageTransitions at membership
  simp only [externalCallLanguageTransitions, List.mem_cons, List.mem_nil_iff,
    or_false] at membership
  rcases membership with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [LanguageDef.validateRewrite, externalCallLanguage, externalCallLanguageTransitions, ctor,
      typed, v, a, query, run, halted, stepReceipt, externalReceipt,
      commonContext, consumeFuel, fetch, branchRule, callRule,
      returnFaultRule, fuelExhaustedRule, branchZeroTransition,
      branchNonzeroTransition, callValueTransition,
      callLanguageFaultTransition, callEngineFaultTransition,
      callResourceFaultTransition, returnValueTransition,
      returnDeclinedTransition, returnLanguageFaultTransition,
      returnEngineFaultTransition, returnResourceFaultTransition,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premisePatterns,
      LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain,
      TypeExpr.baseNames]

/-- The exact authored ExternalCall presentation passes the shared validation gate. -/
theorem externalCallLanguage_validate : externalCallLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide
  exact externalCallLanguage_rewrites_validate

theorem externalCallLanguage_wire_isSome :
    (CanonicalWire.renderLanguage? externalCallLanguage).isSome := by
  decide +kernel

def externalCallLanguageWire : String :=
  (CanonicalWire.renderLanguage? externalCallLanguage).getD ""

theorem externalCallLanguageWire_nonempty :
    externalCallLanguageWire != "" := by
  decide +kernel

/-- The complete authored ExternalCall rule family is non-contextual.  This exposes the
root-rule inversion principle needed by compiler no-invention proofs. -/
theorem externalCallLanguage_rules_noncontextual :
    ∀ rule, rule ∈ externalCallLanguage.rewrites →
      NoncontextualPremises rule.premises := by
  simpa [externalCallLanguage] using externalCallLanguageTransitions_noncontextual

/-- A halted ExternalCall configuration has no authored successor under any relation
environment.  Open relation facts cannot manufacture authority because every
rule must first match a `external-call:run` configuration. -/
theorem no_step_from_halted
    (relationEnv : RelationEnv) (outcome receipt target : Pattern) :
    ¬ langReducesUsing relationEnv externalCallLanguage
      (halted outcome receipt) target := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule ruleMember
  change rule ∈ externalCallLanguageTransitions at ruleMember
  simp only [externalCallLanguageTransitions, List.mem_cons, List.mem_nil_iff,
    or_false] at ruleMember
  rcases ruleMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [matchPatternForRule_eq_syntactic, fuelExhaustedRule,
      branchZeroTransition, branchNonzeroTransition, callValueTransition,
      callLanguageFaultTransition, callEngineFaultTransition,
      callResourceFaultTransition, returnValueTransition,
      returnDeclinedTransition, returnLanguageFaultTransition,
      returnEngineFaultTransition, returnResourceFaultTransition,
      branchRule, callRule, returnFaultRule, run, halted, a, v,
      matchPattern]

/-- The exact binding order produced when a ExternalCall transition matches a running
configuration.  It is exposed because the generic matcher is proof-relevant:
downstream compiler proofs should reuse this certified boundary rather than
recompute the full matcher for every concrete program. -/
def runMatchBindings
    (program pc store fuel receipt : Pattern) : Bindings := [
  ("pc", pc), ("fuel", fuel), ("receipt", receipt),
  ("store", store), ("program", program)]

/-- Every named ExternalCall transition whose left side is the common running
configuration has the same exact structural match. -/
theorem match_run_transition
    (rule : RewriteRule)
    (leftShape : rule.left =
      run (v "program") (v "pc") (v "store")
        (v "fuel") (v "receipt"))
    (program pc store fuel receipt : Pattern) :
    matchPatternForRule externalCallLanguage rule (run program pc store fuel receipt) =
      [runMatchBindings program pc store fuel receipt] := by
  rw [matchPatternForRule_eq_syntactic, leftShape]
  simp [run, a, v, matchPattern, matchArgs, mergeBindings,
    runMatchBindings]

/-- Exact binding fibre for a fetched zero-branch instruction. -/
def branchInstructionBindings
    (slot ifZero ifNonzero : Pattern) : Bindings := [
  ("ifZero", ifZero), ("ifNonzero", ifNonzero), ("slot", slot)]

theorem match_branch_instruction
    (slot ifZero ifNonzero : Pattern) :
    matchPattern
        (a "external-call:branch-zero" [v "slot", v "ifZero", v "ifNonzero"])
        (a "external-call:branch-zero" [slot, ifZero, ifNonzero]) =
      [branchInstructionBindings slot ifZero ifNonzero] := by
  simp [a, v, matchPattern, matchArgs, mergeBindings,
    branchInstructionBindings]

/-- Exact binding fibre for a fetched binary-external instruction. -/
def callInstructionBindings
    (external ifValue ifLanguageFault ifEngineFault ifResourceFault : Pattern) :
    Bindings := [
  ("ifValue", ifValue), ("ifEngineFault", ifEngineFault),
  ("ifResourceFault", ifResourceFault),
  ("ifLanguageFault", ifLanguageFault), ("external", external)]

theorem match_call_instruction
    (external ifValue ifLanguageFault ifEngineFault ifResourceFault : Pattern) :
    matchPattern
        (a "external-call:call-binary"
          [v "external", v "ifValue", v "ifLanguageFault",
           v "ifEngineFault", v "ifResourceFault"])
        (a "external-call:call-binary"
          [external, ifValue, ifLanguageFault, ifEngineFault,
           ifResourceFault]) =
      [callInstructionBindings external ifValue ifLanguageFault
        ifEngineFault ifResourceFault] := by
  simp [a, v, matchPattern, matchArgs, mergeBindings,
    callInstructionBindings]

/-- Exact binding fibre for the successful external-call outcome. -/
theorem match_external_value (nextStore : Pattern) :
    matchPattern (a "external-call:external-value" [v "nextStore"])
        (a "external-call:external-value" [nextStore]) =
      [[("nextStore", nextStore)]] := by
  simp [a, v, matchPattern, matchArgs, mergeBindings]

/-- Exact binding fibre for a fetched value-return instruction. -/
theorem match_return_value (slot : Pattern) :
    matchPattern (a "external-call:return-value" [v "slot"])
        (a "external-call:return-value" [slot]) =
      [[("slot", slot)]] := by
  simp [a, v, matchPattern, matchArgs, mergeBindings]

/-! ## Mandatory OSLF and NTT gate -/

/-- ExternalCall has the intended 21 sorts, 43 constructors, and 12 ordered
transitions.  Exact physical-wire correspondence is a separate theorem rather
than a consequence of these inventory counts. -/
theorem externalCallLanguage_inventory :
    externalCallLanguage.types.length = 21 ∧
    externalCallLanguage.terms.length = 43 ∧
    externalCallLanguage.rewrites.length = 12 := by
  decide

/-- Native type theory detects the exact-integer carrier crossing into ExternalCall
values. -/
theorem exactInteger_value_crossing :
    ("external-call:exact-integer", "Integer", "Value") ∈ unaryCrossings externalCallLanguage := by
  decide

/-- NTT also detects that outcomes are not stores: a store must pass through
an explicit external outcome and continuation, rather than crossing directly
to a terminal outcome. -/
theorem no_store_outcome_crossing :
    ("external-call:invented-store-outcome", "Store", "Outcome") ∉
      unaryCrossings externalCallLanguage := by
  decide

private def natZero : Pattern := a "external-call:nat-zero"
private def labelZero : Pattern := a "external-call:label" [natZero]
private def fuelZero : Pattern := a "external-call:fuel-zero"
private def fuelOne : Pattern := a "external-call:fuel-succ" [fuelZero]
private def receiptNil : Pattern := a "external-call:receipt-nil"
private def storeNil : Pattern := a "external-call:store-nil"
private def returnDeclined : Pattern := a "external-call:return-declined"
private def instructionNil : Pattern := a "external-call:instruction-nil"
private def externalNil : Pattern := a "external-call:external-nil"
private def demoProgram : Pattern :=
  a "external-call:program"
    [a "external-call:instruction-cons" [returnDeclined, instructionNil],
     externalNil, labelZero]
private def stepLimitFault : Pattern :=
  a "external-call:fault" [a "external-call:step-limit"]

/-- A finite, explicit relation environment for the executable diagnostics.
It is evidence for one program, not a universal external-library adequacy
claim. -/
def externalCallDemoRelationEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == "ExternalCallConsumeFuel" then
      [[fuelOne, fuelZero]]
    else if relation == "ExternalCallFetchInstruction" then
      [[demoProgram, labelZero, returnDeclined]]
    else if relation == "ExternalCallStepLimitFault" then
      [[stepLimitFault]]
    else
      []

/-- OSLF synthesized from the authored ExternalCall language and explicit relation
environment. -/
def externalCallLanguageOSLF := langOSLFUsing externalCallDemoRelationEnv externalCallLanguage "Config"

/-- The generated ExternalCall modalities form the expected Galois connection. -/
theorem externalCallLanguage_galois :
    GaloisConnection
      (langDiamondUsing externalCallDemoRelationEnv externalCallLanguage)
      (langBoxUsing externalCallDemoRelationEnv externalCallLanguage) :=
  langGaloisUsing externalCallDemoRelationEnv externalCallLanguage

private def declineStart : Pattern :=
  run demoProgram labelZero storeNil fuelOne receiptNil

private def declineDone : Pattern :=
  halted (a "external-call:outcome-declined") (stepReceipt labelZero receiptNil)

/-- Positive executable control: the authored return-declined instruction
consumes one unit of fuel, retains the distinction from faults, and appends an
ordered step receipt. -/
theorem decline_step_exact :
    rewriteAt (engineBasePremises externalCallDemoRelationEnv) externalCallLanguage 1 declineStart =
      [declineDone] := by
  decide +kernel

/-- Negative executable control: terminal configurations cannot invent a
further ExternalCall step. -/
theorem halted_is_normal :
    rewriteAt (engineBasePremises externalCallDemoRelationEnv) externalCallLanguage 1 declineDone = [] := by
  decide +kernel

/-- Resource exhaustion is a distinct authored terminal observation and adds
its own receipt event. -/
theorem exhausted_step_exact :
    rewriteAt (engineBasePremises externalCallDemoRelationEnv) externalCallLanguage 1
        (run demoProgram labelZero storeNil fuelZero receiptNil) =
      [halted (a "external-call:outcome-resource-fault" [stepLimitFault])
        (a "external-call:receipt-cons"
          [a "external-call:fuel-exhausted-event" [labelZero], receiptNil])] := by
  decide +kernel

#print axioms externalCallLanguage_validate
#print axioms externalCallLanguage_wire_isSome
#print axioms externalCallLanguage_galois
#print axioms decline_step_exact

end Mettapedia.GSLT.LanguageDef.ExternalCallMachine
