import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory

/-!
# C0-pure operational GSLT and native-type diagnostics

This is the theorem-side presentation of the first small C-family target.  Its
machine configurations, five completion classes, ordered receipt events, fuel
boundary, and external-call boundary are authored independently of any C
structure, interpreter, emitter, compiler, or linked library.
-/

namespace Mettapedia.GSLT.LanguageDef.C0PureNTT

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
  a "c0:run" [program, pc, store, fuel, receipt]

def halted (outcome receipt : Pattern) : Pattern :=
  a "c0:halted" [outcome, receipt]

def stepReceipt (pc receipt : Pattern) : Pattern :=
  a "c0:receipt-cons" [a "c0:step-event" [pc], receipt]

def externalReceipt (external outcome pc receipt : Pattern) : Pattern :=
  a "c0:receipt-cons"
    [a "c0:external-event" [external, outcome], stepReceipt pc receipt]

def commonContext : List (String × TypeExpr) :=
  typed [
    ("program", "Program"), ("pc", "Label"), ("store", "Store"),
    ("fuel", "Fuel"), ("nextFuel", "Fuel"), ("receipt", "Receipt")]

def consumeFuel : Premise :=
  query "C0ConsumeFuel" [v "fuel", v "nextFuel"]

def fetch (instruction : Pattern) : Premise :=
  query "C0FetchInstruction" [v "program", v "pc", instruction]

def branchRule (name test target : String) : RewriteRule := {
  name := name
  typeContext := commonContext ++ typed [
    ("slot", "SlotId"), ("value", "Value"),
    ("ifZero", "Label"), ("ifNonzero", "Label")]
  premises := [
    consumeFuel,
    fetch (a "c0:branch-zero" [v "slot", v "ifZero", v "ifNonzero"]),
    query "C0ReadSlot" [v "store", v "slot", v "value"],
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
    fetch (a "c0:call-binary"
      [v "external", v "ifValue", v "ifLanguageFault",
       v "ifEngineFault", v "ifResourceFault"]),
    query "C0CallBinaryExternal"
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
  name := "c0:fuel-exhausted"
  typeContext := typed [
    ("program", "Program"), ("pc", "Label"), ("store", "Store"),
    ("receipt", "Receipt"), ("fault", "Fault")]
  premises := [query "C0StepLimitFault" [v "fault"]]
  left := run (v "program") (v "pc") (v "store")
    (a "c0:fuel-zero") (v "receipt")
  right := halted (a "c0:outcome-resource-fault" [v "fault"])
    (a "c0:receipt-cons"
      [a "c0:fuel-exhausted-event" [v "pc"], v "receipt"])
}

def branchZeroTransition : RewriteRule :=
  branchRule "c0:branch-zero" "C0IsZero" "ifZero"

def branchNonzeroTransition : RewriteRule :=
  branchRule "c0:branch-nonzero" "C0IsNonzero" "ifNonzero"

def callValueTransition : RewriteRule :=
  callRule "c0:call-value" "ifValue" true
    (a "c0:external-value" [v "nextStore"]) (v "nextStore")

def callLanguageFaultTransition : RewriteRule :=
  callRule "c0:call-language-fault" "ifLanguageFault" false
    (a "c0:external-language-fault" [v "fault"]) (v "store")

def callEngineFaultTransition : RewriteRule :=
  callRule "c0:call-engine-fault" "ifEngineFault" false
    (a "c0:external-engine-fault" [v "fault"]) (v "store")

def callResourceFaultTransition : RewriteRule :=
  callRule "c0:call-resource-fault" "ifResourceFault" false
    (a "c0:external-resource-fault" [v "fault"]) (v "store")

def returnValueTransition : RewriteRule := {
  name := "c0:return-value"
  typeContext := commonContext ++ typed [
    ("slot", "SlotId"), ("value", "Value")]
  premises := [
    consumeFuel, fetch (a "c0:return-value" [v "slot"]),
    query "C0ReadSlot" [v "store", v "slot", v "value"]]
  left := run (v "program") (v "pc") (v "store") (v "fuel") (v "receipt")
  right := halted (a "c0:outcome-value" [v "value"])
    (stepReceipt (v "pc") (v "receipt"))
}

def returnDeclinedTransition : RewriteRule := {
  name := "c0:return-declined"
  typeContext := commonContext
  premises := [consumeFuel, fetch (a "c0:return-declined")]
  left := run (v "program") (v "pc") (v "store") (v "fuel") (v "receipt")
  right := halted (a "c0:outcome-declined")
    (stepReceipt (v "pc") (v "receipt"))
}

def returnLanguageFaultTransition : RewriteRule :=
  returnFaultRule "c0:return-language-fault"
    "c0:return-language-fault" "c0:outcome-language-fault"

def returnEngineFaultTransition : RewriteRule :=
  returnFaultRule "c0:return-engine-fault"
    "c0:return-engine-fault" "c0:outcome-engine-fault"

def returnResourceFaultTransition : RewriteRule :=
  returnFaultRule "c0:return-resource-fault"
    "c0:return-resource-fault" "c0:outcome-resource-fault"

def c0PureTransitions : List RewriteRule := [
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

/-- Every C0 transition consults only explicit relation facts.  In particular,
none of the target rules hides a recursive invocation of the C0 evaluator in a
premise. -/
theorem c0PureTransitions_noncontextual :
    ∀ rule, rule ∈ c0PureTransitions →
      NoncontextualPremises rule.premises := by
  intro rule ruleMember
  simp only [c0PureTransitions, List.mem_cons, List.mem_nil_iff,
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

/-- The authored C0-pure operational target. -/
def c0Pure : LanguageDef := {
  name := "C0Pure"
  types := [
    { name := "Integer", carrier := .builtinInt },
    { name := "String", carrier := .builtinString },
    "Nat", "SlotId", "Label", "ExternalId", "Value", "Slot", "Store",
    "Instruction", "InstructionList", "ExternalDecl", "ExternalList",
    "Program", "Fuel", "Fault", "ExternalOutcome", "Outcome", "Event",
    "Receipt", "Config"]
  terms := [
    ctor "c0:nat-zero" "Nat" [],
    ctor "c0:nat-succ" "Nat" [("prior", "Nat")],
    ctor "c0:slot-id" "SlotId" [("index", "Nat")],
    ctor "c0:label" "Label" [("index", "Nat")],
    ctor "c0:external-id" "ExternalId" [("index", "Nat")],
    ctor "c0:exact-integer" "Value" [("value", "Integer")],
    ctor "c0:slot-empty" "Slot" [],
    ctor "c0:slot-value" "Slot" [("value", "Value")],
    ctor "c0:store-nil" "Store" [],
    ctor "c0:store-cons" "Store" [("slot", "Slot"), ("rest", "Store")],
    ctor "c0:branch-zero" "Instruction"
      [("slot", "SlotId"), ("ifZero", "Label"), ("ifNonzero", "Label")],
    ctor "c0:call-binary" "Instruction"
      [("external", "ExternalId"), ("ifValue", "Label"),
       ("ifLanguageFault", "Label"), ("ifEngineFault", "Label"),
       ("ifResourceFault", "Label")],
    ctor "c0:return-value" "Instruction" [("slot", "SlotId")],
    ctor "c0:return-declined" "Instruction" [],
    ctor "c0:return-language-fault" "Instruction" [("fault", "Fault")],
    ctor "c0:return-engine-fault" "Instruction" [("fault", "Fault")],
    ctor "c0:return-resource-fault" "Instruction" [("fault", "Fault")],
    ctor "c0:instruction-nil" "InstructionList" [],
    ctor "c0:instruction-cons" "InstructionList"
      [("instruction", "Instruction"), ("rest", "InstructionList")],
    ctor "c0:binary-external" "ExternalDecl"
      [("external", "ExternalId"), ("linkName", "String"),
       ("firstInput", "SlotId"), ("secondInput", "SlotId"),
       ("output", "SlotId")],
    ctor "c0:external-nil" "ExternalList" [],
    ctor "c0:external-cons" "ExternalList"
      [("external", "ExternalDecl"), ("rest", "ExternalList")],
    ctor "c0:program" "Program"
      [("instructions", "InstructionList"), ("externals", "ExternalList"),
       ("entry", "Label")],
    ctor "c0:fuel-infinite" "Fuel" [],
    ctor "c0:fuel-zero" "Fuel" [],
    ctor "c0:fuel-succ" "Fuel" [("prior", "Fuel")],
    ctor "c0:fault" "Fault" [("name", "String")],
    ctor "c0:external-value" "ExternalOutcome" [("store", "Store")],
    ctor "c0:external-language-fault" "ExternalOutcome" [("fault", "Fault")],
    ctor "c0:external-engine-fault" "ExternalOutcome" [("fault", "Fault")],
    ctor "c0:external-resource-fault" "ExternalOutcome" [("fault", "Fault")],
    ctor "c0:outcome-value" "Outcome" [("value", "Value")],
    ctor "c0:outcome-declined" "Outcome" [],
    ctor "c0:outcome-language-fault" "Outcome" [("fault", "Fault")],
    ctor "c0:outcome-engine-fault" "Outcome" [("fault", "Fault")],
    ctor "c0:outcome-resource-fault" "Outcome" [("fault", "Fault")],
    ctor "c0:step-event" "Event" [("at", "Label")],
    ctor "c0:external-event" "Event"
      [("external", "ExternalId"), ("outcome", "ExternalOutcome")],
    ctor "c0:fuel-exhausted-event" "Event" [("at", "Label")],
    ctor "c0:receipt-nil" "Receipt" [],
    ctor "c0:receipt-cons" "Receipt"
      [("event", "Event"), ("prior", "Receipt")],
    ctor "c0:run" "Config"
      [("program", "Program"), ("pc", "Label"), ("store", "Store"),
       ("fuel", "Fuel"), ("receipt", "Receipt")] (some .rewrite),
    ctor "c0:halted" "Config"
      [("outcome", "Outcome"), ("receipt", "Receipt")]
  ]
  equations := []
  rewrites := c0PureTransitions
}

/-- The complete authored C0 rule family is non-contextual.  This exposes the
root-rule inversion principle needed by compiler no-invention proofs. -/
theorem c0Pure_rules_noncontextual :
    ∀ rule, rule ∈ c0Pure.rewrites →
      NoncontextualPremises rule.premises := by
  simpa [c0Pure] using c0PureTransitions_noncontextual

/-- A halted C0 configuration has no authored successor under any relation
environment.  Open relation facts cannot manufacture authority because every
rule must first match a `c0:run` configuration. -/
theorem no_step_from_halted
    (relationEnv : RelationEnv) (outcome receipt target : Pattern) :
    ¬ langReducesUsing relationEnv c0Pure
      (halted outcome receipt) target := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule ruleMember
  change rule ∈ c0PureTransitions at ruleMember
  simp only [c0PureTransitions, List.mem_cons, List.mem_nil_iff,
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

/-- The exact binding order produced when a C0 transition matches a running
configuration.  It is exposed because the generic matcher is proof-relevant:
downstream compiler proofs should reuse this certified boundary rather than
recompute the full matcher for every concrete program. -/
def runMatchBindings
    (program pc store fuel receipt : Pattern) : Bindings := [
  ("pc", pc), ("fuel", fuel), ("receipt", receipt),
  ("store", store), ("program", program)]

/-- Every named C0 transition whose left side is the common running
configuration has the same exact structural match. -/
theorem match_run_transition
    (rule : RewriteRule)
    (leftShape : rule.left =
      run (v "program") (v "pc") (v "store")
        (v "fuel") (v "receipt"))
    (program pc store fuel receipt : Pattern) :
    matchPatternForRule c0Pure rule (run program pc store fuel receipt) =
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
        (a "c0:branch-zero" [v "slot", v "ifZero", v "ifNonzero"])
        (a "c0:branch-zero" [slot, ifZero, ifNonzero]) =
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
        (a "c0:call-binary"
          [v "external", v "ifValue", v "ifLanguageFault",
           v "ifEngineFault", v "ifResourceFault"])
        (a "c0:call-binary"
          [external, ifValue, ifLanguageFault, ifEngineFault,
           ifResourceFault]) =
      [callInstructionBindings external ifValue ifLanguageFault
        ifEngineFault ifResourceFault] := by
  simp [a, v, matchPattern, matchArgs, mergeBindings,
    callInstructionBindings]

/-- Exact binding fibre for the successful external-call outcome. -/
theorem match_external_value (nextStore : Pattern) :
    matchPattern (a "c0:external-value" [v "nextStore"])
        (a "c0:external-value" [nextStore]) =
      [[("nextStore", nextStore)]] := by
  simp [a, v, matchPattern, matchArgs, mergeBindings]

/-- Exact binding fibre for a fetched value-return instruction. -/
theorem match_return_value (slot : Pattern) :
    matchPattern (a "c0:return-value" [v "slot"])
        (a "c0:return-value" [slot]) =
      [[("slot", slot)]] := by
  simp [a, v, matchPattern, matchArgs, mergeBindings]

/-! ## Mandatory OSLF and NTT gate -/

/-- C0 has the intended 21 sorts, 43 constructors, and 12 ordered
transitions.  Exact physical-wire correspondence is a separate theorem rather
than a consequence of these inventory counts. -/
theorem c0Pure_inventory :
    c0Pure.types.length = 21 ∧
    c0Pure.terms.length = 43 ∧
    c0Pure.rewrites.length = 12 := by
  decide

/-- Native type theory detects the exact-integer carrier crossing into C0
values. -/
theorem exactInteger_value_crossing :
    ("c0:exact-integer", "Integer", "Value") ∈ unaryCrossings c0Pure := by
  decide

/-- NTT also detects that outcomes are not stores: a store must pass through
an explicit external outcome and continuation, rather than crossing directly
to a terminal outcome. -/
theorem no_store_outcome_crossing :
    ("c0:invented-store-outcome", "Store", "Outcome") ∉
      unaryCrossings c0Pure := by
  decide

private def natZero : Pattern := a "c0:nat-zero"
private def labelZero : Pattern := a "c0:label" [natZero]
private def fuelZero : Pattern := a "c0:fuel-zero"
private def fuelOne : Pattern := a "c0:fuel-succ" [fuelZero]
private def receiptNil : Pattern := a "c0:receipt-nil"
private def storeNil : Pattern := a "c0:store-nil"
private def returnDeclined : Pattern := a "c0:return-declined"
private def instructionNil : Pattern := a "c0:instruction-nil"
private def externalNil : Pattern := a "c0:external-nil"
private def demoProgram : Pattern :=
  a "c0:program"
    [a "c0:instruction-cons" [returnDeclined, instructionNil],
     externalNil, labelZero]
private def stepLimitFault : Pattern :=
  a "c0:fault" [a "c0:step-limit"]

/-- A finite, explicit relation environment for the executable diagnostics.
It is evidence for one program, not a universal external-library adequacy
claim. -/
def c0DemoRelationEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == "C0ConsumeFuel" then
      [[fuelOne, fuelZero]]
    else if relation == "C0FetchInstruction" then
      [[demoProgram, labelZero, returnDeclined]]
    else if relation == "C0StepLimitFault" then
      [[stepLimitFault]]
    else
      []

/-- OSLF synthesized from the authored C0 language and explicit relation
environment. -/
def c0PureOSLF := langOSLFUsing c0DemoRelationEnv c0Pure "Config"

/-- The generated C0 modalities form the expected Galois connection. -/
theorem c0Pure_galois :
    GaloisConnection
      (langDiamondUsing c0DemoRelationEnv c0Pure)
      (langBoxUsing c0DemoRelationEnv c0Pure) :=
  langGaloisUsing c0DemoRelationEnv c0Pure

private def declineStart : Pattern :=
  run demoProgram labelZero storeNil fuelOne receiptNil

private def declineDone : Pattern :=
  halted (a "c0:outcome-declined") (stepReceipt labelZero receiptNil)

/-- Positive executable control: the authored return-declined instruction
consumes one unit of fuel, retains the distinction from faults, and appends an
ordered step receipt. -/
theorem decline_step_exact :
    rewriteAt (engineBasePremises c0DemoRelationEnv) c0Pure 1 declineStart =
      [declineDone] := by
  decide +kernel

/-- Negative executable control: terminal configurations cannot invent a
further C0 step. -/
theorem halted_is_normal :
    rewriteAt (engineBasePremises c0DemoRelationEnv) c0Pure 1 declineDone = [] := by
  decide +kernel

/-- Resource exhaustion is a distinct authored terminal observation and adds
its own receipt event. -/
theorem exhausted_step_exact :
    rewriteAt (engineBasePremises c0DemoRelationEnv) c0Pure 1
        (run demoProgram labelZero storeNil fuelZero receiptNil) =
      [halted (a "c0:outcome-resource-fault" [stepLimitFault])
        (a "c0:receipt-cons"
          [a "c0:fuel-exhausted-event" [labelZero], receiptNil])] := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.C0PureNTT
