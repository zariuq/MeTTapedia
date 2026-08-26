import Mettapedia.GSLT.LanguageDef.C1DigitMachine
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# Reified C1 digit-machine LanguageDef

This is the first-order presentation consumed by external transformers.  The
instruction vocabulary is explicit; the bounded primitive transition relation
is named `C1ExecuteInstruction`.  Its independent mathematical realization is
`C1DigitMachine.executeInstruction`, and correspondence remains a separate
qualification theorem rather than a wire-format assumption.
-/

namespace Mettapedia.GSLT.LanguageDef.C1DigitLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

def ctor (label category : String) (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := policy
}

def typed (entries : List (String × String)) : List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

def v (name : String) : Pattern := .fvar name
def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments
def query (relation : String) (arguments : List Pattern) : Premise :=
  .relationQuery relation arguments

def run (program pc buffers registers fuel receipt : Pattern) : Pattern :=
  a "c1:run" [program, pc, buffers, registers, fuel, receipt]

def halted (outcome receipt : Pattern) : Pattern :=
  a "c1:halted" [outcome, receipt]

def commonContext : List (String × TypeExpr) := typed [
  ("program", "Program"), ("pc", "Nat"), ("buffers", "Buffers"),
  ("registers", "Registers"), ("fuel", "Fuel"),
  ("nextFuel", "Fuel"), ("receipt", "Receipt"),
  ("instruction", "Instruction")]

def executeReceipt : Pattern :=
  a "c1:receipt-cons" [
    a "c1:execute-event" [v "pc"],
    v "receipt"]

def fetchedPremises (result : Pattern) : List Premise := [
  query "C1ConsumeFuel" [v "fuel", v "nextFuel"],
  query "C1Fetch" [v "program", v "pc", v "instruction"],
  query "C1ExecuteInstruction" [
    v "instruction", v "buffers", v "registers", executeReceipt, result]
]

def nextTransition : RewriteRule := {
  name := "c1:execute-next"
  typeContext := commonContext ++ typed [
    ("nextBuffers", "Buffers"), ("nextRegisters", "Registers"),
    ("nextPc", "Nat"), ("nextReceipt", "Receipt")]
  premises := fetchedPremises (a "c1:result-next" [
    v "nextBuffers", v "nextRegisters", v "nextPc", v "nextReceipt"])
  left := run (v "program") (v "pc") (v "buffers") (v "registers")
    (v "fuel") (v "receipt")
  right := run (v "program") (v "nextPc") (v "nextBuffers")
    (v "nextRegisters") (v "nextFuel") (v "nextReceipt")
}

def valueTransition : RewriteRule := {
  name := "c1:execute-value"
  typeContext := commonContext ++ typed [
    ("digits", "DigitBuffer"), ("nextReceipt", "Receipt")]
  premises := fetchedPremises (a "c1:result-value" [
    v "digits", v "nextReceipt"])
  left := run (v "program") (v "pc") (v "buffers") (v "registers")
    (v "fuel") (v "receipt")
  right := halted (a "c1:outcome-value" [v "digits"]) (v "nextReceipt")
}

def faultTransition (name result outcome : String) : RewriteRule := {
  name := name
  typeContext := commonContext ++ typed [
    ("fault", "Fault"), ("nextReceipt", "Receipt")]
  premises := fetchedPremises (a result [v "fault", v "nextReceipt"])
  left := run (v "program") (v "pc") (v "buffers") (v "registers")
    (v "fuel") (v "receipt")
  right := halted (a outcome [v "fault"]) (v "nextReceipt")
}

def languageFaultTransition : RewriteRule :=
  faultTransition "c1:execute-language-fault" "c1:result-language-fault"
    "c1:outcome-language-fault"

def engineFaultTransition : RewriteRule :=
  faultTransition "c1:execute-engine-fault" "c1:result-engine-fault"
    "c1:outcome-engine-fault"

def resourceFaultTransition : RewriteRule :=
  faultTransition "c1:execute-resource-fault" "c1:result-resource-fault"
    "c1:outcome-resource-fault"

def missingProgramCounterTransition : RewriteRule := {
  name := "c1:missing-program-counter"
  typeContext := commonContext ++ typed [("fault", "Fault")]
  premises := [
    query "C1ConsumeFuel" [v "fuel", v "nextFuel"],
    query "C1MissingProgramCounter" [v "program", v "pc", v "fault"]]
  left := run (v "program") (v "pc") (v "buffers") (v "registers")
    (v "fuel") (v "receipt")
  right := halted (a "c1:outcome-engine-fault" [v "fault"])
    (a "c1:receipt-cons" [
      a "c1:engine-fault-event" [v "pc", v "fault"], v "receipt"])
}

def fuelExhaustedTransition : RewriteRule := {
  name := "c1:fuel-exhausted"
  typeContext := typed [
    ("program", "Program"), ("pc", "Nat"), ("buffers", "Buffers"),
    ("registers", "Registers"), ("receipt", "Receipt"),
    ("fault", "Fault")]
  premises := [query "C1FuelExhaustedFault" [v "fault"]]
  left := run (v "program") (v "pc") (v "buffers") (v "registers")
    (a "c1:fuel-zero") (v "receipt")
  right := halted (a "c1:outcome-resource-fault" [v "fault"])
    (a "c1:receipt-cons" [
      a "c1:resource-fault-event" [v "pc", v "fault"], v "receipt"])
}

def instructionTerms : List GrammarRule := [
  ctor "c1:set" "Instruction" [
    ("register", "Nat"), ("value", "Nat"), ("next", "Nat")],
  ctor "c1:copy" "Instruction" [
    ("source", "Nat"), ("destination", "Nat"), ("next", "Nat")],
  ctor "c1:increment" "Instruction" [("register", "Nat"), ("next", "Nat")],
  ctor "c1:length" "Instruction" [
    ("buffer", "Nat"), ("destination", "Nat"), ("next", "Nat")],
  ctor "c1:read-or-zero" "Instruction" [
    ("buffer", "Nat"), ("index", "Nat"),
    ("destination", "Nat"), ("next", "Nat")],
  ctor "c1:write" "Instruction" [
    ("buffer", "Nat"), ("index", "Nat"),
    ("digit", "Nat"), ("next", "Nat")],
  ctor "c1:lookup" "Instruction" [
    ("inputs", "RegisterList"), ("outputs", "RegisterList"),
    ("table", "Table"), ("next", "Nat")],
  ctor "c1:branch-lt" "Instruction" [
    ("left", "Nat"), ("right", "Nat"),
    ("ifTrue", "Nat"), ("ifFalse", "Nat")],
  ctor "c1:branch-eq" "Instruction" [
    ("register", "Nat"), ("value", "Nat"),
    ("ifTrue", "Nat"), ("ifFalse", "Nat")],
  ctor "c1:jump" "Instruction" [("next", "Nat")],
  ctor "c1:return-buffer" "Instruction" [("buffer", "Nat")],
  ctor "c1:fail-language" "Instruction" [("fault", "Fault")],
  ctor "c1:fail-engine" "Instruction" [("fault", "Fault")],
  ctor "c1:fail-resource" "Instruction" [("fault", "Fault")]
]

def terms : List GrammarRule := [
  ctor "c1:run" "Config" [
    ("program", "Program"), ("pc", "Nat"), ("buffers", "Buffers"),
    ("registers", "Registers"), ("fuel", "Fuel"), ("receipt", "Receipt")]
    (some .rewrite),
  ctor "c1:halted" "Config" [("outcome", "Outcome"), ("receipt", "Receipt")],
  ctor "c1:fuel-zero" "Fuel" []
] ++ instructionTerms ++ [
  ctor "c1:result-next" "StepResult" [
    ("buffers", "Buffers"), ("registers", "Registers"), ("pc", "Nat"),
    ("receipt", "Receipt")],
  ctor "c1:result-value" "StepResult" [
    ("digits", "DigitBuffer"), ("receipt", "Receipt")],
  ctor "c1:result-language-fault" "StepResult" [
    ("fault", "Fault"), ("receipt", "Receipt")],
  ctor "c1:result-engine-fault" "StepResult" [
    ("fault", "Fault"), ("receipt", "Receipt")],
  ctor "c1:result-resource-fault" "StepResult" [
    ("fault", "Fault"), ("receipt", "Receipt")],
  ctor "c1:outcome-value" "Outcome" [("digits", "DigitBuffer")],
  ctor "c1:outcome-language-fault" "Outcome" [("fault", "Fault")],
  ctor "c1:outcome-engine-fault" "Outcome" [("fault", "Fault")],
  ctor "c1:outcome-resource-fault" "Outcome" [("fault", "Fault")],
  ctor "c1:receipt-cons" "Receipt" [("event", "Event"), ("receipt", "Receipt")],
  ctor "c1:execute-event" "Event" [("pc", "Nat")],
  ctor "c1:language-fault-event" "Event" [("pc", "Nat"), ("fault", "Fault")],
  ctor "c1:engine-fault-event" "Event" [("pc", "Nat"), ("fault", "Fault")],
  ctor "c1:resource-fault-event" "Event" [("pc", "Nat"), ("fault", "Fault")]
]

def transitions : List RewriteRule := [
  fuelExhaustedTransition,
  missingProgramCounterTransition,
  nextTransition,
  valueTransition,
  languageFaultTransition,
  engineFaultTransition,
  resourceFaultTransition
]

def language : LanguageDef := {
  name := "C1DigitMachine"
  types := [
    "Config", "Program", "Buffers", "Registers", "Fuel", "Receipt",
    "Instruction", "RegisterList", "Table", "StepResult", "Outcome",
    "Fault", "Event", "DigitBuffer", "Nat"]
  terms := terms
  equations := []
  rewrites := transitions
}

theorem instruction_count : instructionTerms.length = 14 := by decide
theorem transition_count : transitions.length = 7 := by decide
theorem wire_isSome :
    (CanonicalWire.renderLanguage? language).isSome := by
  decide +kernel

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

theorem wire_nonempty : wire != "" := by decide +kernel

#print axioms instruction_count
#print axioms transition_count
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.C1DigitLanguageDef
