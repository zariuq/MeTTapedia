import Mettapedia.GSLT.LanguageDef.RadixDigitMachine
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# Reified radix-digit-machine LanguageDef

This is the first-order presentation consumed by external transformers.  The
instruction vocabulary is explicit; the bounded primitive transition relation
is named `RadixDigitExecuteInstruction`. Its independent mathematical realization is
`RadixDigitMachine.executeInstruction`, and correspondence remains a separate
qualification theorem rather than a wire-format assumption.
-/

namespace Mettapedia.GSLT.LanguageDef.RadixDigitLanguageDef

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
  a "radix-digit:run" [program, pc, buffers, registers, fuel, receipt]

def halted (outcome receipt : Pattern) : Pattern :=
  a "radix-digit:halted" [outcome, receipt]

def commonContext : List (String × TypeExpr) := typed [
  ("program", "Program"), ("pc", "Nat"), ("buffers", "Buffers"),
  ("registers", "Registers"), ("fuel", "Fuel"),
  ("nextFuel", "Fuel"), ("receipt", "Receipt"),
  ("instruction", "Instruction")]

def executeReceipt : Pattern :=
  a "radix-digit:receipt-cons" [
    a "radix-digit:execute-event" [v "pc"],
    v "receipt"]

def fetchedPremises (result : Pattern) : List Premise := [
  query "RadixDigitConsumeFuel" [v "fuel", v "nextFuel"],
  query "RadixDigitFetch" [v "program", v "pc", v "instruction"],
  query "RadixDigitExecuteInstruction" [
    v "instruction", v "buffers", v "registers", executeReceipt, result]
]

def nextTransition : RewriteRule := {
  name := "radix-digit:execute-next"
  typeContext := commonContext ++ typed [
    ("nextBuffers", "Buffers"), ("nextRegisters", "Registers"),
    ("nextPc", "Nat"), ("nextReceipt", "Receipt")]
  premises := fetchedPremises (a "radix-digit:result-next" [
    v "nextBuffers", v "nextRegisters", v "nextPc", v "nextReceipt"])
  left := run (v "program") (v "pc") (v "buffers") (v "registers")
    (v "fuel") (v "receipt")
  right := run (v "program") (v "nextPc") (v "nextBuffers")
    (v "nextRegisters") (v "nextFuel") (v "nextReceipt")
}

def valueTransition : RewriteRule := {
  name := "radix-digit:execute-value"
  typeContext := commonContext ++ typed [
    ("digits", "DigitBuffer"), ("nextReceipt", "Receipt")]
  premises := fetchedPremises (a "radix-digit:result-value" [
    v "digits", v "nextReceipt"])
  left := run (v "program") (v "pc") (v "buffers") (v "registers")
    (v "fuel") (v "receipt")
  right := halted (a "radix-digit:outcome-value" [v "digits"]) (v "nextReceipt")
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
  faultTransition "radix-digit:execute-language-fault" "radix-digit:result-language-fault"
    "radix-digit:outcome-language-fault"

def engineFaultTransition : RewriteRule :=
  faultTransition "radix-digit:execute-engine-fault" "radix-digit:result-engine-fault"
    "radix-digit:outcome-engine-fault"

def resourceFaultTransition : RewriteRule :=
  faultTransition "radix-digit:execute-resource-fault" "radix-digit:result-resource-fault"
    "radix-digit:outcome-resource-fault"

def missingProgramCounterTransition : RewriteRule := {
  name := "radix-digit:missing-program-counter"
  typeContext := commonContext ++ typed [("fault", "Fault")]
  premises := [
    query "RadixDigitConsumeFuel" [v "fuel", v "nextFuel"],
    query "RadixDigitMissingProgramCounter" [v "program", v "pc", v "fault"]]
  left := run (v "program") (v "pc") (v "buffers") (v "registers")
    (v "fuel") (v "receipt")
  right := halted (a "radix-digit:outcome-engine-fault" [v "fault"])
    (a "radix-digit:receipt-cons" [
      a "radix-digit:engine-fault-event" [v "pc", v "fault"], v "receipt"])
}

def fuelExhaustedTransition : RewriteRule := {
  name := "radix-digit:fuel-exhausted"
  typeContext := typed [
    ("program", "Program"), ("pc", "Nat"), ("buffers", "Buffers"),
    ("registers", "Registers"), ("receipt", "Receipt"),
    ("fault", "Fault")]
  premises := [query "RadixDigitFuelExhaustedFault" [v "fault"]]
  left := run (v "program") (v "pc") (v "buffers") (v "registers")
    (a "radix-digit:fuel-zero") (v "receipt")
  right := halted (a "radix-digit:outcome-resource-fault" [v "fault"])
    (a "radix-digit:receipt-cons" [
      a "radix-digit:resource-fault-event" [v "pc", v "fault"], v "receipt"])
}

def instructionTerms : List GrammarRule := [
  ctor "radix-digit:set" "Instruction" [
    ("register", "Nat"), ("value", "Nat"), ("next", "Nat")],
  ctor "radix-digit:copy" "Instruction" [
    ("source", "Nat"), ("destination", "Nat"), ("next", "Nat")],
  ctor "radix-digit:increment" "Instruction" [("register", "Nat"), ("next", "Nat")],
  ctor "radix-digit:length" "Instruction" [
    ("buffer", "Nat"), ("destination", "Nat"), ("next", "Nat")],
  ctor "radix-digit:read-or-zero" "Instruction" [
    ("buffer", "Nat"), ("index", "Nat"),
    ("destination", "Nat"), ("next", "Nat")],
  ctor "radix-digit:write" "Instruction" [
    ("buffer", "Nat"), ("index", "Nat"),
    ("digit", "Nat"), ("next", "Nat")],
  ctor "radix-digit:lookup" "Instruction" [
    ("inputs", "RegisterList"), ("outputs", "RegisterList"),
    ("table", "Table"), ("next", "Nat")],
  ctor "radix-digit:branch-lt" "Instruction" [
    ("left", "Nat"), ("right", "Nat"),
    ("ifTrue", "Nat"), ("ifFalse", "Nat")],
  ctor "radix-digit:branch-eq" "Instruction" [
    ("register", "Nat"), ("value", "Nat"),
    ("ifTrue", "Nat"), ("ifFalse", "Nat")],
  ctor "radix-digit:jump" "Instruction" [("next", "Nat")],
  ctor "radix-digit:return-buffer" "Instruction" [("buffer", "Nat")],
  ctor "radix-digit:fail-language" "Instruction" [("fault", "Fault")],
  ctor "radix-digit:fail-engine" "Instruction" [("fault", "Fault")],
  ctor "radix-digit:fail-resource" "Instruction" [("fault", "Fault")]
]

def terms : List GrammarRule := [
  ctor "radix-digit:run" "Config" [
    ("program", "Program"), ("pc", "Nat"), ("buffers", "Buffers"),
    ("registers", "Registers"), ("fuel", "Fuel"), ("receipt", "Receipt")]
    (some .rewrite),
  ctor "radix-digit:halted" "Config" [("outcome", "Outcome"), ("receipt", "Receipt")],
  ctor "radix-digit:fuel-zero" "Fuel" []
] ++ instructionTerms ++ [
  ctor "radix-digit:result-next" "StepResult" [
    ("buffers", "Buffers"), ("registers", "Registers"), ("pc", "Nat"),
    ("receipt", "Receipt")],
  ctor "radix-digit:result-value" "StepResult" [
    ("digits", "DigitBuffer"), ("receipt", "Receipt")],
  ctor "radix-digit:result-language-fault" "StepResult" [
    ("fault", "Fault"), ("receipt", "Receipt")],
  ctor "radix-digit:result-engine-fault" "StepResult" [
    ("fault", "Fault"), ("receipt", "Receipt")],
  ctor "radix-digit:result-resource-fault" "StepResult" [
    ("fault", "Fault"), ("receipt", "Receipt")],
  ctor "radix-digit:outcome-value" "Outcome" [("digits", "DigitBuffer")],
  ctor "radix-digit:outcome-language-fault" "Outcome" [("fault", "Fault")],
  ctor "radix-digit:outcome-engine-fault" "Outcome" [("fault", "Fault")],
  ctor "radix-digit:outcome-resource-fault" "Outcome" [("fault", "Fault")],
  ctor "radix-digit:receipt-cons" "Receipt" [("event", "Event"), ("receipt", "Receipt")],
  ctor "radix-digit:execute-event" "Event" [("pc", "Nat")],
  ctor "radix-digit:language-fault-event" "Event" [("pc", "Nat"), ("fault", "Fault")],
  ctor "radix-digit:engine-fault-event" "Event" [("pc", "Nat"), ("fault", "Fault")],
  ctor "radix-digit:resource-fault-event" "Event" [("pc", "Nat"), ("fault", "Fault")]
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
  name := "RadixDigitMachine"
  types := [
    "Config", "Program", "Buffers", "Registers", "Fuel", "Receipt",
    "Instruction", "RegisterList", "Table", "StepResult", "Outcome",
    "Fault", "Event", "DigitBuffer", "Nat"]
  terms := terms
  equations := []
  rewrites := transitions
}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem rewrites_validate :
    ∀ rewrite ∈ language.rewrites,
      LanguageDef.validateRewrite language rewrite = [] := by
  intro rewrite membership
  change rewrite ∈ transitions at membership
  simp only [transitions, List.mem_cons, List.mem_nil_iff, or_false]
    at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [LanguageDef.validateRewrite, language, transitions, terms,
      instructionTerms, ctor, typed, v, a, query, run, halted,
      commonContext, executeReceipt, fetchedPremises, nextTransition,
      valueTransition, faultTransition, languageFaultTransition,
      engineFaultTransition, resourceFaultTransition,
      missingProgramCounterTransition, fuelExhaustedTransition,
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

/-- The exact authored radix-digit-machine presentation passes the shared
validation gate. -/
theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide
  exact rewrites_validate

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

end Mettapedia.GSLT.LanguageDef.RadixDigitLanguageDef
