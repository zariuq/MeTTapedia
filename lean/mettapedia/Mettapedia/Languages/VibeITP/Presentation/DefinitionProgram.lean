import Mettapedia.Languages.VibeITP.Presentation.LiteralCorrespondence
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramSuffix

/-!
# Authored Vibe definition computation

The signature, every parameter and the complete hint list are supplied data.
Preorder traversal consumes one hint at each free-variable application,
including repeated occurrences. All hints, including unused suffixes, must
name a parameter. Parameter arities and descending eta arguments are computed
by equations without imposing a word bound on declared arities.

Body formation and closedness precede definition construction. The resulting
equation need not satisfy the machine-word formation predicate: an admitted
free-variable declaration can have any natural arity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalDefinitions

open ComputationalData ComputationalShift ComputationalInference ComputationalLiterals
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

structure DefinitionRequest where
  constant : Spec.SymId
  parameters : List Spec.SymId
  hints : List Nat
  body : Spec.Term
  deriving Repr

def DefinitionRequest.result (signature : Spec.Sig) (request : DefinitionRequest) : Option Spec.Term :=
  if Spec.WellFormed signature request.body &&
      Spec.definitionAdmissible signature request.parameters request.hints request.body then
    some (Spec.definitionStatement signature request.constant request.parameters request.body)
  else none

def encodeSymbols (symbols : List Spec.SymId) : Term := .list (symbols.map encodeSymbol)

def encodeNatResult : Option (List Nat) → Term
  | none => .sym "None"
  | some values => .expr [.sym "Some", encodeBinders values]

def encodeSymbolResult : Option Spec.SymId → Term
  | none => .sym "None"
  | some symbol => .expr [.sym "Some", encodeSymbol symbol]

def parameterArities (signature : Spec.Sig) : List Spec.SymId → Option (List Nat)
  | [] => some []
  | parameter :: rest => do
      let info ← signature parameter
      if info.kind = .fvar then
        let tail ← parameterArities signature rest
        some (info.arity :: tail)
      else none

private def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def slot (name : String) : Term := .var name
private def equation (name head : String) (arguments : List Term) (body : Term) : Equation :=
  ⟨name, head, arguments, body⟩
private def someResult (value : Term) : Term := call "Some" [value]

def definitionEquations : Program := [
  equation "definition-arities" "vibe:def-arities" [slot "table", slot "parameters"]
    (call "vibe:def-arities-view" [slot "table", call "nik:list-view" [slot "parameters"]]),
  equation "definition-arities-empty" "vibe:def-arities-view" [slot "table", .sym "List:Nil"]
    (someResult (.list [])),
  equation "definition-arities-cons" "vibe:def-arities-view"
    [slot "table", call "List:Cons" [slot "parameter", slot "rest"]]
    (call "vibe:def-arity-info" [call "vibe:lookup-symbol" [slot "table", slot "parameter"],
      slot "table", slot "rest"]),
  equation "definition-arity-unknown" "vibe:def-arity-info" [.sym "None", slot "table", slot "rest"]
    (.sym "None"),
  equation "definition-arity-constant" "vibe:def-arity-info"
    [someResult (call "Vibe:SymInfo" [.sym "Constant", slot "binders"]), slot "table", slot "rest"]
    (.sym "None"),
  equation "definition-arity-fvar" "vibe:def-arity-info"
    [someResult (call "Vibe:SymInfo" [.sym "Fvar", slot "binders"]), slot "table", slot "rest"]
    (call "vibe:def-arities-rest" [call "vibe:list-length" [slot "binders"],
      call "vibe:def-arities" [slot "table", slot "rest"]]),
  equation "definition-arities-refused" "vibe:def-arities-rest" [slot "arity", .sym "None"]
    (.sym "None"),
  equation "definition-arities-success" "vibe:def-arities-rest"
    [slot "arity", someResult (slot "rest")]
    (someResult (call "nik:list-cons" [slot "arity", slot "rest"])),
  equation "definition-info" "vibe:def-info" [slot "table", slot "parameters"]
    (call "vibe:def-info-result" [call "vibe:def-arities" [slot "table", slot "parameters"]]),
  equation "definition-info-refused" "vibe:def-info-result" [.sym "None"] (.sym "None"),
  equation "definition-info-success" "vibe:def-info-result" [someResult (slot "binders")]
    (someResult (call "Vibe:SymInfo" [.sym "Constant", slot "binders"])),
  equation "definition-hint-bounds" "vibe:def-bounds" [slot "parameters", slot "hints"]
    (call "vibe:def-bounds-go" [call "vibe:list-length" [slot "parameters"], slot "hints"]),
  equation "definition-hint-bounds-go" "vibe:def-bounds-go" [slot "count", slot "hints"]
    (call "vibe:def-bounds-view" [slot "count", call "nik:list-view" [slot "hints"]]),
  equation "definition-hint-bounds-empty" "vibe:def-bounds-view" [slot "count", .sym "List:Nil"]
    (.sym "True"),
  equation "definition-hint-bounds-cons" "vibe:def-bounds-view"
    [slot "count", call "List:Cons" [slot "index", slot "rest"]]
    (call "vibe:def-bounds-first" [call "nik:nat-lt" [slot "index", slot "count"],
      slot "count", slot "rest"]),
  equation "definition-hint-out-of-range" "vibe:def-bounds-first"
    [.sym "False", slot "count", slot "rest"] (.sym "False"),
  equation "definition-hint-in-range" "vibe:def-bounds-first"
    [.sym "True", slot "count", slot "rest"]
    (call "vibe:def-bounds-go" [slot "count", slot "rest"]),
  equation "definition-parameter-at" "vibe:def-at" [slot "parameters", slot "index"]
    (call "vibe:def-at-view" [call "nik:list-view" [slot "parameters"], slot "index"]),
  equation "definition-parameter-at-missing" "vibe:def-at-view" [.sym "List:Nil", slot "index"]
    (.sym "None"),
  equation "definition-parameter-at-cons" "vibe:def-at-view"
    [call "List:Cons" [slot "first", slot "rest"], slot "index"]
    (call "vibe:def-at-zero" [call "nik:nat-zero" [slot "index"],
      slot "first", slot "rest", slot "index"]),
  equation "definition-parameter-at-first" "vibe:def-at-zero"
    [.sym "True", slot "first", slot "rest", slot "index"] (someResult (slot "first")),
  equation "definition-parameter-at-later" "vibe:def-at-zero"
    [.sym "False", slot "first", slot "rest", slot "index"]
    (call "vibe:def-at" [slot "rest", call "nik:nat-pred" [slot "index"]]),
  equation "definition-consume-bound" "vibe:def-consume"
    [slot "table", slot "parameters", slot "hints", call "Vibe:BVar" [slot "index"]]
    (someResult (slot "hints")),
  equation "definition-consume-literal" "vibe:def-consume"
    [slot "table", slot "parameters", slot "hints", call "Vibe:Lit" [slot "bytes"]]
    (someResult (slot "hints")),
  equation "definition-consume-application" "vibe:def-consume"
    [slot "table", slot "parameters", slot "hints", call "Vibe:App" [slot "symbol", slot "arguments"]]
    (call "vibe:def-consume-kind" [call "vibe:is-fvar" [slot "table", slot "symbol"],
      slot "table", slot "parameters", slot "hints", slot "symbol", slot "arguments"]),
  equation "definition-consume-constant" "vibe:def-consume-kind"
    [.sym "False", slot "table", slot "parameters", slot "hints", slot "symbol", slot "arguments"]
    (call "vibe:def-consume-args" [slot "table", slot "parameters", slot "hints", slot "arguments"]),
  equation "definition-consume-fvar" "vibe:def-consume-kind"
    [.sym "True", slot "table", slot "parameters", slot "hints", slot "symbol", slot "arguments"]
    (call "vibe:def-consume-hint" [slot "table", slot "parameters", call "nik:list-view" [slot "hints"],
      slot "symbol", slot "arguments"]),
  equation "definition-consume-missing-hint" "vibe:def-consume-hint"
    [slot "table", slot "parameters", .sym "List:Nil", slot "symbol", slot "arguments"] (.sym "None"),
  equation "definition-consume-hint" "vibe:def-consume-hint"
    [slot "table", slot "parameters", call "List:Cons" [slot "index", slot "rest"],
      slot "symbol", slot "arguments"]
    (call "vibe:def-consume-found" [call "vibe:def-at" [slot "parameters", slot "index"],
      slot "table", slot "parameters", slot "rest", slot "symbol", slot "arguments"]),
  equation "definition-consume-unknown-parameter" "vibe:def-consume-found"
    [.sym "None", slot "table", slot "parameters", slot "rest", slot "symbol", slot "arguments"]
    (.sym "None"),
  equation "definition-consume-parameter" "vibe:def-consume-found"
    [someResult (slot "parameter"), slot "table", slot "parameters", slot "rest",
      slot "symbol", slot "arguments"]
    (call "vibe:def-consume-equal" [call "vibe:symbol-eq" [slot "symbol", slot "parameter"],
      slot "table", slot "parameters", slot "rest", slot "arguments"]),
  equation "definition-consume-wrong-parameter" "vibe:def-consume-equal"
    [.sym "False", slot "table", slot "parameters", slot "rest", slot "arguments"] (.sym "None"),
  equation "definition-consume-right-parameter" "vibe:def-consume-equal"
    [.sym "True", slot "table", slot "parameters", slot "rest", slot "arguments"]
    (call "vibe:def-consume-args" [slot "table", slot "parameters", slot "rest", slot "arguments"]),
  equation "definition-consume-arguments" "vibe:def-consume-args"
    [slot "table", slot "parameters", slot "hints", slot "arguments"]
    (call "vibe:def-consume-view" [slot "table", slot "parameters", slot "hints",
      call "nik:list-view" [slot "arguments"]]),
  equation "definition-consume-empty-arguments" "vibe:def-consume-view"
    [slot "table", slot "parameters", slot "hints", .sym "List:Nil"] (someResult (slot "hints")),
  equation "definition-consume-argument-pair" "vibe:def-consume-view"
    [slot "table", slot "parameters", slot "hints", call "List:Cons" [slot "first", slot "rest"]]
    (call "vibe:def-consume-first" [call "vibe:def-consume"
      [slot "table", slot "parameters", slot "hints", slot "first"],
      slot "table", slot "parameters", slot "rest"]),
  equation "definition-consume-argument-refused" "vibe:def-consume-first"
    [.sym "None", slot "table", slot "parameters", slot "rest"] (.sym "None"),
  equation "definition-consume-argument-success" "vibe:def-consume-first"
    [someResult (slot "hints"), slot "table", slot "parameters", slot "rest"]
    (call "vibe:def-consume-args" [slot "table", slot "parameters", slot "hints", slot "rest"]),
  equation "definition-descending" "vibe:def-desc" [slot "arity"]
    (call "vibe:def-desc-zero" [call "nik:nat-zero" [slot "arity"], slot "arity"]),
  equation "definition-descending-empty" "vibe:def-desc-zero" [.sym "True", slot "arity"] (.list []),
  equation "definition-descending-cons" "vibe:def-desc-zero" [.sym "False", slot "arity"]
    (call "nik:list-cons" [call "Vibe:BVar" [call "nik:nat-pred" [slot "arity"]],
      call "vibe:def-desc" [call "nik:nat-pred" [slot "arity"]]]),
  equation "definition-etas" "vibe:def-etas" [slot "parameters", slot "arities"]
    (call "vibe:def-etas-view" [call "nik:list-view" [slot "parameters"],
      call "nik:list-view" [slot "arities"]]),
  equation "definition-etas-empty" "vibe:def-etas-view" [.sym "List:Nil", .sym "List:Nil"] (.list []),
  equation "definition-etas-cons" "vibe:def-etas-view"
    [call "List:Cons" [slot "parameter", slot "rest"], call "List:Cons" [slot "arity", slot "arities"]]
    (call "nik:list-cons" [call "Vibe:App" [slot "parameter", call "vibe:def-desc" [slot "arity"]],
      call "vibe:def-etas" [slot "rest", slot "arities"]]),
  equation "definition-query" "vibe:definition-query"
    [slot "table", slot "constant", slot "parameters", slot "hints", slot "body"]
    (call "vibe:def-formed" [call "vibe:well-formed" [slot "table", slot "body"],
      slot "table", slot "constant", slot "parameters", slot "hints", slot "body"]),
  equation "definition-malformed-body" "vibe:def-formed"
    [.sym "False", slot "table", slot "constant", slot "parameters", slot "hints", slot "body"]
    (.sym "None"),
  equation "definition-formed-body" "vibe:def-formed"
    [.sym "True", slot "table", slot "constant", slot "parameters", slot "hints", slot "body"]
    (call "vibe:def-closed" [call "nik:nat-zero" [call "vibe:depth" [slot "table", slot "body"]],
      slot "table", slot "constant", slot "parameters", slot "hints", slot "body"]),
  equation "definition-open-body" "vibe:def-closed"
    [.sym "False", slot "table", slot "constant", slot "parameters", slot "hints", slot "body"]
    (.sym "None"),
  equation "definition-closed-body" "vibe:def-closed"
    [.sym "True", slot "table", slot "constant", slot "parameters", slot "hints", slot "body"]
    (call "vibe:def-parameters" [call "vibe:def-arities" [slot "table", slot "parameters"],
      slot "table", slot "constant", slot "parameters", slot "hints", slot "body"]),
  equation "definition-invalid-parameters" "vibe:def-parameters"
    [.sym "None", slot "table", slot "constant", slot "parameters", slot "hints", slot "body"]
    (.sym "None"),
  equation "definition-valid-parameters" "vibe:def-parameters"
    [someResult (slot "arities"), slot "table", slot "constant", slot "parameters", slot "hints", slot "body"]
    (call "vibe:def-hints" [call "vibe:def-bounds" [slot "parameters", slot "hints"],
      slot "table", slot "constant", slot "parameters", slot "hints", slot "body", slot "arities"]),
  equation "definition-invalid-hints" "vibe:def-hints"
    [.sym "False", slot "table", slot "constant", slot "parameters", slot "hints", slot "body", slot "arities"]
    (.sym "None"),
  equation "definition-bounded-hints" "vibe:def-hints"
    [.sym "True", slot "table", slot "constant", slot "parameters", slot "hints", slot "body", slot "arities"]
    (call "vibe:def-consumed" [call "vibe:def-consume" [slot "table", slot "parameters", slot "hints", slot "body"],
      slot "constant", slot "parameters", slot "body", slot "arities"]),
  equation "definition-unmatched-occurrences" "vibe:def-consumed"
    [.sym "None", slot "constant", slot "parameters", slot "body", slot "arities"] (.sym "None"),
  equation "definition-matched-occurrences" "vibe:def-consumed"
    [someResult (slot "unused-hints"), slot "constant", slot "parameters", slot "body", slot "arities"]
    (someResult (call "Vibe:App" [encodeSymbol (.builtin .eq), .list [
      call "Vibe:App" [slot "constant", call "vibe:def-etas" [slot "parameters", slot "arities"]], slot "body"]])),
  equation "check-definition" "vibe:check-definition"
    [slot "table", slot "constant", slot "parameters", slot "hints", slot "body", slot "claimed"]
    (call "vibe:check-result" [call "vibe:definition-query"
      [slot "table", slot "constant", slot "parameters", slot "hints", slot "body"], slot "claimed"]) ]

def definitionProgram : Program := literalProgram ++ definitionEquations

theorem definitionEquations_disjoint :
    ∀ equation ∈ definitionEquations, equation.head ∉ literalProgram.calledHeads := by
  have fresh : definitionEquations.all (fun equation =>
      decide (equation.head ∉ literalProgram.calledHeads)) = true := by decide +kernel
  intro equation member
  simpa using List.all_eq_true.mp fresh equation member

theorem definitionProgram_leftLinear : LeftLinear definitionProgram := by
  have additional : LeftLinear definitionEquations := by
    simp [LeftLinear, definitionEquations, equation, call, slot, someResult, encodeSymbol,
      natural, Spec.Builtin.slot, patternVarsList, patternVars]
  intro equation member
  rcases List.mem_append.mp member with old | added
  · exact literalProgram_leftLinear equation old
  · exact additional equation added

theorem definitionProgram_dataSeparated : DataSeparated definitionProgram productDivisionHost where
  undefined := by
    intro head member
    have old := literalProgram_dataSeparated.undefined head member
    have added : definitionEquations.defines head = false := by
      simp [constructorHeads] at member
      rcases member with rfl | rfl | rfl <;> simp [Program.defines, definitionEquations, equation]
    change (literalProgram ++ definitionEquations).any _ = false
    rw [List.any_append]
    change (literalProgram.defines head || definitionEquations.defines head) = false
    rw [old, added]
    rfl
  unhandled := literalProgram_dataSeparated.unhandled

theorem reuse_literal_call {head : String} {arguments : List Term} {result : Term}
    (used : head ∈ literalProgram.calledHeads)
    (computed : Applies literalProgram productDivisionHost head arguments result) :
    Applies definitionProgram productDivisionHost head arguments result :=
  (Applies.append_iff literalProgram definitionEquations productDivisionHost
    definitionEquations_disjoint head used arguments result).mpr computed

theorem definition_equation {head : String} {arguments : List Term} {equation : Equation}
    {environment : Env} {result : Term} (used : head ∈ definitionEquations.map Equation.head)
    (defined : definitionEquations.definesAt head arguments.length = true)
    (selected : definitionEquations.select head arguments = some (equation, environment))
    (body : Evaluates definitionProgram productDivisionHost environment equation.body result) :
    Applies definitionProgram productDivisionHost head arguments result :=
  Applies.suffix_equation definitionEquations_disjoint used defined selected body

theorem definition_apply (head : String) (used : head ∈ definitionEquations.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply definitionProgram productDivisionHost fuel head arguments =
      applyWith definitionEquations productDivisionHost (eval definitionProgram productDivisionHost fuel)
        head arguments :=
  apply_suffix_eq literalProgram definitionEquations productDivisionHost
    definitionEquations_disjoint head used fuel arguments

end Mettapedia.Languages.VibeITP.Presentation.ComputationalDefinitions
