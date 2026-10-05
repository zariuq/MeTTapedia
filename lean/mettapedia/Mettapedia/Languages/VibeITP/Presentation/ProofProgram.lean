import Mettapedia.Languages.VibeITP.Presentation.ProofWitness

/-!
# Authored checking of whole supplied Vibe proofs

Ordered theory entries and proof children are ordinary data. The equations
select actual declarations, propagate completed refusals and reuse the
previously verified static operations. The host remains generic arithmetic
and list operations; neither witness checking nor derivability is a primitive.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalProofs

open ComputationalData ComputationalShift ComputationalInference ComputationalLiterals ComputationalDefinitions
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def theoryOf (table : SignatureTable) (axioms : List Spec.Term) (definitions : List Spec.Definition) : Spec.Theory :=
  ⟨signatureOf table, axioms, definitions⟩

def encodeDefinition (declaration : Spec.Definition) : Term :=
  .list [encodeSymbol declaration.symbol, encodeSymbols declaration.fvars, encode declaration.value]

def encodeDefinitions (declarations : List Spec.Definition) : Term := .list (declarations.map encodeDefinition)

def encodeAxioms (axioms : List Spec.Term) : Term := .list (axioms.map encode)

def encodeAccessResult : Option Term → Term
  | none => .sym "None"
  | some value => .expr [.sym "Some", value]

def encodeWitness : ProofWitness → Term
  | .axiom index => .list [.sym "Proof:Axiom", natural index]
  | .definition index hints => .list [.sym "Proof:Definition", natural index, encodeBinders hints]
  | .modusPonens implication premise =>
      .list [.sym "Proof:MP", encodeWitness implication, encodeWitness premise]
  | .instantiate symbol value child =>
      .list [.sym "Proof:Instantiate", encodeSymbol symbol, encode value, encodeWitness child]
  | .literal request => .list [.sym "Proof:Literal", encodeRequest request]

private def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def slot (name : String) : Term := .var name
private def equation (name head : String) (arguments : List Term) (body : Term) : Equation :=
  ⟨name, head, arguments, body⟩
private def someResult (value : Term) : Term := call "Some" [value]

def proofEquations : Program := [
  equation "proof-entry" "vibe:proof-at" [slot "entries", slot "index"]
    (call "vibe:proof-entry-view" [call "nik:list-view" [slot "entries"], slot "index"]),
  equation "proof-entry-missing" "vibe:proof-entry-view" [.sym "List:Nil", slot "index"] (.sym "None"),
  equation "proof-entry-cons" "vibe:proof-entry-view"
    [call "List:Cons" [slot "first", slot "rest"], slot "index"]
    (call "vibe:proof-entry-zero" [call "nik:nat-zero" [slot "index"], slot "first", slot "rest", slot "index"]),
  equation "proof-entry-first" "vibe:proof-entry-zero"
    [.sym "True", slot "first", slot "rest", slot "index"] (someResult (slot "first")),
  equation "proof-entry-later" "vibe:proof-entry-zero"
    [.sym "False", slot "first", slot "rest", slot "index"]
    (call "vibe:proof-at" [slot "rest", call "nik:nat-pred" [slot "index"]]),
  equation "proof-axiom" "vibe:proof-query"
    [slot "table", slot "axioms", slot "definitions", .list [.sym "Proof:Axiom", slot "index"]]
    (call "vibe:proof-at" [slot "axioms", slot "index"]),
  equation "proof-definition" "vibe:proof-query"
    [slot "table", slot "axioms", slot "definitions", .list [.sym "Proof:Definition", slot "index", slot "hints"]]
    (call "vibe:proof-definition" [call "vibe:proof-at" [slot "definitions", slot "index"], slot "table", slot "hints"]),
  equation "proof-definition-missing" "vibe:proof-definition"
    [.sym "None", slot "table", slot "hints"] (.sym "None"),
  equation "proof-definition-found" "vibe:proof-definition"
    [someResult (.list [slot "constant", slot "parameters", slot "body"]), slot "table", slot "hints"]
    (call "vibe:definition-query" [slot "table", slot "constant", slot "parameters", slot "hints", slot "body"]),
  equation "proof-modus-ponens" "vibe:proof-query"
    [slot "table", slot "axioms", slot "definitions", .list [.sym "Proof:MP", slot "implication", slot "premise"]]
    (call "vibe:proof-mp-first" [
      call "vibe:proof-query" [slot "table", slot "axioms", slot "definitions", slot "implication"],
      slot "table", slot "axioms", slot "definitions", slot "premise"]),
  equation "proof-missing-implication" "vibe:proof-mp-first"
    [.sym "None", slot "table", slot "axioms", slot "definitions", slot "premise"] (.sym "None"),
  equation "proof-implication-checked" "vibe:proof-mp-first"
    [someResult (slot "implication"), slot "table", slot "axioms", slot "definitions", slot "premise"]
    (call "vibe:proof-mp-second" [slot "implication",
      call "vibe:proof-query" [slot "table", slot "axioms", slot "definitions", slot "premise"]]),
  equation "proof-missing-premise" "vibe:proof-mp-second" [slot "implication", .sym "None"] (.sym "None"),
  equation "proof-premise-checked" "vibe:proof-mp-second"
    [slot "implication", someResult (slot "premise")]
    (call "vibe:modus-ponens" [slot "implication", slot "premise"]),
  equation "proof-instantiation" "vibe:proof-query"
    [slot "table", slot "axioms", slot "definitions",
      .list [.sym "Proof:Instantiate", slot "F", slot "value", slot "child"]]
    (call "vibe:proof-instantiation" [
      call "vibe:proof-query" [slot "table", slot "axioms", slot "definitions", slot "child"],
      slot "table", slot "F", slot "value"]),
  equation "proof-instantiation-missing-child" "vibe:proof-instantiation"
    [.sym "None", slot "table", slot "F", slot "value"] (.sym "None"),
  equation "proof-instantiation-checked-child" "vibe:proof-instantiation"
    [someResult (slot "statement"), slot "table", slot "F", slot "value"]
    (call "vibe:thm-instantiate" [slot "table", slot "F", slot "value", slot "statement"]),
  equation "proof-literal" "vibe:proof-query"
    [slot "table", slot "axioms", slot "definitions", .list [.sym "Proof:Literal", slot "request"]]
    (call "vibe:literal-query" [slot "request"]),
  equation "proof-unknown-shape" "vibe:proof-query"
    [slot "table", slot "axioms", slot "definitions", slot "unknown"] (.sym "None"),
  equation "proof-check" "vibe:check-proof"
    [slot "table", slot "axioms", slot "definitions", slot "witness", slot "claimed"]
    (call "vibe:proof-check-result" [
      call "vibe:proof-query" [slot "table", slot "axioms", slot "definitions", slot "witness"], slot "claimed"]),
  equation "proof-check-refused" "vibe:proof-check-result" [.sym "None", slot "claimed"] (.sym "False"),
  equation "proof-check-computed" "vibe:proof-check-result" [someResult (slot "actual"), slot "claimed"]
    (call "vibe:term-eq" [slot "actual", slot "claimed"]) ]

def proofProgram : Program := definitionProgram ++ proofEquations

theorem proofEquations_disjoint :
    ∀ equation ∈ proofEquations, equation.head ∉ definitionProgram.calledHeads := by
  have fresh : proofEquations.all (fun equation =>
      decide (equation.head ∉ definitionProgram.calledHeads)) = true := by decide +kernel
  intro equation member
  simpa using List.all_eq_true.mp fresh equation member

theorem proofProgram_leftLinear : LeftLinear proofProgram := by
  have additional : LeftLinear proofEquations := by
    simp [LeftLinear, proofEquations, equation, call, slot, someResult, patternVarsList, patternVars]
  intro equation member
  rcases List.mem_append.mp member with old | added
  · exact definitionProgram_leftLinear equation old
  · exact additional equation added

theorem proofProgram_dataSeparated : DataSeparated proofProgram productDivisionHost where
  undefined := by
    intro head member
    have old := definitionProgram_dataSeparated.undefined head member
    have added : proofEquations.defines head = false := by
      simp [constructorHeads] at member
      rcases member with rfl | rfl | rfl <;> simp [Program.defines, proofEquations, equation]
    change (definitionProgram ++ proofEquations).any _ = false
    rw [List.any_append]
    change (definitionProgram.defines head || proofEquations.defines head) = false
    rw [old, added]
    rfl
  unhandled := definitionProgram_dataSeparated.unhandled

theorem reuse_definition_call {head : String} {arguments : List Term} {result : Term}
    (used : head ∈ definitionProgram.calledHeads)
    (computed : Applies definitionProgram productDivisionHost head arguments result) :
    Applies proofProgram productDivisionHost head arguments result :=
  (Applies.append_iff definitionProgram proofEquations productDivisionHost
    proofEquations_disjoint head used arguments result).mpr computed

theorem proof_equation {head : String} {arguments : List Term} {equation : Equation}
    {environment : Env} {result : Term} (used : head ∈ proofEquations.map Equation.head)
    (defined : proofEquations.definesAt head arguments.length = true)
    (selected : proofEquations.select head arguments = some (equation, environment))
    (body : Evaluates proofProgram productDivisionHost environment equation.body result) :
    Applies proofProgram productDivisionHost head arguments result :=
  Applies.suffix_equation proofEquations_disjoint used defined selected body

theorem proof_apply (head : String) (used : head ∈ proofEquations.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply proofProgram productDivisionHost fuel head arguments =
      applyWith proofEquations productDivisionHost (eval proofProgram productDivisionHost fuel)
        head arguments :=
  apply_suffix_eq definitionProgram proofEquations productDivisionHost proofEquations_disjoint head used fuel arguments

end Mettapedia.Languages.VibeITP.Presentation.ComputationalProofs
