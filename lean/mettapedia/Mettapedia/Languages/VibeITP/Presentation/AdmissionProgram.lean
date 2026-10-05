import Mettapedia.Languages.VibeITP.Presentation.AdmissionState
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramSuffix

/-!
# Authored static declaration and theory-run equations

Fresh identities are selected by the state, not by a supplied declaration.
Axiom phase, formation and closedness guards precede the append. Definition
checking precedes allocation and publication. List replication and ordered
append are authored traversals over the existing scalar/list primitives.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalAdmission

open ComputationalData ComputationalShift ComputationalDefinitions ComputationalProofs
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def slot (name : String) : Term := .var name
private def equation (name head : String) (arguments : List Term) (body : Term) : Equation :=
  ⟨name, head, arguments, body⟩
private def someResult (value : Term) : Term := call "Some" [value]
private def stateData (phase identity table axioms definitions : Term) : Term :=
  .list [.sym "Vibe:Admission", phase, identity, table, axioms, definitions]
private def statePattern : Term :=
  stateData (slot "phase") (slot "identity") (slot "table") (slot "axioms") (slot "definitions")
private def fresh : Term := .list [.sym "Fresh", slot "identity"]

def admissionEquations : Program := [
  equation "admission-snoc" "vibe:admission-snoc" [slot "items", slot "last"]
    (call "vibe:admission-snoc-view" [call "nik:list-view" [slot "items"], slot "last"]),
  equation "admission-snoc-empty" "vibe:admission-snoc-view" [.sym "List:Nil", slot "last"]
    (.list [slot "last"]),
  equation "admission-snoc-cons" "vibe:admission-snoc-view"
    [call "List:Cons" [slot "first", slot "rest"], slot "last"]
    (call "nik:list-cons" [slot "first", call "vibe:admission-snoc" [slot "rest", slot "last"]]),
  equation "admission-zeros" "vibe:admission-zeros" [slot "count"]
    (call "vibe:admission-zeros-test" [call "nik:nat-zero" [slot "count"], slot "count"]),
  equation "admission-zeros-empty" "vibe:admission-zeros-test" [.sym "True", slot "count"] (.list []),
  equation "admission-zeros-step" "vibe:admission-zeros-test" [.sym "False", slot "count"]
    (call "nik:list-cons" [natural 0, call "vibe:admission-zeros" [call "nik:nat-pred" [slot "count"]]]),
  equation "admission-allocate" "vibe:admission-allocate" [statePattern, slot "kind", slot "binders"]
    (someResult (stateData (slot "phase") (call "nik:nat-add" [slot "identity", natural 1])
      (call "nik:list-cons" [call "Vibe:Binding" [fresh, slot "kind", slot "binders"], slot "table"])
      (slot "axioms") (slot "definitions"))),
  equation "admission-fvar" "vibe:admit" [statePattern, .list [.sym "Declare:Fvar", slot "arity"]]
    (call "vibe:admission-allocate" [statePattern, .sym "Fvar", call "vibe:admission-zeros" [slot "arity"]]),
  equation "admission-constant" "vibe:admit"
    [statePattern, .list [.sym "Declare:Constant", slot "binders"]]
    (call "vibe:admission-allocate" [statePattern, .sym "Constant", slot "binders"]),
  equation "admission-axiom-setup" "vibe:admit"
    [stateData (.sym "Setup") (slot "identity") (slot "table") (slot "axioms") (slot "definitions"),
      .list [.sym "Declare:Axiom", slot "statement"]]
    (call "vibe:admission-axiom-wf" [call "vibe:well-formed" [slot "table", slot "statement"],
      slot "identity", slot "table", slot "axioms", slot "definitions", slot "statement"]),
  equation "admission-axiom-proof-phase" "vibe:admit"
    [stateData (.sym "Proofs") (slot "identity") (slot "table") (slot "axioms") (slot "definitions"),
      .list [.sym "Declare:Axiom", slot "statement"]] (.sym "None"),
  equation "admission-axiom-malformed" "vibe:admission-axiom-wf"
    [.sym "False", slot "identity", slot "table", slot "axioms", slot "definitions", slot "statement"] (.sym "None"),
  equation "admission-axiom-formed" "vibe:admission-axiom-wf"
    [.sym "True", slot "identity", slot "table", slot "axioms", slot "definitions", slot "statement"]
    (call "vibe:admission-axiom-closed" [call "nik:nat-zero" [call "vibe:depth" [slot "table", slot "statement"]],
      slot "identity", slot "table", slot "axioms", slot "definitions", slot "statement"]),
  equation "admission-axiom-open" "vibe:admission-axiom-closed"
    [.sym "False", slot "identity", slot "table", slot "axioms", slot "definitions", slot "statement"] (.sym "None"),
  equation "admission-axiom-append" "vibe:admission-axiom-closed"
    [.sym "True", slot "identity", slot "table", slot "axioms", slot "definitions", slot "statement"]
    (someResult (stateData (.sym "Setup") (slot "identity") (slot "table")
      (call "vibe:admission-snoc" [slot "axioms", slot "statement"]) (slot "definitions"))),
  equation "admission-definition-check" "vibe:admit"
    [statePattern, .list [.sym "Declare:Definition", slot "parameters", slot "hints", slot "body"]]
    (call "vibe:admission-definition-result"
      [call "vibe:definition-query" [slot "table", fresh, slot "parameters", slot "hints", slot "body"],
        statePattern, slot "parameters", slot "body"]),
  equation "admission-definition-refused" "vibe:admission-definition-result"
    [.sym "None", slot "state", slot "parameters", slot "body"] (.sym "None"),
  equation "admission-definition-checked" "vibe:admission-definition-result"
    [someResult (slot "equation"), statePattern, slot "parameters", slot "body"]
    (call "vibe:admission-definition-info"
      [call "vibe:def-info" [slot "table", slot "parameters"] , statePattern, slot "parameters", slot "body"]),
  equation "admission-definition-info-refused" "vibe:admission-definition-info"
    [.sym "None", slot "state", slot "parameters", slot "body"] (.sym "None"),
  equation "admission-definition-publish" "vibe:admission-definition-info"
    [someResult (call "Vibe:SymInfo" [.sym "Constant", slot "binders"]), statePattern, slot "parameters", slot "body"]
    (someResult (stateData (slot "phase") (call "nik:nat-add" [slot "identity", natural 1])
      (call "nik:list-cons" [call "Vibe:Binding" [fresh, .sym "Constant", slot "binders"], slot "table"])
      (slot "axioms") (call "vibe:admission-snoc" [slot "definitions", .list [fresh, slot "parameters", slot "body"]]))),
  equation "admission-enter-proofs" "vibe:admit" [statePattern, .list [.sym "Declare:Proofs"]]
    (someResult (stateData (.sym "Proofs") (slot "identity") (slot "table") (slot "axioms") (slot "definitions"))),
  equation "admission-unknown-declaration" "vibe:admit" [slot "state", slot "unknown"] (.sym "None"),
  equation "admission-run" "vibe:admission-run" [slot "state", slot "declarations"]
    (call "vibe:admission-run-view" [call "nik:list-view" [slot "declarations"], slot "state"]),
  equation "admission-run-empty" "vibe:admission-run-view" [.sym "List:Nil", slot "state"] (someResult (slot "state")),
  equation "admission-run-step" "vibe:admission-run-view"
    [call "List:Cons" [slot "first", slot "rest"], slot "state"]
    (call "vibe:admission-run-next" [call "vibe:admit" [slot "state", slot "first"], slot "rest"]),
  equation "admission-run-refused" "vibe:admission-run-next" [.sym "None", slot "rest"] (.sym "None"),
  equation "admission-run-tail" "vibe:admission-run-next" [someResult (slot "state"), slot "rest"]
    (call "vibe:admission-run" [slot "state", slot "rest"]),
  equation "admission-check" "vibe:check-admitted" [slot "state", slot "declarations", slot "witness", slot "claimed"]
    (call "vibe:check-admitted-result" [call "vibe:admission-run" [slot "state", slot "declarations"] ,
      slot "witness", slot "claimed"]),
  equation "admission-check-refused" "vibe:check-admitted-result" [.sym "None", slot "witness", slot "claimed"] (.sym "False"),
  equation "admission-check-theory" "vibe:check-admitted-result" [someResult statePattern, slot "witness", slot "claimed"]
    (call "vibe:check-proof" [slot "table", slot "axioms", slot "definitions", slot "witness", slot "claimed"]),
  equation "admission-from-initial" "vibe:admission-start" [slot "declarations"]
    (call "vibe:admission-run" [encodeState initialAdmission, slot "declarations"]),
  equation "static-proof-from-initial" "vibe:check-static" [slot "declarations", slot "witness", slot "claimed"]
    (call "vibe:check-admitted" [encodeState initialAdmission, slot "declarations", slot "witness", slot "claimed"]) ]

def admissionProgram : Program := proofProgram ++ admissionEquations

theorem admissionEquations_disjoint :
    ∀ equation ∈ admissionEquations, equation.head ∉ proofProgram.calledHeads := by
  have freshHeads : admissionEquations.all (fun equation => decide (equation.head ∉ proofProgram.calledHeads)) = true :=
    by decide +kernel
  intro equation member
  simpa using List.all_eq_true.mp freshHeads equation member

theorem admissionProgram_leftLinear : LeftLinear admissionProgram := by
  have additional : LeftLinear admissionEquations := by
    simp [LeftLinear, admissionEquations, equation, call, slot, someResult, stateData, statePattern, fresh,
      patternVarsList, patternVars]
  intro equation member
  rcases List.mem_append.mp member with previous | added
  · exact proofProgram_leftLinear equation previous
  · exact additional equation added

theorem admissionProgram_dataSeparated : DataSeparated admissionProgram productDivisionHost where
  undefined := by
    intro head member
    have previous := proofProgram_dataSeparated.undefined head member
    have added : admissionEquations.defines head = false := by
      simp [constructorHeads] at member
      rcases member with rfl | rfl | rfl <;> simp [Program.defines, admissionEquations, equation]
    change (proofProgram ++ admissionEquations).any _ = false
    rw [List.any_append]
    change (proofProgram.defines head || admissionEquations.defines head) = false
    rw [previous, added]
    rfl
  unhandled := proofProgram_dataSeparated.unhandled

theorem reuse_proof_call {head : String} {arguments : List Term} {result : Term}
    (used : head ∈ proofProgram.calledHeads) (computed : Applies proofProgram productDivisionHost head arguments result) :
    Applies admissionProgram productDivisionHost head arguments result :=
  (Applies.append_iff proofProgram admissionEquations productDivisionHost
    admissionEquations_disjoint head used arguments result).mpr computed

theorem admission_equation {head : String} {arguments : List Term} {equation : Equation}
    {environment : Env} {result : Term} (used : head ∈ admissionEquations.map Equation.head)
    (defined : admissionEquations.definesAt head arguments.length = true)
    (selected : admissionEquations.select head arguments = some (equation, environment))
    (body : Evaluates admissionProgram productDivisionHost environment equation.body result) :
    Applies admissionProgram productDivisionHost head arguments result :=
  Applies.suffix_equation admissionEquations_disjoint used defined selected body

theorem admission_apply (head : String) (used : head ∈ admissionEquations.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply admissionProgram productDivisionHost fuel head arguments =
      applyWith admissionEquations productDivisionHost (eval admissionProgram productDivisionHost fuel) head arguments :=
  apply_suffix_eq proofProgram admissionEquations productDivisionHost admissionEquations_disjoint head used fuel arguments

end Mettapedia.Languages.VibeITP.Presentation.ComputationalAdmission
