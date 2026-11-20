import Mettapedia.Languages.MeTTa.PeTTa.BoundCalls
import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation

/-! Captured-call controls over pinned authored function equations. The
quotation reader remains a named boundary; no byte-parser adequacy is claimed. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BoundCallControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../metta/fixtures/petta_bound_calls.metta"
    sha256 "fa9de2efe213716a3eda2a62a585e9d5f287be879bf45466d4f4909b0f9bc7dc"

def program : SpaceSemantics.Program := source.program
def seven : Atom := .grounded (.int 7)
def eight : Atom := .grounded (.int 8)
def call : Atom := .expression [.var "f", seven]
def expression : Atom := .expression [.symbol "let", .var "f", .symbol "bound-call:increment", call]
def initial : Configuration := start Effects.empty expression

def readout : Outcome → Option (List Atom × List Atom × List Atom)
  | .complete _ answers input output => some (answers, input, output)
  | _ => none

private def returnedState : Outcome → Effects.State
  | .complete state _ _ _ => state
  | _ => Effects.empty

private theorem empty_store (state : Effects.State)
    (core : state.core = []) (allocation : state.next = 0)
    (spaces : ∀ index, state.spaces index = [])
    (cells : ∀ name, state.cells name = none)
    (named : state.namedSpaces = []) (fallback : state.namedEmpty = []) : state = Effects.empty := by
  cases state with
  | mk stored next privateSpaces privateCells namedSpaces namedEmpty =>
    simp only at core allocation spaces cells named fallback
    subst stored next namedSpaces namedEmpty
    have spacesEq : privateSpaces = fun _ => [] := funext spaces
    have cellsEq : privateCells = fun _ => none := funext cells
    subst privateSpaces privateCells
    rfl

private theorem exact_outcome (result : Outcome) (state : Effects.State)
    (answers input output : List Atom) (store : returnedState result = state)
    (observed : readout result = some (answers, input, output)) :
    result = .complete state answers input output := by
  cases result with
  | complete actual values pending printed =>
    simp only [readout, Option.some.injEq, Prod.mk.injEq] at observed
    rcases observed with ⟨rfl, rfl, rfl⟩
    simp only [returnedState] at store
    rw [store]
  | exhausted residual => simp [readout] at observed
  | fault reason faulted => simp [readout] at observed

theorem source_equations : program.equations =
    [⟨"bound-call:increment", [.var "x"], .expression [.symbol "+", .var "x", .grounded (.int 1)]⟩,
     ⟨"bound-call:decrement", [.var "x"], .expression [.symbol "-", .var "x", .grounded (.int 1)]⟩] := rfl

/-- A kernel-checked witness of the original fragment boundary. The same
authored expression is data there, rather than an executed captured call. -/
theorem original_fragment_returns_data :
    Eval.run program 40 initial =
      .complete Effects.empty [.expression [.symbol "bound-call:increment", seven]] [] [] := by
  cbv

theorem captured_call_returns :
    BoundCalls.run program 40 initial = .complete Effects.empty [eight] [] [] := by
  apply exact_outcome
  · apply empty_store
    · decide +kernel
    · decide +kernel
    · intro index
      run_tac do
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          goal.assign (← Lean.Meta.mkDecideProof (← goal.getType))
    · intro name
      run_tac do
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          goal.assign (← Lean.Meta.mkDecideProof (← goal.getType))
    · decide +kernel
    · decide +kernel
  · decide +kernel

theorem captured_call_path :
    (BoundCalls.theory program).MultiStep initial (finished Effects.empty [eight] [] []) :=
  BoundCalls.completed_has_path program 40 initial Effects.empty [eight] [] [] captured_call_returns

def residual : Configuration :=
  { state := Effects.empty, control := .returned [.symbol "bound-call:increment"],
    frames := [.bind [] (.var "f") call] }

theorem pause_keeps_binding : BoundCalls.run program 2 initial = .exhausted residual := by rfl

theorem resume_agrees :
    BoundCalls.run program 38 residual = BoundCalls.run program 40 initial :=
  (BoundCalls.run_resume program 2 38 initial residual pause_keeps_binding).symm

theorem resume_returns :
    BoundCalls.run program 38 residual = .complete Effects.empty [eight] [] [] :=
  resume_agrees.trans captured_call_returns


/-- Keeping only a source expression loses the binding-bearing continuation. -/
theorem bare_call_loses_binding :
    readout (BoundCalls.run program 38 (start Effects.empty call)) ≠
      readout (BoundCalls.run program 38 residual) := by decide +kernel

def repeated : Atom := .expression [.symbol "let", .var "f", .symbol "bound-call:increment",
  .expression [.var "f", .expression [.symbol "superpose", .expression [seven, seven]]]]

theorem duplicate_answers_retained :
    readout (BoundCalls.run program 80 (start Effects.empty repeated)) = some ([eight, eight], [], []) := by
  decide +kernel

/-- Frozen declarations determine whether a captured symbol is callable.
Inert unknown heads are not granted code authority by a variable spelling. -/
theorem unknown_head_not_admitted :
    BoundCalls.target program (.evaluate [("f", .symbol "unknown") ] call) = none := by rfl

def unknownStart : Configuration :=
  { state := Effects.empty,
    control := .evaluate [("f", .symbol "unknown")] call }

def quotedStart : Configuration :=
  { state := Effects.empty,
    control := .evaluate [("f", .symbol "bound-call:increment")]
      (.expression [.symbol "quote", call]) }

theorem unknown_call_stays_data :
    readout (BoundCalls.run program 40 unknownStart) =
      some ([.expression [.symbol "unknown", seven]], [], []) := by decide +kernel

theorem quotation_stays_data :
    readout (BoundCalls.run program 40 quotedStart) =
      some ([.expression [.symbol "bound-call:increment", seven]], [], []) := by decide +kernel

def rawProgram : SpaceSemantics.Program :=
  { equations := program.equations,
    declarations := [.expression [.symbol ":", .symbol "bound-call:increment",
      .expression [.symbol "->", .symbol "Atom", .symbol "%Undefined%"]]] }

theorem raw_domain_not_admitted :
    BoundCalls.target rawProgram (.evaluate [("f", .symbol "bound-call:increment")] call) = none := by rfl

theorem unsaturated_not_admitted :
    BoundCalls.target program (.evaluate [("f", .symbol "bound-call:increment")]
      (.expression [.var "f"])) = none := by rfl

def printing : Configuration :=
  { state := Effects.empty,
    control := .arguments [] (.function "println!") [] [.grounded (.string "once")] 1,
    frames := [.collect] }
def printed : Configuration :=
  { state := Effects.empty, control := .returned [Effects.boolean true],
    frames := [.collect], output := [.grounded (.string "once")] }

theorem pause_keeps_output : BoundCalls.run program 1 printing = .exhausted printed := by rfl

theorem output_not_repeated : BoundCalls.run program 1 printed =
    .complete Effects.empty [.expression [Effects.boolean true]] [] [.grounded (.string "once")] := by rfl

end Mettapedia.Languages.MeTTa.PeTTa.BoundCallControls
