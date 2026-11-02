import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerReadout
import Mettapedia.Languages.MeTTa.PeTTa.BridgeDemandLibrary

/-! Stopped controller ticks preserve the complete machine. The machine
argument is captured raw and the quantum is evaluated as declared Number,
using the common mixed-demand call theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTickStopped

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlInstallExecution

private theorem body_returns (state : State) (phase : String) (plan standard runner epochs : Term) (quantum : Nat)
    (stopped : phase = "MlComplete" ∨ phase = "MlBlocked") :
    PureReturns runtime (Library.bind ["machine", "quantum"]
      [encoded (machine phase plan standard runner epochs), number quantum]) state
      (library.body "gslt:ml:tick") state (encoded (machine phase plan standard runner epochs)) := by
  metta_literal
  rcases stopped with rfl | rfl <;> metta_eval with checked unfolding [machine, Library.bind]

theorem stopped_tick_returns (state : State) (phase : String) (plan standard runner epochs : Term) (quantum : Nat)
    (stopped : phase = "MlComplete" ∨ phase = "MlBlocked") :
    PureReturns runtime [] state
      (apply "gslt:ml:tick" [encoded (machine phase plan standard runner epochs), number quantum]) state
      (encoded (machine phase plan standard runner epochs)) := by
  have present : (library.equationOf "gslt:ml:tick").isSome = true := by decide +kernel
  obtain ⟨row, found⟩ := Option.isSome_iff_exists.mp present
  have ready : Library.demandReady library row = true := by
    have checkedRow : ((library.equationOf "gslt:ml:tick").map (Library.demandReady library)).getD false = true := by decide +kernel
    simpa only [found, Option.map_some, Option.getD_some] using checkedRow
  have collected : ArgumentsReturn runtime [] "gslt:ml:tick" 0 state
      [encoded (machine phase plan standard runner epochs), number quantum] state
      [encoded (machine phase plan standard runner epochs), number quantum] := by
    have result := ArgumentsReturn.raw (program := runtime) (caller := []) (head := "gslt:ml:tick") (index := 0)
      (argument := encoded (machine phase plan standard runner epochs))
      (by decide +kernel)
      (ArgumentsReturn.evaluated (program := runtime) (caller := []) (head := "gslt:ml:tick") (index := 1)
        (by decide +kernel) (number_returns runtime [] state quantum) (.nil _ _))
    simpa only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil] using result
  exact Library.demand_call checked found ready [] state state state
    [encoded (machine phase plan standard runner epochs), number quantum]
    [encoded (machine phase plan standard runner epochs), number quantum] _ rfl collected
    (body_returns state phase plan standard runner epochs quantum stopped)

theorem complete_tick_returns (state : State) (plan standard runner epochs : Term) (quantum : Nat) :
    PureReturns runtime [] state
      (apply "gslt:ml:tick" [encoded (machine "MlComplete" plan standard runner epochs), number quantum]) state
      (encoded (machine "MlComplete" plan standard runner epochs)) :=
  stopped_tick_returns state "MlComplete" plan standard runner epochs quantum (Or.inl rfl)

theorem blocked_tick_returns (state : State) (plan standard runner epochs : Term) (quantum : Nat) :
    PureReturns runtime [] state
      (apply "gslt:ml:tick" [encoded (machine "MlBlocked" plan standard runner epochs), number quantum]) state
      (encoded (machine "MlBlocked" plan standard runner epochs)) :=
  stopped_tick_returns state "MlBlocked" plan standard runner epochs quantum (Or.inr rfl)

#print axioms stopped_tick_returns
#print axioms complete_tick_returns
#print axioms blocked_tick_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTickStopped
