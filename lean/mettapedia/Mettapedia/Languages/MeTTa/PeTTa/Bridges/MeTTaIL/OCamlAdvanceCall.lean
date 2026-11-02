import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTickStopped
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgePassiveCapture

/-! Advance has two evaluated numeric arguments and one raw machine.
Its public call uses precisely those declared demands.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceCall

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem returns (state : State) (ticks quantum : Nat) (input answer : Term)
    (bodyReturned : PureReturns runtime (Library.bind ["ticks", "quantum", "machine"]
      [number ticks, number quantum, encoded input]) state (library.body "gslt:ml:advance") state (encoded answer)) :
    PureReturns runtime [] state (apply "gslt:ml:advance" [number ticks, number quantum, encoded input]) state (encoded answer) := by
  have present : (library.equationOf "gslt:ml:advance").isSome = true := by decide +kernel
  obtain ⟨row, found⟩ := Option.isSome_iff_exists.mp present
  have ready : Library.demandReady library row = true := by
    have checkedRow : ((library.equationOf "gslt:ml:advance").map (Library.demandReady library)).getD false = true := by decide +kernel
    simpa only [found, Option.map_some, Option.getD_some] using checkedRow
  apply Library.demand_call checked found ready [] state state state [number ticks, number quantum, encoded input]
    [number ticks, number quantum, encoded input] _ (by metta_literal; rfl)
  · have collected := ArgumentsReturn.evaluated (program := runtime) (caller := []) (head := "gslt:ml:advance") (index := 0)
      (by decide +kernel) (number_returns runtime [] state ticks)
      (.evaluated (by decide +kernel) (number_returns runtime [] state quantum)
        (ArgumentsReturn.raw (argument := encoded input) (by decide +kernel) (.nil _ _)))
    simpa only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, OCamlControllerSource.runtime] using collected
  · exact bodyReturned

theorem zero_returns (state : State) (quantum : Nat) (input : Term) :
    PureReturns runtime [] state (apply "gslt:ml:advance" [number 0, number quantum, encoded input]) state (encoded input) := by
  apply returns
  metta_literal
  metta_eval with checked

#print axioms returns
#print axioms zero_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceCall
