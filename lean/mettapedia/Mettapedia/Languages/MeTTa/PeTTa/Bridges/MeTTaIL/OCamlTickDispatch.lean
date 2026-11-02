import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTickStopped

/-! Actual controller ticks dispatch on the retained runner phase. Running
search uses its declared Number quantum; settled service dispatch retains
the whole runner and epoch history.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTickDispatch

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlInstallExecution

theorem call_returns (state : State) (input answer : Term) (quantum : Nat)
    (bodyReturned : PureReturns runtime (Library.bind ["machine", "quantum"] [encoded input, number quantum]) state
      (library.body "gslt:ml:tick") state (encoded answer)) :
    PureReturns runtime [] state (apply "gslt:ml:tick" [encoded input, number quantum]) state (encoded answer) := by
  have present : (library.equationOf "gslt:ml:tick").isSome = true := by decide +kernel
  obtain ⟨row, found⟩ := Option.isSome_iff_exists.mp present
  have ready : Library.demandReady library row = true := by
    have checkedRow : ((library.equationOf "gslt:ml:tick").map (Library.demandReady library)).getD false = true := by decide +kernel
    simpa only [found, Option.map_some, Option.getD_some] using checkedRow
  apply Library.demand_call checked found ready [] state state state [encoded input, number quantum]
    [encoded input, number quantum] _ (by metta_literal; rfl)
  · have result := ArgumentsReturn.raw (program := runtime) (caller := []) (head := "gslt:ml:tick") (index := 0)
      (argument := encoded input) (by decide +kernel)
      (ArgumentsReturn.evaluated (program := runtime) (caller := []) (head := "gslt:ml:tick") (index := 1)
        (by decide +kernel) (number_returns runtime [] state quantum) (.nil _ _))
    simpa only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, OCamlControllerSource.runtime] using result
  · exact bodyReturned

theorem running_returns (state : State) (plan standard source query states receipts epochs next : Term) (quantum : Nat)
    (ticked : PureReturns runtime [] state
      (apply "gslt:runner:tick" [encoded (.symbol "ClassSearch"), encoded plan, encoded standard,
        encoded (.application "ClassMachine" [.symbol "ClassRunning", source, query, states, receipts]), number quantum]) state
      (encoded next)) :
    PureReturns runtime [] state
      (apply "gslt:ml:tick" [encoded (machine "MlRunning" plan standard
        (.application "ClassMachine" [.symbol "ClassRunning", source, query, states, receipts]) epochs), number quantum]) state
      (encoded (machine "MlRunning" plan standard next epochs)) := by
  apply call_returns
  metta_literal
  metta_eval [ticked] with checked unfolding [machine]

theorem settled_returns (state : State) (plan standard source query states receipts epochs answer : Term) (quantum : Nat)
    (serviced : PureReturns runtime [] state
      (apply "gslt:ml:service" [encoded plan, encoded standard, encoded (doneRunner source query states receipts), encoded epochs]) state
      (encoded answer)) :
    PureReturns runtime [] state
      (apply "gslt:ml:tick" [encoded (machine "MlRunning" plan standard (doneRunner source query states receipts) epochs), number quantum]) state
      (encoded answer) := by
  apply call_returns
  metta_literal
  metta_eval [serviced] with checked unfolding [machine, doneRunner]

theorem blocked_returns (state : State) (plan standard source query states receipts epochs : Term) (quantum : Nat) :
    let runner := Term.application "ClassMachine" [.symbol "ClassBlocked", source, query, states, receipts]
    PureReturns runtime [] state
      (apply "gslt:ml:tick" [encoded (machine "MlRunning" plan standard runner epochs), number quantum]) state
      (encoded (machine "MlBlocked" plan standard runner epochs)) := by
  apply call_returns
  metta_literal
  metta_eval with checked unfolding [machine]

#print axioms call_returns
#print axioms running_returns
#print axioms settled_returns
#print axioms blocked_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTickDispatch
