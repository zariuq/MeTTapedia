import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureInstall

/-! The actual install source preserves the old plan and runner as an
immutable epoch. Its calls to table extension and fresh runner creation
retain their independent operational contracts.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlInstallExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def doneRunner (source query states receipts : Term) : Term :=
  .application "ClassMachine" [.symbol "ClassDone", source, query, states, receipts]

def machine (phase : String) (plan standard runner epochs : Term) : Term :=
  .application "MlMachine" [.symbol phase, plan, standard, runner, epochs]

theorem install_returns (state : State) (oldPlan nextPlan standard source query states receipts epochs row fresh : Term)
    (appended : PureReturns runtime [] state
      (apply "gslt:provider-cache:append" [encoded oldPlan, encoded (encodeList id [row])]) state
      (encoded (.application "Some" [nextPlan])))
    (begun : PureReturns runtime [] state
      (apply "gslt:runner:begin" [encoded (.symbol "ClassSearch"), encoded nextPlan, encoded standard, encoded source]) state
      (encoded fresh)) :
    PureReturns runtime [] state
      (apply "gslt:ml:install" [encoded oldPlan, encoded standard, encoded (doneRunner source query states receipts),
        encoded epochs, encoded row]) state
      (encoded (machine "MlRunning" nextPlan standard fresh
        (.application "LCons" [.application "MlEpoch" [oldPlan, doneRunner source query states receipts], epochs]))) := by
  metta_call checked
  metta_eval [appended, begun] with checked unfolding [doneRunner, machine, encodeList]

#print axioms install_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlInstallExecution
