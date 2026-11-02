import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSourceTerminalAdvance
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceStopped

/-! Zero work cannot publish a fabricated complete controller, while a
stopped machine retains its exact epoch and receipt account under a budget.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerControls

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource OCamlInstallExecution

theorem zero_not_complete (state : State) (plan standard runner epochs : Term) (quantum : Nat) :
    ¬ Runs runtime {state := state, control := (.evaluate []
      (apply "gslt:ml:advance" [number 0, number quantum, encoded (machine "MlRunning" plan standard runner epochs)]))}
      (.complete state [encoded (machine "MlComplete" plan standard runner epochs)] [] []) := by
  intro completed
  have exact := pure_returns_derivation_iff runtime [] state state _ _
    (OCamlAdvanceCall.zero_returns state quantum (machine "MlRunning" plan standard runner epochs)) state
    [encoded (machine "MlComplete" plan standard runner epochs)] [] []
  have answers := (exact.mp completed).2.1
  have same := CettaWireAtom.encode_injective _ _ (List.cons.inj answers).1
  simp [machine] at same

theorem complete_retains_history (state : State) (plan standard runner epochs : Term) (ticks quantum : Nat) :
    PureReturns runtime [] state
      (apply "gslt:ml:advance" [number ticks, number quantum, encoded (machine "MlComplete" plan standard runner epochs)]) state
      (encoded (machine "MlComplete" plan standard runner epochs)) :=
  OCamlAdvanceStopped.returns state "MlComplete" plan standard runner epochs ticks quantum (Or.inl rfl)

#print axioms zero_not_complete
#print axioms complete_retains_history

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerControls
