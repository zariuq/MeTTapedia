import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSearchWireExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlValuesExecution

/-! The common list-length helper transports into the loaded OCaml runtime.
Its application to decoded fields preserves the compiler's tuple arity.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlListLength

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem length_returns {α : Type} (element : α → Term) (state : State) (items : List α) :
    PureReturns runtime [] state (apply "gslt:automata:length" [encoded (encodeList element items)]) state
      (number items.length) := by
  have runner := runner_from_base% ["xs"] (CompleteExecution.complete_length_returns element state items)
    using RetainedMatchingWire.scopedPrimitive_agreement
  through_ocaml ["xs"] runner

theorem fields_length_returns (state : State) (items : List OCaml.Value) :
    PureReturns runtime [] state (apply "gslt:automata:length" [encoded (OCamlValuesExecution.valuesTerm items)]) state
      (number items.length) :=
  length_returns _ state items

#print axioms length_returns
#print axioms fields_length_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlListLength
