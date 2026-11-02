import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16NibbleExecution
import Mettapedia.Languages.MeTTa.PeTTa.BridgeDemand

/-! Hexadecimal nibble selection composes with the actual evaluated
numeric argument, including captured remainder variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16NibbleCall

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem argument_returns (caller : Subst) (state : State) (argument : Atom) (digit : Fin 16)
    (computed : PureReturns wordLibrary.runtime caller state argument state (number digit.val)) :
    PureReturns wordLibrary.runtime caller state (apply "gslt:word16:nibble" [argument]) state
      (encoded (Word16NibbleExecution.nibble digit.val)) := by
  apply authored_demand_call_returns wordLibrary.runtime caller [] state state state "gslt:word16:nibble"
    [argument] [number digit.val] _ _ (by decide) (by decide) (by decide +kernel) (by decide)
  · exact ArgumentsReturn.evaluated (by decide +kernel) computed (.nil _ _)
  · exact Word16NibbleExecution.nibble_clauses digit
  · exact Word16NibbleExecution.nibble_data state digit.val

#print axioms argument_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16NibbleCall
