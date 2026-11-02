import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.NumericMultiplyExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource

/-! The word decoder's final arithmetic continuation uses exact target
multiplication and addition under any retained caller context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16ValueRecovery

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def body : Atom := .expression [.symbol "let", .var "number",
  apply "+" [.var "head", apply "*" [number 16, .var "tail"]],
  .expression [.symbol "Some", .var "number"]]

theorem recovery_returns (state : State) (caller : Subst) (head tail : Nat)
    (fresh : caller.lookup "number" = none) :
    PureReturns wordLibrary.runtime (("tail", number tail) :: ("head", number head) :: caller) state body state
      (encoded (.application "Some" [.natural (head + 16 * tail)])) := by
  apply pure_let_returns _ _ _ "number" _ (number (head + 16 * tail)) _ _ (by simpa [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup] using fresh)
  · apply natural_add_returns
    · exact bound_returns _ _ _ (by rfl)
    · apply natural_mul_returns
      · exact number_returns _ _ _ _
      · exact bound_returns _ _ _ (by rfl)
  · apply data_returns _ _ _ _ _ (by decide +kernel)
    simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, encoded, CettaWireAtom.encode,
      CettaWireAtom.encodeMany]

#print axioms recovery_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16ValueRecovery
