import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16Wire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16ValueRecovery

/-! The actual word decoder combines bounded little-endian digits using
exact integer multiplication and addition, preserving the compiler codec.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16ValueExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem values_returns (state : State) (digits : List (Fin 16)) :
    PureReturns wordLibrary.runtime [] state
      (apply "gslt:word16:value" [encoded (encodeList (fun digit : Fin 16 => Word16NibbleExecution.nibble digit.val) digits)]) state
      (encoded (.application "Some" [.natural (Nat.ofDigits 16 (digits.map Fin.val))])) := by
  induction digits with
  | nil =>
    metta_call word_checked
    metta_eval with word_checked unfolding [encodeList, Nat.ofDigits]
  | cons first rest ih =>
    have digit := Word16NibbleExecution.nibble_value_returns state first
    metta_call word_checked
    metta_eval [digit, ih] with word_checked unfolding [encodeList, Word16NibbleExecution.nibble, Nat.ofDigits]
    have recovered := Word16ValueRecovery.recovery_returns state
      [("rest", encoded (encodeList (fun digit : Fin 16 => Word16NibbleExecution.nibble digit.val) rest)),
       ("digit", encoded (Word16NibbleExecution.nibble first.val)),
       ("digits", encoded (encodeList (fun digit : Fin 16 => Word16NibbleExecution.nibble digit.val) (first :: rest)))]
      first.val (Nat.ofDigits 16 (rest.map Fin.val)) (by rfl)
    simpa [Word16ValueRecovery.body, Nat.ofDigits_cons, Word16NibbleExecution.nibble, encodeList,
      number, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using recovered

#print axioms values_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16ValueExecution
