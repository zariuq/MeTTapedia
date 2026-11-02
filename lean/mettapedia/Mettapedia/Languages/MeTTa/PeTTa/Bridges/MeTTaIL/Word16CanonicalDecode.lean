import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16ValueExecution

/-! Canonical compiler words decode to their original natural number
through the loaded hexadecimal value helper.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16CanonicalDecode

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource

def boundedDigits (number : Nat) : List (Fin 16) :=
  (Nat.digits 16 number).attach.map fun digit => ⟨digit.val, Nat.digits_lt_base (by decide) digit.property⟩

theorem digit_values (number : Nat) : (boundedDigits number).map Fin.val = Nat.digits 16 number := by
  simp [boundedDigits, List.map_map]

theorem digit_terms (number : Nat) :
    encodeList (fun digit : Fin 16 => Word16NibbleExecution.nibble digit.val) (boundedDigits number) =
      Word16Wire.digitsTerm number := by
  have same := congrArg (encodeList Word16NibbleExecution.nibble) (digit_values number)
  simpa only [encodeList_map, Word16Wire.digitsTerm, Function.comp_def] using same

theorem value_returns (state : State) (number : Nat) :
    PureReturns wordLibrary.runtime [] state (apply "gslt:word16:value" [encoded (Word16Wire.digitsTerm number)]) state
      (encoded (.application "Some" [.natural number])) := by
  have returned := Word16ValueExecution.values_returns state (boundedDigits number)
  rw [digit_values, Nat.ofDigits_digits, digit_terms] at returned
  exact returned

#print axioms value_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16CanonicalDecode
