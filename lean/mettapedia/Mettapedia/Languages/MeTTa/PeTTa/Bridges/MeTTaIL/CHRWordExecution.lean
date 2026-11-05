import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRControllerSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.NumericMultiplyExecution
import Mathlib.Data.Nat.Digits.Defs
import Std.Data.String.ToNat

/-! The controller reads canonical occurrence and integer digits using
its actual loaded source. The value is numeric, rather than an ordering of
the printed nibble names. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRWordExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit CHRControllerSource

def nibble (digit : Nat) : Term := .application "PApp" [.string ("R16Nibble" ++ toString digit), .symbol "LNil"]
def digitsTerm (digits : List (Fin 16)) : Term := encodeList (fun digit => nibble digit.val) digits

private theorem selected (digit : Fin 16) :
    ((List.range 16).map (fun n => SpaceSemantics.Equation.mk "gslt:chr:nibble-value"
      [encoded (nibble n)] (number n))).filterMap (fun equation =>
        (SpaceSemantics.matchValue.matchValues [] equation.arguments [encoded (nibble digit.val)]).map
          fun bindings => Control.evaluate bindings equation.body) = [.evaluate [] (number digit.val)] := by
  fin_cases digit <;> simp [List.range_succ, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    nibble, number, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]

theorem nibble_clauses (digit : Fin 16) :
    clauses runtime "gslt:chr:nibble-value" [encoded (nibble digit.val)] = [.evaluate [] (number digit.val)] := by
  rw [clauses_use_only_the_named_equations]
  simp only [CHRControllerSource.runtime]
  rw [Library.owned_equations checked (by decide +kernel)]
  have rows : library.source.equations.filter (·.head == "gslt:chr:nibble-value") =
      (List.range 16).map (fun n => SpaceSemantics.Equation.mk "gslt:chr:nibble-value"
        [encoded (nibble n)] (number n)) := by rfl
  rw [rows]
  exact selected digit

theorem nibble_value_returns (state : State) (digit : Fin 16) :
    PureReturns runtime [] state (apply "gslt:chr:nibble-value" [encoded (nibble digit.val)]) state
      (number digit.val) := by
  apply call_returns runtime [] state state "gslt:chr:nibble-value" [encoded (nibble digit.val)] _
    (by decide +kernel) _ (by decide)
  apply raw_argument_answers runtime [] state state "gslt:chr:nibble-value" (encoded (nibble digit.val))
    [] [] 0 [number digit.val] (by decide +kernel)
  simp only [List.nil_append, CettaWireAtom.applySubst_encode]
  apply authored_function_arguments_return runtime [] [] state state "gslt:chr:nibble-value"
    [encoded (nibble digit.val)] 1 _ _ (by decide) (by decide) (nibble_clauses digit)
  exact number_returns _ _ _ _

theorem digits_value_returns (state : State) (digits : List (Fin 16)) :
    PureReturns runtime [] state (apply "gslt:chr:digits-value" [encoded (digitsTerm digits)]) state
      (number (Nat.ofDigits 16 (digits.map Fin.val))) := by
  induction digits with
  | nil =>
      metta_call checked
      metta_eval with checked unfolding [digitsTerm, encodeList, Nat.ofDigits]
  | cons first rest ih =>
      have digit := nibble_value_returns state first
      metta_call checked
      metta_eval [digit, ih] with checked unfolding [digitsTerm, encodeList, Nat.ofDigits]
      apply natural_add_returns runtime _ state _ _ first.val (16 * Nat.ofDigits 16 (rest.map Fin.val))
      · metta_capture_any digit unfolding [digitsTerm]
      · apply natural_mul_returns runtime _ state _ _ 16 (Nat.ofDigits 16 (rest.map Fin.val))
        · exact number_returns _ _ _ _
        · metta_capture checked using ih unfolding [digitsTerm]

/-- Each compiler-produced digit has its range evidence, without truncating
or accepting a non-canonical numeral. -/
def canonicalDigits (value : Nat) : List (Fin 16) :=
  (Nat.digits 16 value).attach.map fun digit =>
    ⟨digit.val, Nat.digits_lt_base (by decide) digit.property⟩

theorem canonicalDigits_values (value : Nat) :
    (canonicalDigits value).map Fin.val = Nat.digits 16 value := by
  simp [canonicalDigits, List.map_map]

theorem canonical_digits_exact (value : Nat) :
    digitsTerm (canonicalDigits value) = encodeList nibble (Nat.digits 16 value) := by
  rw [← canonicalDigits_values value]
  simp only [digitsTerm, encodeList_map, Function.comp_def]

theorem canonical_digits_value_returns (state : State) (value : Nat) :
    PureReturns runtime [] state
      (apply "gslt:chr:digits-value" [encoded (encodeList nibble (Nat.digits 16 value))]) state
      (number value) := by
  have result := digits_value_returns state (canonicalDigits value)
  simpa only [canonical_digits_exact, canonicalDigits_values, Nat.ofDigits_digits] using result

#print axioms nibble_value_returns
#print axioms digits_value_returns
#print axioms canonical_digits_value_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRWordExecution
