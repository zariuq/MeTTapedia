import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWordExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerWireExecution

/-! The loaded OCaml integer constructor executes to the compiler's exact
sign-and-magnitude representation; numeric inputs retain evaluated demand.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerEncode

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

private theorem wordAgreement : ProgramAgreementOn
    (fun head => head == "gslt:word16:digits") wordLibrary.runtime runtime := by
  apply Library.agreement_on checked
  intro head supported
  have same : head = "gslt:word16:digits" := beq_iff_eq.mp supported
  subst head
  decide +kernel

theorem body_returns (state : State) (number : Int) :
    PureReturns runtime (Library.bind ["number"] [integer number]) state (library.body "gslt:ml:integer") state
      (encoded (OCamlIntegerWire.datum number)) := by
  metta_literal
  apply pure_let_star_returns _ _ _ _ _ _ _ rfl
  apply pure_let_returns _ _ _ "negative" _ (Effects.boolean (decide (number < 0))) _ _ (by rfl)
  · exact integer_lt_returns _ _ state _ _ number 0 (bound_returns _ _ _ (by rfl)) (integer_returns _ _ _ _)
  · apply pure_let_returns _ _ _ "magnitude" _ (WireKit.number number.natAbs) _ _ (by rfl)
    · apply pure_if_returns
      · exact bound_returns _ _ _ (by rfl)
      · by_cases negative : number < 0
        · simp only [negative, decide_true, if_true]
          have computed := integer_sub_returns runtime
            (("negative", Effects.boolean true) :: Library.bind ["number"] [integer number]) state
            (integer 0) (.var "number") 0 number (integer_returns _ _ _ _) (bound_returns _ _ _ (by rfl))
          simpa [zero_sub, Int.natCast_natAbs, abs_of_neg negative, WireKit.number, encoded, CettaWireAtom.encode, integer] using computed
        · simp only [negative, decide_false]
          have same : (number.natAbs : Int) = number := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
          simpa [WireKit.number, encoded, CettaWireAtom.encode, same, integer] using
            (bound_returns runtime _ state (name := "number") (value := integer number) (by rfl))
    · apply pure_let_returns _ _ _ "sign" _ (encoded (OCamlIntegerWire.sign number)) _ _ (by rfl)
      · change PureReturns runtime _ state
          (.expression [.symbol "PApp", .expression [.symbol "if", .var "negative", encoded (.string "MlNegative"),
            encoded (.string "MlNonnegative")], .symbol "LNil"]) state
          (.expression [.symbol "PApp", encoded (.string (if number < 0 then "MlNegative" else "MlNonnegative")), .symbol "LNil"])
        apply PureData.constructor_return runtime _ state "PApp" _ _ (by decide +kernel) (by decide)
        refine .cons ?_ (.cons (symbol_returns _ _ _ _) .nil)
        apply pure_if_returns
        · exact bound_returns _ _ _ (by rfl)
        · by_cases negative : number < 0
          · simp only [negative, decide_true, if_true]
            exact grounded_returns _ _ _ _
          · simp only [negative, decide_false, Bool.false_eq_true, if_false]
            exact grounded_returns _ _ _ _
      · apply pure_let_returns _ _ _ "digits" _ (encoded (Word16Wire.digitsTerm number.natAbs)) _ _ (by rfl)
        · apply Library.demand_call_in word_checked wordAgreement (head := "gslt:word16:digits")
            (by decide +kernel) (by rfl) (by decide +kernel) _ state state state _ [WireKit.number number.natAbs] _
            (by metta_literal; rfl)
          · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:word16:digits") (index := 0)
              (by decide +kernel) (bound_returns _ _ _ (by rfl)) (.nil _ _)
          · exact OCamlWordExecution.digits_body_returns state number.natAbs
        · have pack := pack2_returns state "MlInteger" (OCamlIntegerWire.sign number) (Word16Wire.vectorTerm number.natAbs)
          metta_eval [pack] with checked unfolding [OCamlIntegerWire.datum, Word16Wire.vectorTerm]

theorem integer_returns (state : State) (number : Int) :
    PureReturns runtime [] state (apply "gslt:ml:integer" [WireKit.integer number]) state
      (encoded (OCamlIntegerWire.datum number)) := by
  apply Library.demand_call checked (by rfl) (by decide +kernel) [] state state state
    [WireKit.integer number] [WireKit.integer number] _ (by metta_literal; rfl)
  · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:integer") (index := 0)
      (by decide +kernel) (WireKit.integer_returns _ _ _ _) (.nil _ _)
  · exact body_returns state number

#print axioms integer_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerEncode
