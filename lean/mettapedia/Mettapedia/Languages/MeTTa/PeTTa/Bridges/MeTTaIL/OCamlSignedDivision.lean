import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionRecovery
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SignedMagnitudeExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerDecode
import Mettapedia.Languages.OCaml.SignedDivision

/-! The signed division branch follows the loaded helper: reject zero as
an ordinary source fault, divide exact magnitudes, recover signs, then wrap
and encode the source result.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSignedDivision

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def name (modulo : Bool) : String := if modulo then "MlModulo" else "MlDivide"
def compute (modulo : Bool) (left right : Int) : Int := if modulo then left.tmod right else left.tdiv right

def result (modulo : Bool) (left right : Int) : Term :=
  if right = 0 then OCamlResultServices.faultResult "MlDivisionByZero"
  else OCamlIntegerResult.result (compute modulo left right)

def bindings (modulo : Bool) (left right : Int) : Subst :=
  ("division", encoded (.string (name modulo))) :: ("second", integer right) :: ("first", integer left) ::
    Library.bind ["operator", "left", "right"]
      [encoded (.string (name modulo)), encoded (OCamlIntegerWire.datum left), encoded (OCamlIntegerWire.datum right)]

def recoveryRows : SpaceSemantics.Cases :=
  [(encoded (.string "MlDivide"), apply "gslt:ml:result-integer" [OCamlDivisionRecovery.quotientCode]),
   (encoded (.string "MlModulo"), apply "gslt:ml:result-integer" [OCamlDivisionRecovery.remainderCode]),
   (.var "bad", .symbol "None")]

def recoveryBody : Atom := .expression [.symbol "case", .var "operator",
  .expression (recoveryRows.map fun row => .expression [row.1, row.2])]

theorem recovery_returns (state : State) (caller : Subst) (modulo first second : Bool) (quotient remainder : Nat)
    (operatorRead : caller.lookup "operator" = some (encoded (.string (name modulo))))
    (firstRead : caller.lookup "negativeFirst" = some (Effects.boolean first))
    (secondRead : caller.lookup "negativeSecond" = some (Effects.boolean second))
    (quotientRead : caller.lookup "quotient" = some (number quotient))
    (remainderRead : caller.lookup "remainder" = some (number remainder)) :
    PureReturns runtime caller state recoveryBody state
      (encoded (OCamlIntegerResult.result (if modulo then
        if first then -(remainder : Int) else (remainder : Int)
        else if first = second then (quotient : Int) else -(quotient : Int)))) := by
  cases modulo with
  | false =>
    apply rows_case_returns runtime caller caller state state state (.var "operator")
      (encoded (.string "MlDivide")) _ _ _ recoveryRows rfl
    · exact bound_returns _ _ _ operatorRead
    · metta_select [recoveryRows, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      rfl
    · exact OCamlDivisionRecovery.quotient_returns state caller first second quotient firstRead secondRead quotientRead
  | true =>
    apply rows_case_returns runtime caller caller state state state (.var "operator")
      (encoded (.string "MlModulo")) _ _ _ recoveryRows rfl
    · exact bound_returns _ _ _ operatorRead
    · metta_select [recoveryRows, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      rfl
    · exact OCamlDivisionRecovery.remainder_returns state caller first remainder firstRead remainderRead

def branchBody : Atom := .expression [.symbol "if", apply "==" [.var "second", integer 0],
  apply "gslt:ml:result-fault" [encoded (.string "MlDivisionByZero")],
  .expression [.symbol "let*", .expression
    [.expression [.var "negativeFirst", apply "<" [.var "first", integer 0]],
     .expression [.var "negativeSecond", apply "<" [.var "second", integer 0]],
     .expression [.var "leftMagnitude", .expression [.symbol "if", .var "negativeFirst", apply "-" [integer 0, .var "first"], .var "first"]],
     .expression [.var "rightMagnitude", .expression [.symbol "if", .var "negativeSecond", apply "-" [integer 0, .var "second"], .var "second"]]],
    .expression [.symbol "case", apply "gslt:integer:divmod" [.var "leftMagnitude", .var "rightMagnitude"],
      .expression [.expression [.expression [.symbol "IntegerDivmod", .var "quotient", .var "remainder"], recoveryBody]]]]]

theorem branch_returns (state : State) (modulo : Bool) (left right : Int) :
    PureReturns runtime (bindings modulo left right) state branchBody state (encoded (result modulo left right)) := by
  apply pure_if_returns
  · exact integer_equal_returns _ _ state _ _ right 0 (bound_returns _ _ _ (by rfl)) (integer_returns _ _ _ _)
  · by_cases zero : right = 0
    · simp only [zero, decide_true, if_true, result]
      have fault := OCamlResultServices.fault_result_returns state "MlDivisionByZero"
      metta_capture checked using fault
    · simp only [zero, decide_false, result, if_false]
      apply pure_let_star_returns _ _ _ _ _ _ _ rfl
      apply pure_let_returns _ _ _ "negativeFirst" _ (Effects.boolean (decide (left < 0))) _ _ (by rfl)
      · exact integer_lt_returns _ _ state _ _ left 0 (bound_returns _ _ _ (by rfl)) (integer_returns _ _ _ _)
      · apply pure_let_returns _ _ _ "negativeSecond" _ (Effects.boolean (decide (right < 0))) _ _ (by rfl)
        · exact integer_lt_returns _ _ state _ _ right 0 (bound_returns _ _ _ (by rfl)) (integer_returns _ _ _ _)
        · apply pure_let_returns _ _ _ "leftMagnitude" _ (number left.natAbs) _ _ (by rfl)
          · exact magnitude_returns _ _ state "first" "negativeFirst" left (by rfl) (by rfl)
          · apply pure_let_returns _ _ _ "rightMagnitude" _ (number right.natAbs) _ _ (by rfl)
            · exact magnitude_returns _ _ state "second" "negativeSecond" right (by rfl) (by rfl)
            · apply pure_case_returns _ _ state _ _ _ _ _ rfl
              · apply Library.demand_call_in integer_checked OCamlIntegerAgreement.agreement
                  (head := "gslt:integer:divmod") (by decide +kernel) (by rfl) (by decide +kernel)
                  _ state state state _ [number left.natAbs, number right.natAbs] _ (by metta_literal; rfl)
                · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:integer:divmod") (index := 0)
                    (by decide +kernel) (bound_returns _ _ _ (by rfl))
                    (.evaluated (by decide +kernel) (bound_returns _ _ _ (by rfl)) (.nil _ _))
                · exact OCamlDivisionBody.body_returns state left.natAbs right.natAbs (Int.natAbs_pos.mpr zero)
              · metta_select [IntegerDivisionExecution.resultTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany, bindings, Library.bind]
              · intro selected body found
                metta_select [IntegerDivisionExecution.resultTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany, bindings, Library.bind] at found
                obtain ⟨bindingsSame, bodySame⟩ := found
                subst selected
                subst body
                have same : (if modulo then
                    if decide (left < 0) then -((left.natAbs % right.natAbs : Nat) : Int) else ((left.natAbs % right.natAbs : Nat) : Int)
                    else if decide (left < 0) = decide (right < 0) then ((left.natAbs / right.natAbs : Nat) : Int)
                      else -((left.natAbs / right.natAbs : Nat) : Int)) = compute modulo left right := by
                  cases modulo
                  · exact OCaml.magnitudeQuotient_eq_tdiv left right
                  · simpa [compute, OCaml.magnitudeRemainder] using OCaml.magnitudeRemainder_eq_tmod left right
                rw [← same]
                apply recovery_returns state _ modulo (decide (left < 0)) (decide (right < 0))
                  (left.natAbs / right.natAbs) (left.natAbs % right.natAbs)
                all_goals simp [Subst.lookup, number, encoded, CettaWireAtom.encode]

#print axioms recovery_returns
#print axioms branch_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSignedDivision
