import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.NumericWireExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource
import Mettapedia.Data.Nat.DoublingDivisionStep

/-! Quotient-bit recovery from a returned doubled-divisor result. This is
the literal source continuation's arithmetic, evaluated with integer target
primitives, not a floating approximation.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionRecovery

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def body : Atom := .expression [.symbol "let", .var "twice", .expression [.symbol "+", .var "quotient", .var "quotient"],
  .expression [.symbol "if", .expression [.symbol "<", .var "remainder", .var "divisor"],
    .expression [.symbol "IntegerDivmod", .var "twice", .var "remainder"],
    .expression [.symbol "IntegerDivmod", .expression [.symbol "+", .var "twice", .grounded (.int 1)],
      .expression [.symbol "-", .var "remainder", .var "divisor"]]]]

def bindings (number divisor quotient remainder : Nat) : Subst :=
  [("remainder", WireKit.number remainder), ("quotient", WireKit.number quotient),
    ("divisor", WireKit.number divisor), ("number", WireKit.number number)]

def result (divisor quotient remainder : Nat) : Term :=
  if remainder < divisor then .application "IntegerDivmod" [.natural (quotient + quotient), .natural remainder]
  else .application "IntegerDivmod" [.natural (quotient + quotient + 1), .natural (remainder - divisor)]

theorem recovery_returns (state : State) (number divisor quotient remainder : Nat) :
    PureReturns integerLibrary.runtime (bindings number divisor quotient remainder) state body state
      (encoded (result divisor quotient remainder)) := by
  apply pure_let_returns _ _ _ "twice" _ (WireKit.number (quotient + quotient)) _ _ (by rfl)
  · exact natural_add_returns _ _ state _ _ quotient quotient
      (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))
  · apply pure_if_returns
    · exact natural_lt_returns _ _ state _ _ remainder divisor
        (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))
    · by_cases small : remainder < divisor
      · simp only [small, decide_true, if_true, result]
        metta_eval with integer_checked unfolding [bindings]
      · simp only [small, decide_false, if_false, result]
        have subtraction := natural_sub_returns integerLibrary.runtime
          (("twice", WireKit.number (quotient + quotient)) :: bindings number divisor quotient remainder) state
          (.var "remainder") (.var "divisor") remainder divisor (by omega)
          (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))
        apply PureData.constructor_return _ _ state "IntegerDivmod" _ _ (by decide +kernel) (by decide)
        exact .cons
          (natural_add_returns _ _ state _ _ (quotient + quotient) 1 (bound_returns _ _ _ (by rfl)) (number_returns _ _ _ _))
          (.cons subtraction .nil)

#print axioms recovery_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionRecovery
