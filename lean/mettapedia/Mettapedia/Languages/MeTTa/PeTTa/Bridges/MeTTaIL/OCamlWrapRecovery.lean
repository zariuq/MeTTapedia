import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerWireExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource
import Mettapedia.Languages.OCaml.IntegerWrapAlgorithm

/-! The wrapping continuation recovers the signed representative from
the magnitude remainder using actual target integer operations.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWrapRecovery

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages
open Eval BridgeKit WireKit OCamlControllerSource

def unsigned (negative : Bool) (remainder : Nat) : Int :=
  if negative then if remainder = 0 then 0 else OCaml.integerModulus - remainder else remainder

def wrapped (negative : Bool) (remainder : Nat) : Int :=
  if unsigned negative remainder < OCaml.integerHalf then unsigned negative remainder
  else unsigned negative remainder - OCaml.integerModulus

def body : Atom := .expression [.symbol "let", .var "unsigned",
  .expression [.symbol "if", .var "negative",
    .expression [.symbol "if", .expression [.symbol "==", .var "remainder", .grounded (.int 0)], .grounded (.int 0),
      .expression [.symbol "-", .grounded (.int 9223372036854775808), .var "remainder"]], .var "remainder"],
  .expression [.symbol "if", .expression [.symbol "<", .var "unsigned", .grounded (.int 4611686018427387904)], .var "unsigned",
    .expression [.symbol "-", .var "unsigned", .grounded (.int 9223372036854775808)]]]

def bindings (negative : Bool) (number quotient remainder : Nat) (original : Int) : Subst :=
  [("remainder", WireKit.number remainder), ("quotient", WireKit.number quotient),
    ("magnitude", WireKit.number number), ("negative", Effects.boolean negative), ("number", integer original)]

theorem recovery_returns (state : State) (negative : Bool) (number quotient remainder : Nat) (original : Int) :
    PureReturns runtime (bindings negative number quotient remainder original) state body state
      (integer (wrapped negative remainder)) := by
  apply pure_let_returns _ _ _ "unsigned" _ (integer (unsigned negative remainder)) _ _ (by rfl)
  · apply pure_if_returns
    · exact bound_returns _ _ _ (by rfl)
    · cases negative with
      | false => exact bound_returns _ _ _ (by rfl)
      | true =>
        apply pure_if_returns
        · exact natural_equal_returns _ _ state _ _ remainder 0 (bound_returns _ _ _ (by rfl)) (number_returns _ _ _ _)
        · by_cases zero : remainder = 0
          · simp only [zero, decide_true, if_true, unsigned]
            exact integer_returns _ _ _ _
          · simp only [zero, decide_false, if_false, unsigned]
            exact integer_sub_returns _ _ state _ _ OCaml.integerModulus remainder
              (integer_returns _ _ _ _) (bound_returns _ _ _ (by rfl))
  · apply pure_if_returns
    · exact integer_lt_returns _ _ state _ _ (unsigned negative remainder) OCaml.integerHalf
        (bound_returns _ _ _ (by rfl)) (integer_returns _ _ _ _)
    · by_cases small : unsigned negative remainder < OCaml.integerHalf
      · simp only [small, decide_true, if_true, wrapped]
        exact bound_returns _ _ _ (by rfl)
      · simp only [small, decide_false, if_false, wrapped]
        exact integer_sub_returns _ _ state _ _ (unsigned negative remainder) OCaml.integerModulus
          (bound_returns _ _ _ (by rfl)) (integer_returns _ _ _ _)

#print axioms recovery_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWrapRecovery
