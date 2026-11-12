import Mettapedia.Logic.LP.IndependentOutputUnification

/-!
# Successful finite computations of the chosen total unifier

A successful fuel-bounded computation determines the exact substitution
chosen by the total unifier, not merely an equivalent solution family.
An exhausted bounded computation supplies no rejection certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.PositiveUnificationEvaluation

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]

theorem total_eq_fuel_of_success (fuel : Nat) (problem : List (Term σ × Term σ))
    (success : (unifyFuel fuel problem).isSome = true) :
    unifyTotal problem = unifyFuel fuel problem := by
  cases computed : unifyFuel fuel problem with
  | none => simp [computed] at success
  | some substitution =>
      exact IndependentOutputUnification.Coordinates.fuel_agrees_total
        fuel problem substitution computed

namespace Controls

abbrev signature := IndependentOutputUnification.Controls.signature

def aliases : List (Term signature × Term signature) :=
  [(.var 0, .var 1), (.var 1, .const "answer")]

theorem chosen_alias_is_preserved :
    (unifyTotal aliases).map (fun substitution => substitution 0) =
      some (.const "answer") := by
  rw [total_eq_fuel_of_success 3 aliases (by decide +kernel)]
  rfl

theorem exhaustion_is_not_rejection :
    unifyFuel 0 aliases = none ∧ (unifyTotal aliases).isSome = true := by
  constructor
  · rfl
  · rw [total_eq_fuel_of_success 3 aliases (by decide +kernel)]
    rfl

theorem conflicting_constants_still_reject :
    unifyTotal (σ := signature) [(.const "left", .const "right")] = none := by
  simp [unifyTotal]

end Controls

end Mettapedia.Logic.LP.PositiveUnificationEvaluation
