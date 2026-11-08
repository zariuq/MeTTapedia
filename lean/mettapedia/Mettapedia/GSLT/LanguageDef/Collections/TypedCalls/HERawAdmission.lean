import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns

/-!
# Raw applicability cannot be reconstructed from evaluated values

HE checks the written argument's type before interpreting that argument.
A typed producer can return through an Undefined range without the enclosing
final cast. Consequently two arguments with the same evaluated value can
have different source applicability. A ready invocation must retain the fact
that its earlier check was performed; restarting the whole written call on
its evaluated arguments is not the same continuation.

These controls use the actual existing HE type checker and evaluator. They
do not assert that every current native route makes this mistake.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERawAdmission

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HEReturns.Controls (castSpace num str answersAt)

def written : Atom := .expression [.symbol "k", num 1]
def delivered : Atom := str "s"
def consumer (arg : Atom) : Atom := .expression [.symbol "h", arg]
def signature : Atom := arrowType [.symbol "Number"] Atom.expressionType

def admitted (arg : Atom) (fuel : Nat) : Bool :=
  match checkIfFunctionTypeIsApplicable (consumer arg) signature Atom.undefinedType
      castSpace Bindings.empty fuel with
  | .inl _ => false
  | .inr _ => true

theorem signature_is_declared : getAtomTypes castSpace (.symbol "h") = [signature] := by
  decide

/-- The executable raw lookup profile reports Undefined for this compound
argument. Its enclosing Number check therefore admits it. This is not a
claim that the native recursive inference service reports the same list. -/
theorem written_lookup_profile : getAtomTypes castSpace written = [Atom.undefinedType] := by
  decide

theorem delivered_type : getAtomTypes castSpace delivered = [.symbol "String"] := by decide

set_option maxHeartbeats 1000000 in
theorem written_is_admitted (extra : Nat) : admitted written (extra + 12) = true := by
  cbv

set_option maxHeartbeats 1000000 in
theorem delivered_is_rejected (extra : Nat) : admitted delivered (extra + 12) = false := by
  cbv

/-- The same argument value reaches the next phase from two differently
typed written arguments. No equality of whole function calls is assumed. -/
theorem evaluated_values_agree (extra : Nat) :
    answersAt castSpace written Atom.undefinedType (extra + 15) = [delivered] ∧
      answersAt castSpace delivered Atom.undefinedType (extra + 15) = [delivered] := by
  constructor
  · exact HEReturns.Controls.reply_through_undefined_range (extra + 15) (by omega)
  · unfold answersAt
    have result := HEReturns.evalAtom_grounded (space := castSpace)
      (dispatch := GroundedDispatch.none) (.string "s")
      (type_ := Atom.undefinedType) rfl (by decide) (by decide) Bindings.empty
      (fuel := extra + 14) (by change 1 ≤ extra + 14; omega) []
    change (evalAtom castSpace GroundedDispatch.none (str "s") Atom.undefinedType
      Bindings.empty (extra + 15) []).map _ = _
    have evaluated : evalAtom castSpace GroundedDispatch.none (str "s") Atom.undefinedType
        Bindings.empty (extra + 15) [] = [(str "s", Bindings.empty)] := by
      simpa only [show extra + 14 + 1 = extra + 15 by omega,
        show accepts Atom.undefinedType (getGroundedType (.string "s")) = true from rfl,
        if_true, str] using result
    rw [evaluated]
    rfl

/-- There is no value-only classifier of the preceding raw-argument check,
even for this fixed space, signature, caller and expected type. -/
theorem no_value_only_raw_admission (extra : Nat) :
    ¬ ∃ classify : List Atom → Bool, ∀ arg,
      classify (answersAt castSpace arg Atom.undefinedType (extra + 15)) =
        admitted arg (extra + 12) := by
  rintro ⟨classify, agrees⟩
  have first := agrees written
  have second := agrees delivered
  rw [(evaluated_values_agree extra).1, written_is_admitted] at first
  rw [(evaluated_values_agree extra).2, delivered_is_rejected] at second
  rw [first] at second
  cases second

set_option maxHeartbeats 1000000 in
/-- Literal numeric arguments are the positive case: their raw and reached
value have the same source applicability. -/
theorem numeric_value_admitted (extra : Nat) : admitted (num 1) (extra + 12) = true := by
  cbv

theorem retyping_changes_verdict (extra : Nat) :
    admitted written (extra + 12) ≠ admitted delivered (extra + 12) := by
  rw [written_is_admitted, delivered_is_rejected]
  decide

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERawAdmission
