import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Data
import Std.Data.String.ToNat

/-!
# Natural-number data and small computational primitives

Indices use decimal literals with no machine-word bound. The only operations
here are zero testing and predecessor; neither interprets a guest term or
checks a guest proof. Native implementations must realize these same
unbounded natural operations, or report resource exhaustion separately.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

def natural (value : Nat) : Term := .lit value.repr

def natural? : Term → Option Nat
  | .lit spelling => spelling.toNat?
  | _ => none

@[simp] theorem natural_roundtrip (value : Nat) : natural? (natural value) = some value := by
  simp [natural?, natural, Nat.toNat?_repr]

theorem natural_injective : Function.Injective natural := by
  intro first second same
  have decoded := congrArg natural? same
  simpa using decoded

theorem natural_passive (P : Program) (H : Host) (value : Nat) :
    PassiveData P H (natural value) := .lit _

def naturalHost : Host where
  primitive head arguments :=
    if head = "nik:nat-zero" then
      match arguments with
      | [argument] => match natural? argument with
        | some value => .value (.sym (if value = 0 then "True" else "False"))
        | none => .fault
      | _ => .fault
    else if head = "nik:nat-pred" then
      match arguments with
      | [argument] => match natural? argument with
        | some value => .value (natural value.pred)
        | none => .fault
      | _ => .fault
    else .unhandled

theorem naturalHost_zero (value : Nat) :
    naturalHost.primitive "nik:nat-zero" [natural value] =
      .value (.sym (if value = 0 then "True" else "False")) := by
  simp [naturalHost]

theorem naturalHost_pred (value : Nat) :
    naturalHost.primitive "nik:nat-pred" [natural value] =
      .value (natural value.pred) := by
  simp [naturalHost]

theorem naturalHost_unhandled (head : String) (arguments : List Term)
    (notZero : head ≠ "nik:nat-zero") (notPred : head ≠ "nik:nat-pred") :
    naturalHost.primitive head arguments = .unhandled := by
  simp [naturalHost, notZero, notPred]

theorem predecessor_above_word_range :
    naturalHost.primitive "nik:nat-pred" [natural 18446744073709551617] =
      .value (natural 18446744073709551616) := naturalHost_pred _

theorem malformed_natural_refuses :
    naturalHost.primitive "nik:nat-pred" [.lit "-1"] = .fault := by
  have refused : ("-1" : String).toNat? = none := by
    simp [Bool.eq_false_iff, String.isNat_iff]
  simp [naturalHost, natural?, refused]

theorem unknown_natural_operation_stays_unhandled :
    naturalHost.primitive "foreign:checker" [] = .unhandled := rfl

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
