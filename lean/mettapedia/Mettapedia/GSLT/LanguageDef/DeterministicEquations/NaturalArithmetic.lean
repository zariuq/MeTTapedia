import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalData

/-!
# Unbounded natural arithmetic for computational presentations

These scalar operations act on decoded natural data. Kernel-specific word
bounds and refusal guards remain authored equations. The host preserves the
existing zero/predecessor operations and leaves other names uninterpreted.
This specifies primitive meaning; a native implementation is a separate
realization obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

inductive NaturalBinary where
  | add | monus | maximum | le | lt | equal
  deriving DecidableEq, Repr

def naturalBinary? : String → Option NaturalBinary
  | "nik:nat-add" => some .add
  | "nik:nat-monus" => some .monus
  | "nik:nat-max" => some .maximum
  | "nik:nat-le" => some .le
  | "nik:nat-lt" => some .lt
  | "nik:nat-eq" => some .equal
  | _ => none

def boolean (value : Bool) : Term := .sym (if value then "True" else "False")

def NaturalBinary.result (operation : NaturalBinary) (left right : Nat) : Term :=
  match operation with
  | .add => natural (left + right)
  | .monus => natural (left - right)
  | .maximum => natural (max left right)
  | .le => boolean (decide (left ≤ right))
  | .lt => boolean (decide (left < right))
  | .equal => boolean (decide (left = right))

def naturalArithmeticHost : Host where
  primitive head arguments :=
    match naturalBinary? head with
    | some operation =>
        match arguments with
        | [left, right] =>
            match natural? left, natural? right with
            | some left, some right => .value (operation.result left right)
            | _, _ => .fault
        | _ => .fault
    | none => naturalHost.primitive head arguments

theorem naturalArithmeticHost_binary {head : String} {operation : NaturalBinary}
    (selected : naturalBinary? head = some operation) (left right : Nat) :
    naturalArithmeticHost.primitive head [natural left, natural right] =
      .value (operation.result left right) := by
  simp [naturalArithmeticHost, selected]

theorem naturalArithmeticHost_add (left right : Nat) :
    naturalArithmeticHost.primitive "nik:nat-add" [natural left, natural right] =
      .value (natural (left + right)) :=
  naturalArithmeticHost_binary (head := "nik:nat-add") (operation := .add) rfl left right

theorem naturalArithmeticHost_monus (left right : Nat) :
    naturalArithmeticHost.primitive "nik:nat-monus" [natural left, natural right] =
      .value (natural (left - right)) :=
  naturalArithmeticHost_binary (head := "nik:nat-monus") (operation := .monus) rfl left right

theorem naturalArithmeticHost_max (left right : Nat) :
    naturalArithmeticHost.primitive "nik:nat-max" [natural left, natural right] =
      .value (natural (max left right)) :=
  naturalArithmeticHost_binary (head := "nik:nat-max") (operation := .maximum) rfl left right

theorem naturalArithmeticHost_le (left right : Nat) :
    naturalArithmeticHost.primitive "nik:nat-le" [natural left, natural right] =
      .value (boolean (decide (left ≤ right))) :=
  naturalArithmeticHost_binary (head := "nik:nat-le") (operation := .le) rfl left right

theorem naturalArithmeticHost_lt (left right : Nat) :
    naturalArithmeticHost.primitive "nik:nat-lt" [natural left, natural right] =
      .value (boolean (decide (left < right))) :=
  naturalArithmeticHost_binary (head := "nik:nat-lt") (operation := .lt) rfl left right

theorem naturalArithmeticHost_eq (left right : Nat) :
    naturalArithmeticHost.primitive "nik:nat-eq" [natural left, natural right] =
      .value (boolean (decide (left = right))) :=
  naturalArithmeticHost_binary (head := "nik:nat-eq") (operation := .equal) rfl left right

/-- New scalar operations do not alter the prior zero/predecessor primitive contracts. -/
theorem naturalArithmeticHost_prior (head : String) (arguments : List Term)
    (notNew : naturalBinary? head = none) :
    naturalArithmeticHost.primitive head arguments = naturalHost.primitive head arguments := by
  simp [naturalArithmeticHost, notNew]

theorem naturalArithmeticHost_zero (value : Nat) :
    naturalArithmeticHost.primitive "nik:nat-zero" [natural value] =
      .value (.sym (if value = 0 then "True" else "False")) := naturalHost_zero value

theorem naturalArithmeticHost_pred (value : Nat) :
    naturalArithmeticHost.primitive "nik:nat-pred" [natural value] =
      .value (natural value.pred) := naturalHost_pred value

theorem naturalArithmeticHost_unhandled (head : String) (arguments : List Term)
    (notNew : naturalBinary? head = none)
    (notZero : head ≠ "nik:nat-zero") (notPred : head ≠ "nik:nat-pred") :
    naturalArithmeticHost.primitive head arguments = .unhandled := by
  rw [naturalArithmeticHost_prior head arguments notNew]
  exact naturalHost_unhandled _ _ notZero notPred

theorem naturalArithmeticHost_wrong_arity {head : String} {operation : NaturalBinary}
    (selected : naturalBinary? head = some operation) (arguments : List Term)
    (wrong : arguments.length ≠ 2) :
    naturalArithmeticHost.primitive head arguments = .fault := by
  cases arguments with
  | nil => simp [naturalArithmeticHost, selected]
  | cons first rest =>
      cases rest with
      | nil => simp [naturalArithmeticHost, selected]
      | cons second rest =>
          cases rest with
          | nil => simp at wrong
          | cons third rest => simp [naturalArithmeticHost, selected]

theorem naturalArithmeticHost_non_natural {head : String} {operation : NaturalBinary}
    (selected : naturalBinary? head = some operation) (left right : Term)
    (malformed : natural? left = none ∨ natural? right = none) :
    naturalArithmeticHost.primitive head [left, right] = .fault := by
  rcases malformed with leftBad | rightBad
  · simp [naturalArithmeticHost, selected, leftBad]
  · cases first : natural? left <;> simp [naturalArithmeticHost, selected, first, rightBad]

theorem addition_does_not_wrap_at_word_boundary :
    naturalArithmeticHost.primitive "nik:nat-add"
      [natural 18446744073709551615, natural 1] =
      .value (natural 18446744073709551616) := naturalArithmeticHost_add _ _

theorem strict_bound_comparison_refuses_equal_boundary :
    naturalArithmeticHost.primitive "nik:nat-lt"
      [natural 18446744073709551616, natural 18446744073709551616] =
      .value (.sym "False") := by
  simpa [boolean] using naturalArithmeticHost_lt 18446744073709551616 18446744073709551616

theorem truncated_subtraction_keeps_zero :
    naturalArithmeticHost.primitive "nik:nat-monus" [natural 1, natural 2] =
      .value (natural 0) := naturalArithmeticHost_monus _ _

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
