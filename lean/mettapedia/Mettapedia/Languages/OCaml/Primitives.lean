import Mettapedia.Languages.OCaml.Syntax
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! The pinned 64-bit OCaml profile has 63-bit signed integers. Division and
remainder truncate toward zero; arithmetic wraps. Data comparison follows
typed OCaml values, including constant-before-block variant ordering. A
functional value encountered during comparison raises an ordinary fault.
Malformed IR arguments are reported separately from language faults. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

def integerModulus : Int := 2 ^ 63
def integerHalf : Int := 2 ^ 62

def wrapInteger (value : Int) : Int := (value + integerHalf) % integerModulus - integerHalf

theorem wrapInteger_bounds (value : Int) :
    -integerHalf ≤ wrapInteger value ∧ wrapInteger value < integerHalf := by
  have low := Int.emod_nonneg (value + integerHalf) (by norm_num [integerModulus] : integerModulus ≠ 0)
  have high := Int.emod_lt_of_pos (value + integerHalf) (by norm_num [integerModulus] : 0 < integerModulus)
  dsimp [wrapInteger]
  norm_num [integerHalf, integerModulus] at *
  omega

theorem wrapInteger_fixed (value : Int) (low : -integerHalf ≤ value) (high : value < integerHalf) :
    wrapInteger value = value := by
  have first : 0 ≤ value + integerHalf := by omega
  have last : value + integerHalf < integerModulus := by
    norm_num [integerHalf, integerModulus] at *
    omega
  rw [wrapInteger, Int.emod_eq_of_lt first last]
  omega

theorem wrapInteger_idempotent (value : Int) : wrapInteger (wrapInteger value) = wrapInteger value :=
  wrapInteger_fixed _ (wrapInteger_bounds value).1 (wrapInteger_bounds value).2

private def compareInt (left right : Int) : Ordering :=
  if left < right then .lt else if left = right then .eq else .gt

private def compareNat (left right : Nat) : Ordering :=
  if left < right then .lt else if left = right then .eq else .gt

private def compareBytes : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | first :: rest, second :: tail =>
      match compareNat first.toNat second.toNat with
      | .eq => compareBytes rest tail
      | order => order

abbrev Compared := Except InternalError (Except Fault Ordering)

mutual
  def compareValue : Value → Value → Compared
    | .closure _ _, _ | _, .closure _ _ => .ok (.error .functionalComparison)
    | .literal (.integer left), .literal (.integer right) => .ok (.ok (compareInt left right))
    | .literal (.boolean left), .literal (.boolean right) =>
        .ok (.ok (compareNat left.toNat right.toNat))
    | .literal .unit, .literal .unit | .literal .nil, .literal .nil => .ok (.ok .eq)
    | .literal (.string left), .literal (.string right) => .ok (.ok (compareBytes left right))
    | .literal .nil, .cons _ _ => .ok (.ok .lt)
    | .cons _ _, .literal .nil => .ok (.ok .gt)
    | .cons left rest, .cons right tail => do
        match ← compareValue left right with
        | .error fault => pure (.error fault)
        | .ok .eq => compareValue rest tail
        | .ok order => pure (.ok order)
    | .tuple left, .tuple right =>
        if left.length = right.length then compareFields left right
        else .error (.incomparableValues (.tuple left) (.tuple right))
    | .variant leftType leftTag left, .variant rightType rightTag right =>
        if leftType ≠ rightType then
          .error (.incomparableValues (.variant leftType leftTag left) (.variant rightType rightTag right))
        else if left.isEmpty && !right.isEmpty then .ok (.ok .lt)
        else if !left.isEmpty && right.isEmpty then .ok (.ok .gt)
        else match compareNat leftTag rightTag with
          | .eq => compareFields left right
          | order => .ok (.ok order)
    | left, right => .error (.incomparableValues left right)

  def compareFields : List Value → List Value → Compared
    | [], [] => .ok (.ok .eq)
    | [], _ :: _ => .ok (.ok .lt)
    | _ :: _, [] => .ok (.ok .gt)
    | first :: rest, second :: tail => do
        match ← compareValue first second with
        | .error fault => pure (.error fault)
        | .ok .eq => compareFields rest tail
        | .ok order => pure (.ok order)
end

def comparison (operator : Primitive) (order : Ordering) : Bool :=
  match operator with
  | .equal => order == .eq
  | .different => order != .eq
  | .less => order == .lt
  | .lessEqual => order != .gt
  | .greater => order == .gt
  | .greaterEqual => order != .lt
  | _ => false

def Primitive.eval (operator : Primitive) (arguments : List Value) : Except InternalError Result :=
  match operator, arguments with
  | .add, [.literal (.integer left), .literal (.integer right)] =>
      .ok (.ok (.literal (.integer (wrapInteger (left + right)))))
  | .subtract, [.literal (.integer left), .literal (.integer right)] =>
      .ok (.ok (.literal (.integer (wrapInteger (left - right)))))
  | .multiply, [.literal (.integer left), .literal (.integer right)] =>
      .ok (.ok (.literal (.integer (wrapInteger (left * right)))))
  | .divide, [.literal (.integer left), .literal (.integer right)] =>
      if right = 0 then .ok (.error .divisionByZero)
      else .ok (.ok (.literal (.integer (wrapInteger (left.tdiv right)))))
  | .modulo, [.literal (.integer left), .literal (.integer right)] =>
      if right = 0 then .ok (.error .divisionByZero)
      else .ok (.ok (.literal (.integer (wrapInteger (left.tmod right)))))
  | .negate, [.literal (.integer value)] => .ok (.ok (.literal (.integer (wrapInteger (-value)))))
  | .notBool, [.literal (.boolean value)] => .ok (.ok (.literal (.boolean (!value))))
  | .equal, [left, right] | .different, [left, right]
      | .less, [left, right] | .lessEqual, [left, right]
      | .greater, [left, right] | .greaterEqual, [left, right] => do
        pure ((← compareValue left right).map fun order => .literal (.boolean (comparison operator order)))
  | _, _ => .error (.invalidPrimitiveArguments operator arguments)

end Mettapedia.Languages.OCaml
