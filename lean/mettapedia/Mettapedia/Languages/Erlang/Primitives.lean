import Mettapedia.Languages.Erlang.Syntax

/-! Sequential Erlang primitive results. Integer arithmetic is unbounded;
quotient and remainder truncate toward zero. Comparisons of data use Erlang
term order, including tuple arity before fields and nil before cons.

Ordering of runtime identities and comparisons involving closures require a
separate identity profile. This component returns an explicit internal
diagnostic for those unfinished cases, rather than inventing their order.
It is not yet a complete E0 primitive admission certificate. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang

private def compareInt (left right : Int) : Ordering :=
  if left < right then .lt else if left = right then .eq else .gt

private def compareNat (left right : Nat) : Ordering :=
  if left < right then .lt else if left = right then .eq else .gt

private def rank : Value → Nat
  | .literal (.integer _) => 0
  | .literal (.atom _) => 1
  | .closure _ _ _ => 2
  | .pid _ => 3
  | .tuple _ => 4
  | .literal .nil => 5
  | .cons _ _ => 6

mutual
  def compareData : Value → Value → Except InternalError Ordering
    | .literal (.integer left), .literal (.integer right) => .ok (compareInt left right)
    | .literal (.atom left), .literal (.atom right) => .ok (compare left right)
    | .pid left, .pid right =>
        if left = right then .ok .eq else .error (.comparisonProfileRequired (.pid left) (.pid right))
    | .closure arity left captured, .closure otherArity right other =>
        .error (.comparisonProfileRequired (.closure arity left captured) (.closure otherArity right other))
    | .tuple left, .tuple right =>
        if left.length = right.length then compareFields left right
        else .ok (compareNat left.length right.length)
    | .literal .nil, .literal .nil => .ok .eq
    | .cons left tail, .cons right rest => do
        match ← compareData left right with
        | .eq => compareData tail rest
        | order => pure order
    | left, right => .ok (compareNat (rank left) (rank right))

  def compareFields : List Value → List Value → Except InternalError Ordering
    | [], [] => .ok .eq
    | [], _ :: _ => .ok .lt
    | _ :: _, [] => .ok .gt
    | first :: rest, second :: tail => do
        match ← compareData first second with
        | .eq => compareFields rest tail
        | order => pure order
end

def Value.isProperList : Value → Bool
  | .literal .nil => true
  | .cons _ tail => tail.isProperList
  | _ => false

mutual
  private def sameData : Value → Value → Except InternalError Bool
    | .literal first, .literal second => .ok (first == second)
    | .pid first, .pid second => .ok (first == second)
    | .closure arity function captured, .closure otherArity other rest =>
        .error (.comparisonProfileRequired (.closure arity function captured) (.closure otherArity other rest))
    | .tuple left, .tuple right => sameFields left right
    | .cons head tail, .cons first rest => do
        if ← sameData head first then sameData tail rest else pure false
    | _, _ => .ok false

  private def sameFields : List Value → List Value → Except InternalError Bool
    | [], [] => .ok true
    | head :: tail, first :: rest => do
        if ← sameData head first then sameFields tail rest else pure false
    | _, _ => .ok false
end

abbrev PrimitiveResult := Except InternalError (Except Fault Value)

def Primitive.eval (operator : Primitive) (arguments : List Value) : PrimitiveResult :=
  let success := fun value => Except.ok (Except.ok value)
  let arithmetic := fun operation => match arguments with
    | [.literal (.integer first), .literal (.integer second)] => success (.literal (.integer (operation first second)))
    | _ => .ok (.error .badarith)
  let comparison := fun predicate => match arguments with
    | [left, right] => do pure (.ok (boolean (predicate (← compareData left right))))
    | _ => .ok (.error .badarg)
  let test := fun predicate => match arguments with
    | [value] => success (boolean (predicate value))
    | _ => .ok (.error .badarg)
  let boolBinary := fun operation => match arguments with
    | [left, right] => match boolean? left, boolean? right with
      | some left, some right => success (boolean (operation left right))
      | _, _ => .ok (.error .badarg)
    | _ => .ok (.error .badarg)
  match operator with
  | .add => arithmetic (· + ·)
  | .subtract => arithmetic (· - ·)
  | .multiply => arithmetic (· * ·)
  | .divide | .remainder => match arguments with
    | [.literal (.integer first), .literal (.integer second)] =>
        if second = 0 then .ok (.error .badarith)
        else success (.literal (.integer (if operator == .divide then first.tdiv second else first.tmod second)))
    | _ => .ok (.error .badarith)
  | .negate => match arguments with
    | [.literal (.integer value)] => success (.literal (.integer (-value)))
    | _ => .ok (.error .badarith)
  | .equal | .different => match arguments with
    | [left, right] => do
        let same ← sameData left right
        pure (.ok (boolean (if operator == .equal then same else !same)))
    | _ => .ok (.error .badarg)
  | .less => comparison (· == .lt)
  | .lessEqual => comparison (· != .gt)
  | .greater => comparison (· == .gt)
  | .greaterEqual => comparison (· != .lt)
  | .isInteger => test fun value => match value with | .literal (.integer _) => true | _ => false
  | .isAtom => test fun value => match value with | .literal (.atom _) => true | _ => false
  | .isTuple => test fun value => match value with | .tuple _ => true | _ => false
  | .isList => test Value.isProperList
  | .isPid => test fun value => match value with | .pid _ => true | _ => false
  | .isFunction => test fun value => match value with | .closure _ _ _ => true | _ => false
  | .isFunctionArity => match arguments with
    | [value, .literal (.integer arity)] =>
        if arity < 0 then .ok (.error .badarg)
        else success (boolean (match value with | .closure expected _ _ => arity = (expected : Int) | _ => false))
    | _ => .ok (.error .badarg)
  | .andBool => boolBinary (· && ·)
  | .orBool => boolBinary (· || ·)
  | .xorBool => boolBinary (· != ·)
  | .notBool => match arguments with
    | [value] => match boolean? value with
      | some value => success (boolean (!value))
      | none => .ok (.error .badarg)
    | _ => .ok (.error .badarg)

end Mettapedia.Languages.Erlang
