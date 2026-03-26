-- Relations.lean EXCERPT — singleton chain only
import MeTTailCore

set_option maxHeartbeats 400000

namespace Algorithms.MeTTa.Simple

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match
open MeTTailCore.MeTTaIL.Engine
open MeTTailCore.MeTTaIL.Profile
-- ...
-- rowsOf? lifts an optional single result into the row-list format used by BuiltinTable.
-- Every branch of intrinsicCompareRow? returns at most one result (Option), so the
-- singleton theorem below is structural rather than brute-forced.
private def rowsOf? (o : Option Pattern) : List (List Pattern) :=
  match o with
  | some p => [[p]]
  | none => []

private theorem rowsOf?_length_le_one (o : Option Pattern) :
    (rowsOf? o).length ≤ 1 := by
  cases o <;> simp [rowsOf?]

-- NOTE: hAgreeRaw is LIKELY STILL FALSE even with the 7 runtime guards.
-- A third falsity vector (translator/root-rule fires before arg eval; ref can still expose
-- arg-level reductions on the same term) has NOT yet been ruled out.
-- Do NOT prove raw hAgreeRaw; prove hAgreeSupported (SupportedDeterministic-gated) first.

private def intrinsicCompareRow? (ctor : String) (args : List Pattern) : Option Pattern :=
  match ctor, args with
  | "=", [lhs, rhs] =>
      some (patternOfBool (decide (lhs = rhs)))
  | "if", [cond, thenBr, elseBr] =>
      let condB :=
        match cond with
        | .apply "True" [] => some true
        | .apply "true" [] => some true
        | .apply "False" [] => some false
        | .apply "false" [] => some false
        | _ => none
      match condB with
      | some true => some thenBr
      | some false => some elseBr
      | none => none
  | "if", [cond, thenBr] =>
      let condB :=
        match cond with
        | .apply "True" [] => some true
        | .apply "true" [] => some true
        | .apply "False" [] => some false
        | .apply "false" [] => some false
        | _ => none
      match condB with
      | some true => some thenBr
      | some false => some (.apply "()" [])
      | none => none
  | "and", xs =>
      let bs := xs.map fun x =>
        match x with
        | .apply "True" [] => some true
        | .apply "true" [] => some true
        | .apply "False" [] => some false
        | .apply "false" [] => some false
        | _ => none
      if bs.any (fun b => b = some false) then
        some (patternOfBool false)
      else if bs.all (fun b => b = some true) then
        some (patternOfBool true)
      else
        none
  | "or", xs =>
      let bs := xs.map fun x =>
        match x with
        | .apply "True" [] => some true
        | .apply "true" [] => some true
        | .apply "False" [] => some false
        | .apply "false" [] => some false
        | _ => none
      if bs.any (fun b => b = some true) then
        some (patternOfBool true)
      else if bs.all (fun b => b = some false) then
        some (patternOfBool false)
      else
        none
  | "not", [arg] =>
      let out :=
        match arg with
        | .apply "True" [] => some false
        | .apply "true" [] => some false
        | .apply "False" [] => some true
        | .apply "false" [] => some true
        | _ => none
      match out with
      | some b => some (patternOfBool b)
      | none => none
  | "xor", xs =>
      let bs := xs.map fun x =>
        match x with
        | .apply "True" [] => some true
        | .apply "true" [] => some true
        | .apply "False" [] => some false
        | .apply "false" [] => some false
        | _ => none
      if bs.all Option.isSome then
        let trueCount := (bs.filter (fun b => b == some true)).length
        some (patternOfBool (trueCount % 2 = 1))
      else
        none
  | "append", [lhs, rhs] =>
      some (MeTTailCore.MeTTaIL.Match.tupleOfElems
          (MeTTailCore.MeTTaIL.Match.tupleElems lhs ++
            MeTTailCore.MeTTaIL.Match.tupleElems rhs))
  | "is-member", [x, xs] =>
      let elems := MeTTailCore.MeTTaIL.Match.tupleElems xs
      some (patternOfBool (elems.any (fun e => decide (e = x))))
  | "<", [lhs, rhs] =>
      match intOfPattern? lhs, intOfPattern? rhs with
      | some a, some b => some (patternOfBool (a < b))
      | _, _ =>
          match numericOfPattern? lhs, numericOfPattern? rhs with
          | some a, some b => some (patternOfBool (a < b))
          | _, _ => none
  | ">", [lhs, rhs] =>
      match intOfPattern? lhs, intOfPattern? rhs with
      | some a, some b => some (patternOfBool (a > b))
      | _, _ =>
          match numericOfPattern? lhs, numericOfPattern? rhs with
          | some a, some b => some (patternOfBool (a > b))
          | _, _ => none
  | "<=", [lhs, rhs] =>
      match intOfPattern? lhs, intOfPattern? rhs with
      | some a, some b => some (patternOfBool (a <= b))
      | _, _ =>
          match numericOfPattern? lhs, numericOfPattern? rhs with
          | some a, some b => some (patternOfBool (a <= b))
          | _, _ => none
  | ">=", [lhs, rhs] =>
      match intOfPattern? lhs, intOfPattern? rhs with
      | some a, some b => some (patternOfBool (a >= b))
      | _, _ =>
          match numericOfPattern? lhs, numericOfPattern? rhs with
          | some a, some b => some (patternOfBool (a >= b))
          | _, _ => none
  | "==", [lhs, rhs] =>
      match numericOfPattern? lhs, numericOfPattern? rhs with
      | some a, some b => some (patternOfBool (Float.abs (a - b) <= numericEqTol))
      | _, _ => some (patternOfBool (decide (lhs = rhs)))
  | "!=", [lhs, rhs] =>
      match numericOfPattern? lhs, numericOfPattern? rhs with
      | some a, some b => some (patternOfBool (Float.abs (a - b) > numericEqTol))
      | _, _ => some (patternOfBool (!(decide (lhs = rhs))))
  | "+", x :: y :: rest =>
      match (x :: y :: rest).mapM intOfPattern? with
      | some ns => some (patternOfInt (ns.foldl (fun acc n => acc + n) 0))
      | none =>
          match (x :: y :: rest).mapM numericOfPattern? with
          | some ns => some (patternOfFloat (ns.foldl (fun acc n => acc + n) 0.0))
          | none => none
  | "+", _ => none
  | "-", [] => none
  | "-", [x] =>
      match intOfPattern? x with
      | some n => some (patternOfInt (-n))
      | none =>
          match numericOfPattern? x with
          | some n => some (patternOfFloat (-n))
          | none => none
  | "-", x :: xs =>
      match intOfPattern? x, xs.mapM intOfPattern? with
      | some n0, some rest =>
          some (patternOfInt (rest.foldl (fun acc n => acc - n) n0))
      | _, _ =>
          match numericOfPattern? x, xs.mapM numericOfPattern? with
          | some n0, some rest =>
              some (patternOfFloat (rest.foldl (fun acc n => acc - n) n0))
          | _, _ => none
  | "*", x :: y :: rest =>
      match (x :: y :: rest).mapM intOfPattern? with
      | some ns => some (patternOfInt (ns.foldl (fun acc n => acc * n) 1))
      | none =>
          match (x :: y :: rest).mapM numericOfPattern? with
          | some ns => some (patternOfFloat (ns.foldl (fun acc n => acc * n) 1.0))
          | none => none
  | "*", _ => none
  | "/", [lhs, rhs] =>
      match intOfPattern? lhs, intOfPattern? rhs with
      | some a, some b =>
          if b = 0 then none else some (patternOfInt (a / b))
      | _, _ =>
          match numericOfPattern? lhs, numericOfPattern? rhs with
          | some a, some b =>
              if Float.abs b <= numericEqTol then none else some (patternOfFloat (a / b))
          | _, _ => none
  | "%", [lhs, rhs] =>
      match intOfPattern? lhs, intOfPattern? rhs with
      | some a, some b =>
          if b = 0 then none else some (patternOfInt (a % b))
      | _, _ => none
  | "pow-math", [lhs, rhs] =>
      match floatOfPattern? lhs, floatOfPattern? rhs with
      | some a, some b => some (patternOfFloat (Float.pow a b))
      | _, _ => none
  | "sqrt-math", [x] =>
      match floatOfPattern? x with
      | some n => some (patternOfFloat (Float.sqrt n))
      | none => none
  | "abs-math", [x] =>
      match intOfPattern? x, floatOfPattern? x with
      | some n, _ => some (patternOfInt (Int.ofNat (Int.natAbs n)))
      | none, some n => some (patternOfFloat (Float.abs n))
      | _, _ => none
  | "log-math", [base, x] =>
      match floatOfPattern? base, floatOfPattern? x with
      | some b, some n =>
          if b == 0.0 || b == 1.0 || n <= 0.0 then
            none
          else
            some (patternOfFloat (Float.log n / Float.log b))
      | _, _ => none
  | "trunc-math", [x] =>
      match floatOfPattern? x with
      | some n =>
          let t := if n < 0.0 then Float.ceil n else Float.floor n
          some (patternOfFloat t)
      | none => none
  | "ceil-math", [x] =>
      match floatOfPattern? x with
      | some n => some (patternOfFloat (Float.ceil n))
      | none => none
  | "floor-math", [x] =>
      match floatOfPattern? x with
      | some n => some (patternOfFloat (Float.floor n))
      | none => none
  | "round-math", [x] =>
      match floatOfPattern? x with
      | some n => some (patternOfFloat (Float.round n))
      | none => none
  | "sin-math", [x] =>
      match floatOfPattern? x with
      | some n => some (patternOfFloat (Float.sin n))
      | none => none
  | "asin-math", [x] =>
      match floatOfPattern? x with
      | some n => some (patternOfFloat (Float.asin n))
      | none => none
  | "cos-math", [x] =>
      match floatOfPattern? x with
      | some n => some (patternOfFloat (Float.cos n))
      | none => none
  | "acos-math", [x] =>
      match floatOfPattern? x with
      | some n => some (patternOfFloat (Float.acos n))
      | none => none
  | "tan-math", [x] =>
      match floatOfPattern? x with
      | some n => some (patternOfFloat (Float.tan n))
      | none => none
  | "atan-math", [x] =>
      match floatOfPattern? x with
      | some n => some (patternOfFloat (Float.atan n))
      | none => none
  | "isnan-math", [x] =>
      match floatOfPattern? x with
      | some n => some (patternOfBool (Float.isNaN n))
      | none => none
  | "isinf-math", [x] =>
      match floatOfPattern? x with
      | some n => some (patternOfBool (!Float.isNaN n && !Float.isFinite n))
      | none => none
  | "cons", [head, tail] =>
      some (tupleOfElems (head :: tupleElems tail))
  | "min-atom", [xs] =>
      match intListOfPattern? xs with
      | none => none
      | some [] => none
      | some (x :: rest) =>
          some (patternOfInt (rest.foldl (fun acc n => if n < acc then n else acc) x))
  | "max-atom", [xs] =>
      match intListOfPattern? xs with
      | none => none
      | some [] => none
      | some (x :: rest) =>
          some (patternOfInt (rest.foldl (fun acc n => if n > acc then n else acc) x))
  | _, _ => none

-- Every intrinsicCompareRow? branch returns at most one result (Option), so the row-list
-- wrapper also has length ≤ 1.  This is structural, not a brute-force case split.
private def intrinsicCompareRows (ctor : String) (args : List Pattern) :
    List (List Pattern) :=
  rowsOf? (intrinsicCompareRow? ctor args)

theorem intrinsicCompareRows_length_le_one (ctor : String) (args : List Pattern) :
    (intrinsicCompareRows ctor args).length ≤ 1 := by
  simpa [intrinsicCompareRows] using rowsOf?_length_le_one (intrinsicCompareRow? ctor args)

private def parseIntrinsicCtor? (rel : String) : Option String :=
  if rel.startsWith "intrinsic:" then
    some ((rel.drop 10).toString)
  else
    none

/-- Core profile-backed intrinsic builtins shared by simple runtimes. -/
def coreIntrinsicBuiltins : BuiltinTable where
  relation := fun rel args =>
    match parseIntrinsicCtor? rel with
    | some ctor => intrinsicCompareRows ctor args
    | none => []

def mergeBuiltinTables (left right : BuiltinTable) : BuiltinTable where
  relation := fun rel args => left.relation rel args ++ right.relation rel args

private def conflictingEqBuiltin : BuiltinTable where
  relation := fun rel args =>
    match rel, args with
    | "intrinsic:=", [.apply "True" [], .apply "True" []] =>
        [[.apply "False" []]]
    | _, _ => []

private theorem parseIntrinsicCtor_intrinsicEq :
    parseIntrinsicCtor? "intrinsic:=" = some "=" := by
  native_decide

theorem coreIntrinsicBuiltins_relation_length_le_one (rel : String) (args : List Pattern) :
    (coreIntrinsicBuiltins.relation rel args).length ≤ 1 := by
  simp only [coreIntrinsicBuiltins]
  match parseIntrinsicCtor? rel with
  | some ctor => exact intrinsicCompareRows_length_le_one ctor args
  | none => simp

theorem coreIntrinsicBuiltins_eq_true_true_singleton :
    coreIntrinsicBuiltins.relation "intrinsic:=" [.apply "True" [], .apply "True" []] =
      [[.apply "True" []]] := by
  change
    (match parseIntrinsicCtor? "intrinsic:=" with
    | some ctor => intrinsicCompareRows ctor [.apply "True" [], .apply "True" []]
    | none => []) = [[.apply "True" []]]
  rw [parseIntrinsicCtor_intrinsicEq]
  rfl

theorem mergeBuiltinTables_can_duplicate_intrinsic_results :
    (mergeBuiltinTables coreIntrinsicBuiltins conflictingEqBuiltin).relation
        "intrinsic:=" [.apply "True" [], .apply "True" []] =
      [[.apply "True" []], [.apply "False" []]] := by
  change
    (match parseIntrinsicCtor? "intrinsic:=" with
    | some ctor => intrinsicCompareRows ctor [.apply "True" [], .apply "True" []]
    | none => []) ++ conflictingEqBuiltin.relation "intrinsic:=" [.apply "True" [], .apply "True" []] =
      [[.apply "True" []], [.apply "False" []]]
  rw [parseIntrinsicCtor_intrinsicEq]
  rfl

end Algorithms.MeTTa.Simple
