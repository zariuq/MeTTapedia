import MeTTailCore

namespace Algorithms.MeTTa.Simple

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match
open MeTTailCore.MeTTaIL.Engine
open MeTTailCore.MeTTaIL.Profile

/-- Extensional relation tuple used when lowering frozen profiles into runtime relation
environments and builtin tables. -/
structure RelationTuple where
  relation : String
  tuple : List Pattern
deriving Repr, DecidableEq

def intOfPattern? : Pattern → Option Int
  | .apply tok [] => tok.toInt?
  | _ => none

private def patternOfBool (b : Bool) : Pattern :=
  if b then .apply "True" [] else .apply "False" []

private def patternOfInt (n : Int) : Pattern :=
  .apply s!"{n}" []

private def trimFractionZeros (frac : String) : String :=
  String.ofList ((frac.toList.reverse.dropWhile (· = '0')).reverse)

private def normalizeFloatToken (tok : String) : String :=
  match tok.splitOn "." with
  | [whole, frac] =>
      let frac' := trimFractionZeros frac
      if frac'.isEmpty then
        whole ++ ".0"
      else
        whole ++ "." ++ frac'
  | _ => tok

private def patternOfFloat (x : Float) : Pattern :=
  .apply (normalizeFloatToken (toString x)) []

private def numericEqTol : Float := 0.000001

private def splitSign (tok : String) : Bool × String :=
  if tok.startsWith "-" then
    (true, (tok.drop 1).toString)
  else if tok.startsWith "+" then
    (false, (tok.drop 1).toString)
  else
    (false, tok)

private def floatOfToken? (tok : String) : Option Float :=
  match tok.toInt? with
  | some n => some (Float.ofInt n)
  | none =>
      let (neg, core) := splitSign tok
      match core.splitOn "." with
      | [whole, frac] =>
          if frac.isEmpty then
            none
          else
            let whole' := if whole.isEmpty then "0" else whole
            if !whole'.toList.all Char.isDigit || !frac.toList.all Char.isDigit then
              none
            else
              match (whole' ++ frac).toNat? with
              | none => none
              | some mantissa =>
                  let f := Float.ofScientific mantissa true frac.length
                  some (if neg then -f else f)
      | _ => none

def floatOfPattern? : Pattern → Option Float
  | .apply tok [] => floatOfToken? tok
  | _ => none

def numericOfPattern? (p : Pattern) : Option Float :=
  match intOfPattern? p with
  | some n => some (Float.ofInt n)
  | none => floatOfPattern? p

private def intListOfPattern? : Pattern → Option (List Int)
  | .collection _ elems _ => elems.mapM intOfPattern?
  | .apply head tail =>
      ((.apply head []) :: tail).mapM intOfPattern?
  | _ => none

private def tuplesFor (rows : List RelationTuple) (rel : String) (arity : Nat) :
    List (List Pattern) :=
  rows.filterMap fun row =>
    if row.relation == rel && row.tuple.length == arity then
      some row.tuple
    else
      none

/-- Lower extensional relation tuples into a runtime `RelationEnv`. -/
def relationEnvOfTuples (rows : List RelationTuple) : RelationEnv where
  tuples := fun rel args => tuplesFor rows rel args.length

/-- Lower extensional relation tuples into a runtime builtin relation table. -/
def builtinTableOfTuples (rows : List RelationTuple) : BuiltinTable where
  relation := fun rel args => tuplesFor rows rel args.length

def intrinsicRelationName (ctor : String) : String :=
  s!"intrinsic:{ctor}"

private def intrinsicCompareRows (ctor : String) (args : List Pattern) :
    List (List Pattern) :=
  match ctor, args with
  | "=", [lhs, rhs] =>
      [[patternOfBool (decide (lhs = rhs))]]
  | "if", [cond, thenBr, elseBr] =>
      let condB :=
        match cond with
        | .apply "True" [] => some true
        | .apply "true" [] => some true
        | .apply "False" [] => some false
        | .apply "false" [] => some false
        | _ => none
      match condB with
      | some true => [[thenBr]]
      | some false => [[elseBr]]
      | none => []
  | "if", [cond, thenBr] =>
      let condB :=
        match cond with
        | .apply "True" [] => some true
        | .apply "true" [] => some true
        | .apply "False" [] => some false
        | .apply "false" [] => some false
        | _ => none
      match condB with
      | some true => [[thenBr]]
      | some false => [[.apply "()" []]]
      | none => []
  | "and", xs =>
      let bs := xs.map fun x =>
        match x with
        | .apply "True" [] => some true
        | .apply "true" [] => some true
        | .apply "False" [] => some false
        | .apply "false" [] => some false
        | _ => none
      if bs.any (fun b => b = some false) then
        [[patternOfBool false]]
      else if bs.all (fun b => b = some true) then
        [[patternOfBool true]]
      else
        []
  | "or", xs =>
      let bs := xs.map fun x =>
        match x with
        | .apply "True" [] => some true
        | .apply "true" [] => some true
        | .apply "False" [] => some false
        | .apply "false" [] => some false
        | _ => none
      if bs.any (fun b => b = some true) then
        [[patternOfBool true]]
      else if bs.all (fun b => b = some false) then
        [[patternOfBool false]]
      else
        []
  | "not", [arg] =>
      let out :=
        match arg with
        | .apply "True" [] => some false
        | .apply "true" [] => some false
        | .apply "False" [] => some true
        | .apply "false" [] => some true
        | _ => none
      match out with
      | some b => [[patternOfBool b]]
      | none => []
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
        [[patternOfBool (trueCount % 2 = 1)]]
      else
        []
  | "append", [lhs, rhs] =>
      [[MeTTailCore.MeTTaIL.Match.tupleOfElems
          (MeTTailCore.MeTTaIL.Match.tupleElems lhs ++
            MeTTailCore.MeTTaIL.Match.tupleElems rhs)]]
  | "is-member", [x, xs] =>
      let elems := MeTTailCore.MeTTaIL.Match.tupleElems xs
      [[patternOfBool (elems.any (fun e => decide (e = x)))]]
  | "<", [lhs, rhs] =>
      match intOfPattern? lhs, intOfPattern? rhs with
      | some a, some b => [[patternOfBool (a < b)]]
      | _, _ =>
          match numericOfPattern? lhs, numericOfPattern? rhs with
          | some a, some b => [[patternOfBool (a < b)]]
          | _, _ => []
  | ">", [lhs, rhs] =>
      match intOfPattern? lhs, intOfPattern? rhs with
      | some a, some b => [[patternOfBool (a > b)]]
      | _, _ =>
          match numericOfPattern? lhs, numericOfPattern? rhs with
          | some a, some b => [[patternOfBool (a > b)]]
          | _, _ => []
  | "<=", [lhs, rhs] =>
      match intOfPattern? lhs, intOfPattern? rhs with
      | some a, some b => [[patternOfBool (a <= b)]]
      | _, _ =>
          match numericOfPattern? lhs, numericOfPattern? rhs with
          | some a, some b => [[patternOfBool (a <= b)]]
          | _, _ => []
  | ">=", [lhs, rhs] =>
      match intOfPattern? lhs, intOfPattern? rhs with
      | some a, some b => [[patternOfBool (a >= b)]]
      | _, _ =>
          match numericOfPattern? lhs, numericOfPattern? rhs with
          | some a, some b => [[patternOfBool (a >= b)]]
          | _, _ => []
  | "==", [lhs, rhs] =>
      match numericOfPattern? lhs, numericOfPattern? rhs with
      | some a, some b => [[patternOfBool (Float.abs (a - b) <= numericEqTol)]]
      | _, _ => [[patternOfBool (decide (lhs = rhs))]]
  | "!=", [lhs, rhs] =>
      match numericOfPattern? lhs, numericOfPattern? rhs with
      | some a, some b => [[patternOfBool (Float.abs (a - b) > numericEqTol)]]
      | _, _ => [[patternOfBool (!(decide (lhs = rhs)))]]
  | "+", x :: y :: rest =>
      match (x :: y :: rest).mapM intOfPattern? with
      | some ns => [[patternOfInt (ns.foldl (fun acc n => acc + n) 0)]]
      | none =>
          match (x :: y :: rest).mapM numericOfPattern? with
          | some ns => [[patternOfFloat (ns.foldl (fun acc n => acc + n) 0.0)]]
          | none => []
  | "+", _ => []
  | "-", [] => []
  | "-", [x] =>
      match intOfPattern? x with
      | some n => [[patternOfInt (-n)]]
      | none =>
          match numericOfPattern? x with
          | some n => [[patternOfFloat (-n)]]
          | none => []
  | "-", x :: xs =>
      match intOfPattern? x, xs.mapM intOfPattern? with
      | some n0, some rest =>
          [[patternOfInt (rest.foldl (fun acc n => acc - n) n0)]]
      | _, _ =>
          match numericOfPattern? x, xs.mapM numericOfPattern? with
          | some n0, some rest =>
              [[patternOfFloat (rest.foldl (fun acc n => acc - n) n0)]]
          | _, _ => []
  | "*", x :: y :: rest =>
      match (x :: y :: rest).mapM intOfPattern? with
      | some ns => [[patternOfInt (ns.foldl (fun acc n => acc * n) 1)]]
      | none =>
          match (x :: y :: rest).mapM numericOfPattern? with
          | some ns => [[patternOfFloat (ns.foldl (fun acc n => acc * n) 1.0)]]
          | none => []
  | "*", _ => []
  | "/", [lhs, rhs] =>
      match intOfPattern? lhs, intOfPattern? rhs with
      | some a, some b =>
          if b = 0 then [] else [[patternOfInt (a / b)]]
      | _, _ =>
          match numericOfPattern? lhs, numericOfPattern? rhs with
          | some a, some b =>
              if Float.abs b <= numericEqTol then [] else [[patternOfFloat (a / b)]]
          | _, _ => []
  | "%", [lhs, rhs] =>
      match intOfPattern? lhs, intOfPattern? rhs with
      | some a, some b =>
          if b = 0 then [] else [[patternOfInt (a % b)]]
      | _, _ => []
  | "pow-math", [lhs, rhs] =>
      match floatOfPattern? lhs, floatOfPattern? rhs with
      | some a, some b => [[patternOfFloat (Float.pow a b)]]
      | _, _ => []
  | "sqrt-math", [x] =>
      match floatOfPattern? x with
      | some n => [[patternOfFloat (Float.sqrt n)]]
      | none => []
  | "abs-math", [x] =>
      match intOfPattern? x, floatOfPattern? x with
      | some n, _ => [[patternOfInt (Int.ofNat (Int.natAbs n))]]
      | none, some n => [[patternOfFloat (Float.abs n)]]
      | _, _ => []
  | "log-math", [base, x] =>
      match floatOfPattern? base, floatOfPattern? x with
      | some b, some n =>
          if b == 0.0 || b == 1.0 || n <= 0.0 then
            []
          else
            [[patternOfFloat (Float.log n / Float.log b)]]
      | _, _ => []
  | "trunc-math", [x] =>
      match floatOfPattern? x with
      | some n =>
          let t := if n < 0.0 then Float.ceil n else Float.floor n
          [[patternOfFloat t]]
      | none => []
  | "ceil-math", [x] =>
      match floatOfPattern? x with
      | some n => [[patternOfFloat (Float.ceil n)]]
      | none => []
  | "floor-math", [x] =>
      match floatOfPattern? x with
      | some n => [[patternOfFloat (Float.floor n)]]
      | none => []
  | "round-math", [x] =>
      match floatOfPattern? x with
      | some n => [[patternOfFloat (Float.round n)]]
      | none => []
  | "sin-math", [x] =>
      match floatOfPattern? x with
      | some n => [[patternOfFloat (Float.sin n)]]
      | none => []
  | "asin-math", [x] =>
      match floatOfPattern? x with
      | some n => [[patternOfFloat (Float.asin n)]]
      | none => []
  | "cos-math", [x] =>
      match floatOfPattern? x with
      | some n => [[patternOfFloat (Float.cos n)]]
      | none => []
  | "acos-math", [x] =>
      match floatOfPattern? x with
      | some n => [[patternOfFloat (Float.acos n)]]
      | none => []
  | "tan-math", [x] =>
      match floatOfPattern? x with
      | some n => [[patternOfFloat (Float.tan n)]]
      | none => []
  | "atan-math", [x] =>
      match floatOfPattern? x with
      | some n => [[patternOfFloat (Float.atan n)]]
      | none => []
  | "isnan-math", [x] =>
      match floatOfPattern? x with
      | some n => [[patternOfBool (Float.isNaN n)]]
      | none => []
  | "isinf-math", [x] =>
      match floatOfPattern? x with
      | some n => [[patternOfBool (!Float.isNaN n && !Float.isFinite n)]]
      | none => []
  | "cons", [head, tail] =>
      [[tupleOfElems (head :: tupleElems tail)]]
  | "min-atom", [xs] =>
      match intListOfPattern? xs with
      | none => []
      | some [] => []
      | some (x :: rest) =>
          [[patternOfInt (rest.foldl (fun acc n => if n < acc then n else acc) x)]]
  | "max-atom", [xs] =>
      match intListOfPattern? xs with
      | none => []
      | some [] => []
      | some (x :: rest) =>
          [[patternOfInt (rest.foldl (fun acc n => if n > acc then n else acc) x)]]
  | _, _ => []

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
