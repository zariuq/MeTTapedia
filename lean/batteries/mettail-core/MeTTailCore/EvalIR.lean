-- LLM primer: EvalIR is a MINIMAL evaluator IR for the factorial vertical slice.
-- Only supports: integer literals, boolean literals, if-then-else, ==, -, *, userCall.
-- The reference evaluator is fuel-bounded and sorry-free.
-- Council: Martin-Löf/Coquand/Pfenning (types first), Carneiro/Brown (minimal),
--   Tao/Kolmogorov (proper Value type), Buzzard/Voevodsky (no sorry).
-- `eval` is partial (Lean can't prove termination through evalList HOF), but fully
-- implemented — validated by #eval.

namespace MeTTailCore.EvalIR

/-- Values produced by the evaluator: integers or booleans.
    Tao/Kolmogorov: proper sum type, not int-encoded booleans. -/
inductive EvalValue where
  | int : Int → EvalValue
  | bool : Bool → EvalValue
deriving Repr, DecidableEq, BEq

/-- Minimal evaluator IR for the factorial vertical slice.
    Supports only: integer literals, boolean literals, if-then-else,
    integer equality, subtraction, multiplication, and one user-defined head. -/
inductive EvalNode where
  | intLit : Int → EvalNode
  | boolLit : Bool → EvalNode
  | ifCond : EvalNode → EvalNode → EvalNode → EvalNode
  | eqInt : EvalNode → EvalNode → EvalNode
  | subInt : EvalNode → EvalNode → EvalNode
  | mulInt : EvalNode → EvalNode → EvalNode
  | userCall : String → List EvalNode → EvalNode
deriving Repr, BEq

/-- A user-defined rule: head name, parameter names, body expression. -/
structure EvalRule where
  head : String
  params : List String
  body : EvalNode
deriving Repr

/-- Substitution: replace free variable references in a node with values.
    Variables are represented as `userCall varName []` (nullary calls). -/
partial def substNode (env : List (String × EvalNode)) : EvalNode → EvalNode
  | .intLit n => .intLit n
  | .boolLit b => .boolLit b
  | .ifCond c t e => .ifCond (substNode env c) (substNode env t) (substNode env e)
  | .eqInt a b => .eqInt (substNode env a) (substNode env b)
  | .subInt a b => .subInt (substNode env a) (substNode env b)
  | .mulInt a b => .mulInt (substNode env a) (substNode env b)
  | .userCall head args =>
    match args with
    | [] =>
      match env.find? (fun p => p.1 == head) with
      | some (_, replacement) => replacement
      | none => .userCall head []
    | _ => .userCall head (args.map (substNode env))

/-- Convert an EvalValue back to an EvalNode (for substitution after evaluation). -/
def EvalValue.toNode : EvalValue → EvalNode
  | .int n => .intLit n
  | .bool b => .boolLit b

/-- Reference evaluator — the semantic oracle for the factorial fragment.
    Fuel-bounded: fuel is consumed only by userCall (recursive calls).
    `partial` because Lean can't see termination through the List.map in arg eval. -/
partial def eval (rules : List EvalRule) (fuel : Nat) : EvalNode → Option EvalValue
  | .intLit n => some (.int n)
  | .boolLit b => some (.bool b)
  | .ifCond c t e =>
    match eval rules fuel c with
    | some (.bool true) => eval rules fuel t
    | some (.bool false) => eval rules fuel e
    | _ => none
  | .eqInt a b =>
    match eval rules fuel a, eval rules fuel b with
    | some (.int va), some (.int vb) => some (.bool (va == vb))
    | _, _ => none
  | .subInt a b =>
    match eval rules fuel a, eval rules fuel b with
    | some (.int va), some (.int vb) => some (.int (va - vb))
    | _, _ => none
  | .mulInt a b =>
    match eval rules fuel a, eval rules fuel b with
    | some (.int va), some (.int vb) => some (.int (va * vb))
    | _, _ => none
  | .userCall head args =>
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      -- evaluate arguments
      let evalArgs := args.map (eval rules (fuel' + 1))
      if evalArgs.any Option.isNone then none
      else
        -- find matching rule
        match rules.find? (fun r => r.head == head && r.params.length == args.length) with
        | none => none
        | some rule =>
          -- substitute evaluated args into rule body
          let argNodes := evalArgs.filterMap (fun v =>
            v.map EvalValue.toNode)
          let env := rule.params.zip argNodes
          let body' := substNode env rule.body
          eval rules fuel' body'

/-- The factorial rule in EvalIR form.
    facF(n) = if (n == 0) then 1 else n * facF(n - 1) -/
def factorialRules : List EvalRule :=
  [{ head := "facF"
   , params := ["n"]
   , body := .ifCond
       (.eqInt (.userCall "n" []) (.intLit 0))
       (.intLit 1)
       (.mulInt (.userCall "n" [])
                (.userCall "facF" [.subInt (.userCall "n" []) (.intLit 1)])) }]

end MeTTailCore.EvalIR

open MeTTailCore.EvalIR in
#eval
  let r := eval factorialRules 20 (.userCall "facF" [.intLit 3])
  if r == some (EvalValue.int 6) then "facF(3) = 6 ✓" else "FAIL"

open MeTTailCore.EvalIR in
#eval
  let r := eval factorialRules 100 (.userCall "facF" [.intLit 10])
  if r == some (EvalValue.int 3628800) then "facF(10) = 3628800 ✓" else "FAIL"
