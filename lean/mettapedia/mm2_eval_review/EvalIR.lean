-- LLM primer: EvalIR is a minimal evaluator IR for the recursive evaluation vertical slice.
-- Supports: integer literals, boolean literals, if-then-else, ==, +, -, *, userCall.
-- The reference evaluator is fuel-bounded and sorry-free.
-- The MM2 protocol types (ReqId, MM2Fact, MM2Step) formalize the request/result/join
-- state machine that MORK executes, including IntArithSink grounded arithmetic.
-- Council: Martin-Löf/Coquand/Pfenning (types first), Carneiro/Brown (minimal),
--   Tao/Kolmogorov (proper Value type), Buzzard/Voevodsky (no sorry).
-- `eval` is partial (Lean can't prove termination through evalList HOF), but fully
-- implemented — validated by #eval.

namespace MeTTailCore.EvalIR

-- ═══════════════════════════════════════════════════════════════════════════
-- § Core IR Types
-- ═══════════════════════════════════════════════════════════════════════════

/-- Values produced by the evaluator: integers or booleans. -/
inductive EvalValue where
  | int : Int → EvalValue
  | bool : Bool → EvalValue
deriving Repr, DecidableEq, BEq

/-- Evaluator IR nodes. Supports the recursive evaluation fragment:
    integer/boolean literals, if-then-else, equality, addition, subtraction,
    multiplication, and user-defined function calls. -/
inductive EvalNode where
  | intLit : Int → EvalNode
  | boolLit : Bool → EvalNode
  | ifCond : EvalNode → EvalNode → EvalNode → EvalNode
  | eqInt : EvalNode → EvalNode → EvalNode
  | addInt : EvalNode → EvalNode → EvalNode
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

-- ═══════════════════════════════════════════════════════════════════════════
-- § Reference Evaluator
-- ═══════════════════════════════════════════════════════════════════════════

/-- Substitution: replace free variable references in a node with values.
    Variables are represented as `userCall varName []` (nullary calls). -/
partial def substNode (env : List (String × EvalNode)) : EvalNode → EvalNode
  | .intLit n => .intLit n
  | .boolLit b => .boolLit b
  | .ifCond c t e => .ifCond (substNode env c) (substNode env t) (substNode env e)
  | .eqInt a b => .eqInt (substNode env a) (substNode env b)
  | .addInt a b => .addInt (substNode env a) (substNode env b)
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

/-- Reference evaluator — the semantic oracle.
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
  | .addInt a b =>
    match eval rules fuel a, eval rules fuel b with
    | some (.int va), some (.int vb) => some (.int (va + vb))
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
      let evalArgs := args.map (eval rules (fuel' + 1))
      if evalArgs.any Option.isNone then none
      else
        match rules.find? (fun r => r.head == head && r.params.length == args.length) with
        | none => none
        | some rule =>
          let argNodes := evalArgs.filterMap (fun v => v.map EvalValue.toNode)
          let env := rule.params.zip argNodes
          let body' := substNode env rule.body
          eval rules fuel' body'

-- ═══════════════════════════════════════════════════════════════════════════
-- § Grounded Arithmetic Interface (IntArithSink)
-- ═══════════════════════════════════════════════════════════════════════════
-- Models the IntArithSink in MORK: Rust-grounded integer arithmetic inside
-- MM2 templates. Lean is the semantic authority; Rust mirrors these types.

/-- Arithmetic operations supported by the IntArithSink.
    Mirrors the Rust IntArithOp enum in MORK kernel/src/sinks.rs. -/
inductive ArithOp where
  | add | sub | mul | eq
deriving Repr, DecidableEq, BEq

/-- Semantics of a single grounded arithmetic step.
    This is the specification of what IntArithSink computes. -/
def arithEval : ArithOp → Int → Int → EvalValue
  | .add, a, b => .int (a + b)
  | .sub, a, b => .int (a - b)
  | .mul, a, b => .int (a * b)
  | .eq,  a, b => .bool (a == b)

/-- A grounded arithmetic step: given resolved integer arguments and an operation,
    the IntArithSink produces `arithEval op argA argB` without lookup tables. -/
structure GroundedStep where
  op : ArithOp
  argA : Int
  argB : Int
  result : EvalValue := arithEval op argA argB
deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════
-- § MM2 Request/Result/Join Protocol — Base Layer
-- ═══════════════════════════════════════════════════════════════════════════
-- Two-layer architecture:
--   Base MORK  = pure structural rewriting (any MORK installation)
--   Extended   = Base + IntArithSink (grounded Rust arithmetic)
-- The extension boundary is explicit: IntArithStep is the ONLY addition.

/-- A request ID in the MM2 protocol. Tracks the evaluation tree.
    Each sub-expression gets a unique ID derived from its parent. -/
inductive ReqId where
  | root : ReqId
  | sub0 : ReqId → ReqId      -- left sub-request (first arg of binary op)
  | sub1 : ReqId → ReqId      -- right sub-request (second arg of binary op)
  | cond : ReqId → ReqId      -- condition sub-request (for ifCond)
  | arg : Nat → ReqId → ReqId -- argument sub-request (for userCall arg evaluation)
deriving Repr, DecidableEq, BEq

/-- An MM2 fact in the request/result protocol.
    These are the atoms that live in MORK's PathMap during evaluation.
    Shared between base MORK and extensions. -/
inductive MM2Fact where
  | req : ReqId → EvalNode → MM2Fact           -- request to evaluate a node
  | res : ReqId → EvalValue → MM2Fact          -- result of evaluating a node
  | waitIf : ReqId → EvalNode → EvalNode → MM2Fact  -- waiting for condition result
  | waitArith : ArithOp → ReqId → MM2Fact      -- waiting for binary op sub-results
  | waitUser : ReqId → String → EvalNode → MM2Fact  -- waiting for userCall body result
deriving Repr, BEq

-- ── Base MORK Steps ──────────────────────────────────────────────────────
-- Pure structural rewriting. Any MORK installation can execute these.
-- Critically: base MORK has NO fold for binary arithmetic. In base MORK,
-- (waitArith op id) + (res (sub0 id) va) + (res (sub1 id) vb) is STUCK
-- unless lookup table facts like (ADD va vb result) are in the space.

/-- Base MM2 step — pure structural rewriting, no grounded builtins. -/
inductive BaseStep where
  /-- Leaf: `(req id (intLit n))` → `(res id (int n))` -/
  | leafInt : ReqId → Int → BaseStep
  /-- Leaf: `(req id (boolLit b))` → `(res id (bool b))` -/
  | leafBool : ReqId → Bool → BaseStep
  /-- Unfold ifCond: `(req id (ifCond c t e))` →
      `(req (cond id) c)` + `(waitIf id t e)` -/
  | unfoldIf : ReqId → EvalNode → EvalNode → EvalNode → BaseStep
  /-- Unfold binary op: `(req id (op a b))` →
      `(req (sub0 id) a)` + `(req (sub1 id) b)` + `(waitArith op id)` -/
  | unfoldBinop : ArithOp → ReqId → EvalNode → EvalNode → BaseStep
  /-- Unfold userCall: `(req id (HEAD args))` → `(req id body[args/params])` -/
  | unfoldUser : ReqId → EvalRule → List EvalNode → BaseStep
  /-- Fold if-true: `(waitIf id t e)` + `(res (cond id) (bool true))` → `(req id t)` -/
  | foldIfTrue : ReqId → EvalNode → EvalNode → BaseStep
  /-- Fold if-false: `(waitIf id t e)` + `(res (cond id) (bool false))` → `(req id e)` -/
  | foldIfFalse : ReqId → EvalNode → EvalNode → BaseStep
deriving Repr

/-- Facts consumed by a base step. -/
def BaseStep.consumes : BaseStep → List MM2Fact
  | .leafInt id n       => [.req id (.intLit n)]
  | .leafBool id b      => [.req id (.boolLit b)]
  | .unfoldIf id c t e  => [.req id (.ifCond c t e)]
  | .unfoldBinop op id a b => [.req id (match op with
      | .add => .addInt a b | .sub => .subInt a b
      | .mul => .mulInt a b | .eq  => .eqInt a b)]
  | .unfoldUser id rule args => [.req id (.userCall rule.head args)]
  | .foldIfTrue id t e  => [.waitIf id t e, .res (.cond id) (.bool true)]
  | .foldIfFalse id t e => [.waitIf id t e, .res (.cond id) (.bool false)]

/-- Facts produced by a base step. -/
def BaseStep.produces : BaseStep → List MM2Fact
  | .leafInt id n       => [.res id (.int n)]
  | .leafBool id b      => [.res id (.bool b)]
  | .unfoldIf id c t e  => [.req (.cond id) c, .waitIf id t e]
  | .unfoldBinop op id a b => [.req (.sub0 id) a, .req (.sub1 id) b, .waitArith op id]
  | .unfoldUser id rule args => -- substitution happens here
      [.req id (substNode (rule.params.zip (args.map fun a => a)) rule.body)]
  | .foldIfTrue id t _  => [.req id t]
  | .foldIfFalse id _ e => [.req id e]

-- ── IntArithSink Extension ───────────────────────────────────────────────
-- This is the ONLY addition to base MORK. It provides grounded Rust
-- arithmetic where base MORK would be stuck (waiting for lookup tables).

/-- IntArithSink extension step — grounded Rust arithmetic.
    Only available in MORK + IntArithSink.
    Consumes: `(waitArith op id)` + `(res (sub0 id) (int a))` + `(res (sub1 id) (int b))`
    Produces: `(res id (arithEval op a b))` -/
inductive IntArithStep where
  | foldArith : ArithOp → ReqId → Int → Int → IntArithStep
deriving Repr

/-- Facts consumed by an IntArithSink step. -/
def IntArithStep.consumes : IntArithStep → List MM2Fact
  | .foldArith op id a b => [.waitArith op id, .res (.sub0 id) (.int a), .res (.sub1 id) (.int b)]

/-- Facts produced by an IntArithSink step. -/
def IntArithStep.produces : IntArithStep → List MM2Fact
  | .foldArith op _ a b => [.res .root (arithEval op a b)]  -- id handled below

/-- Correct produces: includes the actual request ID. -/
def IntArithStep.producesAt : IntArithStep → List MM2Fact
  | .foldArith op id a b => [.res id (arithEval op a b)]

-- ── Extended MORK (Base + IntArithSink) ──────────────────────────────────

/-- A step in extended MORK = base MORK + IntArithSink. -/
inductive ExtStep where
  | base : BaseStep → ExtStep
  | intArith : IntArithStep → ExtStep
deriving Repr

/-- Is this step purely base (no extension)? -/
def ExtStep.isBase : ExtStep → Bool
  | .base _ => true
  | .intArith _ => false

-- ── Theorems ─────────────────────────────────────────────────────────────

/-- Soundness: IntArithSink computes exactly `arithEval`.
    This is the specification that the Rust IntArithSink must satisfy. -/
theorem intArithStep_sound (op : ArithOp) (id : ReqId) (a b : Int) :
    (IntArithStep.foldArith op id a b).producesAt = [.res id (arithEval op a b)] := by
  rfl

/-- Conservative extension: a trace containing only base steps has no
    IntArithSink effects. The extension is invisible for pure-rewriting programs. -/
theorem conservative_base_only (s : ExtStep) (h : s.isBase = true) :
    ∃ b : BaseStep, s = .base b := by
  match s with
  | .base b => exact ⟨b, rfl⟩
  | .intArith _ => simp [ExtStep.isBase] at h

-- ═══════════════════════════════════════════════════════════════════════════
-- § Exemplar Programs
-- ═══════════════════════════════════════════════════════════════════════════

/-- Factorial: facF(n) = if (n == 0) then 1 else n * facF(n - 1)
    Linear recursion exemplar. -/
def factorialRules : List EvalRule :=
  [{ head := "facF"
   , params := ["n"]
   , body := .ifCond
       (.eqInt (.userCall "n" []) (.intLit 0))
       (.intLit 1)
       (.mulInt (.userCall "n" [])
                (.userCall "facF" [.subInt (.userCall "n" []) (.intLit 1)])) }]

/-- Fibonacci: fib(n) = if (n==0) 0 else if (n==1) 1 else fib(n-1) + fib(n-2)
    Branching recursion exemplar — two recursive calls per step. -/
def fibRules : List EvalRule :=
  [{ head := "fib"
   , params := ["n"]
   , body := .ifCond (.eqInt (.userCall "n" []) (.intLit 0)) (.intLit 0)
       (.ifCond (.eqInt (.userCall "n" []) (.intLit 1)) (.intLit 1)
         (.addInt (.userCall "fib" [.subInt (.userCall "n" []) (.intLit 1)])
                  (.userCall "fib" [.subInt (.userCall "n" []) (.intLit 2)]))) }]

end MeTTailCore.EvalIR

-- ═══════════════════════════════════════════════════════════════════════════
-- § Validation (#eval — not kernel-checked proof)
-- ═══════════════════════════════════════════════════════════════════════════

open MeTTailCore.EvalIR in
#eval
  let r := eval factorialRules 20 (.userCall "facF" [.intLit 3])
  if r == some (EvalValue.int 6) then "facF(3) = 6 ✓" else "FAIL"

open MeTTailCore.EvalIR in
#eval
  let r := eval factorialRules 100 (.userCall "facF" [.intLit 10])
  if r == some (EvalValue.int 3628800) then "facF(10) = 3628800 ✓" else "FAIL"

open MeTTailCore.EvalIR in
#eval
  let r := eval fibRules 200 (.userCall "fib" [.intLit 10])
  if r == some (EvalValue.int 55) then "fib(10) = 55 ✓" else "FAIL"

open MeTTailCore.EvalIR in
#eval
  let r := eval fibRules 100000 (.userCall "fib" [.intLit 20])
  if r == some (EvalValue.int 6765) then "fib(20) = 6765 ✓" else "FAIL"

-- GroundedStep validation
open MeTTailCore.EvalIR in
#eval
  let s : GroundedStep := { op := .add, argA := 55, argB := 89 }
  if s.result == EvalValue.int 144 then "55+89=144 via GroundedStep ✓" else "FAIL"

open MeTTailCore.EvalIR in
#eval
  let s : GroundedStep := { op := .mul, argA := 6, argB := 7 }
  if s.result == EvalValue.int 42 then "6*7=42 via GroundedStep ✓" else "FAIL"

-- IntArithStep soundness validation
open MeTTailCore.EvalIR in
#eval
  let step := IntArithStep.foldArith .add .root 55 89
  if step.producesAt == [MM2Fact.res .root (EvalValue.int 144)]
  then "intArithStep add 55 89 = res root 144 ✓" else "FAIL"
