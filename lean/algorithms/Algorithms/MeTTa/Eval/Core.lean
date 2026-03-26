import MeTTailCore

/-! # LeanPeTTa Core Types

Verified MeTTa evaluator — core type definitions.

Architecture invariants (council-approved):
1. Session does NOT branch — bindings branch, session threads deterministically
2. ResultBind.binds is full post-context — not delta
3. cut = true means "may be incomplete" — for iterative deepening
-/

namespace Algorithms.MeTTa.Eval

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match hiding applyBindings

-- ─── Session ────────────────────────────────────────────────────────────

/-- A rewrite rule: `(= lhs rhs)`. -/
structure Rule where
  name : String
  left : Pattern
  right : Pattern
  deriving BEq, Repr

/-- Minimal session state for the verified evaluator. -/
structure Session where
  /-- Equation rewrite rules: `(= lhs rhs)`. -/
  rules : List Rule := []
  /-- Default space atoms (the `&self` space). -/
  space : List Pattern := []
  /-- Max reduction fuel (prevents infinite loops). -/
  maxFuel : Nat := 1000
  deriving Repr

-- ─── Binding types ──────────────────────────────────────────────────────

/-- A single result: evaluated term + full binding context. -/
structure ResultBind where
  term : Pattern
  binds : Bindings
  deriving Repr

/-- Evaluator output: updated session, list of results, and truncation flag. -/
structure EvalOut where
  s : Session
  results : List ResultBind
  cut : Bool
  deriving Repr

/-- Callback type for the evaluator (passed to non-recursive helpers). -/
abbrev EvalCallback := Session → Bindings → Pattern → EvalOut

/-- Output of evaluating a tuple of patterns (Cartesian product). -/
structure TupleOut where
  s : Session
  combos : List (List ResultBind)
  cut : Bool

-- ─── Dispatch ───────────────────────────────────────────────────────────

/-- Special forms with non-default evaluation strategies. -/
inductive SpecialForm where
  | superpose | collapse | let_ | letStar
  | if_ | case_ | match_ | once | catch | chain | progn | prog1
  deriving Repr, DecidableEq, BEq

/-- First-level dispatch: atom, special form, or ordinary call. -/
inductive Dispatch where
  | atom
  | special (sf : SpecialForm) (args : List Pattern)
  | ordinary (ctor : String) (args : List Pattern)
  deriving Repr

/-- Apply bindings as substitution. -/
def applyBinds (binds : Bindings) : Pattern → Pattern
  | .fvar x => match binds.find? (fun p => p.1 == x) with
    | some (_, v) => v
    | none => .fvar x
  | .apply c args => .apply c (args.map (applyBinds binds))
  | p => p

/-- Extract elements from an expression (for superpose). -/
def exprElems : Pattern → List Pattern
  | .apply "" tl => tl
  | .apply hd tl => .apply hd [] :: tl
  | other => [other]

/-- Wrap a list of patterns as a single expression (for collapse). -/
def mkExpr : List Pattern → Pattern
  | [] => .apply "()" []
  | [p] => p
  | (.apply hd []) :: tl => .apply hd tl
  | ps => .apply "" ps

/-- Check if a pattern is truthy (i.e., equals True). -/
def isTruthy : Pattern → Bool
  | .apply "True" [] => true
  | _ => false

/-- Resolve a variable from bindings. Non-variables return unchanged. -/
def resolveVar (binds : Bindings) : Pattern → Pattern
  | .fvar x => match binds.find? (fun p => p.1 == x) with
    | some (_, v) => v
    | none => .fvar x
  | t => t

-- ─── Pattern utilities ──────────────────────────────────────────────────

/-- Parse an integer from a pattern like `.apply "42" []`. -/
def Pattern.toInt? : Pattern → Option Int
  | .apply s [] =>
    if s.startsWith "-" then
      (s.drop 1).toNat?.map (fun n => -(n : Int))
    else
      s.toNat?.map (fun n => (n : Int))
  | _ => none

/-- Construct a pattern from an integer. -/
def Pattern.ofInt (n : Int) : Pattern :=
  .apply (toString n) []

/-- Construct a pattern from a boolean. -/
def Pattern.ofBool (b : Bool) : Pattern :=
  .apply (if b then "True" else "False") []

end Algorithms.MeTTa.Eval
