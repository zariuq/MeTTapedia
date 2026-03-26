import Algorithms.MeTTa.Eval.Core
import Algorithms.MeTTa.Eval.Step.Arithmetic
import Algorithms.MeTTa.Eval.Step.PatternOps
import Algorithms.MeTTa.Eval.Step.Logic
import Algorithms.MeTTa.Eval.Step.SpaceOps
import Algorithms.MeTTa.Eval.Step.StreamOps
import Algorithms.MeTTa.Eval.Step.Rules

/-! # LeanPeTTa Head-Step — all-eager operators only

Pure head reducer on already-evaluated args. NO arg reduction.
NO control flow. NO operators with lazy/literal/collecting args.
Those are ALL handled by controlEval? in Eval.lean.

headStep? fires only on all-eager operators where every arg
has already been evaluated by eval?'s Cartesian product.
-/

namespace Algorithms.MeTTa.Eval

open MeTTailCore.MeTTaIL.Syntax

/-- Head-step on all-eager operators. Args are already evaluated. -/
def headStep? (s : Session) (ctor : String) (args : List Pattern) :
    Option (Session × List Pattern) :=
  -- 1. Stateful space ops (add-atom, remove-atom, get-atoms)
  match Step.SpaceOps.evalSpaceOp s ctor args with
  | some result => some result
  | none =>
  -- 2. Pure arithmetic/comparison
  match Step.Arithmetic.evalArithmetic ctor args with
  | some results => some (s, results)
  | none =>
  -- 3. Pattern operations (car-atom, cdr-atom, cons-atom, etc.)
  match Step.PatternOps.evalPatternOp ctor args with
  | some results => some (s, results)
  | none =>
  -- 4. Logic (and, or, not, xor)
  match Step.Logic.evalLogic ctor args with
  | some results => some (s, results)
  | none =>
  -- 5. Stream ops (unique, union, intersection, subtraction)
  match Step.StreamOps.evalStreamOp ctor args with
  | some results => some (s, results)
  | none =>
  -- 6. Equation rewriting (user-defined rules)
  match Step.Rules.ruleStep s (.apply ctor args) with
  | some results => some (s, results)
  | none =>
  -- No head reduction: normal form
  none

/-- Compatibility wrapper for the spec (takes full Pattern). -/
def step? (s : Session) (term : Pattern) : Option (Session × List Pattern) :=
  match term with
  | .apply ctor args => headStep? s ctor args
  | _ => none

end Algorithms.MeTTa.Eval
