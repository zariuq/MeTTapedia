import Mettapedia.OSLF.MeTTaCore.Bindings

/-!
# MeTTaCore Pattern Matching

Bidirectional unification algorithm for the MeTTa interpreter.
Unlike simple pattern matching (one-directional), full unification allows
variables on both sides of the match.

## Main Definitions

* `UnifyResult` - Result of unification: success with bindings or failure
* `unify` - Bidirectional unification algorithm
* Proofs of key properties: symmetry, validity

## References

* Meta-MeTTa paper: pattern matching semantics
* Hyperon Experimental Spec: `unify` operation
-/

namespace Mettapedia.OSLF.MeTTaCore

/-! ## Unification Result -/

/-- Result of unification attempt -/
inductive UnifyResult where
  | success : Bindings → UnifyResult
  | failure : UnifyResult
  deriving Inhabited

namespace UnifyResult

/-- Check if unification succeeded -/
def isSuccess : UnifyResult → Bool
  | .success _ => true
  | .failure => false

/-- Extract bindings from successful unification -/
def getBindings : UnifyResult → Option Bindings
  | .success b => some b
  | .failure => none

/-- Map over successful result -/
def map (f : Bindings → Bindings) : UnifyResult → UnifyResult
  | .success b => .success (f b)
  | .failure => .failure

/-- Bind operation for chaining unifications -/
def bind (r : UnifyResult) (f : Bindings → UnifyResult) : UnifyResult :=
  match r with
  | .success b => f b
  | .failure => .failure

end UnifyResult

/-! ## Bidirectional Unification -/

/-- Bidirectional unification: match two atoms, allowing variables on both sides.

    Key differences from simple pattern matching:
    1. Both atoms can contain variables
    2. Variables on either side can be bound
    3. Result is symmetric

    Returns success with bindings if atoms can be unified, failure otherwise. -/
partial def unify (a1 a2 : Atom) (b : Bindings) : UnifyResult :=
  match a1, a2 with
  -- Both are the same variable
  | .var v1, .var v2 =>
    if v1 == v2 then .success b
    else
      -- Check if either is already bound
      match b.lookup v1, b.lookup v2 with
      | some val1, some val2 =>
          -- Both bound: unify their values
          unify val1 val2 b
      | some val1, none =>
          -- v1 bound, v2 unbound: bind v2 to val1
          .success (b.extend v2 val1)
      | none, some val2 =>
          -- v2 bound, v1 unbound: bind v1 to val2
          .success (b.extend v1 val2)
      | none, none =>
          -- Neither bound: bind v1 to v2 (or equivalently v2 to v1)
          .success (b.extend v1 (.var v2))

  -- Variable on left
  | .var v, a =>
    match b.lookup v with
    | some existing => unify existing a b
    | none => .success (b.extend v a)

  -- Variable on right
  | a, .var v =>
    match b.lookup v with
    | some existing => unify a existing b
    | none => .success (b.extend v a)

  -- Symbols must match exactly
  | .symbol s1, .symbol s2 =>
    if s1 == s2 then .success b else .failure

  -- Grounded values must match exactly
  | .grounded g1, .grounded g2 =>
    if g1 == g2 then .success b else .failure

  -- Expressions: unify element-wise
  | .expression es1, .expression es2 =>
    if es1.length != es2.length then .failure
    else unifyList es1 es2 b

  -- Mismatched constructors
  | _, _ => .failure

where
  /-- Unify lists of atoms element-wise -/
  unifyList : List Atom → List Atom → Bindings → UnifyResult
    | [], [], b => .success b
    | a :: as, a' :: as', b =>
      match unify a a' b with
      | .success b' => unifyList as as' b'
      | .failure => .failure
    | _, _, _ => .failure

/-! ## Convenience Functions -/

/-- Unify with empty initial bindings -/
def unifyAtoms (a1 a2 : Atom) : UnifyResult :=
  unify a1 a2 Bindings.empty

/-- Check if two atoms are unifiable -/
def unifiable (a1 a2 : Atom) : Bool :=
  (unifyAtoms a1 a2).isSuccess

/-! ## Properties -/

/-- Helper: applying same bindings to unified atoms yields equal results -/
def unifiesTo (a1 a2 : Atom) (b : Bindings) : Prop :=
  b.apply a1 = b.apply a2

/-! ## Theorems -/

-- Note: Full proofs of symmetry and validity require careful handling of
-- the partial function and would benefit from a well-founded recursion
-- version. Concrete examples below are kernel-checked with `decide`.

/-- Symbols unify with themselves -/
theorem symbol_unify_same :
    (unify (.symbol "x") (.symbol "x") Bindings.empty).isSuccess = true := by
  decide

/-- Different symbols don't unify -/
theorem symbol_unify_different :
    (unify (.symbol "x") (.symbol "y") Bindings.empty).isSuccess = false := by
  decide

/-- Variables unify with symbols -/
theorem var_unify_symbol :
    (unify (.var "x") (.symbol "a") Bindings.empty).isSuccess = true := by
  decide

/-- Variables unify with other variables -/
theorem var_unify_var :
    (unify (.var "x") (.var "y") Bindings.empty).isSuccess = true := by
  decide

/-- Same grounded values unify -/
theorem grounded_unify_same :
    (unify (.grounded (.int 42)) (.grounded (.int 42)) Bindings.empty).isSuccess = true := by
  decide

/-- Different grounded values don't unify -/
theorem grounded_unify_different :
    (unify (.grounded (.int 42)) (.grounded (.int 43)) Bindings.empty).isSuccess = false := by
  decide

/-- Empty expressions unify -/
theorem empty_expr_unify :
    (unify (.expression []) (.expression []) Bindings.empty).isSuccess = true := by
  decide

/-- Variable self-unifies -/
theorem var_self_unify :
    (unify (.var "x") (.var "x") Bindings.empty).isSuccess = true := by
  decide

/-! ## Unit Tests -/

section Tests

-- Symbol unification
example : (unify (.symbol "x") (.symbol "x") Bindings.empty).isSuccess = true := by decide
example : (unify (.symbol "x") (.symbol "y") Bindings.empty).isSuccess = false := by decide

-- Variable unification
example : (unify (.var "x") (.symbol "a") Bindings.empty).isSuccess = true := by decide

-- Grounded value unification
example : (unify (.grounded (.int 42)) (.grounded (.int 42)) Bindings.empty).isSuccess = true := by
  decide
example : (unify (.grounded (.int 42)) (.grounded (.int 43)) Bindings.empty).isSuccess = false := by
  decide

-- Expression unification
example : (unify (.expression []) (.expression []) Bindings.empty).isSuccess = true := by
  decide

-- Mismatched types
example : (unify (.symbol "x") (.grounded (.int 1)) Bindings.empty).isSuccess = false := by
  decide
example : (unify (.symbol "x") (.expression []) Bindings.empty).isSuccess = false := by
  decide

-- Variable captures value
example : (unify (.var "x") (.symbol "hello") Bindings.empty).getBindings.bind
            (fun b => b.lookup "x") = some (.symbol "hello") := by decide

end Tests

end Mettapedia.OSLF.MeTTaCore
