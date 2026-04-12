-- LLM primer: Atom is a nested inductive with `.expression (List Atom)`.
-- Structural recursion through List Atom requires mutual `where` clauses
-- or fuel-indexing. All existing HE code (queryEquations, simpleMatch, etc.)
-- uses fuel for this reason.
--
-- Key insight: "no equations matched" ≠ "is a value". An atom with no
-- equations can still reduce via grounded dispatch or special forms.
-- Error atoms ARE values even if their subterms are reducible (errors
-- propagate unchanged per EvalSpec.EvalAtom.empty_or_error).

import Mettapedia.Languages.MeTTa.HE.Space

/-!
# IsValue / IsReducible for MeTTa Dispatch

Formal predicates distinguishing values (cannot reduce) from reducible
expressions (can take at least one evaluation step) in the HE MeTTa evaluator.

## Why This Matters

A prior CeTTa optimization conflated "no equations matched in handle_dispatch"
with "this expression is already a value." That is unsound: grounded operations
like `(+ 2 3)` and special forms like `(if True a b)` have no equations but
ARE reducible. This file makes the distinction formal.

## C Seam Mapping

| Lean notion | C location in eval.c |
|-------------|---------------------|
| `isSpecialForm` | `head_id == g_builtin_syms.*` checks in `metta_call` (lines 9644+) |
| `IsValue'.constructor_app` | `handle_dispatch` return-unchanged (line 8973) |
| `IsReducible'.grounded_op` | `dispatch.isExecutable` guard (line 9082) |
| `IsReducible'.special_form` | special form dispatch in `metta_call` |

## References

- Plotkin, "Call-by-Name, Call-by-Value and the Lambda Calculus" (1975)
- `Metatheory/Lambda/CBV.lean` — pattern for `IsValue` + progress
- Peyton Jones, "Implementing lazy functional languages" (1992)
  — constructor vs function distinction by tag
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Special Form Detection -/

/-- MeTTa special form head symbols that always dispatch through dedicated
    evaluation paths, regardless of whether equations exist. -/
def isSpecialForm : Atom → Bool
  | .symbol "superpose" => true
  | .symbol "let"       => true
  | .symbol "let*"      => true
  | .symbol "chain"     => true
  | .symbol "if"        => true
  | .symbol "case"      => true
  | .symbol "collapse"  => true
  | .symbol "unify"     => true
  | .symbol "assertEqual" => true
  | .symbol "assertEqualToResult" => true
  | .symbol "match"     => true
  | .symbol "select"    => true
  | .symbol "bind!"     => true
  | .symbol "new-space" => true
  | .symbol "add-atom"  => true
  | .symbol "remove-atom" => true
  | .symbol "get-atoms" => true
  | .symbol "import!"   => true
  | .symbol "include"   => true
  | .symbol "pragma!"   => true
  | _                   => false

/-- Non-symbol atoms are never special forms. -/
theorem isSpecialForm_false_var (v : String) : isSpecialForm (.var v) = false := rfl
theorem isSpecialForm_false_grounded (g : GroundedValue) : isSpecialForm (.grounded g) = false := rfl
theorem isSpecialForm_false_expression (es : List Atom) : isSpecialForm (.expression es) = false := rfl

/-! ## Prop-valued Inductive Predicates -/

/-- An atom is a MeTTa value: it cannot take any evaluation step.

    Error atoms are values even if their subterms are reducible, because
    the evaluator propagates them unchanged (EvalSpec.EvalAtom.empty_or_error,
    MettaCall.error_passthrough). -/
inductive IsValue' (space : Space) (dispatch : GroundedDispatch) : Atom → Prop where
  /-- Bare symbols are values. -/
  | symbol (s : String) : IsValue' space dispatch (.symbol s)
  /-- Variables are values (substitution is separate). -/
  | var (v : String) : IsValue' space dispatch (.var v)
  /-- Grounded atoms (numbers, bools, strings) are values. -/
  | grounded (g : GroundedValue) : IsValue' space dispatch (.grounded g)
  /-- Unit `()` is a value. -/
  | unit : IsValue' space dispatch (.expression [])
  /-- Error expressions propagate unchanged — always values.
      Ref: EvalSpec.EvalAtom.empty_or_error, MettaCall.error_passthrough. -/
  | error (args : List Atom) :
      IsValue' space dispatch (.expression (.symbol "Error" :: args))
  /-- Constructor applications: expressions where the head satisfies ALL FOUR:
      1. No matching equations in the space
      2. Head is not a grounded executable
      3. Head is not a special form
      4. All arguments are values (recursive) -/
  | constructor_app (op : Atom) (args : List Atom)
      (h_no_eqs : ∀ fuel, queryEquations space (.expression (op :: args)) fuel = [])
      (h_not_exec : dispatch.isExecutable op = false)
      (h_not_special : isSpecialForm op = false)
      (h_args_val : ∀ a, a ∈ args → IsValue' space dispatch a) :
      IsValue' space dispatch (.expression (op :: args))

/-- An atom is reducible: it can take at least one evaluation step.

    Error atoms are explicitly excluded (they propagate unchanged).
    Each constructor witnesses a different reduction mechanism. -/
inductive IsReducible' (space : Space) (dispatch : GroundedDispatch) : Atom → Prop where
  /-- Grounded operations reduce via native dispatch. -/
  | grounded_op (op : Atom) (args : List Atom)
      (h_not_error : isErrorAtom (.expression (op :: args)) = false)
      (h : dispatch.isExecutable op = true) :
      IsReducible' space dispatch (.expression (op :: args))
  /-- Special forms reduce via dedicated evaluation paths. -/
  | special_form (op : Atom) (args : List Atom)
      (h_not_error : isErrorAtom (.expression (op :: args)) = false)
      (h : isSpecialForm op = true) :
      IsReducible' space dispatch (.expression (op :: args))
  /-- Expressions with matching equations reduce via equation dispatch. -/
  | has_equations (op : Atom) (args : List Atom) (fuel : Nat)
      (h_not_error : isErrorAtom (.expression (op :: args)) = false)
      (h : queryEquations space (.expression (op :: args)) fuel ≠ []) :
      IsReducible' space dispatch (.expression (op :: args))
  /-- A non-error expression with a reducible argument is itself reducible. -/
  | reducible_arg (op : Atom) (args : List Atom) (a : Atom)
      (h_not_error : isErrorAtom (.expression (op :: args)) = false)
      (h_mem : a ∈ args)
      (h_red : IsReducible' space dispatch a) :
      IsReducible' space dispatch (.expression (op :: args))

/-! ## Disjointness -/

/-- Values and reducibles are disjoint: no atom can be both. -/
theorem isValue_isReducible_disjoint (space : Space) (dispatch : GroundedDispatch)
    (a : Atom) : IsValue' space dispatch a → IsReducible' space dispatch a → False := by
  intro hv hr
  cases hr with
  | grounded_op op args h_ne h_exec =>
    cases hv with
    | constructor_app _ _ _ h_not_exec _ _ => simp [h_exec] at h_not_exec
    | error _ => simp [isErrorAtom] at h_ne
  | special_form op args h_ne h_special =>
    cases hv with
    | constructor_app _ _ _ _ h_not_special _ => simp [h_special] at h_not_special
    | error _ => simp [isErrorAtom] at h_ne
  | has_equations op args fuel h_ne h_eqs =>
    cases hv with
    | constructor_app _ _ h_no_eqs _ _ _ => exact h_eqs (h_no_eqs fuel)
    | error _ => simp [isErrorAtom] at h_ne
  | reducible_arg op args a h_ne h_mem h_red =>
    cases hv with
    | constructor_app _ _ _ _ _ h_args_val =>
      exact isValue_isReducible_disjoint space dispatch a (h_args_val a h_mem) h_red
    | error _ => simp [isErrorAtom] at h_ne

/-! ## Computable Value Check -/

/-- Fuel-indexed computable predicate: is this atom a MeTTa value? -/
def isValueBool (space : Space) (dispatch : GroundedDispatch) : Atom → Nat → Bool
  | .symbol _, _ => true
  | .var _, _ => true
  | .grounded _, _ => true
  | .expression [], _ => true  -- unit
  | .expression (.symbol "Error" :: _), _ => true  -- error atoms
  | .expression (op :: args), fuel =>
    match fuel with
    | 0 => false  -- conservative at fuel 0
    | n + 1 =>
      queryEquations space (.expression (op :: args)) n == []
      && dispatch.isExecutable op == false
      && isSpecialForm op == false
      && isValueBoolList space dispatch args n
where
  isValueBoolList (space : Space) (dispatch : GroundedDispatch) :
      List Atom → Nat → Bool
    | [], _ => true
    | a :: as, fuel =>
      isValueBool space dispatch a fuel && isValueBoolList space dispatch as fuel

/-! ## Counterexamples

These formalize the three concrete failures from the unsound CeTTa fix. -/

section Counterexamples

private def arithDispatch : GroundedDispatch :=
  { isExecutable := fun a => match a with | .grounded _ => true | _ => false
    execute := fun _ _ => .noReduce }

/-- Counterexample 1: `(+ 2 3)` is reducible via grounded dispatch.
    Removing condition 2 would misclassify this as a value. -/
example : IsReducible' Space.empty arithDispatch
    (.expression [.grounded (.custom "+" ""), .grounded (.int 2), .grounded (.int 3)]) :=
  .grounded_op _ _ rfl rfl

/-- Counterexample 2: `(if True a b)` is reducible via special forms.
    Removing condition 3 would misclassify this as a value. -/
example : IsReducible' Space.empty GroundedDispatch.none
    (.expression [.symbol "if", .symbol "True", .symbol "a", .symbol "b"]) :=
  .special_form _ _ rfl rfl

/-- Positive example: `(S Z)` IS a value (all four conditions met). -/
example : IsValue' Space.empty GroundedDispatch.none
    (.expression [.symbol "S", .symbol "Z"]) := by
  apply IsValue'.constructor_app
  · intro fuel; simp [queryEquations, Space.empty]
  · rfl
  · rfl
  · intro a ha; simp at ha; exact ha ▸ .symbol "Z"

/-- Positive example: `(S (+ 2 3))` is reducible because argument is reducible. -/
example : IsReducible' Space.empty arithDispatch
    (.expression [.symbol "S",
      .expression [.grounded (.custom "+" ""), .grounded (.int 2), .grounded (.int 3)]]) :=
  .reducible_arg _ _ _ rfl (List.mem_singleton.mpr rfl) (.grounded_op _ _ rfl rfl)

/-- Positive example: `(Error x (+ 2 3))` IS a value despite reducible subterm.
    Errors propagate unchanged. -/
example : IsValue' Space.empty arithDispatch
    (.expression [.symbol "Error", .symbol "x",
      .expression [.grounded (.custom "+" ""), .grounded (.int 2), .grounded (.int 3)]]) :=
  .error _

end Counterexamples

/-! ## Connection to MettaCall.no_match -/

/-- If `MettaCall.no_match` applies (no equations, not grounded), and the
    expression is not a special form with all-value arguments, then it is
    a value in the `IsValue'` sense. -/
theorem no_match_value_iff (space : Space) (dispatch : GroundedDispatch)
    (op : Atom) (args : List Atom)
    (h_no_eqs : ∀ fuel, queryEquations space (.expression (op :: args)) fuel = [])
    (h_not_exec : dispatch.isExecutable op = false)
    (h_not_special : isSpecialForm op = false)
    (h_args_val : ∀ a, a ∈ args → IsValue' space dispatch a) :
    IsValue' space dispatch (.expression (op :: args)) :=
  .constructor_app op args h_no_eqs h_not_exec h_not_special h_args_val

end Mettapedia.Languages.MeTTa.HE
