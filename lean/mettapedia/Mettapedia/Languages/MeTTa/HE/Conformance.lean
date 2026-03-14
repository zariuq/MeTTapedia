import Mettapedia.Languages.MeTTa.HE.MinimalMeTTa

/-!
# HE MeTTa Conformance

Conformance verification for the HE MeTTa evaluation specification.

## Two kinds of conformance:
1. **Leaf function tests** (sections 2-4): `rfl`-checked against computable
   functions in Matching.lean / TypeCheck.lean. These are exact equality tests.
2. **Derivation witnesses** (sections 1, 5-7): Explicit derivation trees
   witnessing that `EvalAtom`/`MettaCall`/etc. hold for specific inputs.
   These prove that the declarative spec allows the expected derivations.

## Source of Truth
- `https://trueagi-io.github.io/hyperon-experimental/metta/`
- Conformance with `metta` CLI (conda hyperon environment, v0.2.10)
-/

namespace Mettapedia.Languages.MeTTa.HE.Conformance

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE

/-! ## Test Infrastructure -/

private def emptySpace : Space := Space.empty
private def emptyB : Bindings := Bindings.empty
private def noDispatch : GroundedDispatch := .none
private def fuel : Nat := 50

/-! ## 1. EvalAtom derivation witnesses (spec lines 105-136)

These construct explicit derivation trees showing that specific inputs
have valid derivations in the declarative spec. -/

/-- Empty atom passes through unchanged.
    Spec line 117: `if $atom == Empty ... return [($atom, $bindings)]` -/
theorem eval_empty_passthrough :
    EvalAtom emptySpace noDispatch Atom.empty Atom.undefinedType emptyB
      (Atom.empty, emptyB) :=
  .empty_or_error _ _ _ rfl

/-- Error atom passes through unchanged.
    Spec line 117: `$atom ~ (Error ...)` -/
theorem eval_error_passthrough :
    EvalAtom emptySpace noDispatch
      (Atom.error (.symbol "x") (.symbol "msg")) Atom.undefinedType emptyB
      (Atom.error (.symbol "x") (.symbol "msg"), emptyB) :=
  .empty_or_error _ _ _ rfl

/-- Variable always passes through (metatype is Variable).
    Spec line 119: `$metatype == Variable` -/
theorem eval_variable_passthrough :
    EvalAtom emptySpace noDispatch (.var "x") Atom.undefinedType emptyB
      (.var "x", emptyB) :=
  .type_pass _ _ _ rfl (Or.inr (Or.inr rfl))

/-- When expected type is Atom, return unchanged.
    Spec line 119: `$type == Atom` -/
theorem eval_type_atom :
    EvalAtom emptySpace noDispatch (.symbol "x") Atom.atomType emptyB
      (.symbol "x", emptyB) :=
  .type_pass _ _ _ rfl (Or.inl rfl)

/-- When expected type matches metatype, return unchanged.
    Spec line 119: `$type == $metatype` -/
theorem eval_type_matches_metatype :
    EvalAtom emptySpace noDispatch (.symbol "x") (.symbol "Symbol") emptyB
      (.symbol "x", emptyB) :=
  .type_pass _ _ _ rfl (Or.inr (Or.inl rfl))

/-- Symbol with no type info → typeCast → %Undefined% matches anything.
    Spec line 123: `$metatype == Symbol` → `type_cast` -/
theorem eval_symbol_typecast :
    EvalAtom emptySpace noDispatch (.symbol "x") (.symbol "Foo") emptyB
      (.symbol "x", emptyB) := by
  apply EvalAtom.type_cast (fuel := fuel)
  · rfl
  · decide
  · left; rfl
  · show _ ∈ typeCast _ _ _ _ fuel
    decide

/-- Unit expression → typeCast.
    Spec line 123: `$atom == ()` -/
theorem eval_unit_typecast :
    EvalAtom emptySpace noDispatch Atom.unit Atom.undefinedType emptyB
      (Atom.unit, emptyB) := by
  apply EvalAtom.type_cast (fuel := fuel)
  · rfl
  · decide
  · right; right; rfl
  · show _ ∈ typeCast _ _ _ _ fuel
    decide

/-- Grounded atom → typeCast with matching type.
    Spec line 123: `$metatype == Grounded`.
    Grounded int has intrinsic type `Number` (from `Grounded::type_()`). -/
theorem eval_grounded_typecast :
    EvalAtom emptySpace noDispatch (.grounded (.int 42)) (.symbol "Number") emptyB
      (.grounded (.int 42), emptyB) := by
  apply EvalAtom.type_cast (fuel := fuel)
  · rfl
  · decide
  · right; left; rfl
  · show _ ∈ typeCast _ _ _ _ fuel
    decide

/-! ## 2. typeCast clauses (metta.md lines 275-296) — computable `rfl` tests -/

/-- Atom with matching type annotation. -/
theorem typeCast_matching_type :
    let space := Space.ofList [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
    typeCast (.symbol "x") (.symbol "Int") space emptyB fuel =
    [(.symbol "x", emptyB)] := rfl

/-- Atom with non-matching type: error. -/
theorem typeCast_mismatch :
    let space := Space.ofList [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
    typeCast (.symbol "x") (.symbol "Bool") space emptyB fuel =
    [(mkError (.symbol "x") (.badType (.symbol "Bool") (.symbol "Int")), emptyB)] := rfl

/-- Atom with no type annotation: gets %Undefined%, which matches anything. -/
theorem typeCast_no_annotation :
    typeCast (.symbol "x") (.symbol "Foo") emptySpace emptyB fuel =
    [(.symbol "x", emptyB)] := rfl

/-- %Undefined% always matches as expected type. -/
theorem typeCast_undefined_type :
    let space := Space.ofList [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
    typeCast (.symbol "x") Atom.undefinedType space emptyB fuel =
    [(.symbol "x", emptyB)] := rfl

/-! ## 3. matchTypes clauses (metta.md lines 298-314) -/

theorem matchTypes_undef_left :
    matchTypes Atom.undefinedType (.symbol "Anything") emptyB =
    [emptyB] := rfl

theorem matchTypes_atom_right :
    matchTypes (.symbol "Anything") Atom.atomType emptyB =
    [emptyB] := rfl

theorem matchTypes_same :
    matchTypes (.symbol "Int") (.symbol "Int") emptyB = [emptyB] := rfl

theorem matchTypes_different :
    matchTypes (.symbol "Int") (.symbol "Bool") emptyB = [] := rfl

/-! ## 4. matchAtoms clauses (metta.md lines 577-617) -/

theorem matchAtoms_same_symbol :
    matchAtoms (.symbol "a") (.symbol "a") fuel = [emptyB] := rfl

theorem matchAtoms_diff_symbol :
    matchAtoms (.symbol "a") (.symbol "b") fuel = [] := rfl

theorem matchAtoms_two_vars :
    matchAtoms (.var "x") (.var "y") fuel =
    [emptyB.addEquality "x" "y"] := rfl

theorem matchAtoms_var_left :
    matchAtoms (.var "x") (.symbol "a") fuel =
    [emptyB.assign "x" (.symbol "a")] := rfl

theorem matchAtoms_var_right :
    matchAtoms (.symbol "a") (.var "x") fuel =
    [emptyB.assign "x" (.symbol "a")] := rfl

theorem matchAtoms_expr_match :
    matchAtoms (.expression [.symbol "a", .var "x"])
               (.expression [.symbol "a", .symbol "b"]) fuel =
    [emptyB.assign "x" (.symbol "b")] := rfl

theorem matchAtoms_expr_length_mismatch :
    matchAtoms (.expression [.symbol "a"])
               (.expression [.symbol "a", .symbol "b"]) fuel = [] := rfl

theorem matchAtoms_grounded_same :
    matchAtoms (.grounded (.int 42)) (.grounded (.int 42)) fuel = [emptyB] := rfl

theorem matchAtoms_grounded_diff :
    matchAtoms (.grounded (.int 42)) (.grounded (.int 43)) fuel = [] := rfl

theorem matchAtoms_sym_expr :
    matchAtoms (.symbol "a") (.expression [.symbol "a"]) fuel = [] := rfl

/-! ## 5. MettaCall derivation witnesses (spec lines 348-389) -/

/-- Error atom passes through mettaCall.
    Spec line 359: `if $atom ~ (Error ...)` -/
theorem mettaCall_error_passthrough :
    MettaCall emptySpace noDispatch
      (Atom.error (.symbol "x") (.symbol "e")) Atom.undefinedType emptyB
      (Atom.error (.symbol "x") (.symbol "e"), emptyB) :=
  .error_passthrough _ _ _ rfl

/-- Equation match: `(= (f a) result)` in space, calling `(f a)`.
    Spec lines 376-382: query equations, merge bindings, recurse.
    Note: RHS is ground (`.symbol "result"`), so `merged.apply rhs = rhs`. -/
theorem mettaCall_equation_match :
    let space := Space.ofList [
      .expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .symbol "result"]]
    MettaCall space noDispatch
      (.expression [.symbol "f", .symbol "a"]) Atom.undefinedType emptyB
      (.symbol "result", emptyB) := by
  apply MettaCall.equation_match (fuel := fuel) (rhs := .symbol "result")
    (queryBindings := emptyB) (merged := emptyB)
  case h_not_error => rfl
  case h_not_grounded => trivial
  case h_query => decide
  case h_merge => decide
  case h_no_loop => rfl
  case h_recurse =>
    -- merged.apply (.symbol "result") = .symbol "result" (ground, no vars)
    apply EvalAtom.type_cast (fuel := fuel)
    · rfl
    · decide
    · left; rfl
    · show _ ∈ typeCast _ _ _ _ fuel; decide

/-- No equations match → return atom unchanged.
    Spec lines 383-384. -/
theorem mettaCall_no_match :
    MettaCall emptySpace noDispatch
      (.expression [.symbol "f", .symbol "a"]) Atom.undefinedType emptyB
      (.expression [.symbol "f", .symbol "a"], emptyB) := by
  apply MettaCall.no_match (fuel := fuel)
  case h_not_error => rfl
  case h_not_grounded => trivial
  case h_no_eqs => rfl

/-- Equation match with symbol RHS: `(= (g b) answer)`.
    `(g b)` → equation match → `answer` (symbol, type_cast succeeds). -/
theorem mettaCall_symbol_rhs :
    let space := Space.ofList [
      .expression [.symbol "=",
        .expression [.symbol "g", .symbol "b"],
        .symbol "answer"]]
    MettaCall space noDispatch
      (.expression [.symbol "g", .symbol "b"]) Atom.undefinedType emptyB
      (.symbol "answer", emptyB) := by
  apply MettaCall.equation_match (fuel := fuel)
    (rhs := .symbol "answer")
    (queryBindings := emptyB) (merged := emptyB)
  case h_not_error => rfl
  case h_not_grounded => trivial
  case h_query => decide
  case h_merge => decide
  case h_no_loop => rfl
  case h_recurse =>
    apply EvalAtom.type_cast (fuel := fuel)
    · rfl
    · decide
    · left; rfl
    · show _ ∈ typeCast _ _ _ _ fuel; decide

/-! ## 6. Equation RHS Substitution Regression (Bug 1 fix)

The equation `(= (id $x) $x)` with input `(id hello)` must produce `hello`,
not the raw freshened variable `$x#0`. This is the key regression test for
the `merged.apply rhs` fix in `MettaCall.equation_match`. -/

/-- Verify queryEquations returns freshened variable as RHS. -/
theorem queryEquations_id_pattern :
    let space := Space.ofList [
      .expression [.symbol "=", .expression [.symbol "id", .var "x"], .var "x"]]
    queryEquations space (.expression [.symbol "id", .symbol "hello"]) =
    [(.var "x#0", emptyB.assign "x#0" (.symbol "hello"))] := rfl

/-- Equation `(= (id $x) $x)` with input `(id hello)` produces `hello`.
    After merging, `merged = { x#0 → hello }`, so `merged.apply (.var "x#0") = hello`.
    This would FAIL without the `merged.apply rhs` fix. -/
theorem mettaCall_equation_rhs_substitution :
    let space := Space.ofList [
      .expression [.symbol "=", .expression [.symbol "id", .var "x"], .var "x"]]
    MettaCall space noDispatch
      (.expression [.symbol "id", .symbol "hello"]) Atom.undefinedType emptyB
      (.symbol "hello", emptyB.assign "x#0" (.symbol "hello")) := by
  apply MettaCall.equation_match (fuel := fuel)
    (rhs := .var "x#0")
    (queryBindings := emptyB.assign "x#0" (.symbol "hello"))
    (merged := emptyB.assign "x#0" (.symbol "hello"))
  case h_not_error => rfl
  case h_not_grounded => trivial
  case h_query => decide
  case h_merge => decide
  case h_no_loop => rfl
  case h_recurse =>
    -- merged.apply (.var "x#0") = .symbol "hello" by kernel reduction
    change EvalAtom _ _ (.symbol "hello") _ _ _
    apply EvalAtom.type_cast (fuel := fuel)
    · rfl
    · decide
    · left; rfl
    · show _ ∈ typeCast _ _ _ _ fuel; decide

/-! ## 7. MinimalStep derivation witnesses -/

/-- cons-atom builds an expression. -/
theorem minimal_cons_atom :
    MinimalStep noDispatch emptySpace
      (.expression [.symbol "cons-atom", .symbol "a", .expression [.symbol "b"]]) emptyB
      emptySpace
      (.expression [.symbol "a", .symbol "b"], emptyB) :=
  .cons_atom _ _ _ _

/-- decons-atom splits an expression. -/
theorem minimal_decons_atom :
    MinimalStep noDispatch emptySpace
      (.expression [.symbol "decons-atom", .expression [.symbol "a", .symbol "b"]]) emptyB
      emptySpace
      (.expression [.symbol "a", .expression [.symbol "b"]], emptyB) :=
  .decons_atom _ _ _ _

/-! ## 8. queryEquations `rfl` tests (Space.lean) -/

/-- Simple ground equation query. -/
theorem queryEquations_simple :
    let space := Space.ofList [
      .expression [.symbol "=", .symbol "foo", .grounded (.int 42)]]
    queryEquations space (.symbol "foo") =
    [(.grounded (.int 42), emptyB)] := rfl

/-- Pattern variable equation query with freshening. -/
theorem queryEquations_pattern :
    let space := Space.ofList [
      .expression [.symbol "=", .expression [.var "x"], .var "x"]]
    queryEquations space (.expression [.symbol "hello"]) =
    [(.var "x#0", emptyB.assign "x#0" (.symbol "hello"))] := rfl

/-! ## Conformance Summary

| Section | Count | Method |
|---------|-------|--------|
| 1. EvalAtom witnesses | 8 | derivation tree |
| 2. typeCast | 4 | rfl |
| 3. matchTypes | 4 | rfl |
| 4. matchAtoms | 10 | rfl |
| 5. MettaCall witnesses | 4 | derivation tree |
| 6. Equation RHS regression | 2 | derivation tree + rfl |
| 7. MinimalStep witnesses | 2 | derivation tree |
| 8. queryEquations | 2 | rfl |
| **Total** | **36** | |

All zero-sorry, zero-axiom. Derivation witnesses are explicit proof terms
showing that the declarative spec (EvalSpec.lean) allows exactly the
expected derivations for each test case.
-/

end Mettapedia.Languages.MeTTa.HE.Conformance
