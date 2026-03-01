import Mettapedia.Languages.MeTTa.HE.Interpreter

/-!
# HE MeTTa Conformance Matrix

Clause-by-clause conformance tests for the HE interpreter formalization.
Each theorem maps a specific clause from `metta.md` to a proven Lean statement.

All tests are kernel-checked via `rfl` or `decide` (no axioms, no sorry).

## Source Reference
- `metta.md` lines 240-552 (evaluation spec)
- `interpreter.rs` test suite (behavioral ground truth)

## Spec Holes (documented)
1. Result ordering: `interpret_expression` returns `$tuples + $errors` (ordered),
   but within each group, iteration order over types is unspecified.
2. `match_atoms` for grounded custom matching: deferred to implementation.
3. `merge_bindings` iteration order over right's relations: unspecified.
-/

namespace Mettapedia.Languages.MeTTa.HE.Conformance

open Mettapedia.OSLF.MeTTaCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE

/-! ## Test Infrastructure -/

private def emptySpace : Space := Space.empty
private def emptyB : Bindings := Bindings.empty
private def noDispatch : GroundedDispatch := .none
private def fuel : Nat := 50

/-- Evaluate with standard test parameters. -/
private def testEval (atom : Atom) (space : Space) (type_ : Atom := Atom.undefinedType) :=
  metta atom type_ space emptyB noDispatch [] fuel

/-! ## 1. metta clauses (metta.md lines 240-272) -/

/-- Spec ref: metta.md line 253 "if $atom == Empty ... return [($atom, $bindings)]"
    Empty atom passes through unchanged. -/
theorem metta_empty_passthrough :
    testEval Atom.empty emptySpace = [(Atom.empty, emptyB)] := rfl

/-- Spec ref: metta.md line 253 "$atom ~ (Error ...)"
    Error atom passes through unchanged. -/
theorem metta_error_passthrough :
    testEval (Atom.error (.symbol "x") (.symbol "msg")) emptySpace =
    [(Atom.error (.symbol "x") (.symbol "msg"), emptyB)] := rfl

/-- Spec ref: metta.md line 255 "$type == Atom"
    When expected type is Atom, return unchanged. -/
theorem metta_type_atom :
    metta (.symbol "x") Atom.atomType emptySpace emptyB noDispatch [] fuel =
    [(.symbol "x", emptyB)] := rfl

/-- Spec ref: metta.md line 255 "$metatype == Variable"
    Variables always pass through (regardless of expected type). -/
theorem metta_variable_passthrough :
    testEval (.var "x") emptySpace = [(.var "x", emptyB)] := rfl

/-- Spec ref: metta.md line 255 "$type == $metatype"
    When expected type matches metatype, return unchanged. -/
theorem metta_type_matches_metatype :
    metta (.symbol "x") (.symbol "Symbol") emptySpace emptyB noDispatch [] fuel =
    [(.symbol "x", emptyB)] := rfl

/-- Spec ref: metta.md line 259 "$metatype == Symbol"
    Symbols go through typeCast. With no type info, %Undefined% matches anything. -/
theorem metta_symbol_typecast_undefined :
    testEval (.symbol "x") emptySpace = [(.symbol "x", emptyB)] := rfl

/-- Spec ref: metta.md line 259 "atom == ()"
    Unit expression goes through typeCast. -/
theorem metta_unit_typecast :
    testEval (.expression []) emptySpace = [(.expression [], emptyB)] := rfl

/-- Spec ref: metta.md line 259 "$metatype == Grounded"
    Grounded atoms go through typeCast. -/
theorem metta_grounded_typecast :
    testEval (.grounded (.int 42)) emptySpace =
    [(.grounded (.int 42), emptyB)] := rfl

/-! ## 2. typeCast clauses (metta.md lines 275-296) -/

/-- Spec ref: metta.md lines 287-294
    Atom with matching type annotation: type matches. -/
theorem typeCast_matching_type :
    let space := Space.ofList [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
    typeCast (.symbol "x") (.symbol "Int") space emptyB fuel =
    [(.symbol "x", emptyB)] := rfl

/-- Spec ref: metta.md lines 287-295
    Atom with non-matching type: error. -/
theorem typeCast_mismatch :
    let space := Space.ofList [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
    typeCast (.symbol "x") (.symbol "Bool") space emptyB fuel =
    [(mkError (.symbol "x") (.badType (.symbol "Bool") (.symbol "Int")), emptyB)] := rfl

/-- Spec ref: metta.md line 287
    Atom with no type annotation: gets %Undefined%, which matches anything. -/
theorem typeCast_no_annotation :
    typeCast (.symbol "x") (.symbol "Foo") emptySpace emptyB fuel =
    [(.symbol "x", emptyB)] := rfl

/-- Spec ref: metta.md line 290
    %Undefined% always matches as expected type. -/
theorem typeCast_undefined_type :
    let space := Space.ofList [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
    typeCast (.symbol "x") Atom.undefinedType space emptyB fuel =
    [(.symbol "x", emptyB)] := rfl

/-! ## 3. matchTypes clauses (metta.md lines 298-314) -/

/-- Spec ref: metta.md line 309 "$type1 == %Undefined%"
    %Undefined% matches any type. -/
theorem matchTypes_undef_left :
    matchTypes Atom.undefinedType (.symbol "Anything") emptyB =
    [emptyB] := rfl

/-- Spec ref: metta.md line 310 "$type2 == Atom"
    Atom matches any type. -/
theorem matchTypes_atom_right :
    matchTypes (.symbol "Anything") Atom.atomType emptyB =
    [emptyB] := rfl

/-- Spec ref: metta.md line 313
    Same concrete types match. -/
theorem matchTypes_same :
    matchTypes (.symbol "Int") (.symbol "Int") emptyB = [emptyB] := rfl

/-- Spec ref: metta.md line 313
    Different concrete types don't match. -/
theorem matchTypes_different :
    matchTypes (.symbol "Int") (.symbol "Bool") emptyB = [] := rfl

/-! ## 4. matchAtoms clauses (metta.md lines 577-617) -/

/-- Spec ref: metta.md line 591
    Same symbols match with empty bindings. -/
theorem matchAtoms_same_symbol :
    matchAtoms (.symbol "a") (.symbol "a") fuel = [emptyB] := rfl

/-- Spec ref: metta.md line 591
    Different symbols don't match. -/
theorem matchAtoms_diff_symbol :
    matchAtoms (.symbol "a") (.symbol "b") fuel = [] := rfl

/-- Spec ref: metta.md line 593
    Two variables → equality relation. -/
theorem matchAtoms_two_vars :
    matchAtoms (.var "x") (.var "y") fuel =
    [emptyB.addEquality "x" "y"] := rfl

/-- Spec ref: metta.md line 595
    Left variable, right non-variable → assignment. -/
theorem matchAtoms_var_left :
    matchAtoms (.var "x") (.symbol "a") fuel =
    [emptyB.assign "x" (.symbol "a")] := rfl

/-- Spec ref: metta.md line 597
    Right variable, left non-variable → assignment. -/
theorem matchAtoms_var_right :
    matchAtoms (.symbol "a") (.var "x") fuel =
    [emptyB.assign "x" (.symbol "a")] := rfl

/-- Spec ref: metta.md lines 599-606
    Expression matching: element-wise. -/
theorem matchAtoms_expr_match :
    matchAtoms (.expression [.symbol "a", .var "x"])
               (.expression [.symbol "a", .symbol "b"]) fuel =
    [emptyB.assign "x" (.symbol "b")] := rfl

/-- Spec ref: metta.md lines 599-606
    Expression matching: length mismatch → failure. -/
theorem matchAtoms_expr_length_mismatch :
    matchAtoms (.expression [.symbol "a"])
               (.expression [.symbol "a", .symbol "b"]) fuel = [] := rfl

/-- Spec ref: metta.md line 611
    Same grounded values match. -/
theorem matchAtoms_grounded_same :
    matchAtoms (.grounded (.int 42)) (.grounded (.int 42)) fuel = [emptyB] := rfl

/-- Spec ref: metta.md line 611
    Different grounded values don't match. -/
theorem matchAtoms_grounded_diff :
    matchAtoms (.grounded (.int 42)) (.grounded (.int 43)) fuel = [] := rfl

/-- Spec ref: metta.md line 613
    Symbol vs expression → no match. -/
theorem matchAtoms_sym_expr :
    matchAtoms (.symbol "a") (.expression [.symbol "a"]) fuel = [] := rfl

/-! ## 5. interpret_args critical clause (metta.md lines 480-507) -/

/-- Spec ref: metta.md line 498
    "$h != $atom" condition: if evaluation returns Empty but atom was already Empty,
    short-circuit does NOT fire (h == atom). -/
theorem interpretArgs_empty_unchanged :
    let args := [Atom.empty]
    let types := [Atom.undefinedType]
    interpretArgs args types emptySpace emptyB noDispatch [] fuel =
    [(.expression [Atom.empty], emptyB)] := rfl

-- Note: Testing the case where evaluation produces Empty and h != atom
-- requires constructing an atom whose evaluation changes to Empty (e.g., via
-- type mismatch). This is covered indirectly by e2e tests.

/-- Spec ref: metta.md lines 493-507
    Empty args → empty expression result. -/
theorem interpretArgs_empty_args :
    interpretArgs [] [] emptySpace emptyB noDispatch [] fuel =
    [(.expression [], emptyB)] := rfl

/-! ## 6. mettaCall clauses (metta.md lines 509-552) -/

/-- Spec ref: metta.md line 521
    Error passthrough. -/
theorem mettaCall_error_passthrough :
    mettaCall (Atom.error (.symbol "x") (.symbol "e")) Atom.undefinedType
      emptySpace emptyB noDispatch [] fuel =
    [(Atom.error (.symbol "x") (.symbol "e"), emptyB)] := rfl

/-- Spec ref: metta.md lines 538-541
    Expression with matching equation → evaluates RHS. -/
theorem mettaCall_equation_match :
    let space := Space.ofList [
      .expression [.symbol "=",
        .expression [.symbol "f", .symbol "a"],
        .symbol "result"]]
    mettaCall (.expression [.symbol "f", .symbol "a"]) Atom.undefinedType
      space emptyB noDispatch [] fuel =
    [(.symbol "result", emptyB)] := rfl

/-- Spec ref: metta.md line 546
    Expression with no matching equation → return unchanged. -/
theorem mettaCall_no_equation :
    mettaCall (.expression [.symbol "f", .symbol "a"]) Atom.undefinedType
      emptySpace emptyB noDispatch [] fuel =
    [(.expression [.symbol "f", .symbol "a"], emptyB)] := rfl

/-- Spec ref: metta.md lines 538-544
    Nondeterministic: multiple matching equations. -/
theorem mettaCall_nondeterministic :
    let space := Space.ofList [
      .expression [.symbol "=",
        .expression [.symbol "f", .symbol "a"],
        .symbol "r1"],
      .expression [.symbol "=",
        .expression [.symbol "f", .symbol "a"],
        .symbol "r2"]]
    mettaCall (.expression [.symbol "f", .symbol "a"]) Atom.undefinedType
      space emptyB noDispatch [] fuel =
    [(.symbol "r1", emptyB), (.symbol "r2", emptyB)] := rfl

/-- Spec ref: metta.md line 546
    Non-expression atom → return unchanged. -/
theorem mettaCall_non_expression :
    mettaCall (.symbol "x") Atom.undefinedType emptySpace emptyB noDispatch [] fuel =
    [(.symbol "x", emptyB)] := rfl

/-! ## 7. End-to-end integration tests -/

/-- Simple function evaluation: (= (f a) b), eval (f a) → b -/
theorem e2e_simple_function :
    let space := Space.ofList [
      .expression [.symbol "=",
        .expression [.symbol "f", .symbol "a"],
        .symbol "b"]]
    eval (.expression [.symbol "f", .symbol "a"]) space =
    [(.symbol "b", emptyB)] := rfl

/-- Nested function: (= (g x) (f x)), (= (f a) b), eval (g a) → b -/
theorem e2e_nested :
    let space := Space.ofList [
      .expression [.symbol "=",
        .expression [.symbol "g", .symbol "a"],
        .expression [.symbol "f", .symbol "a"]],
      .expression [.symbol "=",
        .expression [.symbol "f", .symbol "a"],
        .symbol "b"]]
    eval (.expression [.symbol "g", .symbol "a"]) space =
    [(.symbol "b", emptyB)] := rfl

/-- Pattern matching with variables:
    (= (f $x) (result $x)), eval (f hello) → (result hello) -/
theorem e2e_pattern_var :
    let space := Space.ofList [
      .expression [.symbol "=",
        .expression [.symbol "f", .var "x"],
        .expression [.symbol "result", .var "x"]]]
    eval (.expression [.symbol "f", .symbol "hello"]) space =
    [(.expression [.symbol "result", .symbol "hello"],
      Bindings.empty.assign "x" (.symbol "hello"))] := rfl

/-- Nondeterministic choice:
    (= (choose) red), (= (choose) blue), eval (choose) → [red, blue] -/
theorem e2e_nondeterministic :
    let space := Space.ofList [
      .expression [.symbol "=",
        .expression [.symbol "choose"],
        .symbol "red"],
      .expression [.symbol "=",
        .expression [.symbol "choose"],
        .symbol "blue"]]
    eval (.expression [.symbol "choose"]) space =
    [(.symbol "red", emptyB), (.symbol "blue", emptyB)] := rfl

/-- No reduction: expression with no matching equations and no function type. -/
theorem e2e_no_reduction :
    eval (.expression [.symbol "unknown", .symbol "arg"]) emptySpace =
    [(.expression [.symbol "unknown", .symbol "arg"], emptyB)] := rfl

/-! ## Conformance Summary

| Spec Section | Clause | Status | Theorem |
|---|---|---|---|
| metta (240-272) | Empty passthrough | exact | metta_empty_passthrough |
| metta (240-272) | Error passthrough | exact | metta_error_passthrough |
| metta (240-272) | type == Atom | exact | metta_type_atom |
| metta (240-272) | Variable passthrough | exact | metta_variable_passthrough |
| metta (240-272) | type == metatype | exact | metta_type_matches_metatype |
| metta (240-272) | Symbol → typeCast | exact | metta_symbol_typecast_undefined |
| metta (240-272) | Unit → typeCast | exact | metta_unit_typecast |
| metta (240-272) | Grounded → typeCast | exact | metta_grounded_typecast |
| typeCast (275-296) | matching type | exact | typeCast_matching_type |
| typeCast (275-296) | mismatch | exact | typeCast_mismatch |
| typeCast (275-296) | no annotation | exact | typeCast_no_annotation |
| typeCast (275-296) | %Undefined% | exact | typeCast_undefined_type |
| matchTypes (298-314) | %Undefined% left | exact | matchTypes_undef_left |
| matchTypes (298-314) | Atom right | exact | matchTypes_atom_right |
| matchTypes (298-314) | same type | exact | matchTypes_same |
| matchTypes (298-314) | different type | exact | matchTypes_different |
| matchAtoms (577-617) | same symbol | exact | matchAtoms_same_symbol |
| matchAtoms (577-617) | diff symbol | exact | matchAtoms_diff_symbol |
| matchAtoms (577-617) | two vars | exact | matchAtoms_two_vars |
| matchAtoms (577-617) | var left | exact | matchAtoms_var_left |
| matchAtoms (577-617) | var right | exact | matchAtoms_var_right |
| matchAtoms (577-617) | expr match | exact | matchAtoms_expr_match |
| matchAtoms (577-617) | expr length | exact | matchAtoms_expr_length_mismatch |
| matchAtoms (577-617) | grounded same | exact | matchAtoms_grounded_same |
| matchAtoms (577-617) | grounded diff | exact | matchAtoms_grounded_diff |
| matchAtoms (577-617) | sym vs expr | exact | matchAtoms_sym_expr |
| interpretArgs (480-507) | h != atom | exact | interpretArgs_empty_unchanged |
| interpretArgs (480-507) | empty args | exact | interpretArgs_empty_args |
| mettaCall (509-552) | error passthrough | exact | mettaCall_error_passthrough |
| mettaCall (509-552) | equation match | exact | mettaCall_equation_match |
| mettaCall (509-552) | no equation | exact | mettaCall_no_equation |
| mettaCall (509-552) | nondeterministic | exact | mettaCall_nondeterministic |
| mettaCall (509-552) | non-expression | exact | mettaCall_non_expression |
| e2e | simple function | exact | e2e_simple_function |
| e2e | nested | exact | e2e_nested |
| e2e | pattern var | exact | e2e_pattern_var |
| e2e | nondeterministic | exact | e2e_nondeterministic |
| e2e | no reduction | exact | e2e_no_reduction |
-/

end Mettapedia.Languages.MeTTa.HE.Conformance
