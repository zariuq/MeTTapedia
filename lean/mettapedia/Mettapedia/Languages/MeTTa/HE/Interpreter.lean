import Mettapedia.Languages.MeTTa.HE.TypeCheck

/-!
# HE MeTTa Interpreter

Core interpreter functions for Hyperon Experimental MeTTa.
Implements the 6 mutually recursive functions from metta.md lines 240-552
as a fuel-bounded `mutual` block.

## Source Precedence
1. `interpreter.rs` (ground truth)
2. `metta.md` lines 240-552 (spec)

## Main Definitions
* `metta` - Entry point: evaluate atom with expected type (metta.md lines 240-272)
* `interpretExpression` - Interpret expression (metta.md lines 316-356)
* `interpretFunction` - Interpret function call (metta.md lines 452-478)
* `interpretArgs` - Interpret arguments (metta.md lines 480-507)
* `interpretTuple` - Interpret tuple/expression elements (metta.md lines 358-382)
* `mettaCall` - Call MeTTa expression (metta.md lines 509-552)
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.Core (Atom GroundedValue)

/-! ## Core Interpreter

All 6 functions use a shared `fuel : Nat` parameter for termination.
At fuel = 0, the atom is returned unchanged (no reduction).

The `evaluated` parameter tracks expressions that have been evaluated
(optimization from metta.md lines 267-270 to prevent re-evaluation). -/

mutual

/-- Evaluate an atom with expected type in an atomspace.
    Ref: metta.md lines 240-272 "Evaluate atom (metta)".

    Branch structure:
    1. Empty or Error → return unchanged
    2. Type matches metatype, or is Atom, or atom is Variable → return unchanged
    3. Expression already evaluated → return unchanged
    4. Symbol/Grounded/() → type_cast
    5. Expression → interpret_expression, filter success vs error -/
def metta (atom type_ : Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (evaluated : List Atom) (fuel : Nat) : ResultSet :=
  match fuel with
  | 0 => [(atom, b)]
  | n + 1 =>
    -- Line 253: Empty or Error → return unchanged
    if isEmptyAtom atom || isErrorAtom atom then
      [(atom, b)]
    else
      let metatype := getMetaType atom
      -- Line 255: type == Atom or type == metatype or metatype == Variable
      if type_ == Atom.atomType || type_ == metatype || metatype == .symbol "Variable" then
        [(atom, b)]
      -- Line 257: Expression already evaluated
      else if metatype == .symbol "Expression" && evaluated.contains atom then
        [(atom, b)]
      -- Line 259: Symbol or Grounded or unit () → type_cast
      else if metatype == .symbol "Symbol" || metatype == .symbol "Grounded"
              || atom == Atom.unit then
        typeCast atom type_ space b n
      -- Line 261-272: Expression → interpret_expression, filter
      else
        let results := interpretExpression atom type_ space b dispatch evaluated n
        let errors := results.filter fun (a, _) => isErrorAtom a
        let success := results.filter fun (a, _) => !isErrorAtom a
        if !success.isEmpty then
          -- Mark evaluated expressions (optimization, metta.md lines 267-270)
          success
        else
          errors

/-- Interpret an expression.
    Ref: metta.md lines 316-356 "Interpret expression (interpret_expression)".

    Extracts operator, gets its types, branches on function vs non-function types.
    For function types: check applicability → interpret_function → metta_call.
    For non-function/undefined types: interpret_tuple → metta_call. -/
def interpretExpression (atom type_ : Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (evaluated : List Atom) (fuel : Nat) : ResultSet :=
  match fuel with
  | 0 => [(atom, b)]
  | n + 1 =>
    match atom with
    | .expression (op :: _args) =>
      -- Get types of the operator
      let opTypes := getAtomTypes space op
      -- Separate function types from non-function types
      let funcTypes := opTypes.filter isFunctionType
      let nonFuncTypes := opTypes.filter fun t => !isFunctionType t

      -- Try function types first (metta.md lines 335-348)
      let funcResult := funcTypes.foldl (fun acc f =>
        match acc with
        | .inl (prevErrors, _) =>
          match checkIfFunctionTypeIsApplicable atom f type_ space b n with
          | .inl errs =>
            .inl (prevErrors ++ errs.map fun e => (e, b), false)
          | .inr succs =>
            let retType := match getFunctionRetType f with
              | some (.symbol "Expression") => Atom.undefinedType
              | some t => t
              | none => Atom.undefinedType
            let result := succs.flatMap fun sb =>
              let interpd := interpretFunction atom f retType space sb dispatch evaluated n
              interpd.flatMap fun (a, ab) =>
                mettaCall a retType space ab dispatch evaluated n
            .inr result
        | .inr _ => acc  -- Already found a successful function type
      ) (.inl ([], false) : Sum (List ResultPair × Bool) ResultSet)

      match funcResult with
      | .inr result => result
      | .inl (errors, _) =>
        -- Try tuple interpretation if non-function types exist (metta.md lines 350-355)
        let tuples := if !nonFuncTypes.isEmpty then
          let tupResult := interpretTuple atom space b dispatch evaluated n
          tupResult.flatMap fun (a, ab) =>
            mettaCall a type_ space ab dispatch evaluated n
        else []
        tuples ++ errors.map fun (e, eb) => (e, eb)

    | _ => [(atom, b)]  -- Not an expression

/-- Interpret a function call.
    Ref: metta.md lines 452-478 "Interpret function (interpret_function)".

    Evaluates operator via metta, then evaluates arguments via interpret_args.
    Short-circuits on Empty/Error for operator result. -/
def interpretFunction (atom opType _returnType : Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (evaluated : List Atom) (fuel : Nat) : ResultSet :=
  match fuel with
  | 0 => [(atom, b)]
  | n + 1 =>
    match atom with
    | .expression (op :: args) =>
      let argTypes := match getFunctionArgTypes opType with
        | some ts => ts
        | none => []
      -- Evaluate operator (metta.md line 468)
      let opResults := metta op opType space b dispatch evaluated n
      opResults.flatMap fun (h, hb) =>
        -- Short-circuit on Empty/Error (metta.md lines 469-470)
        if isEmptyOrError h then
          [(h, hb)]
        else
          -- Evaluate arguments (metta.md lines 472-476)
          let argResults := interpretArgs args argTypes space hb dispatch evaluated n
          argResults.flatMap fun (t, tb) =>
            if isEmptyOrError t then
              [(t, tb)]
            else
              -- Reconstruct expression with evaluated op and args
              match t with
              | .expression evaluatedArgs => [(.expression (h :: evaluatedArgs), tb)]
              | _ => [(.expression [h, t], tb)]
    | _ => [(atom, b)]

/-- Interpret arguments.
    Ref: metta.md lines 480-507 "Interpret arguments (interpret_args)".

    Recursive head/tail evaluation.
    **Critical clause** (line 498): `($h == Empty or $h ~ Error) and $h != $atom`.
    The short-circuit only fires when the result *changed* to Empty/Error. -/
def interpretArgs (args argTypes : List Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (evaluated : List Atom) (fuel : Nat) : ResultSet :=
  match fuel with
  | 0 => [(.expression args, b)]
  | n + 1 =>
    match args, argTypes with
    | [], _ => [(.expression [], b)]
    | [arg], type_ :: _ =>
      -- Single arg: evaluate and wrap
      let hResults := metta arg type_ space b dispatch evaluated n
      hResults.flatMap fun (h, hb) =>
        -- Critical clause: short-circuit only if result CHANGED (h != arg)
        if isEmptyOrError h && h != arg then
          [(h, hb)]
        else
          [(.expression [h], hb)]
    | arg :: restArgs, type_ :: restTypes =>
      -- Multiple args: evaluate head, recurse on tail
      let hResults := metta arg type_ space b dispatch evaluated n
      hResults.flatMap fun (h, hb) =>
        -- Critical clause (metta.md line 498): short-circuit only if h != arg
        if isEmptyOrError h && h != arg then
          [(h, hb)]
        else
          let tResults := interpretArgs restArgs restTypes space hb dispatch evaluated n
          tResults.flatMap fun (t, tb) =>
            if isEmptyOrError t then
              [(t, tb)]
            else
              match t with
              | .expression ts => [(.expression (h :: ts), tb)]
              | _ => [(.expression [h, t], tb)]
    | arg :: restArgs, [] =>
      -- No type info left: use %Undefined%
      let hResults := metta arg Atom.undefinedType space b dispatch evaluated n
      hResults.flatMap fun (h, hb) =>
        if isEmptyOrError h && h != arg then
          [(h, hb)]
        else
          let tResults := interpretArgs restArgs [] space hb dispatch evaluated n
          tResults.flatMap fun (t, tb) =>
            if isEmptyOrError t then
              [(t, tb)]
            else
              match t with
              | .expression ts => [(.expression (h :: ts), tb)]
              | _ => [(.expression [h, t], tb)]

/-- Interpret tuple (evaluate each element of an expression).
    Ref: metta.md lines 358-382 "Interpret tuple (interpret_tuple)".

    Evaluates head via metta with %Undefined% type, recurses on tail.
    Short-circuits on Empty/Error for both head and tail. -/
def interpretTuple (atom : Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (evaluated : List Atom) (fuel : Nat) : ResultSet :=
  match fuel with
  | 0 => [(atom, b)]
  | n + 1 =>
    match atom with
    | .expression [] => [(.expression [], b)]
    | .expression [hd] =>
      let hResults := metta hd Atom.undefinedType space b dispatch evaluated n
      hResults.flatMap fun (h, hb) =>
        if isEmptyOrError h then [(h, hb)]
        else [(.expression [h], hb)]
    | .expression (hd :: tl) =>
      let hResults := metta hd Atom.undefinedType space b dispatch evaluated n
      hResults.flatMap fun (h, hb) =>
        if isEmptyOrError h then [(h, hb)]
        else
          let tResults := interpretTuple (.expression tl) space hb dispatch evaluated n
          tResults.flatMap fun (t, tb) =>
            if isEmptyOrError t then [(t, tb)]
            else
              match t with
              | .expression ts => [(.expression (h :: ts), tb)]
              | _ => [(.expression [h, t], tb)]
    | other => [(other, b)]

/-- Call a MeTTa expression.
    Ref: metta.md lines 509-552 "Call MeTTa expression (metta_call)".

    Handles:
    1. Error passthrough
    2. Grounded dispatch (Ok/RuntimeError/NoReduce/IncorrectArgument)
    3. Equation query (= atom $X)
    4. Empty result handling -/
def mettaCall (atom type_ : Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (evaluated : List Atom) (fuel : Nat) : ResultSet :=
  match fuel with
  | 0 => [(atom, b)]
  | n + 1 =>
    -- Line 521: Error passthrough
    if isErrorAtom atom then
      [(atom, b)]
    else
      match atom with
      | .expression (op :: args) =>
        -- Check if op is executable grounded atom (line 527)
        if dispatch.isExecutable op then
          match dispatch.execute op args with
          | .ok results =>
            -- Line 530: evaluate each result with merge
            if results.isEmpty then
              [(Atom.empty, b)]
            else
              results.flatMap fun (r, rb) =>
                let merged := mergeBindings rb b n
                merged.flatMap fun mb =>
                  if mb.hasLoop then []
                  else metta r type_ space mb dispatch evaluated n
          | .runtimeError msg =>
            -- Line 532
            [(Atom.error atom (.symbol msg), b)]
          | .noReduce =>
            -- Line 534
            [(atom, b)]
          | .incorrectArgument =>
            -- Line 536
            [(atom, b)]
        else
          -- Non-grounded: query equations (line 538)
          let queryResults := queryEquations space atom n
          if !queryResults.isEmpty then
            let results := queryResults.flatMap fun (rhs, qb) =>
              let merged := mergeBindings qb b n
              merged.flatMap fun mb =>
                if mb.hasLoop then []
                else
                  -- Get value of $X from bindings
                  let resolved := mb.apply rhs n
                  metta resolved type_ space mb dispatch evaluated n
            if results.isEmpty then
              [(Atom.empty, b)]
            else results
          else
            -- No equations match → return unchanged (line 546)
            [(atom, b)]
      | _ =>
        -- Not an expression → return unchanged
        [(atom, b)]

end

/-! ## Convenience API -/

/-- Evaluate an atom with default settings.
    Wraps `metta` with empty bindings, no dispatch, and default fuel. -/
def eval (atom : Atom) (space : Space) (type_ : Atom := Atom.undefinedType)
    (dispatch : GroundedDispatch := .none) (fuel : Nat := 100) : ResultSet :=
  metta atom type_ space Bindings.empty dispatch [] fuel

/-! ## Unit Tests -/

section Tests

-- Simple space with equations
private def s1 : Space := Space.ofList [
  .expression [.symbol "=", .symbol "a", .symbol "b"]
]

-- metta: symbol goes through typeCast, NOT equation lookup.
-- Symbols are not expressions, so (= a b) is NOT consulted here.
-- This matches HE behavior: bare symbols are not auto-evaluated.
example : eval (.symbol "a") s1 = [(.symbol "a", Bindings.empty)] := rfl

-- metta: symbol with no info → unchanged
example : eval (.symbol "x") Space.empty = [(.symbol "x", Bindings.empty)] := rfl

-- metta: Empty passes through
example : eval Atom.empty Space.empty = [(Atom.empty, Bindings.empty)] := rfl

-- metta: Error passes through
example : eval (Atom.error (.symbol "x") (.symbol "err")) Space.empty =
    [(Atom.error (.symbol "x") (.symbol "err"), Bindings.empty)] := rfl

-- metta: variable returns unchanged
example : eval (.var "x") Space.empty = [(.var "x", Bindings.empty)] := rfl

-- Expression evaluation: (f a) with (= (f a) b) → evaluates to b via mettaCall
private def s2 : Space := Space.ofList [
  .expression [.symbol "=",
    .expression [.symbol "f", .symbol "a"],
    .symbol "b"]
]

example : eval (.expression [.symbol "f", .symbol "a"]) s2 =
    [(.symbol "b", Bindings.empty)] := rfl

-- Nondeterministic: two equations for same pattern
private def s3 : Space := Space.ofList [
  .expression [.symbol "=", .symbol "color", .symbol "red"],
  .expression [.symbol "=", .symbol "color", .symbol "green"]
]

-- color is a symbol → typeCast, not equation query
example : eval (.symbol "color") s3 = [(.symbol "color", Bindings.empty)] := rfl

end Tests

end Mettapedia.Languages.MeTTa.HE
