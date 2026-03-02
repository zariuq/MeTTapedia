import Mettapedia.Languages.MeTTa.HE.Matching

/-!
# HE MeTTa Type Checking

Type checking and type casting for the HE interpreter.

## Source Precedence
1. `interpreter.rs` (ground truth)
2. `metta.md` lines 275-450 (spec)

## Main Definitions
* `checkArgumentType` - Check argument type (metta.md lines 429-450)
* `checkIfFunctionTypeIsApplicable` - Check function type applicability (metta.md lines 384-427)
* `typeCast` - Cast atom to expected type (metta.md lines 275-296)
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.Core (Atom GroundedValue)

/-! ## Check Argument Type

Ref: metta.md lines 429-450 "Check argument type (check_argument_type)".
Returns a list of `Sum Atom Bindings` where:
- `Sum.inl t` means type mismatch (actual type `t`)
- `Sum.inr b` means type match with resulting bindings `b` -/

/-- Check if an argument has the expected type.
    Ref: metta.md lines 429-450. -/
def checkArgumentType (space : Space) (arg expectedType : Atom) (b : Bindings)
    (fuel : Nat := 100) : List (Sum Atom Bindings) :=
  let actualTypes := getAtomTypes space arg
  actualTypes.flatMap fun t =>
    let matched := matchTypes expectedType t b fuel
    if matched.isEmpty then
      [Sum.inl t]  -- type mismatch: report actual type
    else
      matched.map Sum.inr

/-! ## Check Function Type Applicability

Ref: metta.md lines 384-427 "Check if function type is applicable".
Returns:
- `Sum.inl errors` if function type is NOT applicable (with error atoms)
- `Sum.inr bindings` if function type IS applicable (with resulting bindings) -/

/-- Check if a function type is applicable to an expression.
    Ref: metta.md lines 384-427.

    Checks:
    1. Argument count matches
    2. Each argument has correct type
    3. Return type matches expected type -/
def checkIfFunctionTypeIsApplicable (expr funcType expectedType : Atom)
    (space : Space) (b : Bindings) (fuel : Nat) : Sum (List Atom) (List Bindings) :=
  match fuel with
  | 0 => .inl []
  | n + 1 =>
    -- Extract expression args (everything after head/operator)
    let exprArgs := match expr with
      | .expression (_ :: args) => args
      | _ => []
    -- Extract function type arg types
    let funcArgTypes := match getFunctionArgTypes funcType with
      | some ts => ts
      | none => []
    -- Extract function return type
    let funcRetType := match getFunctionRetType funcType with
      | some t => t
      | none => Atom.undefinedType

    -- Step 1: Check argument count (metta.md line 397)
    if exprArgs.length != funcArgTypes.length then
      .inl [mkError expr .incorrectNumberOfArguments]
    else
      -- Step 2: Check each argument type (metta.md lines 400-412)
      let (errors, results) := checkArgLoop exprArgs funcArgTypes expr [b] [] space n 1

      -- Step 3: Check return type (metta.md lines 414-421)
      if results.isEmpty then
        .inl errors
      else
        let (retErrors, retResults) := results.foldl (fun (errs, succs) r =>
          let matched := matchTypes expectedType funcRetType r n
          if matched.isEmpty then
            (errs ++ [mkError expr (.badType expectedType funcRetType)], succs)
          else
            (errs, succs ++ matched)
        ) (errors, [])

        -- metta.md lines 423-426
        if retResults.isEmpty then
          .inl retErrors
        else
          .inr retResults
where
  /-- Process each argument position, accumulating errors and successful bindings. -/
  checkArgLoop (args argTypes : List Atom) (expr : Atom) (results errors : List _)
      (space : Space) (fuel idx : Nat) :
      List Atom × List Bindings :=
    match args, argTypes with
    | [], [] => (errors, results)
    | arg :: args', argTy :: argTys' =>
      let (newErrors, newResults) := results.foldl (fun (errs, succs) r =>
        let checks := checkArgumentType space arg argTy r fuel
        checks.foldl (fun (errs', succs') c =>
          match c with
          | .inl t =>
            (errs' ++ [mkError expr (.badArgType (idx - 1) argTy t)], succs')
          | .inr b =>
            (errs', succs' ++ [b])
        ) (errs, succs)
      ) (errors, [])
      checkArgLoop args' argTys' expr newResults newErrors space fuel (idx + 1)
    | _, _ => (errors, results)  -- length mismatch (shouldn't happen)

/-! ## Type Cast

Ref: metta.md lines 275-296 "Cast types (type_cast)".
Gets all types for atom from space, tries to match each against expected type.
Returns on first successful match; accumulates errors for failures. -/

/-- Cast an atom to an expected type.
    Ref: metta.md lines 275-296. -/
def typeCast (atom expectedType : Atom) (space : Space) (b : Bindings)
    (fuel : Nat := 100) : ResultSet :=
  let types := getAtomTypes space atom
  typeCastLoop types atom expectedType b fuel []
where
  /-- Iterate over types; return on first match, accumulate errors.
      Ref: metta.md lines 288-295. -/
  typeCastLoop (types : List Atom) (atom expectedType : Atom)
      (b : Bindings) (fuel : Nat) (noMatch : List Atom) : ResultSet :=
    match types with
    | [] =>
      -- No types matched: return errors for all
      noMatch.map fun t =>
        (mkError atom (.badType expectedType t), b)
    | t :: rest =>
      let mtch := matchTypes t expectedType b fuel
      if mtch.isEmpty then
        -- This type didn't match; record it and continue
        typeCastLoop rest atom expectedType b fuel (noMatch ++ [t])
      else
        -- Match found! Return atom with all successful bindings
        -- (metta.md line 294: early return)
        mtch.map fun m => (atom, m)

/-! ## Unit Tests -/

section Tests

private def testSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "x", .symbol "Int"],
    .expression [.symbol ":", .symbol "y", .symbol "Int"],
    .expression [.symbol ":", .symbol "z", .symbol "Bool"],
    .expression [.symbol ":", .symbol "add",
      .expression [.symbol "->", .symbol "Int", .symbol "Int", .symbol "Int"]]
  ]

-- typeCast: matching type
example : typeCast (.symbol "x") (.symbol "Int") testSpace Bindings.empty 10 =
    [(.symbol "x", Bindings.empty)] := rfl

-- typeCast: any type (%Undefined%)
example : typeCast (.symbol "x") Atom.undefinedType testSpace Bindings.empty 10 =
    [(.symbol "x", Bindings.empty)] := rfl

-- typeCast: type mismatch
example : typeCast (.symbol "z") (.symbol "Int") testSpace Bindings.empty 10 =
    [(mkError (.symbol "z") (.badType (.symbol "Int") (.symbol "Bool")),
      Bindings.empty)] := rfl

-- typeCast: unknown atom gets %Undefined% type, which matches anything
example : typeCast (.symbol "unknown") (.symbol "Foo") testSpace Bindings.empty 10 =
    [(.symbol "unknown", Bindings.empty)] := rfl

-- checkArgumentType
example : checkArgumentType testSpace (.symbol "x") (.symbol "Int") Bindings.empty 10 =
    [Sum.inr Bindings.empty] := rfl
example : checkArgumentType testSpace (.symbol "z") (.symbol "Int") Bindings.empty 10 =
    [Sum.inl (.symbol "Bool")] := rfl

-- checkIfFunctionTypeIsApplicable: correct args
example : checkIfFunctionTypeIsApplicable
    (.expression [.symbol "add", .symbol "x", .symbol "y"])
    (.expression [.symbol "->", .symbol "Int", .symbol "Int", .symbol "Int"])
    Atom.undefinedType testSpace Bindings.empty 10 =
    .inr [Bindings.empty] := rfl

-- checkIfFunctionTypeIsApplicable: wrong arg count
example : checkIfFunctionTypeIsApplicable
    (.expression [.symbol "add", .symbol "x"])
    (.expression [.symbol "->", .symbol "Int", .symbol "Int", .symbol "Int"])
    Atom.undefinedType testSpace Bindings.empty 10 =
    .inl [mkError (.expression [.symbol "add", .symbol "x"]) .incorrectNumberOfArguments] := rfl

end Tests

end Mettapedia.Languages.MeTTa.HE
