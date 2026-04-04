import Mettapedia.Languages.MeTTa.HE.EvalSpec

/-!
# HE MeTTa Total Evaluator

Computable evaluator implementing the 6 mutual inductive relations from
`EvalSpec.lean`. Fuel-indexed for totality; zero `partial def`, zero `sorry`.

## Architecture
- 6 mutual functions mirroring the 6 EvalSpec relations
- Uses leaf functions from Types.lean, Space.lean, Matching.lean, TypeCheck.lean
- Fuel parameter ensures termination; Lean's kernel can reduce small examples

## Correspondence with EvalSpec
| Function              | Spec Relation          | Constructors |
|-----------------------|------------------------|--------------|
| `evalAtom`            | `EvalAtom`             | 5            |
| `interpretExpression` | `InterpretExpression`  | 3            |
| `interpretFunction`   | `InterpretFunction`    | 3            |
| `interpretArgs`       | `InterpretArgs`        | 4            |
| `interpretTuple`      | `InterpretTuple`       | 4            |
| `mettaCall`           | `MettaCall`            | 9            |
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Extract child elements from an atom: expressions unwrap, others wrap in singleton. -/
def atomElements : Atom → List Atom
  | .expression es => es
  | a => [a]

mutual

/-- Evaluate an atom to a result set.
    Ref: EvalSpec.EvalAtom (5 constructors, spec lines 105-136). -/
def evalAtom (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (fuel : Nat) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    if isEmptyOrError atom then
      [(atom, b)]
    else if type_ == Atom.atomType
         || type_ == getMetaType atom
         || getMetaType atom == Atom.variableType then
      [(atom, b)]
    else if getMetaType atom == Atom.symbolType
         || getMetaType atom == Atom.groundedType
         || atom == Atom.unit then
      typeCast atom type_ space b n
    else if getMetaType atom == Atom.expressionType then
      let results := interpretExpression space dispatch atom type_ b n
      let successes := results.filter fun (r, _) => !isErrorAtom r
      if !successes.isEmpty then successes
      else results.filter fun (r, _) => isErrorAtom r
    else [(atom, b)]

/-- Interpret an expression (dispatch to function or tuple path).
    Ref: EvalSpec.InterpretExpression (3 constructors, spec lines 172-210).

    `metta.md:348` has an early `return $result` inside the Ok loop (first
    successful function type wins). This evaluator accumulates results from all
    matching function types. EvalSpec's nondeterminism subsumes both behaviors. -/
def interpretExpression (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (fuel : Nat) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match atom with
    | .expression (op :: _) =>
      let types := getAtomTypes space op
      let funcResults : ResultSet := types.flatMap fun funcType =>
        if isFunctionType funcType then
          match checkIfFunctionTypeIsApplicable atom funcType type_ space b n with
          | .inr succs =>
            succs.flatMap fun b' =>
              let retType :=
                if getFunctionRetType funcType == some Atom.expressionType
                then Atom.undefinedType
                else (getFunctionRetType funcType).getD Atom.undefinedType
              let interpResults := interpretFunction space dispatch atom funcType b' n
              interpResults.flatMap fun (r, rb) =>
                mettaCall space dispatch r retType rb n
          | .inl _ => []
        else []
      let hasNonFunc := types.any fun t =>
        !isFunctionType t || t == Atom.undefinedType
      let tupleResults : ResultSet :=
        if hasNonFunc then
          let interpResults := interpretTuple space dispatch atom b n
          interpResults.flatMap fun (r, rb) =>
            mettaCall space dispatch r type_ rb n
        else []
      let allResults := funcResults ++ tupleResults
      if !allResults.isEmpty then allResults
      else if !hasNonFunc then
        let allChecksFailed := types.all fun funcType =>
          if isFunctionType funcType then
            match checkIfFunctionTypeIsApplicable atom funcType type_ space b n with
            | .inl _ => true
            | .inr _ => false
          else true
        if allChecksFailed then
          types.flatMap fun funcType =>
            if isFunctionType funcType then
              match checkIfFunctionTypeIsApplicable atom funcType type_ space b n with
              | .inl errs => errs.map fun e => (e, b)
              | .inr _ => []
            else []
        else []
      else []
    | _ => []

/-- Interpret a function call (evaluate head, then args).
    Ref: EvalSpec.InterpretFunction (3 constructors, spec lines 296-321). -/
def interpretFunction (space : Space) (dispatch : GroundedDispatch)
    (atom opType : Atom) (b : Bindings) (fuel : Nat) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match atom with
    | .expression (op :: args) =>
      let headResults := evalAtom space dispatch op opType b n
      headResults.flatMap fun (headR, headB) =>
        if isEmptyOrError headR then [(headR, headB)]
        else
          match getFunctionArgTypes opType with
          | some argTypes =>
            let tailResults := interpretArgs space dispatch args argTypes headB n
            tailResults.map fun (tailR, tailB) =>
              if isEmptyOrError tailR then (tailR, tailB)
              else (.expression (headR :: atomElements tailR), tailB)
          | none => []
    | _ => []

/-- Interpret argument list (recursive evaluation of each arg with its type).
    Ref: EvalSpec.InterpretArgs (4 constructors, spec lines 322-347). -/
def interpretArgs (space : Space) (dispatch : GroundedDispatch)
    (args types : List Atom) (b : Bindings) (fuel : Nat) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match args, types with
    | [], [] => [(Atom.unit, b)]
    | arg :: remainingArgs, t :: remainingTypes =>
      let headResults := evalAtom space dispatch arg t b n
      headResults.flatMap fun (headR, headB) =>
        if headR != arg && isEmptyOrError headR then [(headR, headB)]
        else
          let tailResults :=
            interpretArgs space dispatch remainingArgs remainingTypes headB n
          tailResults.map fun (tailR, tailB) =>
            if isEmptyOrError tailR then (tailR, tailB)
            else (.expression (headR :: atomElements tailR), tailB)
    | _, _ => []

/-- Interpret a tuple (recursive element-wise evaluation).
    Ref: EvalSpec.InterpretTuple (4 constructors, spec lines 211-233). -/
def interpretTuple (space : Space) (dispatch : GroundedDispatch)
    (atom : Atom) (b : Bindings) (fuel : Nat) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match atom with
    | .expression [single] =>
      evalAtom space dispatch single Atom.undefinedType b n
    | .expression (hd :: hd2 :: rest) =>
      let headResults := evalAtom space dispatch hd Atom.undefinedType b n
      headResults.flatMap fun (headR, headB) =>
        if isEmptyOrError headR then [(headR, headB)]
        else
          let tailResults :=
            interpretTuple space dispatch (.expression (hd2 :: rest)) headB n
          tailResults.map fun (tailR, tailB) =>
            if isEmptyOrError tailR then (tailR, tailB)
            else (.expression (headR :: atomElements tailR), tailB)
    | _ => []

/-- Call a MeTTa expression (grounded dispatch or equation matching).
    Ref: EvalSpec.MettaCall (9 constructors, spec lines 348-389). -/
def mettaCall (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (fuel : Nat) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    if isErrorAtom atom then [(atom, b)]
    else match atom with
    | .expression (op :: args) =>
      if dispatch.isExecutable op then
        match dispatch.execute op args with
        | .ok results =>
          if results.isEmpty then
            [(Atom.empty, b)]
          else
            results.flatMap fun (nativeR, nativeB) =>
              (mergeBindings nativeB b n).flatMap fun mb =>
                evalAtom space dispatch nativeR type_ mb n
        | .runtimeError msg => [(Atom.error atom (.symbol msg), b)]
        | .noReduce => [(atom, b)]
        | .incorrectArgument => [(atom, b)]
      else
        let eqs := queryEquations space atom n
        if eqs.isEmpty then [(atom, b)]
        else
          eqs.flatMap fun (rhs, qb) =>
            (mergeBindings qb b n).flatMap fun mb =>
              if mb.hasLoop then []
              else evalAtom space dispatch (mb.apply rhs n) type_ mb n
    | _ =>
      let eqs := queryEquations space atom n
      if eqs.isEmpty then [(atom, b)]
      else
        eqs.flatMap fun (rhs, qb) =>
          (mergeBindings qb b n).flatMap fun mb =>
            if mb.hasLoop then []
            else evalAtom space dispatch (mb.apply rhs n) type_ mb n

end

/-- Evaluate a MeTTa atom with default settings. -/
def eval (space : Space) (atom : Atom) (fuel : Nat := 100) : ResultSet :=
  evalAtom space GroundedDispatch.none atom Atom.undefinedType Bindings.empty fuel

section Tests

example : evalAtom Space.empty GroundedDispatch.none
    Atom.empty Atom.atomType Bindings.empty 10 =
    [(Atom.empty, Bindings.empty)] := rfl

example : evalAtom Space.empty GroundedDispatch.none
    (Atom.error (.symbol "x") (.symbol "msg")) Atom.atomType Bindings.empty 10 =
    [(Atom.error (.symbol "x") (.symbol "msg"), Bindings.empty)] := rfl

example : evalAtom Space.empty GroundedDispatch.none
    (.symbol "a") Atom.atomType Bindings.empty 10 =
    [(.symbol "a", Bindings.empty)] := rfl

example : evalAtom Space.empty GroundedDispatch.none
    (.var "x") (.symbol "Int") Bindings.empty 10 =
    [(.var "x", Bindings.empty)] := rfl

example : evalAtom Space.empty GroundedDispatch.none
    (.symbol "a") Atom.symbolType Bindings.empty 10 =
    [(.symbol "a", Bindings.empty)] := rfl

private def typedSpace := Space.ofList [
  .expression [.symbol ":", .symbol "x", .symbol "Int"]
]

example : evalAtom typedSpace GroundedDispatch.none
    (.symbol "x") (.symbol "Int") Bindings.empty 10 =
    [(.symbol "x", Bindings.empty)] := rfl

example : evalAtom typedSpace GroundedDispatch.none
    (.symbol "x") Atom.undefinedType Bindings.empty 10 =
    [(.symbol "x", Bindings.empty)] := rfl

example : evalAtom Space.empty GroundedDispatch.none
    Atom.unit Atom.undefinedType Bindings.empty 10 =
    [(Atom.unit, Bindings.empty)] := rfl

private def eqSpace := Space.ofList [
  .expression [.symbol "=", .symbol "x", .symbol "y"]
]

example : mettaCall eqSpace GroundedDispatch.none
    (.symbol "x") Atom.undefinedType Bindings.empty 10 =
    [(.symbol "y", Bindings.empty)] := rfl

example : mettaCall Space.empty GroundedDispatch.none
    (.symbol "x") Atom.undefinedType Bindings.empty 10 =
    [(.symbol "x", Bindings.empty)] := rfl

example : mettaCall Space.empty GroundedDispatch.none
    (Atom.error (.symbol "x") (.symbol "msg")) Atom.undefinedType Bindings.empty 10 =
    [(Atom.error (.symbol "x") (.symbol "msg"), Bindings.empty)] := rfl

example : interpretArgs Space.empty GroundedDispatch.none
    [] [] Bindings.empty 10 =
    [(Atom.unit, Bindings.empty)] := rfl

example : interpretTuple Space.empty GroundedDispatch.none
    (.expression [.symbol "a"]) Bindings.empty 10 =
    [(.symbol "a", Bindings.empty)] := rfl

example : eval Space.empty (.symbol "a") 10 =
    [(.symbol "a", Bindings.empty)] := rfl

private def tuplEqSpace := Space.ofList [
  .expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .symbol "b"]
]

private def funcSpace := Space.ofList [
  .expression [.symbol ":", .symbol "Z", .symbol "Nat"],
  .expression [.symbol ":", .symbol "S",
    .expression [.symbol "->", .symbol "Nat", .symbol "Nat"]],
  .expression [.symbol ":", .symbol "Add",
    .expression [.symbol "->", .symbol "Nat", .symbol "Nat", .symbol "Nat"]],
  .expression [.symbol "=",
    .expression [.symbol "Add", .var "x", .symbol "Z"],
    .var "x"]
]

example : interpretTuple Space.empty GroundedDispatch.none
    (.expression [.symbol "a", .symbol "b"]) Bindings.empty 10 =
    [(.expression [.symbol "a", .symbol "b"], Bindings.empty)] := rfl

example : interpretArgs Space.empty GroundedDispatch.none
    [.symbol "a"] [Atom.undefinedType] Bindings.empty 10 =
    [(.expression [.symbol "a"], Bindings.empty)] := rfl

example : interpretFunction funcSpace GroundedDispatch.none
    (.expression [.symbol "S", .symbol "Z"])
    (.expression [.symbol "->", .symbol "Nat", .symbol "Nat"])
    Bindings.empty 10 =
    [(.expression [.symbol "S", .symbol "Z"], Bindings.empty)] := rfl

example : interpretExpression Space.empty GroundedDispatch.none
    (.expression [.symbol "a", .symbol "b"]) Atom.undefinedType Bindings.empty 10 =
    [(.expression [.symbol "a", .symbol "b"], Bindings.empty)] := rfl

example : interpretExpression funcSpace GroundedDispatch.none
    (.expression [.symbol "S", .symbol "Z"]) Atom.undefinedType Bindings.empty 10 =
    [(.expression [.symbol "S", .symbol "Z"], Bindings.empty)] := rfl

example : evalAtom tuplEqSpace GroundedDispatch.none
    (.expression [.symbol "f", .symbol "a"]) Atom.undefinedType Bindings.empty 10 =
    [(.symbol "b", Bindings.empty)] := rfl

end Tests

end Mettapedia.Languages.MeTTa.HE
