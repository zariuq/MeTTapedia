import Mettapedia.OSLF.MeTTaIL.PremiseDatalog

/-!
# HE MeTTa Premises as PremiseProgram

Defines the premise relations needed by `mettaHE : LanguageDef` rewrite rules.
These capture HE's evaluation dispatch decisions: metatype checking, function
type applicability, equation query, grounded dispatch, etc.

## Relation Summary

| Relation | Arity | Description |
|----------|-------|-------------|
| isEmpty | 1 | Atom is the Empty sentinel |
| isError | 1 | Atom matches (Error _ _) pattern |
| metaType | 2 | Intrinsic metatype of atom |
| typeMatchesMetaOrAtom | 2 | type == Atom or type == metatype or metatype == Variable |
| typeNotMatchesMetaOrAtom | 2 | explicit positive complement of typeMatchesMetaOrAtom |
| needsTypeCast | 2 | metaType ∈ {Symbol, Grounded} and NOT typeMatchesMetaOrAtom |
| needsInterpExpr | 2 | metaType == Expression and NOT typeMatchesMetaOrAtom |
| atomTypes | 3 | Type annotations (: atom type) from space |
| isFuncType | 1 | Type is an arrow (-> ...) |
| applicableFuncType | 5 | Function type is applicable to expression with expected type |
| needsTupleInterp | 3 | No applicable func type + has non-func types |
| notExpression | 1 | Atom is not an Expression (metatype != Expression) |
| eqQueryResult | 3 | Equation query: (= pattern rhs) matched, rhs resolved |
| eqQueryHas | 2 | Witness that at least one equation matched |
| noEqQuery | 2 | No matching equations in space (index-backed check) |
| groundedCallResult | 3 | Grounded dispatch → Ok result |
| isExecutable | 1 | Atom is an executable grounded atom |
| notExecutable | 1 | Negation of isExecutable |
| typeOf | 3 | Atom has type in space (via annotations) |
| typeMismatch | 4 | Atom's actual type != expected type |
| funcArgTypes | 2 | Extract argument type list from ArrowType |
| changedToEmpty | 2 | New atom is Empty and changed from original |
| changedToError | 2 | New atom is Error and changed from original |
| interpFuncResult | (removed) | moved to explicit rewrite transitions |
| interpTupleResult | (removed) | moved to explicit rewrite transitions |

## Design Notes

- Recursive evaluation semantics should be encoded as explicit rewrite transitions
  in `HELanguageDef.lean`, not hidden in opaque premise builtins.
- Simpler relations (isEmpty, isError, metaType) are pure structural checks
  that compile directly to Ascent pattern matching.
-/

namespace Mettapedia.Languages.MeTTa.HE.Premises

open Mettapedia.OSLF.MeTTaIL.PremiseDatalog
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

/-! ## Atom Predicate Relations -/

/-- `isEmpty(atom)`: atom is the Empty sentinel. -/
private def isEmptyRules : List PRule :=
  [ { headRel := "isEmpty"
      headArgs := [.var "atom"]
      body := [.eq (.var "atom") (.ctor "Empty" [])]
      clauseName := some "isEmpty_check" } ]

/-- `isError(atom)`: atom matches ErrorAtom(source, code). -/
private def isErrorRules : List PRule :=
  [ { headRel := "isError"
      headArgs := [.var "atom"]
      body := [.deconstruct (.var "atom") "ErrorAtom" ["_source", "_code"]]
      clauseName := some "isError_check" } ]

/-- `changedToEmpty(orig, new)`:
    short-circuit guard used by interpretArgs: new == Empty and new != orig. -/
private def changedToEmptyRules : List PRule :=
  [ { headRel := "changedToEmpty"
      headArgs := [.var "orig", .var "new"]
      body := [ .relQuery "isEmpty" [.var "new"]
              , .neq (.var "new") (.var "orig") ]
      clauseName := some "changedToEmpty_guard" } ]

/-- `changedToError(orig, new)`:
    short-circuit guard used by interpretArgs: new is Error and new != orig. -/
private def changedToErrorRules : List PRule :=
  [ { headRel := "changedToError"
      headArgs := [.var "orig", .var "new"]
      body := [ .relQuery "isError" [.var "new"]
              , .neq (.var "new") (.var "orig") ]
      clauseName := some "changedToError_guard" } ]

/-! ## Metatype Relations -/

/-- `metaType(atom, mt)`: intrinsic metatype of atom.
    Ref: metta.md `get_meta_type`. -/
private def metaTypeRules : List PRule :=
  [ -- Symbol atoms → "Symbol"
    { headRel := "metaType"
      headArgs := [.var "atom", .ctor "SymbolType" []]
      body := [.deconstruct (.var "atom") "SymAtom" ["_"]]
      clauseName := some "metaType_symbol" }
  , -- Variable atoms → "Variable"
    { headRel := "metaType"
      headArgs := [.var "atom", .ctor "VariableType" []]
      body := [.deconstruct (.var "atom") "VarAtom" ["_"]]
      clauseName := some "metaType_variable" }
  , -- Expression atoms → "Expression"
    { headRel := "metaType"
      headArgs := [.var "atom", .ctor "ExpressionType" []]
      body := [.deconstruct (.var "atom") "ExprCons" ["_", "_"]]
      clauseName := some "metaType_expression_cons" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "ExpressionType" []]
      body := [.eq (.var "atom") (.ctor "ExprNil" [])]
      clauseName := some "metaType_expression_nil" }
  , -- Grounded atoms → "Grounded"
    { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.deconstruct (.var "atom") "GInt" ["_"]]
      clauseName := some "metaType_grounded_int" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.deconstruct (.var "atom") "GString" ["_"]]
      clauseName := some "metaType_grounded_string" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.deconstruct (.var "atom") "GBool" ["_"]]
      clauseName := some "metaType_grounded_bool" }
  , -- Built-in grounded operators
    { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpAdd" [])]
      clauseName := some "metaType_grounded_op_add" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpSub" [])]
      clauseName := some "metaType_grounded_op_sub" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpMul" [])]
      clauseName := some "metaType_grounded_op_mul" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpDiv" [])]
      clauseName := some "metaType_grounded_op_div" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpMod" [])]
      clauseName := some "metaType_grounded_op_mod" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpLt" [])]
      clauseName := some "metaType_grounded_op_lt" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpGt" [])]
      clauseName := some "metaType_grounded_op_gt" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpEq" [])]
      clauseName := some "metaType_grounded_op_eq" }
  ]

/-! ## Metta Dispatch Relations -/

/-- `typeMatchesMetaOrAtom(atom, type)`:
    type == Atom OR type == metatype(atom) OR metatype(atom) == Variable.
    Ref: metta.md line 255. -/
private def typeMatchesMetaOrAtomRules : List PRule :=
  [ -- type == Atom
    { headRel := "typeMatchesMetaOrAtom"
      headArgs := [.var "atom", .var "ty"]
      body := [.eq (.var "ty") (.ctor "AtomType" [])]
      clauseName := some "typeMatch_atomType" }
  , -- type == metatype(atom)
    { headRel := "typeMatchesMetaOrAtom"
      headArgs := [.var "atom", .var "ty"]
      body := [.relQuery "metaType" [.var "atom", .var "ty"]]
      clauseName := some "typeMatch_sameMetaType" }
  , -- metatype(atom) == Variable
    { headRel := "typeMatchesMetaOrAtom"
      headArgs := [.var "atom", .var "ty"]
      body := [.relQuery "metaType" [.var "atom", .ctor "VariableType" []]]
      clauseName := some "typeMatch_variable" }
  ]

/-- `typeNotMatchesMetaOrAtom(atom, type)`:
    explicit positive complement for dispatch, avoiding negation cycles. -/
private def typeNotMatchesMetaOrAtomRules : List PRule :=
  [ { headRel := "typeNotMatchesMetaOrAtom"
      headArgs := [.var "atom", .var "ty"]
      body := [ .relQuery "metaType" [.var "atom", .var "mt"]
              , .neq (.var "ty") (.ctor "AtomType" [])
              , .neq (.var "mt") (.ctor "VariableType" [])
              , .neq (.var "mt") (.var "ty") ]
      clauseName := some "typeNotMatch_explicit" } ]

/-- `needsTypeCast(atom, type)`:
    metatype ∈ {Symbol, Grounded} AND NOT typeMatchesMetaOrAtom.
    Ref: metta.md line 259. -/
private def needsTypeCastRules : List PRule :=
  [ -- Symbol atom, type doesn't match
    { headRel := "needsTypeCast"
      headArgs := [.var "atom", .var "ty"]
      body := [ .relQuery "metaType" [.var "atom", .ctor "SymbolType" []]
              , .relQuery "typeNotMatchesMetaOrAtom" [.var "atom", .var "ty"] ]
      clauseName := some "needsTypeCast_symbol" }
  , -- Grounded atom, type doesn't match
    { headRel := "needsTypeCast"
      headArgs := [.var "atom", .var "ty"]
      body := [ .relQuery "metaType" [.var "atom", .ctor "GroundedType" []]
              , .relQuery "typeNotMatchesMetaOrAtom" [.var "atom", .var "ty"] ]
      clauseName := some "needsTypeCast_grounded" }
  , -- Unit expression ()
    { headRel := "needsTypeCast"
      headArgs := [.var "atom", .var "ty"]
      body := [ .eq (.var "atom") (.ctor "ExprNil" [])
              , .relQuery "typeNotMatchesMetaOrAtom" [.var "atom", .var "ty"] ]
      clauseName := some "needsTypeCast_unit" }
  ]

/-- `needsInterpExpr(atom, type)`:
    metatype == Expression AND NOT typeMatchesMetaOrAtom.
    Ref: metta.md lines 261-272. -/
private def needsInterpExprRules : List PRule :=
  [ { headRel := "needsInterpExpr"
      headArgs := [.var "atom", .var "ty"]
      body := [ .relQuery "metaType" [.var "atom", .ctor "ExpressionType" []]
              , .relQuery "typeNotMatchesMetaOrAtom" [.var "atom", .var "ty"] ]
      clauseName := some "needsInterpExpr_expression" } ]

/-! ## InterpExpr Dispatch Relations -/

/-- `notExpression(atom)`: atom is not an Expression. -/
private def notExpressionRules : List PRule :=
  [ { headRel := "notExpression"
      headArgs := [.var "atom"]
      body := [ .relQuery "metaType" [.var "atom", .var "mt"]
              , .neq (.var "mt") (.ctor "ExpressionType" []) ]
      clauseName := some "notExpression_check" } ]

/-! ## MettaCall Relations -/

/-- `isExecutable(op)`: op is an executable grounded atom.
    In HE, grounded atoms with execute capability are executable. -/
private def isExecutableRules : List PRule :=
  [ { headRel := "isExecutable"
      headArgs := [.var "op"]
      body := [.compute "checkExecutable" [.var "op"] "_"]
      clauseName := some "isExecutable_grounded" } ]

/-- `notExecutable(op)`: negation of isExecutable. -/
private def notExecutableRules : List PRule :=
  [ { headRel := "notExecutable"
      headArgs := [.var "op"]
      body := [.compute "checkNotExecutable" [.var "op"] "_"]
      clauseName := some "notExecutable_check" } ]

/-! ## Type System Relations -/

/-- `typeOf(space, atom, type)`: atom has type annotation in space.
    Looks for (: atom type) entries in the space's atom list. -/
private def typeOfRules : List PRule :=
  [ { headRel := "typeOf"
      headArgs := [.var "sp", .var "atom", .var "ty"]
      body := [ .deconstruct (.var "sp") "Space" ["atoms"]
              , .compute "findTypeAnnotation" [.var "atoms", .var "atom"] "ty" ]
      clauseName := some "typeOf_annotation" } ]

/-- `typeMismatch(space, atom, expectedType, actualType)`:
    atom has type actualType != expectedType in space.
    Used to produce BadType errors. -/
private def typeMismatchRules : List PRule :=
  [ { headRel := "typeMismatch"
      headArgs := [.var "sp", .var "atom", .var "expected", .var "actual"]
      body := [ .relQuery "typeOf" [.var "sp", .var "atom", .var "actual"]
              , .neq (.var "actual") (.var "expected") ]
      clauseName := some "typeMismatch_check" } ]

/-- `funcArgTypes(opType, argTypes)`:
    structural extractor for ArrowType argument lists. -/
private def funcArgTypesRules : List PRule :=
  [ { headRel := "funcArgTypes"
      headArgs := [.var "opType", .var "argTypes"]
      body := [ .deconstruct (.var "opType") "ArrowType" ["argTypes", "_ret"] ]
      clauseName := some "funcArgTypes_arrow" } ]

/-! ## Equation Query Relations -/

/-- `eqQueryResult(space, atom, rhs)`:
    Equation query: finds (= pattern rhs) in space where pattern matches atom.
    Returns the resolved rhs (with bindings applied).
    Ref: metta.md line 538. -/
private def eqQueryRawRules : List PRule :=
  [ { headRel := "eqQueryRaw"
      headArgs := [.var "sp", .var "atom", .var "rhs"]
      body := [ .computeMany "queryEquationsInSpace" [.var "sp", .var "atom"] "rhs" ]
      clauseName := some "eqQueryRaw_match" } ]

/-- `eqQueryResult(space, atom, rhs)`:
    projected equation query relation derived from `eqQueryRaw`. -/
private def eqQueryResultRules : List PRule :=
  [ { headRel := "eqQueryResult"
      headArgs := [.var "sp", .var "atom", .var "rhs"]
      body := [ .relQuery "eqQueryRaw" [.var "sp", .var "atom", .var "rhs"] ]
      clauseName := some "eqQueryResult_from_raw" } ]

/-- `eqQueryHas(space, atom)`: witness that an equation query has at least one rhs. -/
private def eqQueryHasRules : List PRule :=
  [ { headRel := "eqQueryHas"
      headArgs := [.var "sp", .var "atom"]
      body := [ .relQuery "eqQueryRaw" [.var "sp", .var "atom", .wild] ]
      clauseName := some "eqQueryHas_witness" } ]

/-- `noEqQuery(space, atom)`: no equations match in space. -/
private def noEqQueryRules : List PRule :=
  [ { headRel := "noEqQuery"
      headArgs := [.var "sp", .var "atom"]
      body := [ .notIn "eqQueryHas" [.var "sp", .var "atom"] ]
      clauseName := some "noEqQuery_notIn_has" } ]

/-! ## Complex Structural Relations (Builtins)

These builtins are structural queries over the current space/atom data.
Recursive evaluation is encoded in `HELanguageDef.lean` rewrite transitions. -/

/-- `applicableFuncType(space, atom, expectedType, opType, retType)`:
    A function type is applicable to this expression.
    Combines: getAtomTypes → filter funcTypes → checkIfFunctionTypeIsApplicable. -/
private def applicableFuncTypeRules : List PRule :=
  [ { headRel := "applicableFuncType"
      headArgs := [.var "sp", .var "atom", .var "ty", .var "opType", .var "retType"]
      body := [ .compute "findApplicableFuncType"
                  [.var "sp", .var "atom", .var "ty"] "opType_retType"
              , .deconstruct (.var "opType_retType") "ExprCons" ["opType", "retType"] ]
      clauseName := some "applicableFuncType_check" } ]

/-- `needsTupleInterp(space, atom, type)`:
    No applicable function type AND has non-function types.
    Ref: metta.md lines 350-355. -/
private def needsTupleInterpRules : List PRule :=
  [ { headRel := "needsTupleInterp"
      headArgs := [.var "sp", .var "atom", .var "ty"]
      body := [ .compute "hasNonFuncTypes" [.var "sp", .var "atom"] "ty"
              , .compute "noApplicableFuncType" [.var "sp", .var "atom"] "_" ]
      clauseName := some "needsTupleInterp_check" } ]

/-- `groundedCallResult(space, atom, result)`:
    Grounded dispatch result.
    Extracts op and args from expression, calls grounded dispatch. -/
private def groundedCallResultRules : List PRule :=
  [ { headRel := "groundedCallResult"
      headArgs := [.var "sp", .var "atom", .var "result"]
      body := [ .deconstruct (.var "atom") "ExprCons" ["op", "argsTail"]
              , .relQuery "isExecutable" [.var "op"]
              , .compute "evalGroundedDispatch" [.var "op", .var "argsTail"] "result" ]
      clauseName := some "groundedCallResult_dispatch" } ]

/-! ## Builtin Functions -/

private def heBuiltins : List BuiltinFn :=
  [ { name := "checkExecutable", arity := 1 }
  , { name := "checkNotExecutable", arity := 1 }
  , { name := "findTypeAnnotation", arity := 2 }
  , { name := "queryEquationsInSpace", arity := 2 }
  , { name := "findApplicableFuncType", arity := 3 }
  , { name := "hasNonFuncTypes", arity := 2 }
  , { name := "noApplicableFuncType", arity := 2 }
  , { name := "evalGroundedDispatch", arity := 2 }
  ]

private def heAscentHints : List BackendHint :=
  [ { builtinName := "checkExecutable", backend := "ascent"
      template := "is_executable_grounded({0})" }
  , { builtinName := "checkNotExecutable", backend := "ascent"
      template := "is_not_executable_grounded({0})" }
  , { builtinName := "findTypeAnnotation", backend := "ascent"
      template := "find_type_annotation({0}, {1})" }
  , { builtinName := "queryEquationsInSpace", backend := "ascent"
      template := "query_equations_in_space({0}, {1})" }
  , { builtinName := "findApplicableFuncType", backend := "ascent"
      template := "find_applicable_func_type({0}, {1}, {2})" }
  , { builtinName := "hasNonFuncTypes", backend := "ascent"
      template := "has_non_func_types({0}, {1})" }
  , { builtinName := "noApplicableFuncType", backend := "ascent"
      template := "no_applicable_func_type({0}, {1})" }
  , { builtinName := "evalGroundedDispatch", backend := "ascent"
      template := "eval_grounded_dispatch({0}.clone(), {1}.clone())" }
  ]

/-! ## Complete Premise Program -/

/-- The complete premise program for HE MeTTa.

This captures all premise-driven semantics needed by `mettaHE : LanguageDef`.
Backend renderers compile this to executable code (Ascent rules + Rust helpers). -/
def mettaHEPremises : PremiseProgram where
  relations :=
    [ { name := "isEmpty", paramTypes := ["Atom"] }
    , { name := "isError", paramTypes := ["Atom"] }
    , { name := "metaType", paramTypes := ["Atom", "Atom"] }
    , { name := "typeMatchesMetaOrAtom", paramTypes := ["Atom", "Atom"] }
    , { name := "typeNotMatchesMetaOrAtom", paramTypes := ["Atom", "Atom"] }
    , { name := "needsTypeCast", paramTypes := ["Atom", "Atom"] }
    , { name := "needsInterpExpr", paramTypes := ["Atom", "Atom"] }
    , { name := "notExpression", paramTypes := ["Atom"] }
    , { name := "isExecutable", paramTypes := ["Atom"] }
    , { name := "notExecutable", paramTypes := ["Atom"] }
    , { name := "typeOf", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "typeMismatch", paramTypes := ["Space", "Atom", "Atom", "Atom"] }
    , { name := "funcArgTypes", paramTypes := ["Atom", "Atom"] }
    , { name := "changedToEmpty", paramTypes := ["Atom", "Atom"] }
    , { name := "changedToError", paramTypes := ["Atom", "Atom"] }
    , { name := "eqQueryRaw", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "eqQueryResult", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "eqQueryHas", paramTypes := ["Space", "Atom"] }
    , { name := "noEqQuery", paramTypes := ["Space", "Atom"], hasNegation := true }
    , { name := "groundedCallResult", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "applicableFuncType", paramTypes := ["Space", "Atom", "Atom", "Atom", "Atom"]
        hasNegation := true }
    , { name := "needsTupleInterp", paramTypes := ["Space", "Atom", "Atom"] }
    ]
  rules :=
    isEmptyRules
    ++ isErrorRules
    ++ changedToEmptyRules
    ++ changedToErrorRules
    ++ metaTypeRules
    ++ typeMatchesMetaOrAtomRules
    ++ typeNotMatchesMetaOrAtomRules
    ++ needsTypeCastRules
    ++ needsInterpExprRules
    ++ notExpressionRules
    ++ isExecutableRules
    ++ notExecutableRules
    ++ typeOfRules
    ++ typeMismatchRules
    ++ funcArgTypesRules
    ++ eqQueryRawRules
    ++ eqQueryResultRules
    ++ eqQueryHasRules
    ++ noEqQueryRules
    ++ groundedCallResultRules
    ++ applicableFuncTypeRules
    ++ needsTupleInterpRules
  builtins := heBuiltins
  backendHints := heAscentHints
  coreGroundEvalRelation := none  -- HE does not use a fast-path evaluator
  stateConstructor := some "State"

/-! ## Smoke Checks -/

#eval do
  let prog := mettaHEPremises
  IO.println s!"HE Premises: {prog.relations.length} relations, {prog.rules.length} rules, {prog.builtins.length} builtins"

#eval do
  let wf := mettaHEPremises.wellFormed
  IO.println s!"mettaHEPremises well-formed: {wf}"

#eval do
  match mettaHEPremises.stratify with
  | some strata =>
      IO.println "mettaHEPremises stratification:"
      for (rel, stratum) in strata do
        IO.println s!"  stratum {stratum}: {rel}"
  | none =>
      IO.println "ERROR: mettaHEPremises is NOT stratifiable!"

end Mettapedia.Languages.MeTTa.HE.Premises
