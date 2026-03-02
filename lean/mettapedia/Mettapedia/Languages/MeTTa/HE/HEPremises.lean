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
| needsTypeCast | 2 | metaType ∈ {Symbol, Grounded} and NOT typeMatchesMetaOrAtom |
| needsInterpExpr | 2 | metaType == Expression and NOT typeMatchesMetaOrAtom |
| atomTypes | 3 | Type annotations (: atom type) from space |
| isFuncType | 1 | Type is an arrow (-> ...) |
| applicableFuncType | 5 | Function type is applicable to expression with expected type |
| needsTupleInterp | 3 | No applicable func type + has non-func types |
| notExpression | 1 | Atom is not an Expression (metatype != Expression) |
| eqQueryResult | 3 | Equation query: (= pattern rhs) matched, rhs resolved |
| noEqQuery | 2 | No matching equations in space |
| groundedCallResult | 3 | Grounded dispatch → Ok result |
| isExecutable | 1 | Atom is an executable grounded atom |
| notExecutable | 1 | Negation of isExecutable |
| typeOf | 3 | Atom has type in space (via annotations) |
| typeMismatch | 4 | Atom's actual type != expected type |
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

/-- `needsTypeCast(atom, type)`:
    metatype ∈ {Symbol, Grounded} AND NOT typeMatchesMetaOrAtom.
    Ref: metta.md line 259. -/
private def needsTypeCastRules : List PRule :=
  [ -- Symbol atom, type doesn't match
    { headRel := "needsTypeCast"
      headArgs := [.var "atom", .var "ty"]
      body := [ .relQuery "metaType" [.var "atom", .ctor "SymbolType" []]
              , .notIn "typeMatchesMetaOrAtom" [.var "atom", .var "ty"]
              , .notIn "isEmpty" [.var "atom"]
              , .notIn "isError" [.var "atom"] ]
      clauseName := some "needsTypeCast_symbol" }
  , -- Grounded atom, type doesn't match
    { headRel := "needsTypeCast"
      headArgs := [.var "atom", .var "ty"]
      body := [ .relQuery "metaType" [.var "atom", .ctor "GroundedType" []]
              , .notIn "typeMatchesMetaOrAtom" [.var "atom", .var "ty"]
              , .notIn "isEmpty" [.var "atom"]
              , .notIn "isError" [.var "atom"] ]
      clauseName := some "needsTypeCast_grounded" }
  , -- Unit expression ()
    { headRel := "needsTypeCast"
      headArgs := [.var "atom", .var "ty"]
      body := [ .eq (.var "atom") (.ctor "ExprNil" [])
              , .notIn "typeMatchesMetaOrAtom" [.var "atom", .var "ty"]
              , .notIn "isEmpty" [.var "atom"]
              , .notIn "isError" [.var "atom"] ]
      clauseName := some "needsTypeCast_unit" }
  ]

/-- `needsInterpExpr(atom, type)`:
    metatype == Expression AND NOT typeMatchesMetaOrAtom AND NOT empty/error.
    Ref: metta.md lines 261-272. -/
private def needsInterpExprRules : List PRule :=
  [ { headRel := "needsInterpExpr"
      headArgs := [.var "atom", .var "ty"]
      body := [ .relQuery "metaType" [.var "atom", .ctor "ExpressionType" []]
              , .notIn "typeMatchesMetaOrAtom" [.var "atom", .var "ty"]
              , .notIn "isEmpty" [.var "atom"]
              , .notIn "isError" [.var "atom"] ]
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
      body := [.notIn "isExecutable" [.var "op"]]
      clauseName := some "notExecutable_neg" } ]

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

/-! ## Equation Query Relations -/

/-- `eqQueryResult(space, atom, rhs)`:
    Equation query: finds (= pattern rhs) in space where pattern matches atom.
    Returns the resolved rhs (with bindings applied).
    Ref: metta.md line 538. -/
private def eqQueryResultRules : List PRule :=
  [ { headRel := "eqQueryResult"
      headArgs := [.var "sp", .var "atom", .var "rhs"]
      body := [ .deconstruct (.var "sp") "Space" ["atoms"]
              , .computeMany "queryEquationsAll" [.var "atoms", .var "atom"] "rhs" ]
      clauseName := some "eqQueryResult_match" } ]

/-- `noEqQuery(space, atom)`: no equations match in space. -/
private def noEqQueryRules : List PRule :=
  [ { headRel := "noEqQuery"
      headArgs := [.var "sp", .var "atom"]
      body := [.notIn "eqQueryResult" [.var "sp", .var "atom", .wild]]
      clauseName := some "noEqQuery_neg" } ]

/-! ## Complex Multi-Step Relations (Builtins)

These relations encapsulate HE's multi-step evaluation sequences.
They are implemented as Rust builtins rather than pure datalog because
they involve recursive evaluation (the HE interpreter's mutual recursion). -/

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
      body := [ .notIn "applicableFuncType"
                  [.var "sp", .var "atom", .var "ty", .wild, .wild]
              , .compute "hasNonFuncTypes" [.var "sp", .var "atom"] "_" ]
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
  , { name := "findTypeAnnotation", arity := 2 }
  , { name := "queryEquationsAll", arity := 2 }
  , { name := "findApplicableFuncType", arity := 3 }
  , { name := "hasNonFuncTypes", arity := 2 }
  , { name := "evalGroundedDispatch", arity := 2 }
  ]

private def heAscentHints : List BackendHint :=
  [ { builtinName := "checkExecutable", backend := "ascent"
      template := "is_executable_grounded({0})" }
  , { builtinName := "findTypeAnnotation", backend := "ascent"
      template := "find_type_annotation({0}, {1})" }
  , { builtinName := "queryEquationsAll", backend := "ascent"
      template := "query_equations_all({0}, {1})" }
  , { builtinName := "findApplicableFuncType", backend := "ascent"
      template := "find_applicable_func_type({0}, {1}, {2})" }
  , { builtinName := "hasNonFuncTypes", backend := "ascent"
      template := "has_non_func_types({0}, {1})" }
  , { builtinName := "evalGroundedDispatch", backend := "ascent"
      template := "eval_grounded_dispatch({0}, {1})" }
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
    , { name := "needsTypeCast", paramTypes := ["Atom", "Atom"] }
    , { name := "needsInterpExpr", paramTypes := ["Atom", "Atom"] }
    , { name := "notExpression", paramTypes := ["Atom"] }
    , { name := "isExecutable", paramTypes := ["Atom"] }
    , { name := "notExecutable", paramTypes := ["Atom"] }
    , { name := "typeOf", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "typeMismatch", paramTypes := ["Space", "Atom", "Atom", "Atom"] }
    , { name := "eqQueryResult", paramTypes := ["Space", "Atom", "Atom"]
        hasNegation := true }
    , { name := "noEqQuery", paramTypes := ["Space", "Atom"] }
    , { name := "groundedCallResult", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "applicableFuncType", paramTypes := ["Space", "Atom", "Atom", "Atom", "Atom"]
        hasNegation := true }
    , { name := "needsTupleInterp", paramTypes := ["Space", "Atom", "Atom"] }
    ]
  rules :=
    isEmptyRules
    ++ isErrorRules
    ++ metaTypeRules
    ++ typeMatchesMetaOrAtomRules
    ++ needsTypeCastRules
    ++ needsInterpExprRules
    ++ notExpressionRules
    ++ isExecutableRules
    ++ notExecutableRules
    ++ typeOfRules
    ++ typeMismatchRules
    ++ eqQueryResultRules
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
