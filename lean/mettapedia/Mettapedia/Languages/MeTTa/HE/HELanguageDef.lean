import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# HE MeTTa Language Definition (OSLF LanguageDef)

Defines the Hyperon Experimental MeTTa interpreter as a `LanguageDef` state machine.
This is the source-of-truth for generating Rust/Ascent backends via `ExportBackend`.

## Design Mapping

HE's 6 mutually recursive interpreter functions become *instructions*.
Each case branch in the HE interpreter becomes a *rewrite rule*.
Non-determinism (HE's `ResultSet`) is handled by multiple Ascent tuples.

```
HE Function          → Instruction         → When used
────────────────────────────────────────────────────────
metta                → Metta(atom, type)    → entry point
interpretExpression  → InterpExpr(atom, type) → metta when Expression
interpretFunction    → InterpFunc(atom, opType, retType) → interpExpr + funcType
interpretArgs        → InterpArgs(head, tail, types) → interpFunc arg eval
interpretTuple       → InterpTuple(atom)    → interpExpr + no funcType
mettaCall            → MettaCall(atom, type) → after interp* completes
typeCast             → TypeCast(atom, type) → metta when Symbol/Grounded
```

## Error Atoms

Unlike MeTTaFull (which returns AFalse on type mismatch), HE constructs explicit
`(Error source (BadArgType pos expected actual))` atoms as first-class values.

## Relation to HE Formalization

This LanguageDef is *derived from* the HE interpreter in `Interpreter.lean`.
Conformance is established by showing that the state machine's reachable
states correspond to the interpreter's `ResultSet` outputs.

## References

- HE/Interpreter.lean — source formalization (37 conformance theorems)
- HE/Types.lean — ErrorCode, Bindings, ResultSet
- metta.md lines 240-552 — HE interpreter spec
-/

namespace Mettapedia.Languages.MeTTa.HE.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Shared Type Abbreviations -/

private def atom : TypeExpr := .base "Atom"
private def space : TypeExpr := .base "Space"
private def instr : TypeExpr := .base "Instr"

private def simple (n : String) (t : TypeExpr := atom) : TermParam := .simple n t

/-! ## HE MeTTa LanguageDef

### Types
- **State**: The evaluation state `⟨instr | space | out⟩`
- **Instr**: Instructions corresponding to HE's evaluation functions
- **Atom**: Atoms including error atoms
- **Space**: Atomspace (list of atoms)

### Instruction Set (one per HE evaluation function + helpers)

| Instruction | HE Function | Parameters |
|------------|-------------|------------|
| Metta | metta | atom, type |
| InterpExpr | interpretExpression | atom, type |
| InterpFunc | interpretFunction | atom, opType, retType |
| InterpArgs | interpretArgs | head, rest, types |
| InterpTuple | interpretTuple | atom |
| MettaCall | mettaCall | atom, type |
| TypeCast | typeCast | atom, type |
| Return | (result delivery) | result |
| Done | (terminal) | — |

### Error Atom Constructors

| Constructor | Shape | Example |
|------------|-------|---------|
| ErrorAtom | (Error source code) | (Error (+ 1 "a") (BadArgType 1 Int String)) |
| BadArgType | (BadArgType pos expected actual) | |
| BadType | (BadType expected actual) | |
-/

def mettaHE : LanguageDef := {
  name := "MeTTaHE",
  types := ["State", "Instr", "Atom", "Space"],
  terms := [
    -- #### State
    { label := "State", category := "State",
      params := [simple "instr" instr, simple "space" space, simple "out"],
      syntaxPattern := [.terminal "⟨", .nonTerminal "instr", .terminal "|",
                        .nonTerminal "space", .terminal "|", .nonTerminal "out",
                        .terminal "⟩"] },

    -- #### Instructions (HE evaluation function entry points)

    -- metta(atom, type): top-level entry point
    -- Ref: metta.md lines 240-272
    { label := "Metta", category := "Instr",
      params := [simple "atom", simple "ty"],
      syntaxPattern := [.terminal "metta", .terminal "(", .nonTerminal "atom",
                        .terminal ",", .nonTerminal "ty", .terminal ")"] },

    -- interpretExpression(atom, type): interpret expression
    -- Ref: metta.md lines 316-356
    { label := "InterpExpr", category := "Instr",
      params := [simple "atom", simple "ty"],
      syntaxPattern := [.terminal "interp-expr", .terminal "(", .nonTerminal "atom",
                        .terminal ",", .nonTerminal "ty", .terminal ")"] },

    -- interpretFunction(atom, opType, retType): interpret function call
    -- Ref: metta.md lines 452-478
    { label := "InterpFunc", category := "Instr",
      params := [simple "atom", simple "opType", simple "retType"],
      syntaxPattern := [.terminal "interp-func", .terminal "(", .nonTerminal "atom",
                        .terminal ",", .nonTerminal "opType", .terminal ",",
                        .nonTerminal "retType", .terminal ")"] },

    -- interpretArgs(head, rest, types): interpret arguments one by one
    -- Ref: metta.md lines 480-507
    -- `head` = currently evaluating argument
    -- `rest` = remaining arguments (cons-list)
    -- `types` = remaining expected types (cons-list)
    { label := "InterpArgs", category := "Instr",
      params := [simple "head", simple "rest", simple "types"],
      syntaxPattern := [.terminal "interp-args", .terminal "(", .nonTerminal "head",
                        .terminal ",", .nonTerminal "rest", .terminal ",",
                        .nonTerminal "types", .terminal ")"] },

    -- interpretTuple(atom): interpret tuple/expression elements
    -- Ref: metta.md lines 358-382
    { label := "InterpTuple", category := "Instr",
      params := [simple "atom"],
      syntaxPattern := [.terminal "interp-tuple", .terminal "(", .nonTerminal "atom",
                        .terminal ")"] },

    -- mettaCall(atom, type): call MeTTa expression
    -- Ref: metta.md lines 509-552
    { label := "MettaCall", category := "Instr",
      params := [simple "atom", simple "ty"],
      syntaxPattern := [.terminal "metta-call", .terminal "(", .nonTerminal "atom",
                        .terminal ",", .nonTerminal "ty", .terminal ")"] },

    -- typeCast(atom, type): type cast
    -- Ref: metta.md lines 274-314
    { label := "TypeCast", category := "Instr",
      params := [simple "atom", simple "ty"],
      syntaxPattern := [.terminal "type-cast", .terminal "(", .nonTerminal "atom",
                        .terminal ",", .nonTerminal "ty", .terminal ")"] },

    -- Return(result): deliver a computed result
    { label := "Return", category := "Instr",
      params := [simple "result"],
      syntaxPattern := [.terminal "return", .terminal "(", .nonTerminal "result",
                        .terminal ")"] },

    -- Done: terminal state
    { label := "Done", category := "Instr",
      params := [],
      syntaxPattern := [.terminal "done"] },

    -- #### Atom Constructors

    -- Sentinel atoms
    { label := "Empty", category := "Atom", params := [],
      syntaxPattern := [.terminal "Empty"] },

    -- Error atom: (Error source code)
    { label := "ErrorAtom", category := "Atom",
      params := [simple "source", simple "code"],
      syntaxPattern := [.terminal "Error", .terminal "(", .nonTerminal "source",
                        .terminal ",", .nonTerminal "code", .terminal ")"] },

    -- Error codes
    { label := "BadArgType", category := "Atom",
      params := [simple "argpos", simple "expected", simple "actual"],
      syntaxPattern := [.terminal "BadArgType", .terminal "(", .nonTerminal "argpos",
                        .terminal ",", .nonTerminal "expected", .terminal ",",
                        .nonTerminal "actual", .terminal ")"] },

    { label := "BadType", category := "Atom",
      params := [simple "expected", simple "actual"],
      syntaxPattern := [.terminal "BadType", .terminal "(", .nonTerminal "expected",
                        .terminal ",", .nonTerminal "actual", .terminal ")"] },

    { label := "StackOverflow", category := "Atom", params := [],
      syntaxPattern := [.terminal "StackOverflow"] },

    { label := "NoReturn", category := "Atom", params := [],
      syntaxPattern := [.terminal "NoReturn"] },

    { label := "IncorrectNumberOfArguments", category := "Atom", params := [],
      syntaxPattern := [.terminal "IncorrectNumberOfArguments"] },

    -- Boolean atoms
    { label := "True", category := "Atom", params := [],
      syntaxPattern := [.terminal "True"] },
    { label := "False", category := "Atom", params := [],
      syntaxPattern := [.terminal "False"] },

    -- Metatype atoms (used as return values of getMetaType)
    { label := "SymbolType", category := "Atom", params := [],
      syntaxPattern := [.terminal "Symbol"] },
    { label := "VariableType", category := "Atom", params := [],
      syntaxPattern := [.terminal "Variable"] },
    { label := "ExpressionType", category := "Atom", params := [],
      syntaxPattern := [.terminal "Expression"] },
    { label := "GroundedType", category := "Atom", params := [],
      syntaxPattern := [.terminal "Grounded"] },

    -- Type atoms
    { label := "AtomType", category := "Atom", params := [],
      syntaxPattern := [.terminal "Atom"] },
    { label := "UndefinedType", category := "Atom", params := [],
      syntaxPattern := [.terminal "%Undefined%"] },

    -- Arrow type constructor: (-> argTypes... retType)
    { label := "ArrowType", category := "Atom",
      params := [simple "args", simple "ret"],
      syntaxPattern := [.terminal "->", .terminal "(", .nonTerminal "args",
                        .terminal ",", .nonTerminal "ret", .terminal ")"] },

    -- Grounded values (integers, strings, booleans)
    { label := "GInt", category := "Atom",
      params := [simple "intTok"],
      syntaxPattern := [.terminal "gint", .terminal "(", .nonTerminal "intTok",
                        .terminal ")"] },
    { label := "GString", category := "Atom",
      params := [simple "strTok"],
      syntaxPattern := [.terminal "gstring", .terminal "(", .nonTerminal "strTok",
                        .terminal ")"] },
    { label := "GBool", category := "Atom",
      params := [simple "boolTok"],
      syntaxPattern := [.terminal "gbool", .terminal "(", .nonTerminal "boolTok",
                        .terminal ")"] },

    -- Symbol atom (user-defined name)
    { label := "SymAtom", category := "Atom",
      params := [simple "name"],
      syntaxPattern := [.terminal "sym", .terminal "(", .nonTerminal "name",
                        .terminal ")"] },

    -- Variable atom
    { label := "VarAtom", category := "Atom",
      params := [simple "name"],
      syntaxPattern := [.terminal "var", .terminal "(", .nonTerminal "name",
                        .terminal ")"] },

    -- Expression atom (cons-list of sub-atoms)
    -- Expressions use cons-list encoding for variable-arity
    { label := "ExprCons", category := "Atom",
      params := [simple "head", simple "tail"],
      syntaxPattern := [.terminal "expr-cons", .terminal "(", .nonTerminal "head",
                        .terminal ",", .nonTerminal "tail", .terminal ")"] },
    { label := "ExprNil", category := "Atom", params := [],
      syntaxPattern := [.terminal "expr-nil"] },

    -- Continuation frames encoded in State.out
    { label := "KAfterOp", category := "Atom",
      params := [simple "argsTail", simple "opType", simple "retType", simple "kont"],
      syntaxPattern := [.terminal "k-after-op", .terminal "(",
                        .nonTerminal "argsTail", .terminal ",",
                        .nonTerminal "opType", .terminal ",",
                        .nonTerminal "retType", .terminal ",",
                        .nonTerminal "kont", .terminal ")"] },
    { label := "KAfterArgs", category := "Atom",
      params := [simple "head", simple "retType", simple "kont"],
      syntaxPattern := [.terminal "k-after-args", .terminal "(",
                        .nonTerminal "head", .terminal ",",
                        .nonTerminal "retType", .terminal ",",
                        .nonTerminal "kont", .terminal ")"] },
    { label := "KTupleTail", category := "Atom",
      params := [simple "tail", simple "kont"],
      syntaxPattern := [.terminal "k-tuple-tail", .terminal "(",
                        .nonTerminal "tail", .terminal ",",
                        .nonTerminal "kont", .terminal ")"] },
    { label := "KTupleCons", category := "Atom",
      params := [simple "head", simple "kont"],
      syntaxPattern := [.terminal "k-tuple-cons", .terminal "(",
                        .nonTerminal "head", .terminal ",",
                        .nonTerminal "kont", .terminal ")"] },
    { label := "KArgTail", category := "Atom",
      params := [simple "origHead", simple "rest", simple "types", simple "kont"],
      syntaxPattern := [.terminal "k-arg-tail", .terminal "(",
                        .nonTerminal "origHead", .terminal ",",
                        .nonTerminal "rest", .terminal ",",
                        .nonTerminal "types", .terminal ",",
                        .nonTerminal "kont", .terminal ")"] },
    { label := "KArgCons", category := "Atom",
      params := [simple "head", simple "kont"],
      syntaxPattern := [.terminal "k-arg-cons", .terminal "(",
                        .nonTerminal "head", .terminal ",",
                        .nonTerminal "kont", .terminal ")"] },

    -- Builtin operation symbols
    { label := "OpAdd", category := "Atom", params := [],
      syntaxPattern := [.terminal "+"] },
    { label := "OpSub", category := "Atom", params := [],
      syntaxPattern := [.terminal "-"] },
    { label := "OpMul", category := "Atom", params := [],
      syntaxPattern := [.terminal "*"] },
    { label := "OpDiv", category := "Atom", params := [],
      syntaxPattern := [.terminal "/"] },
    { label := "OpMod", category := "Atom", params := [],
      syntaxPattern := [.terminal "%"] },
    { label := "OpLt", category := "Atom", params := [],
      syntaxPattern := [.terminal "<"] },
    { label := "OpGt", category := "Atom", params := [],
      syntaxPattern := [.terminal ">"] },
    { label := "OpEq", category := "Atom", params := [],
      syntaxPattern := [.terminal "=="] },

    -- Equation entry in space: (= left right)
    { label := "EqAtom", category := "Atom",
      params := [simple "left", simple "right"],
      syntaxPattern := [.terminal "=", .terminal "(", .nonTerminal "left",
                        .terminal ",", .nonTerminal "right", .terminal ")"] },

    -- Type annotation in space: (: atom type)
    { label := "TypeAnnotation", category := "Atom",
      params := [simple "atom", simple "ty"],
      syntaxPattern := [.terminal ":", .terminal "(", .nonTerminal "atom",
                        .terminal ",", .nonTerminal "ty", .terminal ")"] },

    -- #### Space

    -- Space is a list of atoms (equations, type annotations, etc.)
    { label := "Space", category := "Space",
      params := [simple "atoms"],
      syntaxPattern := [.terminal "space", .terminal "(", .nonTerminal "atoms",
                        .terminal ")"] }
  ],

  equations := [],

  -- ### Rewrite Rules
  -- Each rule corresponds to a case/branch in HE's interpreter functions.
  -- Premise relations defined in HEPremises.lean.

  rewrites := [
    -- #### M: metta rules (metta.md lines 240-272)

    -- M1: Empty atom → return unchanged
    -- if $atom == Empty: return [($atom, $bindings)]
    { name := "M_Empty",
      typeContext := [("atom", atom), ("ty", atom), ("space", .base "Space"),
                      ("out", atom)],
      premises := [.relationQuery "isEmpty" [.fvar "atom"]],
      left  := .apply "State" [.apply "Metta" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "atom"],
                                .fvar "space", .fvar "out"] },

    -- M2: Error atom → return unchanged
    { name := "M_Error",
      typeContext := [("atom", atom), ("ty", atom), ("space", .base "Space"),
                      ("out", atom)],
      premises := [.relationQuery "isError" [.fvar "atom"]],
      left  := .apply "State" [.apply "Metta" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "atom"],
                                .fvar "space", .fvar "out"] },

    -- M3: type == Atom or type == metatype or metatype == Variable → return unchanged
    { name := "M_TypeMatch",
      typeContext := [("atom", atom), ("ty", atom), ("space", .base "Space"),
                      ("out", atom)],
      premises := [.relationQuery "typeMatchesMetaOrAtom" [.fvar "atom", .fvar "ty"]],
      left  := .apply "State" [.apply "Metta" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "atom"],
                                .fvar "space", .fvar "out"] },

    -- M4: Symbol or Grounded → typeCast
    -- if metaType(atom) ∈ {Symbol, Grounded} or atom == ()
    { name := "M_SymbolOrGrounded",
      typeContext := [("atom", atom), ("ty", atom), ("space", .base "Space"),
                      ("out", atom)],
      premises := [.relationQuery "needsTypeCast" [.fvar "atom", .fvar "ty"]],
      left  := .apply "State" [.apply "Metta" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "TypeCast" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"] },

    -- M5: Expression → interpretExpression
    { name := "M_Expression",
      typeContext := [("atom", atom), ("ty", atom), ("space", .base "Space"),
                      ("out", atom)],
      premises := [.relationQuery "needsInterpExpr" [.fvar "atom", .fvar "ty"]],
      left  := .apply "State" [.apply "Metta" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "InterpExpr" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"] },

    -- #### IE: interpretExpression rules (metta.md lines 316-356)

    -- IE1: Expression with applicable function type → interpretFunction → mettaCall
    -- For each function type that passes checkIfFunctionTypeIsApplicable
    { name := "IE_FuncType",
      typeContext := [("atom", atom), ("ty", atom), ("opType", atom),
                      ("retType", atom), ("space", .base "Space"), ("out", atom)],
      premises := [.relationQuery "applicableFuncType"
                     [.fvar "space", .fvar "atom", .fvar "ty",
                      .fvar "opType", .fvar "retType"]],
      left  := .apply "State" [.apply "InterpExpr" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "InterpFunc" [.fvar "atom", .fvar "opType",
                                                     .fvar "retType"],
                                .fvar "space", .fvar "out"] },

    -- IE2: No applicable function type + has non-function types → interpretTuple → mettaCall
    { name := "IE_TupleType",
      typeContext := [("atom", atom), ("ty", atom),
                      ("space", .base "Space"), ("out", atom)],
      premises := [.relationQuery "needsTupleInterp"
                     [.fvar "space", .fvar "atom", .fvar "ty"]],
      left  := .apply "State" [.apply "InterpExpr" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "InterpTuple" [.fvar "atom"],
                                .fvar "space", .fvar "out"] },

    -- IE3: Not an expression → return unchanged
    { name := "IE_NotExpr",
      typeContext := [("atom", atom), ("ty", atom),
                      ("space", .base "Space"), ("out", atom)],
      premises := [.relationQuery "notExpression" [.fvar "atom"]],
      left  := .apply "State" [.apply "InterpExpr" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "atom"],
                                .fvar "space", .fvar "out"] },

    -- #### IF: interpretFunction rules (metta.md lines 452-478)
    -- Explicit call/return frames encoded in State.out.

    -- IF1: Evaluate operator of (op args...)
    { name := "IF_Start",
      typeContext := [("op", atom), ("argsTail", atom), ("opType", atom),
                      ("retType", atom), ("space", .base "Space"), ("out", atom)],
      premises := [],
      left  := .apply "State"
                  [.apply "InterpFunc"
                    [.apply "ExprCons" [.fvar "op", .fvar "argsTail"],
                     .fvar "opType", .fvar "retType"],
                   .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Metta" [.fvar "op", .fvar "opType"],
                                .fvar "space",
                                .apply "KAfterOp"
                                  [.fvar "argsTail", .fvar "opType", .fvar "retType",
                                   .fvar "out"]] },

    -- IF2: Empty expression as function call → return unchanged
    { name := "IF_Nil",
      typeContext := [("opType", atom), ("retType", atom),
                      ("space", .base "Space"), ("out", atom)],
      premises := [],
      left  := .apply "State" [.apply "InterpFunc"
                                  [.apply "ExprNil" [], .fvar "opType", .fvar "retType"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.apply "ExprNil" []],
                                .fvar "space", .fvar "out"] },

    -- IF3: Non-expression function input → return unchanged
    { name := "IF_NotExpr",
      typeContext := [("atom", atom), ("opType", atom), ("retType", atom),
                      ("space", .base "Space"), ("out", atom)],
      premises := [.relationQuery "notExpression" [.fvar "atom"]],
      left  := .apply "State" [.apply "InterpFunc" [.fvar "atom", .fvar "opType",
                                                     .fvar "retType"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "atom"],
                                .fvar "space", .fvar "out"] },

    -- IF4/5: Operator reduced to Empty/Error → short-circuit
    { name := "IF_AfterOp_Empty",
      typeContext := [("h", atom), ("argsTail", atom), ("opType", atom), ("retType", atom),
                      ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "isEmpty" [.fvar "h"]],
      left  := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space",
                                .apply "KAfterOp" [.fvar "argsTail", .fvar "opType",
                                                    .fvar "retType", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space", .fvar "k"] },
    { name := "IF_AfterOp_Error",
      typeContext := [("h", atom), ("argsTail", atom), ("opType", atom), ("retType", atom),
                      ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "isError" [.fvar "h"]],
      left  := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space",
                                .apply "KAfterOp" [.fvar "argsTail", .fvar "opType",
                                                    .fvar "retType", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space", .fvar "k"] },

    -- IF6: No args (op only) → call mettaCall directly.
    { name := "IF_AfterOp_NoArgs",
      typeContext := [("h", atom), ("mt", atom), ("opType", atom), ("retType", atom),
                      ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "metaType" [.fvar "h", .fvar "mt"]],
      left  := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space",
                                .apply "KAfterOp"
                                  [.apply "ExprNil" [], .fvar "opType", .fvar "retType",
                                   .fvar "k"]],
      right := .apply "State"
                  [.apply "MettaCall"
                    [.apply "ExprCons" [.fvar "h", .apply "ExprNil" []], .fvar "retType"],
                   .fvar "space", .fvar "k"] },

    -- IF7: Operator reduced to a regular atom → evaluate args one by one with types.
    { name := "IF_AfterOp_EvalArgs",
      typeContext := [("h", atom), ("mt", atom), ("argHead", atom), ("argRest", atom),
                      ("opType", atom), ("argTypes", atom), ("retType", atom),
                      ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "metaType" [.fvar "h", .fvar "mt"],
                   .relationQuery "funcArgTypes" [.fvar "opType", .fvar "argTypes"]],
      left  := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space",
                                .apply "KAfterOp"
                                  [.apply "ExprCons" [.fvar "argHead", .fvar "argRest"],
                                   .fvar "opType", .fvar "retType", .fvar "k"]],
      right := .apply "State" [.apply "InterpArgs" [.fvar "argHead", .fvar "argRest",
                                                     .fvar "argTypes"],
                                .fvar "space",
                                .apply "KAfterArgs" [.fvar "h", .fvar "retType", .fvar "k"]] },

    -- IF8/9: Arg tuple reduced to Empty/Error → short-circuit
    { name := "IF_AfterArgs_Empty",
      typeContext := [("h", atom), ("retType", atom), ("argsEval", atom),
                      ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "isEmpty" [.fvar "argsEval"]],
      left  := .apply "State" [.apply "Return" [.fvar "argsEval"],
                                .fvar "space",
                                .apply "KAfterArgs" [.fvar "h", .fvar "retType", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.fvar "argsEval"],
                                .fvar "space", .fvar "k"] },
    { name := "IF_AfterArgs_Error",
      typeContext := [("h", atom), ("retType", atom), ("argsEval", atom),
                      ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "isError" [.fvar "argsEval"]],
      left  := .apply "State" [.apply "Return" [.fvar "argsEval"],
                                .fvar "space",
                                .apply "KAfterArgs" [.fvar "h", .fvar "retType", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.fvar "argsEval"],
                                .fvar "space", .fvar "k"] },

    -- IF10: Rebuild and call mettaCall on (h argsEval)
    { name := "IF_AfterArgs_Call",
      typeContext := [("h", atom), ("retType", atom), ("argsEval", atom),
                      ("mt", atom), ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "metaType" [.fvar "argsEval", .fvar "mt"]],
      left  := .apply "State" [.apply "Return" [.fvar "argsEval"],
                                .fvar "space",
                                .apply "KAfterArgs" [.fvar "h", .fvar "retType", .fvar "k"]],
      right := .apply "State"
                  [.apply "MettaCall" [.apply "ExprCons" [.fvar "h", .fvar "argsEval"],
                                       .fvar "retType"],
                   .fvar "space", .fvar "k"] },

    -- #### IA: interpretArgs rules (metta.md lines 480-507)
    -- Typed per-argument evaluation, one argument at a time.

    -- IA1: Next arg has declared type.
    { name := "IA_Start_Typed",
      typeContext := [("head", atom), ("rest", atom), ("ty", atom), ("typeRest", atom),
                      ("space", .base "Space"), ("out", atom)],
      premises := [],
      left  := .apply "State"
                  [.apply "InterpArgs"
                    [.fvar "head", .fvar "rest",
                     .apply "ExprCons" [.fvar "ty", .fvar "typeRest"]],
                   .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Metta" [.fvar "head", .fvar "ty"],
                                .fvar "space",
                                .apply "KArgTail"
                                  [.fvar "head", .fvar "rest", .fvar "typeRest", .fvar "out"]] },

    -- IA2: No declared type left; use UndefinedType.
    { name := "IA_Start_Undef",
      typeContext := [("head", atom), ("rest", atom),
                      ("space", .base "Space"), ("out", atom)],
      premises := [],
      left  := .apply "State" [.apply "InterpArgs"
                                  [.fvar "head", .fvar "rest", .apply "ExprNil" []],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Metta" [.fvar "head", .apply "UndefinedType" []],
                                .fvar "space",
                                .apply "KArgTail"
                                  [.fvar "head", .fvar "rest", .apply "ExprNil" [], .fvar "out"]] },

    -- IA3/4: Short-circuit on Empty/Error.
    { name := "IA_Head_Empty",
      typeContext := [("h", atom), ("origHead", atom), ("rest", atom), ("types", atom),
                      ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "changedToEmpty" [.fvar "origHead", .fvar "h"]],
      left  := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space",
                                .apply "KArgTail"
                                  [.fvar "origHead", .fvar "rest", .fvar "types", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.fvar "h"], .fvar "space", .fvar "k"] },
    { name := "IA_Head_Error",
      typeContext := [("h", atom), ("origHead", atom), ("rest", atom), ("types", atom),
                      ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "changedToError" [.fvar "origHead", .fvar "h"]],
      left  := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space",
                                .apply "KArgTail"
                                  [.fvar "origHead", .fvar "rest", .fvar "types", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.fvar "h"], .fvar "space", .fvar "k"] },

    -- IA5: Tail exhausted; wrap singleton list [h].
    { name := "IA_Head_RestNil",
      typeContext := [("h", atom), ("mt", atom), ("origHead", atom), ("types", atom),
                      ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "metaType" [.fvar "h", .fvar "mt"]],
      left  := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space",
                                .apply "KArgTail"
                                  [.fvar "origHead", .apply "ExprNil" [], .fvar "types", .fvar "k"]],
      right := .apply "State"
                  [.apply "Return" [.apply "ExprCons" [.fvar "h", .apply "ExprNil" []]],
                   .fvar "space", .fvar "k"] },

    -- IA6: Evaluate remaining tail args recursively.
    { name := "IA_Head_Recurse",
      typeContext := [("h", atom), ("mt", atom), ("origHead", atom),
                      ("nextArg", atom), ("nextRest", atom), ("types", atom),
                      ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "metaType" [.fvar "h", .fvar "mt"]],
      left  := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space",
                                .apply "KArgTail"
                                  [.fvar "origHead",
                                   .apply "ExprCons" [.fvar "nextArg", .fvar "nextRest"],
                                   .fvar "types", .fvar "k"]],
      right := .apply "State" [.apply "InterpArgs" [.fvar "nextArg", .fvar "nextRest",
                                                     .fvar "types"],
                                .fvar "space",
                                .apply "KArgCons" [.fvar "h", .fvar "k"]] },

    -- IA7/8: Tail reduction short-circuit.
    { name := "IA_Tail_Empty",
      typeContext := [("h", atom), ("t", atom), ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "isEmpty" [.fvar "t"]],
      left  := .apply "State" [.apply "Return" [.fvar "t"],
                                .fvar "space",
                                .apply "KArgCons" [.fvar "h", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.fvar "t"], .fvar "space", .fvar "k"] },
    { name := "IA_Tail_Error",
      typeContext := [("h", atom), ("t", atom), ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "isError" [.fvar "t"]],
      left  := .apply "State" [.apply "Return" [.fvar "t"],
                                .fvar "space",
                                .apply "KArgCons" [.fvar "h", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.fvar "t"], .fvar "space", .fvar "k"] },

    -- IA9: Rebuild argument list with evaluated head and tail.
    { name := "IA_Tail_Cons",
      typeContext := [("h", atom), ("t", atom), ("mt", atom),
                      ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "metaType" [.fvar "t", .fvar "mt"]],
      left  := .apply "State" [.apply "Return" [.fvar "t"],
                                .fvar "space",
                                .apply "KArgCons" [.fvar "h", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.apply "ExprCons" [.fvar "h", .fvar "t"]],
                                .fvar "space", .fvar "k"] },

    -- #### IT: interpretTuple rules (metta.md lines 358-382)
    -- Recursive element evaluation via continuation frames.

    -- IT1: Empty tuple/list
    { name := "IT_Nil",
      typeContext := [("space", .base "Space"), ("out", atom)],
      premises := [],
      left  := .apply "State" [.apply "InterpTuple" [.apply "ExprNil" []],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.apply "ExprNil" []],
                                .fvar "space", .fvar "out"] },

    -- IT2: Evaluate tuple head under UndefinedType
    { name := "IT_StartCons",
      typeContext := [("head", atom), ("tail", atom),
                      ("space", .base "Space"), ("out", atom)],
      premises := [],
      left  := .apply "State" [.apply "InterpTuple"
                                  [.apply "ExprCons" [.fvar "head", .fvar "tail"]],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Metta" [.fvar "head", .apply "UndefinedType" []],
                                .fvar "space",
                                .apply "KTupleTail" [.fvar "tail", .fvar "out"]] },

    -- IT3/4: Head reduced to Empty/Error → short-circuit
    { name := "IT_Head_Empty",
      typeContext := [("h", atom), ("tail", atom), ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "isEmpty" [.fvar "h"]],
      left  := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space",
                                .apply "KTupleTail" [.fvar "tail", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space", .fvar "k"] },
    { name := "IT_Head_Error",
      typeContext := [("h", atom), ("tail", atom), ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "isError" [.fvar "h"]],
      left  := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space",
                                .apply "KTupleTail" [.fvar "tail", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space", .fvar "k"] },

    -- IT5: Tail empty → return singleton tuple [h]
    { name := "IT_Head_TailNil",
      typeContext := [("h", atom), ("mt", atom), ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "metaType" [.fvar "h", .fvar "mt"]],
      left  := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space",
                                .apply "KTupleTail" [.apply "ExprNil" [], .fvar "k"]],
      right := .apply "State"
                  [.apply "Return" [.apply "ExprCons" [.fvar "h", .apply "ExprNil" []]],
                   .fvar "space", .fvar "k"] },

    -- IT6: Recurse on non-empty tail
    { name := "IT_Head_Recurse",
      typeContext := [("h", atom), ("mt", atom), ("tHead", atom), ("tTail", atom),
                      ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "metaType" [.fvar "h", .fvar "mt"]],
      left  := .apply "State" [.apply "Return" [.fvar "h"],
                                .fvar "space",
                                .apply "KTupleTail"
                                  [.apply "ExprCons" [.fvar "tHead", .fvar "tTail"],
                                   .fvar "k"]],
      right := .apply "State"
                  [.apply "InterpTuple" [.apply "ExprCons" [.fvar "tHead", .fvar "tTail"]],
                   .fvar "space",
                   .apply "KTupleCons" [.fvar "h", .fvar "k"]] },

    -- IT7/8: Tail reduced to Empty/Error → short-circuit
    { name := "IT_Tail_Empty",
      typeContext := [("h", atom), ("t", atom), ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "isEmpty" [.fvar "t"]],
      left  := .apply "State" [.apply "Return" [.fvar "t"],
                                .fvar "space",
                                .apply "KTupleCons" [.fvar "h", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.fvar "t"],
                                .fvar "space", .fvar "k"] },
    { name := "IT_Tail_Error",
      typeContext := [("h", atom), ("t", atom), ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "isError" [.fvar "t"]],
      left  := .apply "State" [.apply "Return" [.fvar "t"],
                                .fvar "space",
                                .apply "KTupleCons" [.fvar "h", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.fvar "t"],
                                .fvar "space", .fvar "k"] },

    -- IT9: Rebuild tuple from evaluated head and tail
    { name := "IT_Tail_Cons",
      typeContext := [("h", atom), ("t", atom), ("mt", atom),
                      ("k", atom), ("space", .base "Space")],
      premises := [.relationQuery "metaType" [.fvar "t", .fvar "mt"]],
      left  := .apply "State" [.apply "Return" [.fvar "t"],
                                .fvar "space",
                                .apply "KTupleCons" [.fvar "h", .fvar "k"]],
      right := .apply "State" [.apply "Return" [.apply "ExprCons" [.fvar "h", .fvar "t"]],
                                .fvar "space", .fvar "k"] },

    -- #### MC: mettaCall rules (metta.md lines 509-552)

    -- MC1: Error passthrough
    { name := "MC_Error",
      typeContext := [("atom", atom), ("ty", atom),
                      ("space", .base "Space"), ("out", atom)],
      premises := [.relationQuery "isError" [.fvar "atom"]],
      left  := .apply "State" [.apply "MettaCall" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "atom"],
                                .fvar "space", .fvar "out"] },

    -- MC2: Grounded dispatch → execute → metta each result
    { name := "MC_Grounded",
      typeContext := [("atom", atom), ("ty", atom), ("result", atom),
                      ("space", .base "Space"), ("out", atom)],
      premises := [.relationQuery "groundedCallResult"
                     [.fvar "space", .fvar "atom", .fvar "result"]],
      left  := .apply "State" [.apply "MettaCall" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Metta" [.fvar "result", .fvar "ty"],
                                .fvar "space", .fvar "out"] },

    -- MC3: Non-grounded → equation query → metta each resolved result
    { name := "MC_Equation",
      typeContext := [("atom", atom), ("ty", atom), ("rhs", atom),
                      ("space", .base "Space"), ("out", atom)],
      premises := [.relationQuery "eqQueryResult"
                     [.fvar "space", .fvar "atom", .fvar "rhs"],
                   .relationQuery "notExecutable" [.fvar "atom"]],
      left  := .apply "State" [.apply "MettaCall" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Metta" [.fvar "rhs", .fvar "ty"],
                                .fvar "space", .fvar "out"] },

    -- MC4: Non-grounded, no equations → return unchanged
    { name := "MC_NoMatch",
      typeContext := [("atom", atom), ("ty", atom),
                      ("space", .base "Space"), ("out", atom)],
      premises := [.relationQuery "noEqQuery" [.fvar "space", .fvar "atom"],
                   .relationQuery "notExecutable" [.fvar "atom"]],
      left  := .apply "State" [.apply "MettaCall" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "atom"],
                                .fvar "space", .fvar "out"] },

    -- #### TC: typeCast rules (metta.md lines 274-314)

    -- TC1: Type matches → return unchanged
    { name := "TC_Match",
      typeContext := [("atom", atom), ("ty", atom),
                      ("space", .base "Space"), ("out", atom)],
      premises := [.relationQuery "typeOf" [.fvar "space", .fvar "atom", .fvar "ty"]],
      left  := .apply "State" [.apply "TypeCast" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return" [.fvar "atom"],
                                .fvar "space", .fvar "out"] },

    -- TC2: Type mismatch → Error(atom, BadType(expected, actual))
    { name := "TC_Mismatch",
      typeContext := [("atom", atom), ("ty", atom), ("actual", atom),
                      ("space", .base "Space"), ("out", atom)],
      premises := [.relationQuery "typeMismatch"
                     [.fvar "space", .fvar "atom", .fvar "ty", .fvar "actual"]],
      left  := .apply "State" [.apply "TypeCast" [.fvar "atom", .fvar "ty"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Return"
                  [.apply "ErrorAtom" [.fvar "atom",
                    .apply "BadType" [.fvar "ty", .fvar "actual"]]],
                                .fvar "space",
                                .fvar "out"] },

    -- #### R: Return/Done rules

    -- R1: Return delivers result to Done when continuation stack is empty
    { name := "R_Done",
      typeContext := [("result", atom), ("space", .base "Space"), ("out", atom)],
      premises := [.relationQuery "isEmpty" [.fvar "out"]],
      left  := .apply "State" [.apply "Return" [.fvar "result"],
                                .fvar "space", .fvar "out"],
      right := .apply "State" [.apply "Done" [],
                                .fvar "space", .fvar "result"] }
  ]
}

/-! ## Smoke Checks -/

-- Verify basic structure
#eval do
  let lang := mettaHE
  IO.println s!"Language: {lang.name}"
  IO.println s!"Types: {lang.types.length}"
  IO.println s!"Terms: {lang.terms.length}"
  IO.println s!"Rewrites: {lang.rewrites.length}"
  IO.println s!"Equations: {lang.equations.length}"
  let instrLabels := lang.terms.filter (fun (r : GrammarRule) => r.category == "Instr")
    |>.map (fun (r : GrammarRule) => r.label)
  IO.println s!"Instructions: {instrLabels}"
  let atomCount := lang.terms.filter (fun (r : GrammarRule) => r.category == "Atom") |>.length
  IO.println s!"Atom constructors: {atomCount}"

end Mettapedia.Languages.MeTTa.HE.LanguageDef
