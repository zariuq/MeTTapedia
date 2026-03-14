import Mettapedia.OSLF.MeTTaIL.PremiseDatalog

/-!
# MeTTa Full Premises as PremiseProgram

Translates the 10 premise relations from `Premises.lean` (direct Lean functions)
into a `PremiseProgram` (inspectable datalog IR). This is the source-of-truth
for backend code generation.

## Relation Summary

| Relation | Arity | Description |
|----------|-------|-------------|
| eqnLookup | 3 | Equation lookup in Space |
| noEqnLookup | 2 | Negation of eqnLookup |
| neq | 2 | Structural inequality |
| typeOf | 3 | Type lookup in Space |
| notTypeOf | 3 | Negation of typeOf |
| cast | 4 | Type conversion + typable identity |
| notCast | 3 | Negation of cast |
| groundedCall | 3-4 | Grounded operation dispatch |
| noGroundedCall | 2-3 | Negation of groundedCall |
| nonBoolAtom | 1 | Not a boolean atom |

## LLM Primer
- `eqnLookup` traverses a cons-list (ACons/ANil) inside Space(eqs, tys).
  This is expressed as two recursive datalog rules + a helper `eqListContains`.
- `groundedCall` delegates to builtins (int_add, string_concat, etc.).
  The recursive evaluator (`coreGroundEvalRelation`) handles nested calls.
- Negation relations (noEqnLookup, notTypeOf, etc.) use `notIn` guards.
- `cast` has BOTH conversion logic (builtin) AND typable identity (typeOf).
-/

namespace Mettapedia.Languages.MeTTa.OSLFCore.FullPremises

open Mettapedia.OSLF.MeTTaIL.PremiseDatalog
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

/-! ## Helper Relations

These internal relations are used by the main premise relations but
are not directly referenced in rewrite rules. -/

/-- Rules for `eqListContains(eqList, src, dst)`:
    Traverses a cons-list of AEqEntry, finding all entries matching src. -/
private def eqListContainsRules : List PRule :=
  [ -- Base case: entry at head matches
    { headRel := "eqListContains"
      headArgs := [.var "list", .var "src", .var "dst"]
      body := [ .deconstruct (.var "list") "ACons" ["entry", "tail"]
              , .deconstruct (.var "entry") "AEqEntry" ["esrc", "edst"]
              , .eq (.var "esrc") (.var "src") ]
      clauseName := some "eqListContains_head" }
  , -- Recursive case: skip non-matching head, recurse on tail
    { headRel := "eqListContains"
      headArgs := [.var "list", .var "src", .var "dst"]
      body := [ .deconstruct (.var "list") "ACons" ["_", "tail"]
              , .relQuery "eqListContains" [.var "tail", .var "src", .var "dst"] ]
      clauseName := some "eqListContains_tail" } ]

/-- Rules for `typeListContains(tyList, atom, ty)`:
    Traverses a cons-list of ATypeEntry, checking for a matching (atom, ty) pair. -/
private def typeListContainsRules : List PRule :=
  [ -- Base case: entry at head matches
    { headRel := "typeListContains"
      headArgs := [.var "list", .var "atom", .var "ty"]
      body := [ .deconstruct (.var "list") "ACons" ["entry", "tail"]
              , .deconstruct (.var "entry") "ATypeEntry" ["a", "t"]
              , .eq (.var "a") (.var "atom")
              , .eq (.var "t") (.var "ty") ]
      clauseName := some "typeListContains_head" }
  , -- Recursive case
    { headRel := "typeListContains"
      headArgs := [.var "list", .var "atom", .var "ty"]
      body := [ .deconstruct (.var "list") "ACons" ["_", "tail"]
              , .relQuery "typeListContains" [.var "tail", .var "atom", .var "ty"] ]
      clauseName := some "typeListContains_tail" } ]

/-! ## Main Premise Relations -/

/-- Rules for `eqnLookup(space, src, dst)`:
    Extract eqs from Space and look up src in the equation list. -/
private def eqnLookupRules : List PRule :=
  [ { headRel := "eqnLookup"
      headArgs := [.var "sp", .var "src", .var "dst"]
      body := [ .deconstruct (.var "sp") "Space" ["eqs", "_tys"]
              , .relQuery "eqListContains" [.var "eqs", .var "src", .var "dst"] ]
      clauseName := some "eqnLookup_via_eqList" } ]

/-- Rules for `noEqnLookup(space, src)`:
    Negation — no equation maps src in this space. -/
private def noEqnLookupRules : List PRule :=
  [ { headRel := "noEqnLookup"
      headArgs := [.var "sp", .var "src"]
      body := [ .notIn "eqnLookup" [.var "sp", .var "src", .wild] ]
      clauseName := some "noEqnLookup_neg" } ]

/-- Rules for `neq(lhs, rhs)`:
    Structural inequality. -/
private def neqRules : List PRule :=
  [ { headRel := "neq"
      headArgs := [.var "lhs", .var "rhs"]
      body := [ .neq (.var "lhs") (.var "rhs") ]
      clauseName := some "neq_structural" } ]

/-- Rules for `typeOf(space, atom, ty)`:
    Extract tys from Space and check if (atom, ty) is in the type list. -/
private def typeOfRules : List PRule :=
  [ { headRel := "typeOf"
      headArgs := [.var "sp", .var "atom", .var "ty"]
      body := [ .deconstruct (.var "sp") "Space" ["_eqs", "tys"]
              , .relQuery "typeListContains" [.var "tys", .var "atom", .var "ty"] ]
      clauseName := some "typeOf_via_typeList" } ]

/-- Rules for `notTypeOf(space, atom, ty)`:
    Negation — atom does not have type ty in this space. -/
private def notTypeOfRules : List PRule :=
  [ { headRel := "notTypeOf"
      headArgs := [.var "sp", .var "atom", .var "ty"]
      body := [ .notIn "typeOf" [.var "sp", .var "atom", .var "ty"] ]
      clauseName := some "notTypeOf_neg" } ]

/-- Rules for `cast(space, atom, ty, out)`:
    Type conversion via builtin, falling back to typable identity. -/
private def castRules : List PRule :=
  [ -- Conversion via builtin
    { headRel := "cast"
      headArgs := [.var "sp", .var "atom", .var "ty", .var "out"]
      body := [ .compute "castConversion" [.var "atom", .var "ty"] "out" ]
      clauseName := some "cast_conversion" }
  , -- Typable identity fallback: if atom has the target type, output = atom
    { headRel := "cast"
      headArgs := [.var "sp", .var "atom", .var "ty", .var "atom"]
      body := [ .relQuery "typeOf" [.var "sp", .var "atom", .var "ty"] ]
      clauseName := some "cast_identity" } ]

/-- Rules for `notCast(space, atom, ty)`:
    Negation — no cast result exists. -/
private def notCastRules : List PRule :=
  [ { headRel := "notCast"
      headArgs := [.var "sp", .var "atom", .var "ty"]
      body := [ .notIn "cast" [.var "sp", .var "atom", .var "ty", .wild] ]
      clauseName := some "notCast_neg" } ]

/-- Rules for `groundedCall3(op, arg, out)`:
    Unary grounded operations (not, bool-to-sym, etc.). -/
private def groundedCall3Rules : List PRule :=
  [ { headRel := "groundedCall3"
      headArgs := [.var "op", .var "arg", .var "out"]
      body := [ .compute "groundedCall1" [.var "op", .var "arg"] "out" ]
      clauseName := some "groundedCall3_builtin" } ]

/-- Rules for `groundedCall4(op, lhs, rhs, out)`:
    Binary grounded operations (+, -, *, /, %, <, <=, >, >=, ==, concat, etc.). -/
private def groundedCall4Rules : List PRule :=
  [ { headRel := "groundedCall4"
      headArgs := [.var "op", .var "lhs", .var "rhs", .var "out"]
      body := [ .compute "groundedCall2" [.var "op", .var "lhs", .var "rhs"] "out" ]
      clauseName := some "groundedCall4_builtin" } ]

/-- Rules for `noGroundedCall3(op, arg)`:
    Negation — unary grounded call has no result. -/
private def noGroundedCall3Rules : List PRule :=
  [ { headRel := "noGroundedCall3"
      headArgs := [.var "op", .var "arg"]
      body := [ .notIn "groundedCall3" [.var "op", .var "arg", .wild] ]
      clauseName := some "noGroundedCall3_neg" } ]

/-- Rules for `noGroundedCall4(op, lhs, rhs)`:
    Negation — binary grounded call has no result. -/
private def noGroundedCall4Rules : List PRule :=
  [ { headRel := "noGroundedCall4"
      headArgs := [.var "op", .var "lhs", .var "rhs"]
      body := [ .notIn "groundedCall4" [.var "op", .var "lhs", .var "rhs", .wild] ]
      clauseName := some "noGroundedCall4_neg" } ]

/-- Rules for `nonBoolAtom(cond)`:
    Succeeds if cond is not GBoolTrue or GBoolFalse. -/
private def nonBoolAtomRules : List PRule :=
  [ { headRel := "nonBoolAtom"
      headArgs := [.var "cond"]
      body := [ .neq (.var "cond") (.literal (.apply "GBoolTrue" []))
              , .neq (.var "cond") (.literal (.apply "GBoolFalse" [])) ]
      clauseName := some "nonBoolAtom_check" } ]

/-! ## Builtin Functions -/

/-- Builtins required by the MeTTa premise program.

Note: These are the abstract function signatures. Backend-specific
implementation templates are in `backendHints`. -/
private def mettaBuiltins : List BuiltinFn :=
  [ { name := "castConversion", arity := 2 }    -- (atom, ty) → out
  , { name := "groundedCall1", arity := 2 }     -- (op, arg) → out
  , { name := "groundedCall2", arity := 3 }     -- (op, lhs, rhs) → out
  ]

/-- Ascent backend hints for MeTTa builtins. -/
private def mettaAscentHints : List BackendHint :=
  [ { builtinName := "castConversion", backend := "ascent"
      template := "cast_conversion_builtin({0}, {1})" }
  , { builtinName := "groundedCall1", backend := "ascent"
      template := "eval_ground_builtin_call_1({0}, {1})" }
  , { builtinName := "groundedCall2", backend := "ascent"
      template := "eval_ground_builtin_call_2({0}, {1}, {2})" }
  ]

/-! ## Complete Premise Program -/

/-- The complete premise program for MeTTaFull.

This is the IR source-of-truth for all premise-driven semantics.
Backend renderers (Ascent, MORK, ZAM) consume this to generate
executable code. -/
def mettaFullPremises : PremiseProgram where
  relations :=
    [ { name := "eqListContains", paramTypes := ["Atom", "Atom", "Atom"] }
    , { name := "typeListContains", paramTypes := ["Atom", "Atom", "Atom"] }
    , { name := "eqnLookup", paramTypes := ["Space", "Atom", "Atom"]
        hasNegation := true }
    , { name := "noEqnLookup", paramTypes := ["Space", "Atom"] }
    , { name := "neq", paramTypes := ["Atom", "Atom"] }
    , { name := "typeOf", paramTypes := ["Space", "Atom", "Atom"]
        hasNegation := true }
    , { name := "notTypeOf", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "cast", paramTypes := ["Space", "Atom", "Atom", "Atom"]
        hasNegation := true }
    , { name := "notCast", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "groundedCall3", paramTypes := ["Atom", "Atom", "Atom"]
        hasNegation := true }
    , { name := "groundedCall4", paramTypes := ["Atom", "Atom", "Atom", "Atom"]
        hasNegation := true }
    , { name := "noGroundedCall3", paramTypes := ["Atom", "Atom"] }
    , { name := "noGroundedCall4", paramTypes := ["Atom", "Atom", "Atom"] }
    , { name := "nonBoolAtom", paramTypes := ["Atom"] }
    ]
  rules :=
    eqListContainsRules
    ++ typeListContainsRules
    ++ eqnLookupRules
    ++ noEqnLookupRules
    ++ neqRules
    ++ typeOfRules
    ++ notTypeOfRules
    ++ castRules
    ++ notCastRules
    ++ groundedCall3Rules
    ++ groundedCall4Rules
    ++ noGroundedCall3Rules
    ++ noGroundedCall4Rules
    ++ nonBoolAtomRules
  builtins := mettaBuiltins
  backendHints := mettaAscentHints
  coreGroundEvalRelation := some "coreGroundEvalLookup"
  stateConstructor := some "State"

/-! ## Well-formedness and Stratification Checks -/

#eval do
  let wf := mettaFullPremises.wellFormed
  IO.println s!"mettaFullPremises well-formed: {wf}"

#eval do
  match mettaFullPremises.stratify with
  | some strata =>
      IO.println "mettaFullPremises stratification:"
      for (rel, stratum) in strata do
        IO.println s!"  stratum {stratum}: {rel}"
  | none =>
      IO.println "ERROR: mettaFullPremises is NOT stratifiable!"

#eval do
  IO.println s!"mettaFullPremises relation count: {mettaFullPremises.relations.length}"
  IO.println s!"mettaFullPremises rule count: {mettaFullPremises.rules.length}"
  IO.println s!"mettaFullPremises builtin count: {mettaFullPremises.builtins.length}"

end Mettapedia.Languages.MeTTa.OSLFCore.FullPremises
