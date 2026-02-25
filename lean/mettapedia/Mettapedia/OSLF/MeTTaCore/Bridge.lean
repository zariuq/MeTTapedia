import Mettapedia.OSLF.MeTTaCore.RewriteRules
import Mettapedia.OSLF.MeTTaCore.Types
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# MeTTaCore ↔ MeTTaIL Bridge

Integration between MeTTaCore (interpreter specification) and MeTTaIL
(process calculus meta-language). This bridge enables:

1. Converting MeTTaIL language definitions to MeTTaCore atomspaces
2. Converting MeTTaIL patterns to MeTTaCore atoms
3. Proving that MeTTaCore evaluation respects MeTTaIL semantics

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│  MeTTaIL: Language definitions (ρ-calculus, π-calculus, etc.)  │
│    - Pattern syntax                                             │
│    - Equations (bidirectional)                                  │
│    - Rewrite rules (directional)                                │
├─────────────────────────────────────────────────────────────────┤
│                    ↓ patternToAtom ↓                            │
│                    ↓ equationToAtom ↓                           │
├─────────────────────────────────────────────────────────────────┤
│  MeTTaCore: Interpreter specification                           │
│    - Atoms (symbol, var, grounded, expression)                  │
│    - Atomspace (knowledge base)                                 │
│    - Evaluation (rewrite rules)                                 │
└─────────────────────────────────────────────────────────────────┘
```

## References

* Meta-MeTTa paper: "MeTTa evaluates LanguageDefs"
* MeTTaIL Rust implementation
-/

namespace Mettapedia.OSLF.MeTTaCore.Bridge

open MeTTaIL.Syntax

/-! ## Pattern to Atom Conversion -/

/-- Convert a collection type to its symbol representation -/
def collTypeToSymbol : CollType → String
  | .vec => "Vec"
  | .hashBag => "Bag"
  | .hashSet => "Set"

/-- Convert a MeTTaIL Pattern to a MeTTaCore Atom.

    This is the core bridge function. The mapping is:
    - Pattern.var v → Atom.var v
    - Pattern.apply c args → Atom.expression (symbol c :: args.map patternToAtom)
    - Pattern.lambda x body → Atom.expression [symbol "λ", var x, patternToAtom body]
    - Pattern.collection ct elems rest → Atom.expression (collType :: elems ++ [rest])
    - Pattern.subst body x repl → (patternToAtom body)[x := patternToAtom repl]
-/
def patternToAtom : Pattern → Atom
  | .var name => .var name
  | .apply constructor args =>
      .expression (.symbol constructor :: args.map patternToAtom)
  | .lambda x body =>
      .expression [.symbol "λ", .var x, patternToAtom body]
  | .multiLambda xs body =>
      let vars := xs.map Atom.var
      .expression (.symbol "λ*" :: vars ++ [patternToAtom body])
  | .subst body x repl =>
      -- Represent substitution as an expression
      -- In evaluation, this would be computed
      .expression [.symbol "subst", patternToAtom body, .var x, patternToAtom repl]
  | .collection ct elems rest =>
      let elemAtoms := elems.map patternToAtom
      let restAtom := rest.map (fun r => [.var r]) |>.getD []
      .expression (.symbol (collTypeToSymbol ct) :: elemAtoms ++ restAtom)

/-- Convert a MeTTaCore Atom back to a MeTTaIL Pattern (if possible).
    This is a partial inverse of patternToAtom. -/
def atomToPattern : Atom → Option Pattern
  | .var name => some (.var name)
  | .symbol s => some (.apply s [])  -- Treat symbols as nullary constructors
  | .expression (.symbol constructor :: args) =>
      if constructor == "λ" then
        match args with
        | [.var x, body] => atomToPattern body |>.map (.lambda x ·)
        | _ => none
      else if constructor == "subst" then
        match args with
        | [body, .var x, repl] => do
            let body' ← atomToPattern body
            let repl' ← atomToPattern repl
            return .subst body' x repl'
        | _ => none
      else
        let patArgs := args.filterMap atomToPattern
        if patArgs.length == args.length then
          some (.apply constructor patArgs)
        else
          none
  | _ => none

/-! ## Equation to Atom Conversion -/

/-- Convert a MeTTaIL Equation to a MeTTaCore equality atom: `(= lhs rhs)` -/
def equationToAtom (eq : Equation) : Atom :=
  Atom.equality (patternToAtom eq.left) (patternToAtom eq.right)

/-- Convert a list of equations to atoms -/
def equationsToAtoms (eqs : List Equation) : List Atom :=
  eqs.map equationToAtom

/-! ## Type Expression to Atom Conversion -/

/-- Convert a MeTTaIL TypeExpr to a MeTTaCore type atom -/
def typeExprToAtom : TypeExpr → Atom
  | .base name => .symbol name
  | .arrow dom cod =>
      functionType [typeExprToAtom dom] (typeExprToAtom cod)
  | .multiBinder inner =>
      .expression [.symbol "Multi", typeExprToAtom inner]
  | .collection ct inner =>
      .expression [.symbol (collTypeToSymbol ct), typeExprToAtom inner]

/-! ## Language Definition to Atomspace -/

/-- Create an atomspace from a list of equations.
    This is the core bridge: MeTTaIL equations become MeTTaCore knowledge. -/
def equationsToAtomspace (eqs : List Equation) : Atomspace :=
  Atomspace.ofList (equationsToAtoms eqs)

/-- Add type declarations from grammar rules to atomspace -/
def addGrammarTypes (space : Atomspace) (rules : List GrammarRule) : Atomspace :=
  rules.foldl (fun acc rule =>
    -- Add type annotation for the constructor
    let constructorType := .symbol rule.category
    let constructorAtom := .symbol rule.label
    acc.addType constructorAtom constructorType
  ) space

/-! ## Evaluation Bridge -/

/-- Evaluate a MeTTaIL pattern in a MeTTaCore atomspace.
    This bridges the gap between MeTTaIL reduction and MeTTaCore evaluation. -/
def evaluatePattern (eqs : List Equation) (pat : Pattern) (fuel : Nat) : Multiset Atom :=
  let space := equationsToAtomspace eqs
  let atom := patternToAtom pat
  evaluate fuel space atom

/-! ## Soundness Properties -/

/-- Pattern conversion preserves variable names (concrete example) -/
theorem patternToAtom_var_example :
    patternToAtom (.var "x") = .var "x" := by decide

/-- Pattern conversion preserves constructor applications (concrete example) -/
theorem patternToAtom_apply_example :
    patternToAtom (.apply "Nil" []) = .expression [.symbol "Nil"] := by decide

/-- Pattern conversion preserves lambda abstractions (concrete example) -/
theorem patternToAtom_lambda_example :
    patternToAtom (.lambda "x" (.var "x")) =
    .expression [.symbol "λ", .var "x", .var "x"] := by decide

/-- Equation conversion creates proper equality atoms -/
theorem equationToAtom_structure (eq : Equation) :
    ∃ lhs rhs, equationToAtom eq = .expression [.symbol "=", lhs, rhs] :=
  ⟨patternToAtom eq.left, patternToAtom eq.right, rfl⟩

/-- Round-trip check for variable patterns.
    Note: We use Option.isSome since Pattern doesn't have DecidableEq -/
theorem roundtrip_var_succeeds :
    (atomToPattern (patternToAtom (.var "x"))).isSome = true := by decide

/-- Round-trip check for nullary applications -/
theorem roundtrip_apply_nullary_succeeds :
    (atomToPattern (patternToAtom (.apply "Nil" []))).isSome = true := by decide

/-! ## Example: ρ-calculus Bridge -/

/-- Example: The COMM rule from ρ-calculus as an equation.
    { n!(q) | for(x <- n){p} } ~> { p[@q/x] }

    In MeTTaIL:
    - LHS: PPar [POutput (NQuote q) n, PInput (PVar x) n p]
    - RHS: p[q/x]  (substitution)
-/
def exampleCommLhs : Pattern :=
  .apply "PPar" [
    .apply "POutput" [.apply "NQuote" [.var "q"], .var "n"],
    .apply "PInput" [.var "x", .var "n", .var "p"]
  ]

def exampleCommRhs : Pattern :=
  .subst (.var "p") "x" (.apply "NQuote" [.var "q"])

def exampleCommEquation : Equation := {
  name := "COMM"
  typeContext := [("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc")]
  premises := []
  left := exampleCommLhs
  right := exampleCommRhs
}

/-- The COMM equation as a MeTTaCore atom -/
example : equationToAtom exampleCommEquation =
    .expression [
      .symbol "=",
      .expression [
        .symbol "PPar",
        .expression [.symbol "POutput", .expression [.symbol "NQuote", .var "q"], .var "n"],
        .expression [.symbol "PInput", .var "x", .var "n", .var "p"]
      ],
      .expression [.symbol "subst", .var "p", .var "x", .expression [.symbol "NQuote", .var "q"]]
    ] := by decide

/-! ## Unit Tests -/

section Tests

-- Pattern conversion
example : patternToAtom (.var "x") = .var "x" := by decide
example : patternToAtom (.apply "Nil" []) = .expression [.symbol "Nil"] := by decide
example : patternToAtom (.apply "Cons" [.var "h", .var "t"]) =
          .expression [.symbol "Cons", .var "h", .var "t"] := by decide

-- Lambda conversion
example : patternToAtom (.lambda "x" (.var "x")) =
          .expression [.symbol "λ", .var "x", .var "x"] := by decide

-- Collection conversion
example : patternToAtom (.collection .hashBag [.var "a", .var "b"] none) =
          .expression [.symbol "Bag", .var "a", .var "b"] := by decide

-- Type expression conversion
example : typeExprToAtom (.base "Proc") = .symbol "Proc" := rfl
example : typeExprToAtom (.arrow (.base "Name") (.base "Proc")) =
          .expression [.symbol "->", .symbol "Name", .symbol "Proc"] := rfl

end Tests

end Mettapedia.OSLF.MeTTaCore.Bridge
