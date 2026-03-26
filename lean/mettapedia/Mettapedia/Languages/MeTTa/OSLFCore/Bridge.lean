import Mettapedia.Languages.MeTTa.OSLFCore.RewriteRules
import Mettapedia.Languages.MeTTa.OSLFCore.Types
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

namespace Mettapedia.Languages.MeTTa.OSLFCore.Bridge

open Mettapedia.OSLF.MeTTaIL.Syntax

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
  | .bvar n => .var ("#b" ++ toString n)
  | .fvar name => .var name
  | .apply constructor args =>
      .expression (.symbol constructor :: args.map patternToAtom)
  | .lambda _nm body =>
      .expression [.symbol "λ", patternToAtom body]
  | .multiLambda n _nms body =>
      .expression [.symbol "λ*", .symbol (toString n), patternToAtom body]
  | .subst body repl =>
      .expression [.symbol "subst", patternToAtom body, patternToAtom repl]
  | .collection ct elems rest =>
      let elemAtoms := elems.map patternToAtom
      let restAtom := rest.map (fun r => [.var r]) |>.getD []
      .expression (.symbol (collTypeToSymbol ct) :: elemAtoms ++ restAtom)

/-- Convert a MeTTaCore Atom back to a MeTTaIL Pattern (if possible).
    This is a partial inverse of patternToAtom. -/
def atomToPattern : Atom → Option Pattern
  | .var name => some (.fvar name)
  | .symbol s => some (.apply s [])  -- Treat symbols as nullary constructors
  | .expression (.symbol constructor :: args) =>
      if constructor == "λ" then
        match args with
        | [body] => atomToPattern body |>.map (.lambda none)
        | _ => none
      else if constructor == "subst" then
        match args with
        | [body, repl] => do
            let body' ← atomToPattern body
            let repl' ← atomToPattern repl
            return .subst body' repl'
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
    patternToAtom (.fvar "x") = .var "x" := by simp [patternToAtom]

/-- Pattern conversion preserves constructor applications (concrete example) -/
theorem patternToAtom_apply_example :
    patternToAtom (.apply "Nil" []) = .expression [.symbol "Nil"] := by
  simp [patternToAtom]

/-- Pattern conversion preserves lambda abstractions (concrete example) -/
theorem patternToAtom_lambda_example :
    patternToAtom (.lambda none (.bvar 0)) =
    .expression [.symbol "λ", .var ("#b" ++ toString 0)] := by
  simp [patternToAtom]

/-- Equation conversion creates proper equality atoms -/
theorem equationToAtom_structure (eq : Equation) :
    ∃ lhs rhs, equationToAtom eq = .expression [.symbol "=", lhs, rhs] :=
  ⟨patternToAtom eq.left, patternToAtom eq.right, rfl⟩

/-- Round-trip check for variable patterns. -/
theorem roundtrip_var_succeeds :
    (atomToPattern (patternToAtom (.fvar "x"))).isSome = true := by
  simp [patternToAtom, atomToPattern]

/-- Round-trip check for nullary applications -/
theorem roundtrip_apply_nullary_succeeds :
    (atomToPattern (patternToAtom (.apply "Nil" []))).isSome = true := by
  simp [patternToAtom, atomToPattern]

/-! ## Example: ρ-calculus Bridge -/

/-- Example: The COMM rule from ρ-calculus as an equation.
    { n!(q) | for(x <- n){p} } ~> { p[@q/x] }

    In MeTTaIL:
    - LHS: PPar [POutput (NQuote q) n, PInput (PVar x) n p]
    - RHS: p[q/x]  (substitution)
-/
def exampleCommLhs : Pattern :=
  .apply "PPar" [
    .apply "POutput" [.apply "NQuote" [.fvar "q"], .fvar "n"],
    .apply "PInput" [.fvar "x", .fvar "n", .fvar "p"]
  ]

def exampleCommRhs : Pattern :=
  .subst (.fvar "p") (.apply "NQuote" [.fvar "q"])

def exampleCommEquation : Equation := {
  name := "COMM"
  typeContext := [("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc")]
  premises := []
  left := exampleCommLhs
  right := exampleCommRhs
}

/-- The COMM equation as a MeTTaCore atom -/
example : equationToAtom exampleCommEquation =
    Atom.expression [
      .symbol "=",
      .expression [
        .symbol "PPar",
        .expression [.symbol "POutput", .expression [.symbol "NQuote", Atom.var "q"], Atom.var "n"],
        .expression [.symbol "PInput", Atom.var "x", Atom.var "n", Atom.var "p"]
      ],
      .expression [.symbol "subst", Atom.var "p", .expression [.symbol "NQuote", Atom.var "q"]]
    ] := by simp [equationToAtom, Atom.equality, exampleCommEquation, exampleCommLhs, exampleCommRhs, patternToAtom]

/-! ## Unit Tests -/

section Tests

-- Pattern conversion
example : patternToAtom (.fvar "x") = .var "x" := by simp [patternToAtom]
example : patternToAtom (.apply "Nil" []) = .expression [.symbol "Nil"] := by
  simp [patternToAtom]
example : patternToAtom (.apply "Cons" [.fvar "h", .fvar "t"]) =
          .expression [.symbol "Cons", .var "h", .var "t"] := by
  simp [patternToAtom]

-- Lambda conversion (locally nameless: one arg)
example : patternToAtom (.lambda none (.bvar 0)) =
          .expression [.symbol "λ", .var ("#b" ++ toString 0)] := by
  simp [patternToAtom]

-- Collection conversion
example : patternToAtom (.collection .hashBag [.fvar "a", .fvar "b"] none) =
          .expression [.symbol "Bag", .var "a", .var "b"] := by
  simp [patternToAtom, collTypeToSymbol]

-- Type expression conversion
example : typeExprToAtom (.base "Proc") = .symbol "Proc" := rfl
example : typeExprToAtom (.arrow (.base "Name") (.base "Proc")) =
          .expression [.symbol "->", .symbol "Name", .symbol "Proc"] := rfl

end Tests

end Mettapedia.Languages.MeTTa.OSLFCore.Bridge
