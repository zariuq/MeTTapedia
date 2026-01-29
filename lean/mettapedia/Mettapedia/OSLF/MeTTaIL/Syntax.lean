import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic

/-!
# MeTTaIL Language Definition Syntax

Formalization of the MeTTaIL `language!` macro structure from
`/home/zar/claude/hyperon/mettail-rust/`.

This file defines the abstract syntax for MeTTaIL language definitions,
mirroring the Rust implementation's AST types in `macros/src/ast/`.

## Structure

The MeTTaIL `language!` macro accepts:
- `name`: Language identifier
- `types`: List of category names (Proc, Name, etc.)
- `terms`: Constructor definitions with syntax patterns
- `equations`: Bidirectional equality rules
- `rewrites`: Directional rewrite rules

## References

- `/home/zar/claude/hyperon/mettail-rust/macros/src/ast/`
- Williams & Stay, "Native Type Theory" (ACT 2021)
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Collection Types -/

/-- Collection types supported by MeTTaIL -/
inductive CollType where
  | vec      : CollType  -- Vec(T): ordered list
  | hashBag  : CollType  -- HashBag(T): multiset (with counts)
  | hashSet  : CollType  -- HashSet(T): set (no duplicates)
deriving DecidableEq, Repr

/-! ## Type Expressions -/

/-- Type expressions in MeTTaIL -/
inductive TypeExpr where
  | base : String → TypeExpr
  | arrow : TypeExpr → TypeExpr → TypeExpr
  | multiBinder : TypeExpr → TypeExpr
  | collection : CollType → TypeExpr → TypeExpr
deriving Repr

namespace TypeExpr

def baseType (name : String) : TypeExpr := .base name
def proc : TypeExpr := baseType "Proc"
def name : TypeExpr := baseType "Name"
def term : TypeExpr := baseType "Term"
def funType (dom cod : TypeExpr) : TypeExpr := .arrow dom cod
def bag (elem : TypeExpr) : TypeExpr := .collection .hashBag elem
def vec (elem : TypeExpr) : TypeExpr := .collection .vec elem
def set (elem : TypeExpr) : TypeExpr := .collection .hashSet elem

end TypeExpr

/-! ## Term Parameters -/

/-- Term parameters for constructor arguments -/
inductive TermParam where
  | simple : String → TypeExpr → TermParam
  | abstraction : String → String → TypeExpr → TermParam
  | multiAbstraction : String → String → TypeExpr → TermParam
deriving Repr

/-! ## Syntax Items -/

/-- Syntax items for grammar rules -/
inductive SyntaxItem where
  | terminal : String → SyntaxItem
  | nonTerminal : String → SyntaxItem
  | separator : String → SyntaxItem
  | delimiter : String → String → SyntaxItem
deriving Repr

/-! ## Grammar Rules (Constructors) -/

/-- A grammar rule defines a constructor -/
structure GrammarRule where
  label : String
  category : String
  params : List TermParam
  syntaxPattern : List SyntaxItem  -- renamed from 'syntax' to avoid keyword conflict
deriving Repr

/-! ## Patterns -/

/-- Pattern terms (non-recursive part) -/
inductive PatternTermBase where
  | var : String → PatternTermBase
deriving Repr

/-- Patterns with collection support -/
inductive Pattern where
  | var : String → Pattern
  | apply : String → List Pattern → Pattern
  | lambda : String → Pattern → Pattern
  | multiLambda : List String → Pattern → Pattern
  | subst : Pattern → String → Pattern → Pattern
  | collection : CollType → List Pattern → Option String → Pattern
deriving Repr

namespace Pattern

def mkVar (name : String) : Pattern := .var name

def mkApp (constructor : String) (args : List Pattern) : Pattern :=
  .apply constructor args

def mkBag (elements : List Pattern) (rest : Option String := none) : Pattern :=
  .collection .hashBag elements rest

end Pattern

/-! ## Custom Induction Principle for Pattern

Pattern is a nested inductive (contains `List Pattern`), so the standard
`induction` tactic doesn't work. We define a custom recursor that handles
both Pattern and List Pattern simultaneously.
-/

/-- Custom induction principle for Pattern that handles nested List Pattern.

    This is the key to proving properties about Pattern by structural induction.
    The standard recursor doesn't work because Pattern contains List Pattern.

    Usage:
    ```
    theorem my_theorem (p : Pattern) : P p := by
      apply Pattern.inductionOn p
      · -- var case
      · -- apply case (with IH for list)
      · -- lambda case
      · -- multiLambda case
      · -- subst case
      · -- collection case (with IH for list)
    ```
-/
def Pattern.inductionOn {motive : Pattern → Prop}
    (p : Pattern)
    (hvar : ∀ name, motive (.var name))
    (happly : ∀ constructor args, (∀ q ∈ args, motive q) → motive (.apply constructor args))
    (hlambda : ∀ x body, motive body → motive (.lambda x body))
    (hmultiLambda : ∀ xs body, motive body → motive (.multiLambda xs body))
    (hsubst : ∀ body x repl, motive body → motive repl → motive (.subst body x repl))
    (hcollection : ∀ ct elems rest, (∀ q ∈ elems, motive q) → motive (.collection ct elems rest))
    : motive p :=
  match p with
  | .var name => hvar name
  | .apply constructor args =>
    happly constructor args (fun q _hq => inductionOn q hvar happly hlambda hmultiLambda hsubst hcollection)
  | .lambda x body =>
    hlambda x body (inductionOn body hvar happly hlambda hmultiLambda hsubst hcollection)
  | .multiLambda xs body =>
    hmultiLambda xs body (inductionOn body hvar happly hlambda hmultiLambda hsubst hcollection)
  | .subst body x repl =>
    hsubst body x repl
      (inductionOn body hvar happly hlambda hmultiLambda hsubst hcollection)
      (inductionOn repl hvar happly hlambda hmultiLambda hsubst hcollection)
  | .collection ct elems rest =>
    hcollection ct elems rest (fun q _hq => inductionOn q hvar happly hlambda hmultiLambda hsubst hcollection)
termination_by sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have h := List.sizeOf_lt_of_mem _hq; omega)
    | omega

/-! ## Premises -/

/-- Freshness condition: x # P -/
structure FreshnessCondition where
  varName : String
  term : Pattern
deriving Repr

/-- Premises for rules -/
inductive Premise where
  | freshness : FreshnessCondition → Premise
  | congruence : Pattern → Pattern → Premise
  | relationQuery : String → List Pattern → Premise
deriving Repr

/-! ## Equations -/

/-- An equation defines bidirectional equality -/
structure Equation where
  name : String
  typeContext : List (String × TypeExpr)
  premises : List Premise
  left : Pattern
  right : Pattern
deriving Repr

/-! ## Rewrite Rules -/

/-- A rewrite rule defines a directional reduction -/
structure RewriteRule where
  name : String
  typeContext : List (String × TypeExpr)
  premises : List Premise
  left : Pattern
  right : Pattern
deriving Repr

/-! ## Complete Language Definition -/

/-- A complete MeTTaIL language definition -/
structure LanguageDef where
  name : String
  types : List String
  terms : List GrammarRule
  equations : List Equation
  rewrites : List RewriteRule
deriving Repr

namespace LanguageDef

def empty (name : String) : LanguageDef :=
  { name, types := [], terms := [], equations := [], rewrites := [] }

def addType (lang : LanguageDef) (ty : String) : LanguageDef :=
  { lang with types := lang.types ++ [ty] }

def addTerm (lang : LanguageDef) (rule : GrammarRule) : LanguageDef :=
  { lang with terms := lang.terms ++ [rule] }

def addEquation (lang : LanguageDef) (eq : Equation) : LanguageDef :=
  { lang with equations := lang.equations ++ [eq] }

def addRewrite (lang : LanguageDef) (rw : RewriteRule) : LanguageDef :=
  { lang with rewrites := lang.rewrites ++ [rw] }

end LanguageDef

/-! ## ρ-Calculus Example -/

/-- The ρ-calculus language definition -/
def rhoCalc : LanguageDef := {
  name := "RhoCalc",
  types := ["Proc", "Name"],
  terms := [
    -- PZero . |- "0" : Proc
    { label := "PZero", category := "Proc", params := [],
      syntaxPattern := [.terminal "0"] },

    -- PDrop . n:Name |- "*" "(" n ")" : Proc
    { label := "PDrop", category := "Proc",
      params := [.simple "n" TypeExpr.name],
      syntaxPattern := [.terminal "*", .terminal "(", .nonTerminal "n", .terminal ")"] },

    -- NQuote . p:Proc |- "@" "(" p ")" : Name
    { label := "NQuote", category := "Name",
      params := [.simple "p" TypeExpr.proc],
      syntaxPattern := [.terminal "@", .terminal "(", .nonTerminal "p", .terminal ")"] },

    -- PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc
    { label := "PPar", category := "Proc",
      params := [.simple "ps" (TypeExpr.bag TypeExpr.proc)],
      syntaxPattern := [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"] },

    -- POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc
    { label := "POutput", category := "Proc",
      params := [.simple "n" TypeExpr.name, .simple "q" TypeExpr.proc],
      syntaxPattern := [.nonTerminal "n", .terminal "!", .terminal "(", .nonTerminal "q", .terminal ")"] },

    -- PInput . n:Name, ^x.p:[Name -> Proc] |- n "?" x "." "{" p "}" : Proc
    { label := "PInput", category := "Proc",
      params := [.simple "n" TypeExpr.name,
                 .abstraction "x" "p" (TypeExpr.funType TypeExpr.name TypeExpr.proc)],
      syntaxPattern := [.nonTerminal "n", .terminal "?", .nonTerminal "x",
                        .terminal ".", .terminal "{", .nonTerminal "p", .terminal "}"] }
  ],
  equations := [
    -- (NQuote (PDrop N)) = N
    { name := "QuoteDrop",
      typeContext := [("N", TypeExpr.name)],
      premises := [],
      left := .apply "NQuote" [.apply "PDrop" [.var "N"]],
      right := .var "N" }
  ],
  rewrites := [
    -- Comm: { n!(q) | for(x<-n){p} | ...rest } ~> { p[@q/x] | ...rest }
    { name := "Comm",
      typeContext := [("n", TypeExpr.name), ("p", TypeExpr.proc), ("q", TypeExpr.proc)],
      premises := [],
      left := .collection .hashBag [
        .apply "PInput" [.var "n", .lambda "x" (.var "p")],
        .apply "POutput" [.var "n", .var "q"]
      ] (some "rest"),
      right := .collection .hashBag [
        .subst (.var "p") "x" (.apply "NQuote" [.var "q"])
      ] (some "rest") },

    -- ParCong: | S ~> T |- {S, ...rest} ~> {T, ...rest}
    { name := "ParCong",
      typeContext := [],
      premises := [.congruence (.var "S") (.var "T")],
      left := .collection .hashBag [.var "S"] (some "rest"),
      right := .collection .hashBag [.var "T"] (some "rest") }
  ]
}

/-! ## Summary

This file provides the abstract syntax for MeTTaIL language definitions,
matching the Rust implementation structure:

- `TypeExpr` ↔ `macros/src/ast/types.rs::TypeExpr`
- `TermParam` ↔ `macros/src/ast/grammar.rs::TermParam`
- `GrammarRule` ↔ `macros/src/ast/grammar.rs::GrammarRule`
- `Pattern` ↔ `macros/src/ast/pattern.rs::Pattern`
- `Equation` ↔ `macros/src/ast/language.rs::Equation`
- `RewriteRule` ↔ `macros/src/ast/language.rs::RewriteRule`
- `LanguageDef` ↔ `macros/src/ast/language.rs::LanguageDef`

**Next**: Connect this syntax to categorical semantics via interpretation
into a λ-theory (see `Semantics.lean`).
-/

end Mettapedia.OSLF.MeTTaIL.Syntax
