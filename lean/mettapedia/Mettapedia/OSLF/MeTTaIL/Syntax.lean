import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic

/-!
# MeTTaIL Language Definition Syntax (Locally Nameless)

Formalization of the MeTTaIL `language!` macro structure from
`/home/zar/claude/hyperon/mettail-rust/`.

Uses **locally nameless** representation: bound variables are de Bruijn indices
(`.bvar n`), free variables / metavariables are named (`.fvar x`). Binders
carry no names — α-equivalent patterns are syntactically identical.

## References

- `/home/zar/claude/hyperon/mettail-rust/macros/src/ast/`
- Williams & Stay, "Native Type Theory" (ACT 2021)
- Meredith & Stay, "Operational Semantics in Logical Form"
- Aydemir et al., "Engineering Formal Metatheory" (POPL 2008)
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

/-- Term parameters for constructor arguments.
    In locally nameless, abstraction/multiAbstraction carry only the
    body variable name (for metavar matching) and type — the binder name
    is implicit via de Bruijn indices. -/
inductive TermParam where
  | simple : String → TypeExpr → TermParam
  | abstraction : String → TypeExpr → TermParam
  | multiAbstraction : String → TypeExpr → TermParam
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
  syntaxPattern : List SyntaxItem
deriving Repr

/-! ## Patterns (Locally Nameless) -/

/-- Patterns using locally nameless representation.
    - `.bvar n`: bound variable (de Bruijn index `n`, counting from innermost binder)
    - `.fvar x`: free variable / metavariable (named)
    - `.lambda body`: binder — no name needed, BVar 0 = the bound variable
    - `.subst body repl`: substitute `repl` for BVar 0 in `body`
    α-equivalent patterns are definitionally equal. -/
inductive Pattern where
  | bvar : Nat → Pattern
  | fvar : String → Pattern
  | apply : String → List Pattern → Pattern
  | lambda : Pattern → Pattern
  | multiLambda : Nat → Pattern → Pattern
  | subst : Pattern → Pattern → Pattern
  | collection : CollType → List Pattern → Option String → Pattern
deriving Repr

/-! ## DecidableEq for Pattern

Pattern is a nested inductive (contains `List Pattern`), so `deriving DecidableEq`
fails. We define it manually via mutual recursion on Pattern and List Pattern.
-/

mutual
  private def decEqPattern : (a b : Pattern) → Decidable (a = b)
    | .bvar n₁, .bvar n₂ =>
      if h : n₁ = n₂ then isTrue (by subst h; rfl)
      else isFalse (by intro h'; cases h'; exact h rfl)
    | .fvar x₁, .fvar x₂ =>
      if h : x₁ = x₂ then isTrue (by subst h; rfl)
      else isFalse (by intro h'; cases h'; exact h rfl)
    | .apply c₁ args₁, .apply c₂ args₂ =>
      if hc : c₁ = c₂ then
        match decEqPatternList args₁ args₂ with
        | isTrue ha => isTrue (by subst hc; subst ha; rfl)
        | isFalse ha => isFalse (by intro h; cases h; exact ha rfl)
      else isFalse (by intro h; cases h; exact hc rfl)
    | .lambda b₁, .lambda b₂ =>
      match decEqPattern b₁ b₂ with
      | isTrue hb => isTrue (by subst hb; rfl)
      | isFalse hb => isFalse (by intro h; cases h; exact hb rfl)
    | .multiLambda n₁ b₁, .multiLambda n₂ b₂ =>
      if hn : n₁ = n₂ then
        match decEqPattern b₁ b₂ with
        | isTrue hb => isTrue (by subst hn; subst hb; rfl)
        | isFalse hb => isFalse (by intro h; cases h; exact hb rfl)
      else isFalse (by intro h; cases h; exact hn rfl)
    | .subst b₁ r₁, .subst b₂ r₂ =>
      match decEqPattern b₁ b₂, decEqPattern r₁ r₂ with
      | isTrue hb, isTrue hr => isTrue (by subst hb; subst hr; rfl)
      | isFalse hb, _ => isFalse (by intro h; cases h; exact hb rfl)
      | _, isFalse hr => isFalse (by intro h; cases h; exact hr rfl)
    | .collection ct₁ es₁ r₁, .collection ct₂ es₂ r₂ =>
      if hct : ct₁ = ct₂ then
        match decEqPatternList es₁ es₂ with
        | isTrue he =>
          if hr : r₁ = r₂ then isTrue (by subst hct; subst he; subst hr; rfl)
          else isFalse (by intro h; cases h; exact hr rfl)
        | isFalse he => isFalse (by intro h; cases h; exact he rfl)
      else isFalse (by intro h; cases h; exact hct rfl)
    -- Cross-constructor cases (7 × 6 = 42)
    | .bvar _, .fvar _ => isFalse Pattern.noConfusion
    | .bvar _, .apply _ _ => isFalse Pattern.noConfusion
    | .bvar _, .lambda _ => isFalse Pattern.noConfusion
    | .bvar _, .multiLambda _ _ => isFalse Pattern.noConfusion
    | .bvar _, .subst _ _ => isFalse Pattern.noConfusion
    | .bvar _, .collection _ _ _ => isFalse Pattern.noConfusion
    | .fvar _, .bvar _ => isFalse Pattern.noConfusion
    | .fvar _, .apply _ _ => isFalse Pattern.noConfusion
    | .fvar _, .lambda _ => isFalse Pattern.noConfusion
    | .fvar _, .multiLambda _ _ => isFalse Pattern.noConfusion
    | .fvar _, .subst _ _ => isFalse Pattern.noConfusion
    | .fvar _, .collection _ _ _ => isFalse Pattern.noConfusion
    | .apply _ _, .bvar _ => isFalse Pattern.noConfusion
    | .apply _ _, .fvar _ => isFalse Pattern.noConfusion
    | .apply _ _, .lambda _ => isFalse Pattern.noConfusion
    | .apply _ _, .multiLambda _ _ => isFalse Pattern.noConfusion
    | .apply _ _, .subst _ _ => isFalse Pattern.noConfusion
    | .apply _ _, .collection _ _ _ => isFalse Pattern.noConfusion
    | .lambda _, .bvar _ => isFalse Pattern.noConfusion
    | .lambda _, .fvar _ => isFalse Pattern.noConfusion
    | .lambda _, .apply _ _ => isFalse Pattern.noConfusion
    | .lambda _, .multiLambda _ _ => isFalse Pattern.noConfusion
    | .lambda _, .subst _ _ => isFalse Pattern.noConfusion
    | .lambda _, .collection _ _ _ => isFalse Pattern.noConfusion
    | .multiLambda _ _, .bvar _ => isFalse Pattern.noConfusion
    | .multiLambda _ _, .fvar _ => isFalse Pattern.noConfusion
    | .multiLambda _ _, .apply _ _ => isFalse Pattern.noConfusion
    | .multiLambda _ _, .lambda _ => isFalse Pattern.noConfusion
    | .multiLambda _ _, .subst _ _ => isFalse Pattern.noConfusion
    | .multiLambda _ _, .collection _ _ _ => isFalse Pattern.noConfusion
    | .subst _ _, .bvar _ => isFalse Pattern.noConfusion
    | .subst _ _, .fvar _ => isFalse Pattern.noConfusion
    | .subst _ _, .apply _ _ => isFalse Pattern.noConfusion
    | .subst _ _, .lambda _ => isFalse Pattern.noConfusion
    | .subst _ _, .multiLambda _ _ => isFalse Pattern.noConfusion
    | .subst _ _, .collection _ _ _ => isFalse Pattern.noConfusion
    | .collection _ _ _, .bvar _ => isFalse Pattern.noConfusion
    | .collection _ _ _, .fvar _ => isFalse Pattern.noConfusion
    | .collection _ _ _, .apply _ _ => isFalse Pattern.noConfusion
    | .collection _ _ _, .lambda _ => isFalse Pattern.noConfusion
    | .collection _ _ _, .multiLambda _ _ => isFalse Pattern.noConfusion
    | .collection _ _ _, .subst _ _ => isFalse Pattern.noConfusion

  private def decEqPatternList : (a b : List Pattern) → Decidable (a = b)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (fun h => by cases h)
    | _ :: _, [] => isFalse (fun h => by cases h)
    | x :: xs, y :: ys =>
      match decEqPattern x y, decEqPatternList xs ys with
      | isTrue hx, isTrue hxs => isTrue (by subst hx; subst hxs; rfl)
      | isFalse hx, _ => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs => isFalse (by intro h; cases h; exact hxs rfl)
end

instance : DecidableEq Pattern := decEqPattern
instance : BEq Pattern := ⟨fun a b => decide (a = b)⟩

namespace Pattern

def mkFVar (name : String) : Pattern := .fvar name
def mkBVar (n : Nat) : Pattern := .bvar n

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

/-- Custom induction principle for Pattern that handles nested List Pattern. -/
def Pattern.inductionOn {motive : Pattern → Prop}
    (p : Pattern)
    (hbvar : ∀ n, motive (.bvar n))
    (hfvar : ∀ x, motive (.fvar x))
    (happly : ∀ constructor args, (∀ q ∈ args, motive q) →
      motive (.apply constructor args))
    (hlambda : ∀ body, motive body → motive (.lambda body))
    (hmultiLambda : ∀ n body, motive body → motive (.multiLambda n body))
    (hsubst : ∀ body repl, motive body → motive repl → motive (.subst body repl))
    (hcollection : ∀ ct elems rest, (∀ q ∈ elems, motive q) →
      motive (.collection ct elems rest))
    : motive p :=
  match p with
  | .bvar n => hbvar n
  | .fvar x => hfvar x
  | .apply constructor args =>
    happly constructor args (fun q _hq =>
      inductionOn q hbvar hfvar happly hlambda hmultiLambda hsubst hcollection)
  | .lambda body =>
    hlambda body
      (inductionOn body hbvar hfvar happly hlambda hmultiLambda hsubst hcollection)
  | .multiLambda n body =>
    hmultiLambda n body
      (inductionOn body hbvar hfvar happly hlambda hmultiLambda hsubst hcollection)
  | .subst body repl =>
    hsubst body repl
      (inductionOn body hbvar hfvar happly hlambda hmultiLambda hsubst hcollection)
      (inductionOn repl hbvar hfvar happly hlambda hmultiLambda hsubst hcollection)
  | .collection ct elems rest =>
    hcollection ct elems rest (fun q _hq =>
      inductionOn q hbvar hfvar happly hlambda hmultiLambda hsubst hcollection)
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
  /-- Collection shapes where one-step congruence descent is permitted.
      This controls subterm/context rewriting in the generic engine.
      By default all collection kinds are enabled. -/
  congruenceCollections : List CollType := [.vec, .hashBag, .hashSet]
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

/-- Predicate view for congruence-descent permission. -/
def allowsCongruenceIn (lang : LanguageDef) (ct : CollType) : Prop :=
  ct ∈ lang.congruenceCollections

instance (lang : LanguageDef) (ct : CollType) :
    Decidable (LanguageDef.allowsCongruenceIn lang ct) := by
  unfold LanguageDef.allowsCongruenceIn
  infer_instance

end LanguageDef

/-! ## ρ-Calculus Example

In locally nameless, rule patterns use `.fvar` for metavariables and
`.lambda body` (no binder name) for abstractions. The COMM rule's
`.subst body repl` substitutes `repl` for BVar 0 in `body`. -/

/-- The ρ-calculus language definition -/
def rhoCalc : LanguageDef := {
  name := "RhoCalc",
  types := ["Proc", "Name"],
  -- Canonical ρ process contexts are parallel-bag contexts.
  -- Source: present-moment.pdf states set accumulation is an optional extension
  -- and "not strictly necessary ... we could simply use parallel composition
  -- to accumulate the states."
  congruenceCollections := [.hashBag],
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

    -- PInput . n:Name, ^p:[Name -> Proc] |- n "?" "." "{" p "}" : Proc
    { label := "PInput", category := "Proc",
      params := [.simple "n" TypeExpr.name,
                 .abstraction "p" (TypeExpr.funType TypeExpr.name TypeExpr.proc)],
      syntaxPattern := [.nonTerminal "n", .terminal "?",
                        .terminal ".", .terminal "{", .nonTerminal "p", .terminal "}"] }
  ],
  equations := [
    -- (NQuote (PDrop N)) = N
    { name := "QuoteDrop",
      typeContext := [("N", TypeExpr.name)],
      premises := [],
      left := .apply "NQuote" [.apply "PDrop" [.fvar "N"]],
      right := .fvar "N" }
  ],
  rewrites := [
    -- Comm: { n!(q) | for(<-n){p} | ...rest } ~> { p[@q] | ...rest }
    -- In LN: the input pattern is λ.body where BVar 0 is the received name.
    -- The subst node replaces BVar 0 in p with NQuote(q).
    { name := "Comm",
      typeContext := [("n", TypeExpr.name), ("p", TypeExpr.proc), ("q", TypeExpr.proc)],
      premises := [],
      left := .collection .hashBag [
        .apply "PInput" [.fvar "n", .lambda (.fvar "p")],
        .apply "POutput" [.fvar "n", .fvar "q"]
      ] (some "rest"),
      right := .collection .hashBag [
        .subst (.fvar "p") (.apply "NQuote" [.fvar "q"])
      ] (some "rest") },

    -- Drop: *(@p) ~> p
    { name := "Drop",
      typeContext := [("p", TypeExpr.proc)],
      premises := [],
      left := .apply "PDrop" [.apply "NQuote" [.fvar "p"]],
      right := .fvar "p" },

    -- ParCong: | S ~> T |- {S, ...rest} ~> {T, ...rest}
    { name := "ParCong",
      typeContext := [],
      premises := [.congruence (.fvar "S") (.fvar "T")],
      left := .collection .hashBag [.fvar "S"] (some "rest"),
      right := .collection .hashBag [.fvar "T"] (some "rest") }
  ]
}

/-- Optional ρ extension with set-context congruence enabled.

    Canonical `rhoCalc` keeps bag-only process contexts.
    This extension models the finite-set accumulation variant discussed
    in `present-moment.pdf` (sets are useful but optional). -/
def rhoCalcSetExt : LanguageDef :=
  { rhoCalc with
      name := "RhoCalcSetExt"
      congruenceCollections := [.hashBag, .hashSet] }

end Mettapedia.OSLF.MeTTaIL.Syntax
