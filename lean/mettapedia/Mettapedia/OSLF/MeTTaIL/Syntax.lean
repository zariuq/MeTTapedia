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

/-! ## Type Declarations and Carriers -/

/-- Carrier class for declared language types. -/
inductive CarrierKind where
  | ast
  | tokenLabel
  | tokenRaw
  | tokenProof
  | tokenPath
  | builtinInt
  | builtinString
  | builtinBool
deriving DecidableEq, Repr

/-- Named type declaration in the authored language definition. -/
structure TypeDecl where
  name : String
  carrier : CarrierKind := .ast
deriving DecidableEq, Repr

namespace TypeDecl

def plain (typeName : String) : TypeDecl := { name := typeName }

end TypeDecl

instance : Coe String TypeDecl := ⟨TypeDecl.plain⟩
instance : ToString TypeDecl := ⟨TypeDecl.name⟩

instance : Membership String (List TypeDecl) where
  mem decls typeName := typeName ∈ decls.map (·.name)

/-! ## Type Expressions -/

/-- Type expressions in MeTTaIL -/
inductive TypeExpr where
  | base : String → TypeExpr
  | arrow : TypeExpr → TypeExpr → TypeExpr
  | multiBinder : TypeExpr → TypeExpr
  | collection : CollType → TypeExpr → TypeExpr
deriving Repr, DecidableEq

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
    The single authoritative `LanguageDef` preserves authored binder names when
    available, while locally nameless patterns still erase them operationally.
    This keeps the Lean authoring surface close to Rust `language!` without
    introducing a second "surface AST". -/
inductive TermParam where
  | simple : String → TypeExpr → TermParam
  | abstractionNamed : Option String → String → TypeExpr → TermParam
  | multiAbstractionNamed : List String → String → TypeExpr → TermParam
deriving Repr, DecidableEq

namespace TermParam

/-- Backward-compatible abstraction constructor. Binder name is absent. -/
@[match_pattern] abbrev abstraction (bodyName : String) (ty : TypeExpr) : TermParam :=
  .abstractionNamed none bodyName ty

/-- Backward-compatible multi-abstraction constructor. Binder names are absent. -/
@[match_pattern] abbrev multiAbstraction (bodyName : String) (ty : TypeExpr) : TermParam :=
  .multiAbstractionNamed [] bodyName ty

/-- Preserve a single authored binder name on the term parameter. -/
def abstractionWithBinder (binderName bodyName : String) (ty : TypeExpr) : TermParam :=
  .abstractionNamed (some binderName) bodyName ty

/-- Preserve multiple authored binder names on the term parameter. -/
def multiAbstractionWithBinders (binderNames : List String) (bodyName : String) (ty : TypeExpr) :
    TermParam :=
  .multiAbstractionNamed binderNames bodyName ty

/-- Body metavariable name carried by the parameter. -/
def bodyName : TermParam → String
  | .simple name _ => name
  | .abstractionNamed _ name _ => name
  | .multiAbstractionNamed _ name _ => name

/-- Authored binder names, if present. -/
def binderNames : TermParam → List String
  | .simple _ _ => []
  | .abstractionNamed binder? _ _ => binder?.toList
  | .multiAbstractionNamed binders _ _ => binders

/-- Parameter type expression. -/
def typeExpr : TermParam → TypeExpr
  | .simple _ ty => ty
  | .abstractionNamed _ _ ty => ty
  | .multiAbstractionNamed _ _ ty => ty

end TermParam

/-! ## Syntax Items -/

mutual

/-- Syntax items for grammar rules.
    The `.op` branch carries Rust-style metasyntax like `*zip`, `*map`,
    `*opt`, and chained `.*sep`. -/
inductive SyntaxItem where
  | terminal : String → SyntaxItem
  | nonTerminal : String → SyntaxItem
  | separator : String → SyntaxItem
  | delimiter : String → String → SyntaxItem
  | op : SyntaxPatternOp → SyntaxItem
deriving Repr

/-- Rust-style compile-time syntax operators authored inside `terms { ... }`
    syntax patterns. These stay in the single Lean `LanguageDef` rather than
    being hidden in backend text. -/
inductive SyntaxPatternOp where
  | var : String → SyntaxPatternOp
  | sep : String → String → Option SyntaxPatternOp → SyntaxPatternOp
  | zip : String → String → SyntaxPatternOp
  | map : SyntaxPatternOp → List String → List SyntaxItem → SyntaxPatternOp
  | opt : List SyntaxItem → SyntaxPatternOp
deriving Repr

end

/-! ## DecidableEq for SyntaxItem / SyntaxPatternOp

These are mutual because syntax operators can contain nested `List SyntaxItem`
payloads (`map` / `opt`), and syntax items can contain operators via `.op`.
-/

mutual
  private def decEqSyntaxItem : (a b : SyntaxItem) → Decidable (a = b)
    | .terminal s₁, .terminal s₂ =>
        if h : s₁ = s₂ then isTrue (by subst h; rfl)
        else isFalse (by intro h'; cases h'; exact h rfl)
    | .nonTerminal s₁, .nonTerminal s₂ =>
        if h : s₁ = s₂ then isTrue (by subst h; rfl)
        else isFalse (by intro h'; cases h'; exact h rfl)
    | .separator s₁, .separator s₂ =>
        if h : s₁ = s₂ then isTrue (by subst h; rfl)
        else isFalse (by intro h'; cases h'; exact h rfl)
    | .delimiter l₁ r₁, .delimiter l₂ r₂ =>
        if hl : l₁ = l₂ then
          if hr : r₁ = r₂ then
            isTrue (by subst hl; subst hr; rfl)
          else
            isFalse (by intro h'; cases h'; exact hr rfl)
        else
          isFalse (by intro h'; cases h'; exact hl rfl)
    | .op op₁, .op op₂ =>
        match decEqSyntaxPatternOp op₁ op₂ with
        | isTrue h => isTrue (by subst h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .terminal _, .nonTerminal _ => isFalse SyntaxItem.noConfusion
    | .terminal _, .separator _ => isFalse SyntaxItem.noConfusion
    | .terminal _, .delimiter _ _ => isFalse SyntaxItem.noConfusion
    | .terminal _, .op _ => isFalse SyntaxItem.noConfusion
    | .nonTerminal _, .terminal _ => isFalse SyntaxItem.noConfusion
    | .nonTerminal _, .separator _ => isFalse SyntaxItem.noConfusion
    | .nonTerminal _, .delimiter _ _ => isFalse SyntaxItem.noConfusion
    | .nonTerminal _, .op _ => isFalse SyntaxItem.noConfusion
    | .separator _, .terminal _ => isFalse SyntaxItem.noConfusion
    | .separator _, .nonTerminal _ => isFalse SyntaxItem.noConfusion
    | .separator _, .delimiter _ _ => isFalse SyntaxItem.noConfusion
    | .separator _, .op _ => isFalse SyntaxItem.noConfusion
    | .delimiter _ _, .terminal _ => isFalse SyntaxItem.noConfusion
    | .delimiter _ _, .nonTerminal _ => isFalse SyntaxItem.noConfusion
    | .delimiter _ _, .separator _ => isFalse SyntaxItem.noConfusion
    | .delimiter _ _, .op _ => isFalse SyntaxItem.noConfusion
    | .op _, .terminal _ => isFalse SyntaxItem.noConfusion
    | .op _, .nonTerminal _ => isFalse SyntaxItem.noConfusion
    | .op _, .separator _ => isFalse SyntaxItem.noConfusion
    | .op _, .delimiter _ _ => isFalse SyntaxItem.noConfusion

  private def decEqSyntaxPatternOp : (a b : SyntaxPatternOp) → Decidable (a = b)
    | .var s₁, .var s₂ =>
        if h : s₁ = s₂ then isTrue (by subst h; rfl)
        else isFalse (by intro h'; cases h'; exact h rfl)
    | .sep c₁ s₁ src₁, .sep c₂ s₂ src₂ =>
        if hc : c₁ = c₂ then
          if hs : s₁ = s₂ then
            match decEqSyntaxPatternOpOption src₁ src₂ with
            | isTrue hsrc => isTrue (by subst hc; subst hs; subst hsrc; rfl)
            | isFalse hsrc => isFalse (by intro h'; cases h'; exact hsrc rfl)
          else
            isFalse (by intro h'; cases h'; exact hs rfl)
        else
          isFalse (by intro h'; cases h'; exact hc rfl)
    | .zip l₁ r₁, .zip l₂ r₂ =>
        if hl : l₁ = l₂ then
          if hr : r₁ = r₂ then
            isTrue (by subst hl; subst hr; rfl)
          else
            isFalse (by intro h'; cases h'; exact hr rfl)
        else
          isFalse (by intro h'; cases h'; exact hl rfl)
    | .map src₁ params₁ body₁, .map src₂ params₂ body₂ =>
        match decEqSyntaxPatternOp src₁ src₂ with
        | isTrue hsrc =>
            if hparams : params₁ = params₂ then
              match decEqSyntaxItemList body₁ body₂ with
              | isTrue hbody => isTrue (by subst hsrc; subst hparams; subst hbody; rfl)
              | isFalse hbody => isFalse (by intro h'; cases h'; exact hbody rfl)
            else
              isFalse (by intro h'; cases h'; exact hparams rfl)
        | isFalse hsrc =>
            isFalse (by intro h'; cases h'; exact hsrc rfl)
    | .opt inner₁, .opt inner₂ =>
        match decEqSyntaxItemList inner₁ inner₂ with
        | isTrue h => isTrue (by subst h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .var _, .sep _ _ _ => isFalse SyntaxPatternOp.noConfusion
    | .var _, .zip _ _ => isFalse SyntaxPatternOp.noConfusion
    | .var _, .map _ _ _ => isFalse SyntaxPatternOp.noConfusion
    | .var _, .opt _ => isFalse SyntaxPatternOp.noConfusion
    | .sep _ _ _, .var _ => isFalse SyntaxPatternOp.noConfusion
    | .sep _ _ _, .zip _ _ => isFalse SyntaxPatternOp.noConfusion
    | .sep _ _ _, .map _ _ _ => isFalse SyntaxPatternOp.noConfusion
    | .sep _ _ _, .opt _ => isFalse SyntaxPatternOp.noConfusion
    | .zip _ _, .var _ => isFalse SyntaxPatternOp.noConfusion
    | .zip _ _, .sep _ _ _ => isFalse SyntaxPatternOp.noConfusion
    | .zip _ _, .map _ _ _ => isFalse SyntaxPatternOp.noConfusion
    | .zip _ _, .opt _ => isFalse SyntaxPatternOp.noConfusion
    | .map _ _ _, .var _ => isFalse SyntaxPatternOp.noConfusion
    | .map _ _ _, .sep _ _ _ => isFalse SyntaxPatternOp.noConfusion
    | .map _ _ _, .zip _ _ => isFalse SyntaxPatternOp.noConfusion
    | .map _ _ _, .opt _ => isFalse SyntaxPatternOp.noConfusion
    | .opt _, .var _ => isFalse SyntaxPatternOp.noConfusion
    | .opt _, .sep _ _ _ => isFalse SyntaxPatternOp.noConfusion
    | .opt _, .zip _ _ => isFalse SyntaxPatternOp.noConfusion
    | .opt _, .map _ _ _ => isFalse SyntaxPatternOp.noConfusion

  private def decEqSyntaxPatternOpOption :
      (a b : Option SyntaxPatternOp) → Decidable (a = b)
    | none, none => isTrue rfl
    | some a, some b =>
        match decEqSyntaxPatternOp a b with
        | isTrue h => isTrue (by subst h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | none, some _ => isFalse (by intro h; cases h)
    | some _, none => isFalse (by intro h; cases h)

  private def decEqSyntaxItemList :
      (a b : List SyntaxItem) → Decidable (a = b)
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
        match decEqSyntaxItem x y, decEqSyntaxItemList xs ys with
        | isTrue hx, isTrue hxs => isTrue (by subst hx; subst hxs; rfl)
        | isFalse hx, _ => isFalse (by intro h'; cases h'; exact hx rfl)
        | _, isFalse hxs => isFalse (by intro h'; cases h'; exact hxs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq SyntaxItem := decEqSyntaxItem
instance : DecidableEq SyntaxPatternOp := decEqSyntaxPatternOp

namespace SyntaxPatternOp

mutual
  private def freeRefsOp : SyntaxPatternOp → List String
    | .var name => [name]
    | .sep collection _ none => [collection]
    | .sep _ _ (some source) => freeRefsOp source
    | .zip left right => [left, right]
    | .map source binders body =>
        freeRefsOp source ++ freeRefsItems binders body
    | .opt inner => freeRefsItems [] inner

  private def freeRefsItems (bound : List String) : List SyntaxItem → List String
    | [] => []
    | item :: rest =>
        freeRefsItem bound item ++ freeRefsItems bound rest

  private def freeRefsItem (bound : List String) : SyntaxItem → List String
    | .terminal _ => []
    | .nonTerminal name =>
        if name ∈ bound then [] else [name]
    | .separator _ => []
    | .delimiter _ _ => []
    | .op op => freeRefsOpWithBound bound op

  private def freeRefsOpWithBound (bound : List String) : SyntaxPatternOp → List String
    | .var name =>
        if name ∈ bound then [] else [name]
    | .sep collection _ none =>
        if collection ∈ bound then [] else [collection]
    | .sep _ _ (some source) => freeRefsOpWithBound bound source
    | .zip left right =>
        let leftRefs := if left ∈ bound then [] else [left]
        let rightRefs := if right ∈ bound then [] else [right]
        leftRefs ++ rightRefs
    | .map source binders body =>
        freeRefsOpWithBound bound source ++ freeRefsItems (binders ++ bound) body
    | .opt inner =>
        freeRefsItems bound inner
end

/-- Free syntax-variable references used by an operator after accounting for
    variables bound by nested `*map` closures. -/
def freeRefs (op : SyntaxPatternOp) : List String :=
  freeRefsOp op

end SyntaxPatternOp

namespace SyntaxItem

/-- Free syntax-variable references used by an authored syntax item. -/
def freeRefs : SyntaxItem → List String
  | .terminal _ => []
  | .nonTerminal name => [name]
  | .separator _ => []
  | .delimiter _ _ => []
  | .op patOp => patOp.freeRefs

end SyntaxItem

/-! ## Grammar Rules (Constructors) -/

/-- Evaluation policy for authored grammar rules.
    - `.rewrite`: pure rewrite-driven term
    - `.fold`: host-native fold implementation (typed contract in LanguageDef)
    - `.oracle`: external/host effectful implementation boundary -/
inductive TermEvalPolicy where
  | rewrite
  | fold
  | oracle
deriving Repr, DecidableEq

/-- A grammar rule defines a constructor. `syntaxPattern` is the single
    authored syntax authority and may contain both plain tokens/nonterminals and
    Rust-style metasyntax operators. -/
structure GrammarRule where
  label : String
  category : String
  params : List TermParam
  syntaxPattern : List SyntaxItem
  evalPolicy? : Option TermEvalPolicy := none
deriving Repr, DecidableEq

/-! ## Patterns (Locally Nameless) -/

/-- Patterns using locally nameless representation.
    - `.bvar n`: bound variable (de Bruijn index `n`, counting from innermost binder)
    - `.fvar x`: free variable / metavariable (named)
    - `.lambda binderName? body`: binder — `binderName?` preserves the authored name
      for export/diagnostics, BVar 0 = the bound variable
    - `.subst body repl`: substitute `repl` for BVar 0 in `body`
    Binder names are retained metadata, so structural equality sees them.
    Direct lambda matching ignores display names; repeated metavariable
    consistency remains structural until a canonical-metadata profile is
    admitted. -/
inductive Pattern where
  | bvar : Nat → Pattern
  | fvar : String → Pattern
  | apply : String → List Pattern → Pattern
  | lambda : Option String → Pattern → Pattern
  | multiLambda : Nat → List String → Pattern → Pattern
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
    | .lambda nm₁ b₁, .lambda nm₂ b₂ =>
      if hn : nm₁ = nm₂ then
        match decEqPattern b₁ b₂ with
        | isTrue hb => isTrue (by subst hn; subst hb; rfl)
        | isFalse hb => isFalse (by intro h; cases h; exact hb rfl)
      else isFalse (by intro h; cases h; exact hn rfl)
    | .multiLambda n₁ nms₁ b₁, .multiLambda n₂ nms₂ b₂ =>
      if hn : n₁ = n₂ then
        if hnms : nms₁ = nms₂ then
          match decEqPattern b₁ b₂ with
          | isTrue hb => isTrue (by subst hn; subst hnms; subst hb; rfl)
          | isFalse hb => isFalse (by intro h; cases h; exact hb rfl)
        else isFalse (by intro h; cases h; exact hnms rfl)
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
    | .bvar _, .lambda _ _ => isFalse Pattern.noConfusion
    | .bvar _, .multiLambda _ _ _ => isFalse Pattern.noConfusion
    | .bvar _, .subst _ _ => isFalse Pattern.noConfusion
    | .bvar _, .collection _ _ _ => isFalse Pattern.noConfusion
    | .fvar _, .bvar _ => isFalse Pattern.noConfusion
    | .fvar _, .apply _ _ => isFalse Pattern.noConfusion
    | .fvar _, .lambda _ _ => isFalse Pattern.noConfusion
    | .fvar _, .multiLambda _ _ _ => isFalse Pattern.noConfusion
    | .fvar _, .subst _ _ => isFalse Pattern.noConfusion
    | .fvar _, .collection _ _ _ => isFalse Pattern.noConfusion
    | .apply _ _, .bvar _ => isFalse Pattern.noConfusion
    | .apply _ _, .fvar _ => isFalse Pattern.noConfusion
    | .apply _ _, .lambda _ _ => isFalse Pattern.noConfusion
    | .apply _ _, .multiLambda _ _ _ => isFalse Pattern.noConfusion
    | .apply _ _, .subst _ _ => isFalse Pattern.noConfusion
    | .apply _ _, .collection _ _ _ => isFalse Pattern.noConfusion
    | .lambda _ _, .bvar _ => isFalse Pattern.noConfusion
    | .lambda _ _, .fvar _ => isFalse Pattern.noConfusion
    | .lambda _ _, .apply _ _ => isFalse Pattern.noConfusion
    | .lambda _ _, .multiLambda _ _ _ => isFalse Pattern.noConfusion
    | .lambda _ _, .subst _ _ => isFalse Pattern.noConfusion
    | .lambda _ _, .collection _ _ _ => isFalse Pattern.noConfusion
    | .multiLambda _ _ _, .bvar _ => isFalse Pattern.noConfusion
    | .multiLambda _ _ _, .fvar _ => isFalse Pattern.noConfusion
    | .multiLambda _ _ _, .apply _ _ => isFalse Pattern.noConfusion
    | .multiLambda _ _ _, .lambda _ _ => isFalse Pattern.noConfusion
    | .multiLambda _ _ _, .subst _ _ => isFalse Pattern.noConfusion
    | .multiLambda _ _ _, .collection _ _ _ => isFalse Pattern.noConfusion
    | .subst _ _, .bvar _ => isFalse Pattern.noConfusion
    | .subst _ _, .fvar _ => isFalse Pattern.noConfusion
    | .subst _ _, .apply _ _ => isFalse Pattern.noConfusion
    | .subst _ _, .lambda _ _ => isFalse Pattern.noConfusion
    | .subst _ _, .multiLambda _ _ _ => isFalse Pattern.noConfusion
    | .subst _ _, .collection _ _ _ => isFalse Pattern.noConfusion
    | .collection _ _ _, .bvar _ => isFalse Pattern.noConfusion
    | .collection _ _ _, .fvar _ => isFalse Pattern.noConfusion
    | .collection _ _ _, .apply _ _ => isFalse Pattern.noConfusion
    | .collection _ _ _, .lambda _ _ => isFalse Pattern.noConfusion
    | .collection _ _ _, .multiLambda _ _ _ => isFalse Pattern.noConfusion
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

/-- Backward-compatible alias used by legacy process-calculus files. -/
@[match_pattern] abbrev var (name : String) : Pattern := .fvar name

def zipHead : String := "$zip"
def mapHead : String := "$map"
def evalHead : String := "$eval"

def mkFVar (name : String) : Pattern := .fvar name
def mkBVar (n : Nat) : Pattern := .bvar n

def mkApp (constructor : String) (args : List Pattern) : Pattern :=
  .apply constructor args

def mkBag (elements : List Pattern) (rest : Option String := none) : Pattern :=
  .collection .hashBag elements rest

/-- Structured rule-pattern zip inside the one `Pattern` type. -/
def zip (first second : Pattern) : Pattern :=
  .apply zipHead [first, second]

/-- Structured rule-pattern map inside the one `Pattern` type. The body binds
    the given parameters through the existing `multiLambda` node. -/
def map (source : Pattern) (params : List String) (body : Pattern) : Pattern :=
  .apply mapHead [source, .multiLambda params.length params body]

/-- Structured authored eval/substitution surface inside the one `Pattern`
    type. This stays distinct from `.subst`, which is the older explicit
    locally-nameless single-binder substitution node. -/
def eval (scope repl : Pattern) : Pattern :=
  .apply evalHead [scope, repl]

def zipArgs? : Pattern → Option (Pattern × Pattern)
  | .apply head [first, second] =>
      if head = zipHead then some (first, second) else none
  | _ => none

def mapArgs? : Pattern → Option (Pattern × List String × Pattern)
  | .apply head [source, .multiLambda _ params body] =>
      if head = mapHead then some (source, params, body) else none
  | _ => none

def evalArgs? : Pattern → Option (Pattern × Pattern)
  | .apply head [scope, repl] =>
      if head = evalHead then some (scope, repl) else none
  | _ => none

/-- Detect the authored `...rest` collection remainder shape. This stays within
    the existing locally nameless `Pattern` representation instead of
    introducing a second authored pattern AST. -/
def collectionRestName? : Pattern → Option String
  | .collection _ [] (some rest) => some rest
  | _ => none

end Pattern

/-! ## JSON Serialization for Artifact Export

These produce JSON matching the Rust `PatternNode` / `PremiseNode` enums
which use `#[serde(tag = "kind", rename_all = "snake_case")]`.
The format is language-agnostic — any `LanguageDef` can use it. -/

private def jsonEscapeSyntax (s : String) : String :=
  s.foldl
    (fun acc c =>
      acc ++
      match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | _ => String.singleton c)
    ""

private def jsonStrSyntax (s : String) : String :=
  "\"" ++ jsonEscapeSyntax s ++ "\""

private def jsonNatSyntax (n : Nat) : String :=
  toString n

mutual
  partial def Pattern.renderJson : Pattern → String
    | .bvar n => "{\"kind\":\"bvar\",\"index\":" ++ jsonNatSyntax n ++ "}"
    | .fvar name => "{\"kind\":\"fvar\",\"name\":" ++ jsonStrSyntax name ++ "}"
    | pat@(.apply ctor args) =>
        match Pattern.zipArgs? pat with
        | some (first, second) =>
            "{\"kind\":\"zip\",\"first\":" ++ first.renderJson
              ++ ",\"second\":" ++ second.renderJson ++ "}"
        | none =>
            match Pattern.mapArgs? pat with
            | some (source, params, body) =>
                let paramsJson := "[" ++ String.intercalate "," (params.map jsonStrSyntax) ++ "]"
                "{\"kind\":\"map\",\"source\":" ++ source.renderJson
                  ++ ",\"params\":" ++ paramsJson
                  ++ ",\"body\":" ++ body.renderJson ++ "}"
            | none =>
                match Pattern.evalArgs? pat with
                | some (scope, repl) =>
                    "{\"kind\":\"eval\",\"scope\":" ++ scope.renderJson
                      ++ ",\"repl\":" ++ repl.renderJson ++ "}"
                | none =>
                    "{\"kind\":\"apply\",\"ctor\":" ++ jsonStrSyntax ctor
                      ++ ",\"args\":[" ++ String.intercalate "," (renderJsonPatternList args) ++ "]}"
    | .lambda binderName? body =>
        let nmJson := match binderName? with
          | none => "null"
          | some nm => jsonStrSyntax nm
        "{\"kind\":\"lambda\",\"binder_name\":" ++ nmJson
          ++ ",\"body\":" ++ body.renderJson ++ "}"
    | .multiLambda arity binderNames body =>
        let nmsJson := "[" ++ String.intercalate "," (binderNames.map jsonStrSyntax) ++ "]"
        "{\"kind\":\"multi_lambda\",\"arity\":" ++ jsonNatSyntax arity
          ++ ",\"binder_names\":" ++ nmsJson
          ++ ",\"body\":" ++ body.renderJson ++ "}"
    | .subst body repl =>
        "{\"kind\":\"subst\",\"body\":" ++ body.renderJson
          ++ ",\"repl\":" ++ repl.renderJson ++ "}"
    | .collection ct elements rest =>
        let ctStr := match ct with
          | .vec => "vec"
          | .hashBag => "hash_bag"
          | .hashSet => "hash_set"
        let restJson := match rest with
          | none => "null"
          | some r => jsonStrSyntax r
        "{\"kind\":\"collection\",\"collection_type\":"
          ++ jsonStrSyntax ctStr
          ++ ",\"elements\":[" ++ String.intercalate "," (renderJsonPatternList elements)
          ++ "],\"rest\":" ++ restJson ++ "}"
  partial def renderJsonPatternList : List Pattern → List String
    | [] => []
    | p :: ps => p.renderJson :: renderJsonPatternList ps
end

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
    (hlambda : ∀ nm body, motive body → motive (.lambda nm body))
    (hmultiLambda : ∀ n nms body, motive body → motive (.multiLambda n nms body))
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
  | .lambda nm body =>
    hlambda nm body
      (inductionOn body hbvar hfvar happly hlambda hmultiLambda hsubst hcollection)
  | .multiLambda n nms body =>
    hmultiLambda n nms body
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
deriving Repr, DecidableEq

/-- Premises for rules -/
inductive Premise where
  | freshness : FreshnessCondition → Premise
  | congruence : Pattern → Pattern → Premise
  | relationQuery : String → List Pattern → Premise
  | forAll : String → String → Premise → Premise
deriving Repr, DecidableEq

def Premise.renderJson : Premise → String
  | .freshness fc =>
      "{\"kind\":\"freshness\",\"var_name\":" ++ jsonStrSyntax fc.varName
        ++ ",\"term\":" ++ fc.term.renderJson ++ "}"
  | .congruence lhs rhs =>
      "{\"kind\":\"congruence\",\"lhs\":" ++ lhs.renderJson
        ++ ",\"rhs\":" ++ rhs.renderJson ++ "}"
  | .relationQuery rel args =>
      "{\"kind\":\"relation_query\",\"relation\":" ++ jsonStrSyntax rel
        ++ ",\"args\":[" ++ String.intercalate "," (args.map Pattern.renderJson) ++ "]}"
  | .forAll collection param body =>
      "{\"kind\":\"for_all\",\"collection\":" ++ jsonStrSyntax collection
        ++ ",\"param\":" ++ jsonStrSyntax param
        ++ ",\"body\":" ++ body.renderJson ++ "}"

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

/-! ## Declarative reflective substitution -/

/-- Serializable data for a reflective process/name presentation.

The declaration identifies the two sorts and the constructors needed to
compile paper-style name equality and communication substitution.  The
`quoteDropEquation` field links the operational compiler to an equation that
is already authored in the same `LanguageDef`; it does not silently add an
equation. -/
structure ReflectivePresentationDecl where
  name : String
  rewriteRule : String
  processSort : String
  nameSort : String
  quoteConstructor : String
  dropConstructor : String
  inputConstructor : String
  outputConstructor : String
  parallelCollection : CollType
  parallelUnitConstructor : String
  quoteDropEquation : String
deriving Repr, DecidableEq

namespace ReflectivePresentationDecl

/-- Stable data rendering for the authored reflective-semantics declaration. -/
def renderJson (declaration : ReflectivePresentationDecl) : String :=
  "{\"name\":" ++ jsonStrSyntax declaration.name ++
    ",\"rewrite_rule\":" ++ jsonStrSyntax declaration.rewriteRule ++
    ",\"process_sort\":" ++ jsonStrSyntax declaration.processSort ++
    ",\"name_sort\":" ++ jsonStrSyntax declaration.nameSort ++
    ",\"quote_constructor\":" ++ jsonStrSyntax declaration.quoteConstructor ++
    ",\"drop_constructor\":" ++ jsonStrSyntax declaration.dropConstructor ++
    ",\"input_constructor\":" ++ jsonStrSyntax declaration.inputConstructor ++
    ",\"output_constructor\":" ++ jsonStrSyntax declaration.outputConstructor ++
    ",\"parallel_collection\":" ++
      jsonStrSyntax (match declaration.parallelCollection with
        | .vec => "vec" | .hashBag => "hash_bag" | .hashSet => "hash_set") ++
    ",\"parallel_unit_constructor\":" ++
      jsonStrSyntax declaration.parallelUnitConstructor ++
    ",\"quote_drop_equation\":" ++
      jsonStrSyntax declaration.quoteDropEquation ++ "}"

end ReflectivePresentationDecl

/-! ## Proof-calculus declarations

These declarations are part of the language definition itself.  Runtime and
checker presentations may serialize or index them, but may not supply a
second, independently authored rule table.
-/

/-- Stable external identifier for one inference rule. -/
structure RuleId where
  value : String
deriving Repr, DecidableEq

/-- Structural declaration of one proof-judgment form. -/
structure JudgmentDecl where
  head : String
  arity : Nat
deriving Repr, DecidableEq

/-- Generic, decidable obligations attached to an inference-rule instance.
Argument positions refer to the rule's ordered metavariable/argument vectors;
the checker interprets each constructor without a language-specific branch. -/
inductive RuleSideCondition where
  /-- The result argument must be the binder-eliminating substitution of the
  replacement argument into the body argument.  At ambient depth `d`, the body
  is declared at `d + 1` and the replacement and result at `d`. -/
  | explicitSubstitution
      (ambientDepth bodyArgument replacementArgument resultArgument : Nat)
deriving Repr, DecidableEq

/-- One ordered inference-rule schema.  Each metavariable records its exact
occurrence depth; premise order is proof-child order. -/
structure RuleSchema where
  id : RuleId
  metavariables : List (String × Nat)
  premises : List Pattern
  conclusion : Pattern
  sideConditions : List RuleSideCondition := []
deriving Repr, DecidableEq

/-- Rooted declaration of the binary judgment used for explicit conversion
certificates.  Conversion steps themselves remain ordinary inference rules. -/
structure ConversionDecl where
  judgmentHead : String
  version : String
deriving Repr, DecidableEq

/-! ## Complete Language Definition -/

/-- Signature for a derived relation declaration in the logic layer. -/
structure LogicRelationDecl where
  name : String
  argTypes : List TypeExpr
deriving Repr

/-! ### Typed Datalog rules (function-free LP)

These types provide a properly typed Datalog (function-free Horn clause) AST
for LanguageDef logic rules. They bridge to `Mettapedia.Logic.LP.Core` for
proven semantics (T_P operator, least Herbrand model, fixpoint theorems).

Using String names for relations, variables, and constants matches the
LanguageDef surface and the OSLF `RelationEnv` encoding. The bridge to
LP.Core converts List→Fin and String→abstract types. -/

/-- A Datalog term: variable or constant (function-free, no compound terms). -/
inductive DatalogTerm where
  | var : String → DatalogTerm
  | const : String → DatalogTerm
deriving Repr, DecidableEq

/-- A Datalog atom: relation name applied to argument terms. -/
structure DatalogAtom where
  rel : String
  args : List DatalogTerm
deriving Repr, DecidableEq

namespace DatalogAtom

/-- Variable names occurring in an atom. -/
def vars (a : DatalogAtom) : List String :=
  a.args.filterMap fun | .var v => some v | .const _ => none

end DatalogAtom

/-- A Datalog clause: `head :- body₁, body₂, ...` (definite Horn clause).
    When `body` is empty, this is a fact. -/
structure DatalogClause where
  head : DatalogAtom
  body : List DatalogAtom
  /-- Optional clause name for traceability. -/
  name : String := ""
deriving Repr, DecidableEq

namespace DatalogClause

/-- A clause is safe (range-restricted) when every head variable appears in the body.
    This is the standard Datalog safety condition. -/
def isSafe (c : DatalogClause) : Bool :=
  c.head.vars.all fun v => c.body.any fun b => v ∈ b.vars

/-- A fact: a clause with empty body. -/
def isFact (c : DatalogClause) : Bool :=
  c.body.isEmpty

end DatalogClause

/-- Backend-agnostic logic declarations authored alongside rules.
    - `relation`: declares a relation signature (name + arg types)
    - `ruleText`: legacy plain-text rules (deprecated, opaque to Lean)
    - `datalogClause`: typed Datalog rule with proven LP.Core semantics -/
inductive LogicDecl where
  | relation : LogicRelationDecl → LogicDecl
  | ruleText : String → LogicDecl
  | datalogClause : DatalogClause → LogicDecl
deriving Repr

/-- Signature for host/runtime-provided oracle operations. -/
structure OracleDecl where
  name : String
  argTypes : List TypeExpr
  resultType : TypeExpr
deriving Repr

/-! ### Language Options

Options classify runtime/backend/semantic behavior, matching Rust's
`options { ... }` block in `language!`. Classified per GPT-Pro's
recommendation:
- **semantic**: change what language is being defined (e.g., `higher_order`)
- **operational**: affect execution strategy, not denotation (e.g., `dispatch`)
- **backend**: host integration (e.g., `mork_backend`)
- **debug**: observability only (e.g., `log_semiring_model_path`) -/

/-- Classification of a language option's semantic weight.
    Determines whether the option changes the language denotation
    or only affects operational/backend behavior. -/
inductive OptionClass where
  | semantic      -- changes what language is defined
  | operational   -- affects execution strategy, not denotation
  | backend       -- host integration
  | debug         -- observability only
deriving Repr, DecidableEq

/-- A typed option value, matching Rust's `AttributeValue` variants. -/
inductive OptionValue where
  | bool : Bool → OptionValue
  | int : Int → OptionValue
  | float : Float → OptionValue
  | keyword : String → OptionValue
  | str : String → OptionValue
deriving Repr

/-- A single language option: key + value + semantic classification. -/
structure LangOption where
  key : String
  value : OptionValue
  class_ : OptionClass := .operational
deriving Repr

/-- Single authoritative language definition.
    This matches the Rust `language!` design: one `LanguageDef`, with the
    macro/DSL providing the human-facing surface syntax directly. -/
structure LanguageDef where
  name : String
  /-- Language options (beam_width, dispatch, higher_order, etc.).
      Matches Rust's `options { ... }` block. Default empty. -/
  options : List LangOption := []
  types : List TypeDecl
  terms : List GrammarRule
  equations : List Equation
  rewrites : List RewriteRule
  /-- Collection shapes where one-step congruence descent is permitted.
      This controls subterm/context rewriting in the generic engine.
      Default is empty: each language should opt in explicitly. -/
  congruenceCollections : List CollType := []
  logic : List LogicDecl := []
  oracles : List OracleDecl := []
  /-- Named, validated reflective-semantics declarations.  Rules opt in by
      being named by a declaration; an empty list preserves ordinary
      syntactic rewriting for every rule. -/
  reflectivePresentations : List ReflectivePresentationDecl := []
  /-- Proof-judgment signatures authored at the same root as the syntax and
      operational rules. -/
  judgments : List JudgmentDecl := []
  /-- Ordered proof-calculus rules authored at the same root.  A checker-side
      presentation is a derived view of these declarations, never a second
      language-specific source. -/
  inferenceRules : List RuleSchema := []
  /-- Optional rooted conversion interface.  When present, it names a declared
      binary judgment whose ordinary inference proofs are conversion edges. -/
  conversion : Option ConversionDecl := none
deriving Repr

/-- Legacy compatibility wrapper.
    Direction is intentional: legacy depends on the new LanguageDef,
    never the other way around. -/
structure LegacyLanguageDef extends LanguageDef where
  legacyCompatOnly : Unit := ()
deriving Repr

namespace LanguageDef

def empty (name : String) : LanguageDef :=
  { name, types := [], terms := [], equations := [], rewrites := [] }

/-- Construct the original operational core while leaving every optional
    extension at its declared default.  Keeping this wrapper stable prevents
    additions to `LanguageDef` from shifting generated positional arguments. -/
def ofCore
    (name : String)
    (types : List TypeDecl)
    (terms : List GrammarRule)
    (equations : List Equation)
    (rewrites : List RewriteRule)
    (congruenceCollections : List CollType := [])
    (logic : List LogicDecl := [])
    (oracles : List OracleDecl := []) : LanguageDef :=
  { name
    types
    terms
    equations
    rewrites
    congruenceCollections
    logic
    oracles }

def addType (lang : LanguageDef) (typeName : String) : LanguageDef :=
  { lang with types := lang.types ++ [TypeDecl.plain typeName] }

def addTypeDecl (lang : LanguageDef) (typeDecl : TypeDecl) : LanguageDef :=
  { lang with types := lang.types ++ [typeDecl] }

def typeNames (lang : LanguageDef) : List String :=
  lang.types.map (·.name)

def hasTypeNamed (lang : LanguageDef) (typeName : String) : Prop :=
  typeName ∈ lang.typeNames

instance (lang : LanguageDef) (typeName : String) :
    Decidable (lang.hasTypeNamed typeName) := by
  unfold LanguageDef.hasTypeNamed LanguageDef.typeNames
  infer_instance

@[simp] theorem hasTypeNamed_iff (lang : LanguageDef) (typeName : String) :
    lang.hasTypeNamed typeName ↔ typeName ∈ lang.typeNames := Iff.rfl

def addTypeNamed (lang : LanguageDef) (typeName : String) : LanguageDef :=
  addType lang typeName

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

/-- Forgetful lowering from the new language surface to legacy core. -/
def toLegacy (lang : LanguageDef) : LegacyLanguageDef :=
  { toLanguageDef := lang }

/-- Compatibility embedding from legacy core into the new language surface. -/
def fromLegacy (legacy : LegacyLanguageDef) : LanguageDef :=
  legacy.toLanguageDef

@[simp] theorem toLegacy_fromLegacy (legacy : LegacyLanguageDef) :
    toLegacy (fromLegacy legacy) = legacy := by
  cases legacy
  rfl

@[simp] theorem fromLegacy_toLegacy (lang : LanguageDef) :
    fromLegacy (toLegacy lang) = lang := rfl

end LanguageDef

/-! ## Language Validation -/

/-- Semantic validation error for an authored `LanguageDef`. -/
structure ValidationError where
  context : String
  message : String
deriving Repr, BEq, DecidableEq

namespace ValidationError

def render (err : ValidationError) : String :=
  s!"[{err.context}] {err.message}"

end ValidationError

/-! Relation modes are execution-profile data. They are deliberately separate
from relation signatures until the Metamath and HOL anchors determine whether
modes belong in the common presentation schema. -/

inductive RelationArgMode where
  | input
  | output
deriving Repr, DecidableEq, BEq

structure RelationModeDecl where
  relation : String
  args : List RelationArgMode
deriving Repr, DecidableEq

abbrev RelationModeTable := List RelationModeDecl

namespace RelationModeTable

/-- Look up an unambiguous mode declaration at an exact arity. Missing and
duplicate declarations both fail closed. -/
def lookup? (table : RelationModeTable) (relation : String) (arity : Nat) :
    Option (List RelationArgMode) :=
  match table.filter fun decl => decl.relation == relation && decl.args.length == arity with
  | [decl] => some decl.args
  | _ => none

end RelationModeTable

namespace TypeExpr

/-- Base type names referenced by a type expression. -/
def baseNames : TypeExpr → List String
  | .base name => [name]
  | .arrow dom cod => baseNames dom ++ baseNames cod
  | .multiBinder inner => baseNames inner
  | .collection _ inner => baseNames inner

end TypeExpr

namespace Pattern

mutual
  /-- Constructor references occurring in a pattern, paired with arity.
  The three well-formed metasyntax applications are structural and therefore
  do not count their outer heads as language constructors. -/
  def constructorRefs : Pattern → List (String × Nat)
    | .bvar _ => []
    | .fvar _ => []
    | .apply ctor args =>
        let nested := constructorRefsList args
        match ctor, args with
        | "$zip", [_, _] => nested
        | "$map", [_, .multiLambda _ _ _] => nested
        | "$eval", [_, _] => nested
        | _, _ => (ctor, args.length) :: nested
    | .lambda _ body => constructorRefs body
    | .multiLambda _ _ body => constructorRefs body
    | .subst body repl => constructorRefs body ++ constructorRefs repl
    | .collection _ elems _ => constructorRefsList elems

  def constructorRefsList : List Pattern → List (String × Nat)
    | [] => []
    | pattern :: patterns =>
        constructorRefs pattern ++ constructorRefsList patterns
end

/-- Named metavariable positions in a pattern. Lambda binder names are only
export/diagnostic metadata in the locally nameless representation; actual
bound occurrences are `.bvar` and therefore do not appear here. Collection
rest names are metavariable positions and do appear. -/
def freeFvarNames : Pattern → List String
  | .bvar _ => []
  | .fvar name => [name]
  | .apply _ args => args.flatMap freeFvarNames
  | .lambda _ body => freeFvarNames body
  | .multiLambda _ _ body => freeFvarNames body
  | .subst body replacement => freeFvarNames body ++ freeFvarNames replacement
  | .collection _ elems rest =>
      elems.flatMap freeFvarNames ++ rest.toList

mutual

/-- Locally closed, metavariable-free patterns at a binder depth.  A
collection rest is a metavariable position.  A substitution body is checked
under one additional de Bruijn binder because `subst body replacement`
eliminates `body`'s index zero. -/
def isGroundAt (depth : Nat) : Pattern → Bool
  | .bvar index => decide (index < depth)
  | .fvar _ => false
  | .apply _ args => isGroundListAt depth args
  | .lambda _ body => isGroundAt (depth + 1) body
  | .multiLambda arity _ body => isGroundAt (depth + arity) body
  | .subst body replacement =>
      isGroundAt (depth + 1) body && isGroundAt depth replacement
  | .collection _ elems rest =>
      isGroundListAt depth elems && rest.isNone

def isGroundListAt (depth : Nat) : List Pattern → Bool
  | [] => true
  | pattern :: rest => isGroundAt depth pattern && isGroundListAt depth rest

end

/-- Closed executable data: no free pattern metavariables, no unresolved
collection rest, and every de Bruijn index is in scope. -/
def isGround (pattern : Pattern) : Bool := pattern.isGroundAt 0

mutual

/-- Locally closed pattern schema at a binder depth.  Unlike `isGroundAt`,
free metavariables and collection-rest metavariables are permitted; de Bruijn
indices must still be in scope. -/
def isWellScopedAt (depth : Nat) : Pattern → Bool
  | .bvar index => decide (index < depth)
  | .fvar _ => true
  | .apply _ args => isWellScopedListAt depth args
  | .lambda _ body => isWellScopedAt (depth + 1) body
  | .multiLambda arity _ body => isWellScopedAt (depth + arity) body
  | .subst body replacement =>
      isWellScopedAt (depth + 1) body && isWellScopedAt depth replacement
  | .collection _ elems _ => isWellScopedListAt depth elems

def isWellScopedListAt (depth : Nat) : List Pattern → Bool
  | [] => true
  | pattern :: rest =>
      isWellScopedAt depth pattern && isWellScopedListAt depth rest

end

/-- Locally closed pattern schema at top level. -/
def isWellScoped (pattern : Pattern) : Bool := pattern.isWellScopedAt 0

mutual

/-- Canonical locally nameless metadata profile.  Verified matching can require
this form so structural equality and α-equivalence coincide; display names may
be retained outside that boundary for diagnostics/export. -/
def hasCanonicalBinderMetadata : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | .apply _ args => hasCanonicalBinderMetadataList args
  | .lambda binder body => binder.isNone && hasCanonicalBinderMetadata body
  | .multiLambda _ binders body =>
      binders.isEmpty && hasCanonicalBinderMetadata body
  | .subst body replacement =>
      hasCanonicalBinderMetadata body && hasCanonicalBinderMetadata replacement
  | .collection _ elems _ => hasCanonicalBinderMetadataList elems

def hasCanonicalBinderMetadataList : List Pattern → Bool
  | [] => true
  | pattern :: rest =>
      hasCanonicalBinderMetadata pattern && hasCanonicalBinderMetadataList rest

end

end Pattern

namespace Premise

/-- Relation names referenced by a premise tree. -/
def relationRefs : Premise → List String
  | .freshness _ => []
  | .congruence _ _ => []
  | .relationQuery rel _ => [rel]
  | .forAll _ _ body => relationRefs body

/-- Relation calls paired with their authored arity, including nested `forAll`
bodies. -/
def relationCalls : Premise → List (String × Nat)
  | .freshness _ => []
  | .congruence _ _ => []
  | .relationQuery relation args => [(relation, args.length)]
  | .forAll _ _ body => relationCalls body

end Premise

namespace LanguageDef

private def mkValidationError (context message : String) : ValidationError :=
  { context, message }

def duplicateErrorsAux
    (context what : String) (seen remaining : List String) : List ValidationError :=
  match remaining with
  | [] => []
  | name :: rest =>
      let tailErrors := duplicateErrorsAux context what (name :: seen) rest
      if name ∈ seen then
        mkValidationError context s!"duplicate {what} `{name}`" :: tailErrors
      else
        tailErrors
termination_by remaining.length

def duplicateErrors (context what : String) (names : List String) : List ValidationError :=
  duplicateErrorsAux context what [] names

private theorem duplicateErrorsAux_eq_nil_of_nodup
    (context what : String) (seen remaining : List String)
    (hnodup : remaining.Nodup)
    (hfresh : ∀ name ∈ remaining, name ∉ seen) :
    duplicateErrorsAux context what seen remaining = [] := by
  induction remaining generalizing seen with
  | nil => simp [duplicateErrorsAux]
  | cons name rest ih =>
      have hsplit := List.nodup_cons.mp hnodup
      have hname : name ∉ seen := hfresh name (by simp)
      have htail : ∀ other ∈ rest, other ∉ name :: seen := by
        intro other hother hmember
        rcases List.mem_cons.mp hmember with heq | hseen
        · exact hsplit.1 (heq ▸ hother)
        · exact hfresh other (by simp [hother]) hseen
      simp [duplicateErrorsAux, hname, ih (seen := name :: seen) hsplit.2 htail]

/-- A duplicate scan produces no errors for a duplicate-free name list. -/
@[simp] theorem duplicateErrors_eq_nil_of_nodup
    (context what : String) (names : List String) (hnodup : names.Nodup) :
    duplicateErrors context what names = [] := by
  apply duplicateErrorsAux_eq_nil_of_nodup context what [] names hnodup
  simp

private def validateTypeExpr (knownTypes : List String) (context : String) (ty : TypeExpr) :
    List ValidationError :=
  (TypeExpr.baseNames ty).flatMap fun name =>
    if name ∈ knownTypes then
      []
    else
      [mkValidationError context s!"unknown type `{name}`"]

/-- A type expression contributes no validation errors when all of its base
type names are declared. -/
@[simp] theorem validateTypeExpr_eq_nil_of_baseNames
    (knownTypes : List String) (context : String) (ty : TypeExpr)
    (hknown : ∀ name ∈ ty.baseNames, name ∈ knownTypes) :
    validateTypeExpr knownTypes context ty = [] := by
  unfold validateTypeExpr
  rw [List.flatMap_eq_nil_iff]
  intro name hname
  simp [hknown name hname]

mutual

private def validateSyntaxPatternOp
    (ctx : String)
    (bound : List String)
    (op : SyntaxPatternOp) : List ValidationError :=
  match op with
  | .var name =>
      if name ∈ bound then [] else [mkValidationError ctx s!"unknown syntax parameter `{name}`"]
  | .sep collection _ none =>
      if collection ∈ bound then [] else [mkValidationError ctx s!"unknown syntax parameter `{collection}`"]
  | .sep _ _ (some source) =>
      validateSyntaxPatternOp ctx bound source
  | .zip left right =>
      (if left ∈ bound then [] else [mkValidationError ctx s!"unknown syntax parameter `{left}`"]) ++
      (if right ∈ bound then [] else [mkValidationError ctx s!"unknown syntax parameter `{right}`"])
  | .map source params body =>
      validateSyntaxPatternOp ctx bound source ++
      validateSyntaxPatternItems ctx (params ++ bound) body
  | .opt inner =>
      validateSyntaxPatternItems ctx bound inner
termination_by sizeOf op
decreasing_by
  all_goals simp_wf
  all_goals omega

private def validateSyntaxPatternItem
    (ctx : String)
    (bound : List String)
    (item : SyntaxItem) : List ValidationError :=
  match item with
  | .terminal _ => []
  | .nonTerminal name =>
      if name ∈ bound then [] else [mkValidationError ctx s!"unknown syntax parameter `{name}`"]
  | .separator _ => []
  | .delimiter _ _ => []
  | .op op => validateSyntaxPatternOp ctx bound op
termination_by sizeOf item
decreasing_by
  all_goals simp_wf

private def validateSyntaxPatternItems
    (ctx : String)
    (bound : List String)
    (items : List SyntaxItem) : List ValidationError :=
  match items with
  | [] => []
  | item :: rest =>
      validateSyntaxPatternItem ctx bound item ++
        validateSyntaxPatternItems ctx bound rest
termination_by sizeOf items
decreasing_by
  all_goals simp_wf
  all_goals omega

end

private def validateSyntaxPattern
    (ctx : String)
    (boundNames : List String)
    (items : List SyntaxItem) : List ValidationError :=
  validateSyntaxPatternItems ctx boundNames items

/-- An omitted surface-syntax pattern contributes no validation errors.

This public simp lemma keeps the recursive syntax validator encapsulated while
allowing constructor-only language definitions to discharge `validate = []`
by kernel reduction. -/
@[simp] theorem validateSyntaxPattern_nil (ctx : String) (boundNames : List String) :
    validateSyntaxPattern ctx boundNames [] = [] := by
  simp [validateSyntaxPattern, validateSyntaxPatternItems]

private theorem validateSyntaxPatternItems_nonTerminals
    (ctx : String) (boundNames names : List String)
    (hbound : ∀ name ∈ names, name ∈ boundNames) :
    validateSyntaxPatternItems ctx boundNames (names.map SyntaxItem.nonTerminal) = [] := by
  induction names with
  | nil => simp [validateSyntaxPatternItems]
  | cons name names ih =>
      have hname : name ∈ boundNames := hbound name (by simp)
      have hrest : ∀ other ∈ names, other ∈ boundNames := by
        intro other hother
        exact hbound other (by simp [hother])
      simp [validateSyntaxPatternItems, validateSyntaxPatternItem, hname, ih hrest]

/-- Parameter-only concrete syntax is valid when every referenced nonterminal
is among the constructor's bound parameter names. -/
@[simp] theorem validateSyntaxPattern_nonTerminals
    (ctx : String) (boundNames names : List String)
    (hbound : ∀ name ∈ names, name ∈ boundNames) :
    validateSyntaxPattern ctx boundNames (names.map SyntaxItem.nonTerminal) = [] := by
  simpa [validateSyntaxPattern] using
    validateSyntaxPatternItems_nonTerminals ctx boundNames names hbound

/-- A first-order concrete-syntax row made only of literal terminals and
declared nonterminal parameters contributes no validation errors. -/
@[simp] theorem validateSyntaxPattern_terminalsAndBoundNonTerminals
    (ctx : String) (boundNames : List String) (items : List SyntaxItem)
    (allowed : ∀ item ∈ items,
      match item with
      | .terminal _ => True
      | .nonTerminal name => name ∈ boundNames
      | .separator _ | .delimiter _ _ | .op _ => False) :
    validateSyntaxPattern ctx boundNames items = [] := by
  unfold validateSyntaxPattern
  induction items with
  | nil => simp [validateSyntaxPatternItems]
  | cons item rest inductionHypothesis =>
      have headAllowed := allowed item (by simp)
      have restAllowed : ∀ candidate ∈ rest,
          match candidate with
          | .terminal _ => True
          | .nonTerminal name => name ∈ boundNames
          | .separator _ | .delimiter _ _ | .op _ => False := by
        intro candidate membership
        exact allowed candidate (by simp [membership])
      cases item with
      | terminal token =>
          simp [validateSyntaxPatternItems, validateSyntaxPatternItem,
            inductionHypothesis restAllowed]
      | nonTerminal name =>
          simp [validateSyntaxPatternItems, validateSyntaxPatternItem,
            headAllowed, inductionHypothesis restAllowed]
      | separator token => contradiction
      | delimiter openToken closeToken => contradiction
      | op operation => contradiction

/-- The canonical parameter-only syntax generated from a constructor
signature passes syntax validation, including parameters that carry authored
binder metadata. -/
@[simp] theorem validateSyntaxPattern_termParameters
    (ctx : String) (params : List TermParam) :
    validateSyntaxPattern ctx
      (params.flatMap fun param =>
        TermParam.bodyName param :: TermParam.binderNames param)
      (params.map fun param =>
        SyntaxItem.nonTerminal (TermParam.bodyName param)) = [] := by
  have hbound : ∀ name ∈ params.map TermParam.bodyName,
      name ∈ params.flatMap (fun param =>
        TermParam.bodyName param :: TermParam.binderNames param) := by
    intro name hname
    simp only [List.mem_map] at hname
    obtain ⟨param, hparam, rfl⟩ := hname
    simp only [List.mem_flatMap]
    exact ⟨param, hparam, by simp⟩
  simpa [List.map_map, Function.comp_def] using
    validateSyntaxPattern_nonTerminals ctx
      (params.flatMap fun param =>
        TermParam.bodyName param :: TermParam.binderNames param)
      (params.map TermParam.bodyName) hbound

section SyntaxPatternValidationRegression

example : validateSyntaxPattern "fixture" ["x", "y"]
    [.nonTerminal "x", .nonTerminal "y"] = [] := by
  simp [validateSyntaxPattern, validateSyntaxPatternItems, validateSyntaxPatternItem]

example : validateSyntaxPattern "fixture" ["xs"]
    [.op (.map (.sep "xs" "," (some (.var "xs"))) ["x"]
      [.nonTerminal "x", .op (.opt [.nonTerminal "x"])])] = [] := by
  simp [validateSyntaxPattern, validateSyntaxPatternItems,
    validateSyntaxPatternItem, validateSyntaxPatternOp]

example : validateSyntaxPattern "fixture" ["xs"]
    [.op (.map (.sep "unused" "," (some (.var "missingSource"))) ["x"]
      [.op (.opt [.nonTerminal "missingBody"])])] =
      [mkValidationError "fixture" s!"unknown syntax parameter `{"missingSource"}`",
       mkValidationError "fixture" s!"unknown syntax parameter `{"missingBody"}`"] := by
  simp [validateSyntaxPattern, validateSyntaxPatternItems,
    validateSyntaxPatternItem, validateSyntaxPatternOp]

example : validateSyntaxPattern "fixture" ["xs"]
    [.op (.sep "missingCollection" "," none)] =
      [mkValidationError "fixture" s!"unknown syntax parameter `{"missingCollection"}`"] := by
  simp [validateSyntaxPattern, validateSyntaxPatternItems,
    validateSyntaxPatternItem, validateSyntaxPatternOp]

end SyntaxPatternValidationRegression

def validatePatternConstructors
    (ctx : String)
    (constructors : List GrammarRule)
    (pat : Pattern) : List ValidationError :=
  (Pattern.constructorRefs pat).flatMap fun (ctor, arity) =>
    match constructors.filter fun decl => decl.label == ctor with
    | [] => [mkValidationError ctx s!"unknown constructor `{ctor}/{arity}`"]
    | [decl] =>
        if decl.params.length == arity then
          []
        else
          [mkValidationError ctx
            s!"constructor `{ctor}` expects arity {decl.params.length}, got {arity}"]
    | _ => [mkValidationError ctx s!"ambiguous constructor `{ctor}/{arity}`"]

def validatePremises
    (ctx : String) (relations : List LogicRelationDecl) (premises : List Premise) :
    List ValidationError :=
  premises.flatMap fun prem =>
    prem.relationCalls.flatMap fun (relation, arity) =>
      match relations.filter fun decl =>
        decl.name == relation && decl.argTypes.length == arity with
      | [_] => []
      | [] => [mkValidationError ctx s!"unknown relation `{relation}/{arity}`"]
      | _ => [mkValidationError ctx s!"ambiguous relation `{relation}/{arity}`"]

/-- Free (unshadowed) fvar names of a pattern. -/
def patternFvarNames (bound : List String) (pattern : Pattern) : List String :=
  pattern.freeFvarNames.filter fun name => !(bound.contains name)

/-- Binder names introduced anywhere in a pattern. -/
def patternBinderNames : Pattern → List String
  | .bvar _ => []
  | .fvar _ => []
  | .apply _ args => args.attach.flatMap (fun ⟨q, _⟩ => patternBinderNames q)
  | .lambda b body =>
      (match b with | some n => [n] | none => []) ++ patternBinderNames body
  | .multiLambda _ bs body => bs ++ patternBinderNames body
  | .subst a b => patternBinderNames a ++ patternBinderNames b
  | .collection _ elems _ =>
      elems.attach.flatMap (fun ⟨q, _⟩ => patternBinderNames q)

def premisePatterns : Premise → List Pattern
  | .freshness fc => [fc.term]
  | .congruence l r => [l, r]
  | .relationQuery _ args => args
  | .forAll _ _ p => premisePatterns p

/-- Free fvars in a premise, respecting the local parameter of `forAll`. -/
def premiseFvarNames (bound : List String) : Premise → List String
  | .freshness fc => patternFvarNames bound fc.term
  | .congruence left right =>
      patternFvarNames bound left ++ patternFvarNames bound right
  | .relationQuery _ args => args.flatMap (patternFvarNames bound)
  | .forAll _ param body => premiseFvarNames (param :: bound) body

/-- Fvars that may escape a successfully evaluated premise as new bindings in
the current generic premise semantics. Freshness is a check only; a `forAll`
parameter and bindings local to its body do not escape. Congruence matches its
target, and relation queries match their argument patterns against rows. -/
def premiseProducedFvarNames (bound : List String) : Premise → List String
  | .freshness _ => []
  | .congruence _ target => patternFvarNames bound target
  | .relationQuery _ args => args.flatMap (patternFvarNames bound)
  | .forAll _ _ _ => []

def premiseForAllParams : Premise → List String
  | .forAll _ param p => param :: premiseForAllParams p
  | _ => []

/-- Anti-wildcard checks on one rule-shaped item (rewrite or equation):
(f) a free pattern variable sharing a name with ANY declared constructor label
    is a silent wildcard / arity misuse / typo — error;
(b) a binder or forAll-param named like a declared label is ambiguous
    authorship — error;
(d) a typeContext name colliding with a declared label — error;
(dangling) a right-hand-side variable bound neither on the left nor by an
    output-capable premise position leaks into outputs as a free atom — error. -/
def validateRulePatterns
    (ctx : String) (knownConstructors : List String)
    (typeContext : List (String × TypeExpr)) (premises : List Premise)
    (left right : Pattern) : List ValidationError :=
  let premPats := premises.flatMap premisePatterns
  let scopeErrors :=
    if ([left, right] ++ premPats).all Pattern.isWellScoped then
      []
    else
      [mkValidationError ctx "rule contains an out-of-scope de Bruijn index"]
  let labelCollisions :=
    ((patternFvarNames [] left ++ patternFvarNames [] right ++
        premises.flatMap (premiseFvarNames [])).eraseDups).flatMap fun n =>
      if knownConstructors.contains n then
        [mkValidationError ctx
          s!"pattern variable `{n}` collides with declared constructor label `{n}` (silent wildcard)"]
      else []
  let binderCollisions :=
    ((patternBinderNames left ++ patternBinderNames right ++
        premPats.flatMap patternBinderNames ++
        premises.flatMap premiseForAllParams).eraseDups).flatMap fun n =>
      if knownConstructors.contains n then
        [mkValidationError ctx
          s!"binder `{n}` shadows declared constructor label `{n}`"]
      else []
  let ctxCollisions :=
    typeContext.filterMap fun (n, _) =>
      if knownConstructors.contains n then
        some (mkValidationError ctx
          s!"typeContext declares `{n}` which is also a constructor label")
      else none
  let boundByLeftOrPremises :=
    patternFvarNames [] left ++ premises.flatMap (premiseProducedFvarNames [])
  let dangling :=
    ((patternFvarNames [] right).eraseDups).flatMap fun n =>
      if boundByLeftOrPremises.contains n || knownConstructors.contains n then []
      else
        [mkValidationError ctx
          s!"right-hand side variable `{n}` is bound neither on the left nor by a premise"]
  scopeErrors ++ labelCollisions ++ binderCollisions ++ ctxCollisions ++ dangling

/-- Validation errors contributed by one rewrite rule in a language.  This is
the proof-facing decomposition of the corresponding `LanguageDef.validate`
component; it uses the same constructor, relation, scope, and wildcard checks. -/
def validateRewrite (lang : LanguageDef) (rewrite : RewriteRule) :
    List ValidationError :=
  let knownTypes := lang.typeNames
  let knownConstructors := lang.terms.map (·.label)
  let knownRelations := lang.logic.filterMap fun
    | .relation signature => some signature
    | .ruleText _ | .datalogClause _ => none
  let ctx := s!"rewrite {rewrite.name}"
  let ctxTypeErrs := rewrite.typeContext.flatMap fun (_, type) =>
    validateTypeExpr knownTypes ctx type
  let premiseErrs := validatePremises ctx knownRelations rewrite.premises
  let lhsCtorErrs :=
    validatePatternConstructors (ctx ++ " lhs") lang.terms rewrite.left
  let rhsCtorErrs :=
    validatePatternConstructors (ctx ++ " rhs") lang.terms rewrite.right
  let premiseCtorErrs := (rewrite.premises.flatMap premisePatterns).flatMap
    (validatePatternConstructors (ctx ++ " premise") lang.terms)
  let wildcardErrs :=
    validateRulePatterns ctx knownConstructors rewrite.typeContext
      rewrite.premises rewrite.left rewrite.right
  ctxTypeErrs ++ premiseErrs ++ lhsCtorErrs ++ rhsCtorErrs ++
    premiseCtorErrs ++ wildcardErrs

/-- Generic semantic validation for an authored `LanguageDef`.
    This complements macro-time parsing checks with cross-reference checks on
    types, constructor names, relation names, and syntax-parameter usage. -/
def validate (lang : LanguageDef) : List ValidationError :=
  let knownTypes := lang.typeNames
  let knownConstructors := lang.terms.map (·.label)
  let knownRelations := lang.logic.filterMap fun
    | .relation sig => some sig
    | .ruleText _ | .datalogClause _ => none
  let typeDupErrs := duplicateErrors lang.name "type" knownTypes
  let ctorDupErrs := duplicateErrors lang.name "constructor" knownConstructors
  let equationDupErrs := duplicateErrors lang.name "equation" (lang.equations.map (·.name))
  let rewriteDupErrs := duplicateErrors lang.name "rewrite rule" (lang.rewrites.map (·.name))
  let logicDupErrs :=
    duplicateErrors lang.name "logic relation"
      (lang.logic.foldl
        (fun acc decl =>
          match decl with
          | .relation sig => s!"{sig.name}/{sig.argTypes.length}" :: acc
          | .ruleText _ => acc
          | .datalogClause _ => acc)
        [])
  let oracleDupErrs := duplicateErrors lang.name "oracle" (lang.oracles.map (·.name))
  let termErrs :=
    lang.terms.flatMap fun term =>
      let ctx := s!"term {term.label}"
      let paramNames :=
        term.params.flatMap fun param =>
          TermParam.bodyName param :: TermParam.binderNames param
      let categoryErrs :=
        if term.category ∈ knownTypes then [] else [mkValidationError ctx s!"unknown category `{term.category}`"]
      let paramTypeErrs := term.params.flatMap fun param => validateTypeExpr knownTypes ctx (TermParam.typeExpr param)
      let syntaxErrs := validateSyntaxPattern ctx paramNames term.syntaxPattern
      categoryErrs ++ paramTypeErrs ++ syntaxErrs
  let equationErrs :=
    lang.equations.flatMap fun eqn =>
      let ctx := s!"equation {eqn.name}"
      let ctxTypeErrs := eqn.typeContext.flatMap fun (_, ty) => validateTypeExpr knownTypes ctx ty
      let premiseErrs := validatePremises ctx knownRelations eqn.premises
      let lhsCtorErrs := validatePatternConstructors (ctx ++ " lhs") lang.terms eqn.left
      let rhsCtorErrs := validatePatternConstructors (ctx ++ " rhs") lang.terms eqn.right
      let premiseCtorErrs := (eqn.premises.flatMap premisePatterns).flatMap
        (validatePatternConstructors (ctx ++ " premise") lang.terms)
      let wildcardErrs :=
        validateRulePatterns ctx knownConstructors eqn.typeContext eqn.premises eqn.left eqn.right
      ctxTypeErrs ++ premiseErrs ++ lhsCtorErrs ++ rhsCtorErrs ++
        premiseCtorErrs ++ wildcardErrs
  let rewriteErrs := lang.rewrites.flatMap (validateRewrite lang)
  let logicTypeErrs :=
    lang.logic.flatMap fun decl =>
      match decl with
      | .relation sig =>
          sig.argTypes.flatMap fun ty => validateTypeExpr knownTypes s!"logic relation {sig.name}" ty
      | .ruleText _ => []
      | .datalogClause dc =>
          -- Check safety: every head variable appears in body
          if dc.isSafe then []
          else [mkValidationError lang.name s!"unsafe Datalog clause {dc.name}: head variable not in body"]
  let oracleTypeErrs :=
    lang.oracles.flatMap fun oracle =>
      let ctx := s!"oracle {oracle.name}"
      (oracle.argTypes.flatMap fun ty => validateTypeExpr knownTypes ctx ty) ++
      validateTypeExpr knownTypes ctx oracle.resultType
  typeDupErrs ++ ctorDupErrs ++ equationDupErrs ++ rewriteDupErrs ++
  logicDupErrs ++ oracleDupErrs ++
  termErrs ++ equationErrs ++ rewriteErrs ++ logicTypeErrs ++ oracleTypeErrs

/-- Kernel-checkable sufficient conditions for a constructor-signature-only
language to pass the full `LanguageDef.validate` gate. Surface syntax may be
omitted or be the canonical parameter-only pattern; options and congruence
declarations are immaterial to structural validation. -/
theorem validate_eq_nil_of_constructorOnly
    (lang : LanguageDef)
    (hequations : lang.equations = [])
    (hrewrites : lang.rewrites = [])
    (hlogic : lang.logic = [])
    (horacles : lang.oracles = [])
    (htypes : lang.typeNames.Nodup)
    (hconstructors : (lang.terms.map (·.label)).Nodup)
    (hcategory : ∀ term ∈ lang.terms, term.category ∈ lang.typeNames)
    (hparams : ∀ term ∈ lang.terms, ∀ param ∈ term.params,
      ∀ typeName ∈ (TermParam.typeExpr param).baseNames,
        typeName ∈ lang.typeNames)
    (hsyntax : ∀ term ∈ lang.terms,
      term.syntaxPattern = [] ∨
      term.syntaxPattern = term.params.map (fun param =>
        SyntaxItem.nonTerminal (TermParam.bodyName param))) :
    lang.validate = [] := by
  simp [validate, hequations, hrewrites, hlogic, horacles, htypes,
    hconstructors]
  intro term hterm
  refine ⟨hcategory term hterm, ?_, ?_⟩
  · intro param hparam
    apply validateTypeExpr_eq_nil_of_baseNames
    exact hparams term hterm param hparam
  · rcases hsyntax term hterm with hnone | hcanonical
    · rw [hnone]
      exact validateSyntaxPattern_nil _ _
    · rw [hcanonical]
      exact validateSyntaxPattern_termParameters _ _

/-- Kernel-checkable sufficient conditions for a language whose operational
rules are rewrite declarations over an otherwise constructor-only signature.
Each rewrite must pass the same per-rule checks used by `LanguageDef.validate`;
this theorem only decomposes the aggregate gate into reusable obligations. -/
theorem validate_eq_nil_of_constructorAndRewrites
    (lang : LanguageDef)
    (hequations : lang.equations = [])
    (hlogic : lang.logic = [])
    (horacles : lang.oracles = [])
    (htypes : lang.typeNames.Nodup)
    (hconstructors : (lang.terms.map (·.label)).Nodup)
    (hrewrites : (lang.rewrites.map (·.name)).Nodup)
    (hcategory : ∀ term ∈ lang.terms, term.category ∈ lang.typeNames)
    (hparams : ∀ term ∈ lang.terms, ∀ param ∈ term.params,
      ∀ typeName ∈ (TermParam.typeExpr param).baseNames,
        typeName ∈ lang.typeNames)
    (hsyntax : ∀ term ∈ lang.terms,
      term.syntaxPattern = [] ∨
      term.syntaxPattern = term.params.map (fun param =>
        SyntaxItem.nonTerminal (TermParam.bodyName param)))
    (hrewriteValid : ∀ rewrite ∈ lang.rewrites,
      validateRewrite lang rewrite = []) :
    lang.validate = [] := by
  simp [validate, hequations, hlogic, horacles, htypes, hconstructors,
    hrewrites]
  constructor
  · intro term hterm
    refine ⟨hcategory term hterm, ?_, ?_⟩
    · intro param hparam
      apply validateTypeExpr_eq_nil_of_baseNames
      exact hparams term hterm param hparam
    · rcases hsyntax term hterm with hnone | hcanonical
      · rw [hnone]
        exact validateSyntaxPattern_nil _ _
      · rw [hcanonical]
        exact validateSyntaxPattern_termParameters _ _
  · exact hrewriteValid

/-! ## Ordered execution-flow admission

`validate` checks the authored presentation structurally.  The following
second gate checks whether premise execution can obtain every binding before
it is consumed. Relation argument modes are supplied by the execution
profile; they are not guessed from relation names. -/

private structure FlowState where
  termAvail : List String

private def FlowState.addBindings (state : FlowState) (names : List String) : FlowState :=
  let names := names.eraseDups
  { termAvail := (names ++ state.termAvail).eraseDups }

private def missingNames (available required : List String) : List String :=
  required.eraseDups.filter fun name => !(available.contains name)

private def availabilityErrors
    (ctx role : String) (available required : List String) : List ValidationError :=
  (missingNames available required).map fun name =>
    mkValidationError ctx s!"{role} uses `{name}` before it is bound"

/-- Cross-check supplied execution modes against declared relation signatures.
Unused declared relations need no mode, but every supplied mode must name one
unambiguous signature at the exact arity, and duplicate mode declarations fail
closed. -/
private def relationModeErrors
    (lang : LanguageDef) (modes : RelationModeTable) : List ValidationError :=
  let signatures := lang.logic.filterMap fun
    | .relation sig => some sig
    | .ruleText _ | .datalogClause _ => none
  let duplicateModeErrors :=
    duplicateErrors lang.name "relation mode"
      (modes.map fun mode => s!"{mode.relation}/{mode.args.length}")
  let signatureErrors := modes.flatMap fun mode =>
    let matching := signatures.filter fun sig =>
      sig.name == mode.relation && sig.argTypes.length == mode.args.length
    match matching with
    | [_] => []
    | [] =>
        [mkValidationError lang.name
          s!"relation mode `{mode.relation}/{mode.args.length}` has no declared signature"]
    | _ =>
        [mkValidationError lang.name
          s!"relation mode `{mode.relation}/{mode.args.length}` has an ambiguous signature"]
  duplicateModeErrors ++ signatureErrors

private def checkPremiseFlow
    (modes : RelationModeTable) (ruleCtx : String) :
    List Premise → Nat → FlowState → FlowState × List ValidationError
  | [], _, state => (state, [])
  | premise :: rest, index, state =>
      let ctx := s!"{ruleCtx} premise {index}"
      let (nextState, hereErrors) :=
        match premise with
        | .freshness fc =>
            let subjectErrors := availabilityErrors ctx "freshness subject"
              state.termAvail [fc.varName]
            let termErrors := availabilityErrors ctx "freshness term"
              state.termAvail fc.term.freeFvarNames
            (state, subjectErrors ++ termErrors)
        | .congruence source target =>
            let sourceErrors := availabilityErrors ctx "congruence source"
              state.termAvail source.freeFvarNames
            (state.addBindings target.freeFvarNames, sourceErrors)
        | .relationQuery relation args =>
            match modes.lookup? relation args.length with
            | none =>
                (state, [mkValidationError ctx
                  s!"missing or ambiguous relation mode for `{relation}/{args.length}`"])
            | some argModes =>
                let paired := args.zip argModes
                let inputErrors := paired.zipIdx.flatMap fun (entry, argIndex) =>
                  match entry.2 with
                  | .input => availabilityErrors ctx
                      s!"relation `{relation}` input {argIndex}" state.termAvail
                      entry.1.freeFvarNames
                  | .output => []
                let outputs := paired.flatMap fun entry =>
                  match entry.2 with
                  | .input => []
                  | .output => entry.1.freeFvarNames
                (state.addBindings outputs, inputErrors)
        | .forAll collection _ _ =>
            (state, [mkValidationError ctx
              s!"forAll over `{collection}` is unsupported by this execution-flow profile"])
      let (finalState, laterErrors) :=
        checkPremiseFlow modes ruleCtx rest (index + 1) nextState
      (finalState, hereErrors ++ laterErrors)

private def directedRuleFlowErrors
    (modes : RelationModeTable) (ctx : String)
    (premises : List Premise) (left right : Pattern) : List ValidationError :=
  let leftFvars := left.freeFvarNames.eraseDups
  let initial : FlowState :=
    { termAvail := leftFvars }
  let (finalState, premiseErrors) := checkPremiseFlow modes ctx premises 0 initial
  premiseErrors ++ availabilityErrors ctx "right-hand side"
    finalState.termAvail right.freeFvarNames

/-- Ordered binding-flow errors for a selected execution profile. Rewrites
are checked left-to-right; equations are checked in both orientations. -/
def executionFlowErrors (lang : LanguageDef) (modes : RelationModeTable) :
    List ValidationError :=
  lang.rewrites.flatMap (fun rule =>
    directedRuleFlowErrors modes s!"rewrite {rule.name}"
      rule.premises rule.left rule.right) ++
  lang.equations.flatMap (fun equation =>
    directedRuleFlowErrors modes s!"equation {equation.name} (forward)"
      equation.premises equation.left equation.right ++
    directedRuleFlowErrors modes s!"equation {equation.name} (reverse)"
      equation.premises equation.right equation.left)

/-- Structural validation plus ordered, profile-indexed execution-flow
admission. This does not claim source adequacy or proof-checker correctness. -/
def executionAdmissionErrors (lang : LanguageDef) (modes : RelationModeTable) :
    List ValidationError :=
  lang.validate ++ relationModeErrors lang modes ++ lang.executionFlowErrors modes

/-- A language paired with evidence that the executable structural and binding
flow gates pass for a particular relation-mode table. -/
structure FlowAdmitted (modes : RelationModeTable) where
  lang : LanguageDef
  admitted : lang.executionAdmissionErrors modes = []

/-- Fail-closed constructor for the execution-flow wrapper. -/
def admitExecutionFlow? (lang : LanguageDef) (modes : RelationModeTable) :
    Option (FlowAdmitted modes) :=
  if h : lang.executionAdmissionErrors modes = [] then
    some ⟨lang, h⟩
  else
    none

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
        .apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
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

/-! ## Nullary-constructor resolution in authored patterns

The `languageDef!` surface lets rewrite/equation/premise patterns mention
declared NULLARY constructors by bare name (`KDone`, `BlockEmpty`, …). The
pattern elaborator, however, renders every bare identifier as `Pattern.fvar` —
a match-anything pattern variable on a LHS, a free atom on a RHS. That
silently turns every nullary-constructor mention into a wildcard
(probe-verified on `metamathCore`, 2026-07-09: `ReturnDbDone`'s `KDone`
matched every kont and the compile machine dropped statements). This pass
restores the intended reading: an `.fvar n` whose name is the label of a
declared zero-parameter grammar rule becomes the nullary application
`.apply n []`, uniformly in rewrite rules (both sides), equations, and
premise patterns. Names that are NOT nullary labels (tokens, genuine pattern
variables) are untouched.

The `languageDef!` macro applies this pass to every value it builds.
Programmatically-constructed `LanguageDef`s (explicit `.apply` patterns) are
unaffected by construction; the pass is idempotent (`resolveNullary_idem`). -/

mutual

def Pattern.resolveNullary (ls bound : List String) : Pattern → Pattern
  | .bvar k => .bvar k
  | .fvar n =>
      if ls.contains n && !(bound.contains n) then .apply n [] else .fvar n
  | .apply c args => .apply c (Pattern.resolveNullaryList ls bound args)
  | .lambda b body => .lambda b (Pattern.resolveNullary ls bound body)
  | .multiLambda k bs body =>
      .multiLambda k bs (Pattern.resolveNullary ls bound body)
  | .subst a b =>
      .subst (Pattern.resolveNullary ls bound a) (Pattern.resolveNullary ls bound b)
  | .collection ct elems rest =>
      .collection ct (Pattern.resolveNullaryList ls bound elems) rest

def Pattern.resolveNullaryList (ls bound : List String) : List Pattern → List Pattern
  | [] => []
  | p :: r =>
      Pattern.resolveNullary ls bound p :: Pattern.resolveNullaryList ls bound r

end

def Premise.resolveNullary (ls bound : List String) : Premise → Premise
  | .freshness fc =>
      .freshness { fc with term := fc.term.resolveNullary ls bound }
  | .congruence l r =>
      .congruence (l.resolveNullary ls bound) (r.resolveNullary ls bound)
  | .relationQuery rel args =>
      .relationQuery rel (Pattern.resolveNullaryList ls bound args)
  | .forAll collection param p =>
      .forAll collection param (Premise.resolveNullary ls (param :: bound) p)

mutual

/-- Structural condition saying that nullary resolution has no work to do in a
pattern. Collection rest names are explicit metavariable positions and are not
bare constructor occurrences. -/
def Pattern.nullaryClean (ls bound : List String) : Pattern → Bool
  | .bvar _ => true
  | .fvar n => !(ls.contains n && !(bound.contains n))
  | .apply _ args => Pattern.nullaryCleanList ls bound args
  | .lambda _ body => Pattern.nullaryClean ls bound body
  | .multiLambda _ _ body => Pattern.nullaryClean ls bound body
  | .subst body replacement =>
      Pattern.nullaryClean ls bound body && Pattern.nullaryClean ls bound replacement
  | .collection _ elems _ => Pattern.nullaryCleanList ls bound elems

def Pattern.nullaryCleanList (ls bound : List String) : List Pattern → Bool
  | [] => true
  | pattern :: rest =>
      Pattern.nullaryClean ls bound pattern && Pattern.nullaryCleanList ls bound rest

end

/-- Structural cleanliness for every pattern position in a premise, respecting
the parameter (the second `forAll` field) as the scoped name. -/
def Premise.nullaryClean (ls bound : List String) : Premise → Bool
  | .freshness fc => fc.term.nullaryClean ls bound
  | .congruence left right =>
      left.nullaryClean ls bound && right.nullaryClean ls bound
  | .relationQuery _ args => Pattern.nullaryCleanList ls bound args
  | .forAll _ param body => Premise.nullaryClean ls (param :: bound) body

def RewriteRule.resolveNullary (ls : List String) (r : RewriteRule) : RewriteRule :=
  { r with
      premises := r.premises.map (Premise.resolveNullary ls [])
      left := r.left.resolveNullary ls []
      right := r.right.resolveNullary ls [] }

def RewriteRule.nullaryClean (ls : List String) (r : RewriteRule) : Bool :=
  r.premises.all (Premise.nullaryClean ls []) &&
    r.left.nullaryClean ls [] && r.right.nullaryClean ls []

def Equation.resolveNullary (ls : List String) (e : Equation) : Equation :=
  { e with
      premises := e.premises.map (Premise.resolveNullary ls [])
      left := e.left.resolveNullary ls []
      right := e.right.resolveNullary ls [] }

def Equation.nullaryClean (ls : List String) (e : Equation) : Bool :=
  e.premises.all (Premise.nullaryClean ls []) &&
    e.left.nullaryClean ls [] && e.right.nullaryClean ls []

namespace LanguageDef

/-- Labels of declared zero-parameter constructors. -/
def nullaryLabels (lang : LanguageDef) : List String :=
  lang.terms.filterMap (fun r => if r.params.isEmpty then some r.label else none)

/-- Worker with an explicit label set — indexed families sharing `terms`
resolve with a FIXED set, so monotonicity lemmas survive resolution verbatim. -/
def resolveNullaryWith (ls : List String) (lang : LanguageDef) : LanguageDef :=
  { lang with
      rewrites := lang.rewrites.map (RewriteRule.resolveNullary ls)
      equations := lang.equations.map (Equation.resolveNullary ls) }

/-- Resolve bare nullary-constructor names in all authored patterns.

NAMED THEOREM TARGET (match-semantics correspondence — formulation pinned
2026-07-09, dual-seat-confirmed, not yet proved): naked inclusion
`DeclReduces (resolve L) ⊆ DeclReduces L` is FALSE — an RHS-only nullary
mention changes the OUTPUT term. The confirmed package, with
`resolveTerm := Pattern.resolveNullary (nullaryLabels L) []` and `p` called
SATURATED when `resolveTerm p = p`:
(backward) for saturated `p`, `DeclReduces (resolve L) p q →
  ∃ q₀, DeclReduces L p q₀ ∧ resolveTerm q₀ = q`;
(forward, intended instances) an `L`-step whose match and premise solutions
  assign every nullary pseudo-variable its constant maps to a
  `resolve L`-step between the resolved endpoints;
(closure) `resolveTerm` is idempotent, so the saturated fragment is
  `resolve L`-closed and `resolveTerm` is a functional bisimulation
  (a P_ω-coalgebra homomorphism) between `L`-on-intended-matches and
  `resolve L`. -/
def resolveNullaryPatterns (lang : LanguageDef) : LanguageDef :=
  resolveNullaryWith lang.nullaryLabels lang

/-- Executable, structural criterion for a definition on which the whole
nullary-resolution pass is the identity. -/
def resolveNullaryClean (lang : LanguageDef) : Bool :=
  lang.rewrites.all (RewriteRule.nullaryClean lang.nullaryLabels) &&
    lang.equations.all (Equation.nullaryClean lang.nullaryLabels)

end LanguageDef

/-- Diagnostic (sweep aid): the fvar names in authored rewrite/equation
patterns that collide with nullary-constructor labels in resolvable (unshadowed)
positions — exactly what `resolveNullaryPatterns` rewrites. -/
def LanguageDef.nullaryFvarCollisions (lang : LanguageDef) : List String :=
  let ls := lang.nullaryLabels
  let rec patNames (bound : List String) : Pattern → List String
    | .bvar _ => []
    | .fvar n => if ls.contains n && !(bound.contains n) then [n] else []
    | .apply _ args => args.attach.flatMap (fun ⟨p, _⟩ => patNames bound p)
    | .lambda _ body => patNames bound body
    | .multiLambda _ _ body => patNames bound body
    | .subst a b => patNames bound a ++ patNames bound b
    | .collection _ elems _ => elems.attach.flatMap (fun ⟨p, _⟩ => patNames bound p)
  let rec premiseNames (bound : List String) : Premise → List String
    | .freshness fc => patNames bound fc.term
    | .congruence left right => patNames bound left ++ patNames bound right
    | .relationQuery _ args => args.flatMap (patNames bound)
    | .forAll _ param body => premiseNames (param :: bound) body
  ((lang.rewrites.flatMap (fun r =>
      r.premises.flatMap (premiseNames []) ++ patNames [] r.left ++ patNames [] r.right)) ++
    (lang.equations.flatMap (fun e =>
      e.premises.flatMap (premiseNames []) ++ patNames [] e.left ++ patNames [] e.right))).eraseDups

mutual

theorem Pattern.resolveNullary_idem (ls bound : List String) (p : Pattern) :
    Pattern.resolveNullary ls bound (Pattern.resolveNullary ls bound p)
      = Pattern.resolveNullary ls bound p := by
  cases p with
  | bvar k => rfl
  | fvar n =>
      by_cases h : ls.contains n && !(bound.contains n)
      · simp only [Pattern.resolveNullary, if_pos h, Pattern.resolveNullaryList]
      · simp only [Pattern.resolveNullary, if_neg h]
  | apply c args =>
      simp [Pattern.resolveNullary, Pattern.resolveNullaryList_idem ls bound args]
  | lambda b body =>
      simp [Pattern.resolveNullary, Pattern.resolveNullary_idem ls _ body]
  | multiLambda k bs body =>
      simp [Pattern.resolveNullary, Pattern.resolveNullary_idem ls _ body]
  | subst a b =>
      simp [Pattern.resolveNullary, Pattern.resolveNullary_idem ls bound a,
        Pattern.resolveNullary_idem ls bound b]
  | collection ct elems rest =>
      simp [Pattern.resolveNullary, Pattern.resolveNullaryList_idem ls bound elems]

theorem Pattern.resolveNullaryList_idem (ls bound : List String) (ps : List Pattern) :
    Pattern.resolveNullaryList ls bound (Pattern.resolveNullaryList ls bound ps)
      = Pattern.resolveNullaryList ls bound ps := by
  cases ps with
  | nil => rfl
  | cons p r =>
      simp [Pattern.resolveNullaryList, Pattern.resolveNullary_idem ls bound p,
        Pattern.resolveNullaryList_idem ls bound r]

end

mutual

theorem Pattern.resolveNullary_eq_self_of_clean
    (ls bound : List String) (pattern : Pattern)
    (hclean : pattern.nullaryClean ls bound = true) :
    pattern.resolveNullary ls bound = pattern := by
  cases pattern with
  | bvar index => rfl
  | fvar name =>
      simp [Pattern.nullaryClean] at hclean
      simp [Pattern.resolveNullary]
      intro hls
      rcases hclean with hnot | hbound
      · exact (hnot hls).elim
      · exact hbound
  | apply constructor args =>
      simp only [Pattern.nullaryClean] at hclean
      simp [Pattern.resolveNullary,
        Pattern.resolveNullaryList_eq_self_of_clean ls bound args hclean]
  | lambda binder body =>
      simp only [Pattern.nullaryClean] at hclean
      simp [Pattern.resolveNullary,
        Pattern.resolveNullary_eq_self_of_clean ls _ body hclean]
  | multiLambda arity binders body =>
      simp only [Pattern.nullaryClean] at hclean
      simp [Pattern.resolveNullary,
        Pattern.resolveNullary_eq_self_of_clean ls _ body hclean]
  | subst body replacement =>
      simp only [Pattern.nullaryClean, Bool.and_eq_true] at hclean
      simp [Pattern.resolveNullary,
        Pattern.resolveNullary_eq_self_of_clean ls bound body hclean.1,
        Pattern.resolveNullary_eq_self_of_clean ls bound replacement hclean.2]
  | collection collectionType elems rest =>
      simp only [Pattern.nullaryClean] at hclean
      simp [Pattern.resolveNullary,
        Pattern.resolveNullaryList_eq_self_of_clean ls bound elems hclean]

theorem Pattern.resolveNullaryList_eq_self_of_clean
    (ls bound : List String) (patterns : List Pattern)
    (hclean : Pattern.nullaryCleanList ls bound patterns = true) :
    Pattern.resolveNullaryList ls bound patterns = patterns := by
  cases patterns with
  | nil => rfl
  | cons pattern rest =>
      simp only [Pattern.nullaryCleanList, Bool.and_eq_true] at hclean
      simp [Pattern.resolveNullaryList,
        Pattern.resolveNullary_eq_self_of_clean ls bound pattern hclean.1,
        Pattern.resolveNullaryList_eq_self_of_clean ls bound rest hclean.2]

end


theorem Premise.resolveNullary_eq_self_of_clean
    (ls bound : List String) (premise : Premise)
    (hclean : premise.nullaryClean ls bound = true) :
    premise.resolveNullary ls bound = premise := by
  induction premise generalizing bound with
  | freshness fc =>
      simp only [Premise.nullaryClean] at hclean
      simp [Premise.resolveNullary,
        Pattern.resolveNullary_eq_self_of_clean ls bound fc.term hclean]
  | congruence left right =>
      simp only [Premise.nullaryClean, Bool.and_eq_true] at hclean
      simp [Premise.resolveNullary,
        Pattern.resolveNullary_eq_self_of_clean ls bound left hclean.1,
        Pattern.resolveNullary_eq_self_of_clean ls bound right hclean.2]
  | relationQuery relation args =>
      simp only [Premise.nullaryClean] at hclean
      simp [Premise.resolveNullary,
        Pattern.resolveNullaryList_eq_self_of_clean ls bound args hclean]
  | forAll collection param body ih =>
      simp only [Premise.nullaryClean] at hclean
      simp [Premise.resolveNullary, ih (param :: bound) hclean]

private theorem Premise.resolveNullary_map_eq_self_of_all_clean
    (ls bound : List String) (premises : List Premise)
    (hclean : premises.all (Premise.nullaryClean ls bound) = true) :
    premises.map (Premise.resolveNullary ls bound) = premises := by
  induction premises with
  | nil => rfl
  | cons premise rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hclean
      simp [Premise.resolveNullary_eq_self_of_clean ls bound premise hclean.1,
        ih hclean.2]

theorem RewriteRule.resolveNullary_eq_self_of_clean
    (ls : List String) (rule : RewriteRule)
    (hclean : rule.nullaryClean ls = true) :
    rule.resolveNullary ls = rule := by
  cases rule with
  | mk name typeContext premises left right =>
      simp only [RewriteRule.nullaryClean, Bool.and_eq_true] at hclean
      have hpremises := Premise.resolveNullary_map_eq_self_of_all_clean
        ls [] premises hclean.1.1
      simp [RewriteRule.resolveNullary, hpremises,
        Pattern.resolveNullary_eq_self_of_clean ls [] left hclean.1.2,
        Pattern.resolveNullary_eq_self_of_clean ls [] right hclean.2]

theorem Equation.resolveNullary_eq_self_of_clean
    (ls : List String) (equation : Equation)
    (hclean : equation.nullaryClean ls = true) :
    equation.resolveNullary ls = equation := by
  cases equation with
  | mk name typeContext premises left right =>
      simp only [Equation.nullaryClean, Bool.and_eq_true] at hclean
      have hpremises := Premise.resolveNullary_map_eq_self_of_all_clean
        ls [] premises hclean.1.1
      simp [Equation.resolveNullary, hpremises,
        Pattern.resolveNullary_eq_self_of_clean ls [] left hclean.1.2,
        Pattern.resolveNullary_eq_self_of_clean ls [] right hclean.2]

private theorem RewriteRule.resolveNullary_map_eq_self_of_all_clean
    (ls : List String) (rules : List RewriteRule)
    (hclean : rules.all (RewriteRule.nullaryClean ls) = true) :
    rules.map (RewriteRule.resolveNullary ls) = rules := by
  induction rules with
  | nil => rfl
  | cons rule rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hclean
      simp [RewriteRule.resolveNullary_eq_self_of_clean ls rule hclean.1,
        ih hclean.2]

private theorem Equation.resolveNullary_map_eq_self_of_all_clean
    (ls : List String) (equations : List Equation)
    (hclean : equations.all (Equation.nullaryClean ls) = true) :
    equations.map (Equation.resolveNullary ls) = equations := by
  induction equations with
  | nil => rfl
  | cons equation rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hclean
      simp [Equation.resolveNullary_eq_self_of_clean ls equation hclean.1,
        ih hclean.2]

theorem LanguageDef.resolveNullaryPatterns_eq_self_of_clean
    (lang : LanguageDef) (hclean : lang.resolveNullaryClean = true) :
    lang.resolveNullaryPatterns = lang := by
  simp only [LanguageDef.resolveNullaryClean, Bool.and_eq_true] at hclean
  unfold LanguageDef.resolveNullaryPatterns LanguageDef.resolveNullaryWith
  rw [RewriteRule.resolveNullary_map_eq_self_of_all_clean _ _ hclean.1]
  rw [Equation.resolveNullary_map_eq_self_of_all_clean _ _ hclean.2]

theorem Premise.resolveNullary_idem (ls bound : List String) (premise : Premise) :
    Premise.resolveNullary ls bound (Premise.resolveNullary ls bound premise) =
      Premise.resolveNullary ls bound premise := by
  induction premise generalizing bound with
  | freshness fc =>
      simp [Premise.resolveNullary, Pattern.resolveNullary_idem]
  | congruence left right =>
      simp [Premise.resolveNullary, Pattern.resolveNullary_idem]
  | relationQuery relation args =>
      simp [Premise.resolveNullary, Pattern.resolveNullaryList_idem]
  | forAll collection param body ih =>
      simp [Premise.resolveNullary, ih]

theorem RewriteRule.resolveNullary_idem (ls : List String) (rule : RewriteRule) :
    RewriteRule.resolveNullary ls (RewriteRule.resolveNullary ls rule) =
      RewriteRule.resolveNullary ls rule := by
  cases rule
  simp [RewriteRule.resolveNullary, Premise.resolveNullary_idem,
    Pattern.resolveNullary_idem]

theorem Equation.resolveNullary_idem (ls : List String) (equation : Equation) :
    Equation.resolveNullary ls (Equation.resolveNullary ls equation) =
      Equation.resolveNullary ls equation := by
  cases equation
  simp [Equation.resolveNullary, Premise.resolveNullary_idem,
    Pattern.resolveNullary_idem]

theorem LanguageDef.resolveNullaryWith_idem
    (ls : List String) (lang : LanguageDef) :
    LanguageDef.resolveNullaryWith ls (LanguageDef.resolveNullaryWith ls lang) =
      LanguageDef.resolveNullaryWith ls lang := by
  cases lang
  simp [LanguageDef.resolveNullaryWith, RewriteRule.resolveNullary_idem,
    Equation.resolveNullary_idem]

@[simp] theorem LanguageDef.nullaryLabels_resolveNullaryWith
    (ls : List String) (lang : LanguageDef) :
    (LanguageDef.resolveNullaryWith ls lang).nullaryLabels = lang.nullaryLabels := by
  rfl

theorem LanguageDef.resolveNullaryPatterns_idem (lang : LanguageDef) :
    lang.resolveNullaryPatterns.resolveNullaryPatterns = lang.resolveNullaryPatterns := by
  simp [LanguageDef.resolveNullaryPatterns, LanguageDef.resolveNullaryWith_idem]

/-! Scope fixtures: `forAll` parameters are named scoped variables, whereas
lambda names are metadata and actual lambda-bound occurrences are `.bvar`. -/
section ResolveNullaryFixtures

-- Ground data use structural applications; `.fvar` remains a metavariable,
-- even when its spelling happens to look like a source token.
#guard (Pattern.apply "wff" []).isGround
#guard !(Pattern.fvar "wff").isGround
#guard (Pattern.lambda (some "x") (.bvar 0)).isGround
#guard !(Pattern.bvar 0).isGround
#guard !(Pattern.collection .hashBag [] (some "rest")).isGround
#guard (Pattern.lambda none (.bvar 0)).hasCanonicalBinderMetadata
#guard !(Pattern.lambda (some "x") (.bvar 0)).hasCanonicalBinderMetadata
#guard (Pattern.multiLambda 2 [] (.bvar 1)).hasCanonicalBinderMetadata
#guard !(Pattern.multiLambda 2 ["x", "y"] (.bvar 1)).hasCanonicalBinderMetadata

private def forAllCapturePremise : Premise :=
  .forAll "K" "x"
    (.freshness
      { varName := "v"
        term := .apply "Pair" [.fvar "x", .fvar "K"] })

-- `forAll` stores (collection, parameter, body): only the parameter shadows.
-- Freshness terms are traversed, so the unshadowed nullary `K` resolves while
-- the parameter occurrence `x` remains a variable even when `x` is a label.
#guard decide
    (forAllCapturePremise.resolveNullary ["K", "x"] [] =
      .forAll "K" "x"
        (.freshness
          { varName := "v"
            term := .apply "Pair" [.fvar "x", .apply "K" []] }))

private def binderToy : LanguageDef :=
  { name := "ShadowToy"
    types := [TypeDecl.plain "T"]
    terms := [{ label := "x", category := "T", params := [],
                syntaxPattern := [.terminal "x"] }]
    equations := []
    rewrites := [{ name := "r", typeContext := [], premises := []
                   left := .lambda (some "x") (.bvar 0)
                   right := .fvar "x" }] }

-- The actual bound occurrence survives; the free RHS occurrence resolves.
#guard decide ((binderToy.resolveNullaryPatterns.rewrites.map (fun r => (r.left, r.right)))
    = [(.lambda (some "x") (.bvar 0), .apply "x" [])])

private def metadataFvarToy : LanguageDef :=
  { binderToy with
      name := "MetadataFvarToy"
      rewrites := [{ name := "r", typeContext := [], premises := []
                     left := .lambda (some "x") (.fvar "x")
                     right := .apply "x" [] }] }

-- A lambda's authored name is metadata, not a scope for `.fvar`; retaining
-- this wildcard would be a false cleanliness result.
#guard metadataFvarToy.resolveNullaryClean = false
#guard decide ((metadataFvarToy.resolveNullaryPatterns.rewrites.map (fun r => r.left))
    = [.lambda (some "x") (.apply "x" [])])
#guard metadataFvarToy.resolveNullaryPatterns.resolveNullaryClean

-- idempotence, executably, on the fixture
#guard decide
    (binderToy.resolveNullaryPatterns.resolveNullaryPatterns.rewrites.map
        (fun r => (r.left, r.right))
      = binderToy.resolveNullaryPatterns.rewrites.map (fun r => (r.left, r.right)))

-- validate-level negative fixtures: each anti-wildcard error class must fire
private def wildToy (rw : RewriteRule) : LanguageDef :=
  { name := "WildToy"
    types := [TypeDecl.plain "T"]
    terms := [{ label := "K", category := "T", params := [],
                syntaxPattern := [.terminal "K"] },
              { label := "F", category := "T",
                params := [.simple "a" (.base "T")],
                syntaxPattern := [.terminal "F", .nonTerminal "a"] }]
    equations := []
    rewrites := [rw] }

-- (f) free pattern variable colliding with an arity-1 label F = silent wildcard
#guard decide ((wildToy (RewriteRule.mk "r" [] []
    (.apply "K" []) (.fvar "F"))).validate ≠ [])
-- unknown nullary applications are not implicitly accepted as data
#guard decide ((wildToy (RewriteRule.mk "r" [] []
    (.apply "Ghost" []) (.apply "K" []))).validate ≠ [])
-- declared constructors must be used at their exact grammar arity
#guard decide ((wildToy (RewriteRule.mk "r" [] []
    (.apply "F" []) (.apply "K" []))).validate ≠ [])
-- locally nameless schemas cannot contain an out-of-scope de Bruijn index
#guard decide ((wildToy (RewriteRule.mk "r" [] []
    (.bvar 0) (.apply "K" []))).validate ≠ [])
-- constructor validation traverses premise patterns as well as endpoints
#guard decide ((wildToy (RewriteRule.mk "r" []
    [.freshness { varName := "x", term := .apply "Ghost" [] }]
    (.apply "F" [.fvar "x"]) (.fvar "x"))).validate ≠ [])
#guard decide ((wildToy (RewriteRule.mk "r" []
    [.congruence (.apply "F" []) (.fvar "x")]
    (.apply "K" []) (.fvar "x"))).validate ≠ [])
-- (b) binder shadowing a declared label
#guard decide ((wildToy (RewriteRule.mk "r" [] []
    (.lambda (some "K") (.bvar 0)) (.apply "K" []))).validate ≠ [])
-- (b-forAll) the second field is the scoped parameter and must be checked
#guard decide ((wildToy (RewriteRule.mk "r" []
    [.forAll "items" "K" (.congruence (.fvar "K") (.fvar "K"))]
    (.apply "K" []) (.apply "K" []))).validate ≠ [])
-- (d) typeContext colliding with a declared label
#guard decide ((wildToy (RewriteRule.mk "r" [("K", .base "T")] []
    (.apply "K" []) (.apply "K" []))).validate ≠ [])
-- (dangling) RHS variable bound nowhere
#guard decide ((wildToy (RewriteRule.mk "r" [] []
    (.apply "K" []) (.fvar "ghost"))).validate ≠ [])
-- freshness checks do not manufacture bindings for variables in their terms
#guard decide ((wildToy (RewriteRule.mk "r" []
    [.freshness { varName := "v", term := .fvar "ghost" }]
    (.apply "K" []) (.fvar "ghost"))).validate ≠ [])
-- a `forAll` parameter is local to its body and cannot escape to the RHS
#guard decide ((wildToy (RewriteRule.mk "r" []
    [.forAll "items" "x" (.congruence (.fvar "x") (.fvar "x"))]
    (.apply "K" []) (.fvar "x"))).validate ≠ [])
-- congruence target matching may introduce a binding used by the RHS
#guard decide ((wildToy (RewriteRule.mk "r" []
    [.congruence (.fvar "x") (.fvar "y")]
    (.apply "F" [.fvar "x"]) (.fvar "y"))).validate = [])
-- and a fully-clean rule validates
#guard decide ((wildToy (RewriteRule.mk "r" [] []
    (.apply "F" [.fvar "x"]) (.fvar "x"))).validate = [])

private def ioRelationModes : RelationModeTable :=
  [{ relation := "rel", args := [.input, .output] }]

private def modeCheckedFlowToy : LanguageDef :=
  { wildToy (RewriteRule.mk "flow" []
      [.relationQuery "rel" [.fvar "source", .fvar "target"]]
      (.apply "F" [.fvar "source"]) (.fvar "target")) with
    logic := [.relation
      { name := "rel", argTypes := [.base "T", .base "T"] }] }

private def wrongRelationArityToy : LanguageDef :=
  { modeCheckedFlowToy with
    rewrites := [RewriteRule.mk "flow" []
      [.relationQuery "rel" [.fvar "source"]]
      (.apply "F" [.fvar "source"]) (.fvar "source")] }

-- Supplied modes are checked against the declared signature, not inferred from
-- the relation spelling.
#guard modeCheckedFlowToy.validate.isEmpty
#guard !wrongRelationArityToy.validate.isEmpty
#guard (modeCheckedFlowToy.executionAdmissionErrors ioRelationModes).isEmpty
#guard !(modeCheckedFlowToy.executionAdmissionErrors
    (ioRelationModes ++ ioRelationModes)).isEmpty
#guard !(modeCheckedFlowToy.executionAdmissionErrors
    [{ relation := "rel", args := [.input] }]).isEmpty
#guard !(modeCheckedFlowToy.executionAdmissionErrors
    [{ relation := "undeclared", args := [.input, .output] }]).isEmpty

private def duplicateRuleNameToy : LanguageDef :=
  let rule := RewriteRule.mk "duplicate" [] []
    (.apply "F" [.fvar "x"]) (.fvar "x")
  { wildToy rule with rewrites := [rule, rule] }

#guard !duplicateRuleNameToy.validate.isEmpty

-- Freshness subjects and collection rests must be actual matcher bindings.
#guard (wildToy (RewriteRule.mk "flow" []
    [.freshness
      { varName := "x"
        term := .collection .hashBag [] (some "rest") }]
    (.apply "Pair"
      [.fvar "x", .collection .hashBag [] (some "rest")])
    (.collection .hashBag [] (some "rest")))).executionFlowErrors [] |>.isEmpty

-- Lambda display names are metadata ignored by matching, not binding evidence.
#guard !((wildToy (RewriteRule.mk "flow" []
    [.freshness
      { varName := "x"
        term := .collection .hashBag [] (some "rest") }]
    (.apply "Pair"
      [.lambda (some "x") (.bvar 0), .collection .hashBag [] (some "rest")])
    (.collection .hashBag [] (some "rest")))).executionFlowErrors []).isEmpty

-- Congruence consumes its source and produces bindings from its target.
#guard (wildToy (RewriteRule.mk "flow" []
    [.congruence (.fvar "source") (.fvar "target")]
    (.apply "F" [.fvar "source"]) (.fvar "target"))).executionFlowErrors [] |>.isEmpty

-- A mode-declared relation can produce a value that a later freshness check
-- and the RHS consume.
#guard (wildToy (RewriteRule.mk "flow" []
    [.relationQuery "rel" [.fvar "source", .fvar "target"],
     .freshness { varName := "target", term := .fvar "source" }]
    (.apply "F" [.fvar "source"]) (.fvar "target"))).executionFlowErrors
      ioRelationModes |>.isEmpty

-- Freshness consumes no bindings and cannot use names that are wholly absent.
#guard !((wildToy (RewriteRule.mk "flow" []
    [.freshness { varName := "ghost", term := .fvar "missing" }]
    (.apply "K" []) (.apply "K" []))).executionFlowErrors []).isEmpty

-- Premise order matters: a later relation output cannot justify an earlier
-- freshness check.
#guard !((wildToy (RewriteRule.mk "flow" []
    [.freshness { varName := "target", term := .fvar "source" },
     .relationQuery "rel" [.fvar "source", .fvar "target"]]
    (.apply "F" [.fvar "source"]) (.fvar "target"))).executionFlowErrors
      ioRelationModes).isEmpty

-- A congruence source must already be available.
#guard !((wildToy (RewriteRule.mk "flow" []
    [.congruence (.fvar "source") (.fvar "target")]
    (.apply "K" []) (.fvar "target"))).executionFlowErrors []).isEmpty

-- `forAll` remains an explicit unsupported capability in this flow profile.
#guard !((wildToy (RewriteRule.mk "flow" []
    [.forAll "items" "x" (.congruence (.fvar "x") (.fvar "x"))]
    (.apply "K" []) (.apply "K" []))).executionFlowErrors []).isEmpty

private def asymmetricFlowEquation : Equation :=
  { name := "asymmetric"
    typeContext := []
    premises := [.relationQuery "rel" [.fvar "source", .fvar "target"]]
    left := .apply "F" [.fvar "source"]
    right := .apply "F" [.fvar "target"] }

-- Equation admission checks both orientations; this mode assignment supports
-- the forward direction but not the reverse one.
#guard !(({ wildToy (RewriteRule.mk "noop" [] []
      (.apply "K" []) (.apply "K" [])) with
    rewrites := []
    equations := [asymmetricFlowEquation] }).executionFlowErrors
      ioRelationModes).isEmpty

-- The wrapper is fail-closed but intentionally claims only structural and
-- ordered-flow admission, not source adequacy.
#guard ((wildToy (RewriteRule.mk "r" [] []
    (.apply "F" [.fvar "x"]) (.fvar "x"))).admitExecutionFlow? []).isSome
#guard ((wildToy (RewriteRule.mk "r" [] []
    (.apply "K" []) (.fvar "ghost"))).admitExecutionFlow? []).isNone

example : binderToy.resolveNullaryPatterns.resolveNullaryPatterns =
    binderToy.resolveNullaryPatterns :=
  LanguageDef.resolveNullaryPatterns_idem binderToy

end ResolveNullaryFixtures

end Mettapedia.OSLF.MeTTaIL.Syntax
