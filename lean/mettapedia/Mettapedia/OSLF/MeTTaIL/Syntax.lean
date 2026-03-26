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

/-- A grammar rule defines a constructor. `syntaxPattern` is the single
    authored syntax authority and may contain both plain tokens/nonterminals and
    Rust-style metasyntax operators. -/
structure GrammarRule where
  label : String
  category : String
  params : List TermParam
  syntaxPattern : List SyntaxItem
deriving Repr, DecidableEq

/-! ## Patterns (Locally Nameless) -/

/-- Patterns using locally nameless representation.
    - `.bvar n`: bound variable (de Bruijn index `n`, counting from innermost binder)
    - `.fvar x`: free variable / metavariable (named)
    - `.lambda binderName? body`: binder — `binderName?` preserves the authored name
      for export/diagnostics, BVar 0 = the bound variable
    - `.subst body repl`: substitute `repl` for BVar 0 in `body`
    α-equivalent patterns are definitionally equal (binder name is metadata). -/
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
deriving Repr

/-- Premises for rules -/
inductive Premise where
  | freshness : FreshnessCondition → Premise
  | congruence : Pattern → Pattern → Premise
  | relationQuery : String → List Pattern → Premise
  | forAll : String → String → Premise → Premise
deriving Repr

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
  /-- Optional authored spellings for preserving exact surface details that are
      not structurally represented in `Pattern`, such as quoted nullary heads
      or uppercase metavariable spellings. Binder names themselves are already
      stored structurally in `Pattern`. -/
  premiseSurface : List String := []
  leftSurface? : Option String := none
  rightSurface? : Option String := none
deriving Repr

/-! ## Rewrite Rules -/

/-- A rewrite rule defines a directional reduction -/
structure RewriteRule where
  name : String
  typeContext : List (String × TypeExpr)
  premises : List Premise
  left : Pattern
  right : Pattern
  /-- Optional authored spellings for preserving exact surface details that are
      not structurally represented in `Pattern`, such as quoted nullary heads
      or uppercase metavariable spellings. Binder names themselves are already
      stored structurally in `Pattern`. -/
  premiseSurface : List String := []
  leftSurface? : Option String := none
  rightSurface? : Option String := none
deriving Repr

/-! ## Complete Language Definition -/

/-- Signature for a derived relation declaration in the logic layer. -/
structure LogicRelationDecl where
  name : String
  argTypes : List TypeExpr
deriving Repr

/-- Backend-agnostic logic declarations authored alongside rules.
    `ruleText` is intentionally plain text for now so we can migrate authoring
    style first without forcing an immediate backend-specific AST. -/
inductive LogicDecl where
  | relation : LogicRelationDecl → LogicDecl
  | ruleText : String → LogicDecl
deriving Repr

/-- Signature for host/runtime-provided oracle operations. -/
structure OracleDecl where
  name : String
  argTypes : List TypeExpr
  resultType : TypeExpr
deriving Repr

/-- Single authoritative language definition.
    This matches the Rust `language!` design: one `LanguageDef`, with the
    macro/DSL providing the human-facing surface syntax directly. -/
structure LanguageDef where
  name : String
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

namespace TypeExpr

/-- Base type names referenced by a type expression. -/
def baseNames : TypeExpr → List String
  | .base name => [name]
  | .arrow dom cod => baseNames dom ++ baseNames cod
  | .multiBinder inner => baseNames inner
  | .collection _ inner => baseNames inner

end TypeExpr

namespace Pattern

/-- Constructor references occurring in a pattern, paired with arity. -/
partial def constructorRefs : Pattern → List (String × Nat)
  | .bvar _ => []
  | .fvar _ => []
  | pat@(.apply ctor args) =>
      match Pattern.zipArgs? pat with
      | some (first, second) => constructorRefs first ++ constructorRefs second
      | none =>
          match Pattern.mapArgs? pat with
          | some (source, _, body) => constructorRefs source ++ constructorRefs body
          | none =>
              match Pattern.evalArgs? pat with
              | some (scope, repl) => constructorRefs scope ++ constructorRefs repl
              | none => (ctor, args.length) :: (args.flatMap constructorRefs)
  | .lambda _ body => constructorRefs body
  | .multiLambda _ _ body => constructorRefs body
  | .subst body repl => constructorRefs body ++ constructorRefs repl
  | .collection _ elems _ => elems.flatMap constructorRefs

end Pattern

namespace Premise

/-- Relation names referenced by a premise tree. -/
def relationRefs : Premise → List String
  | .freshness _ => []
  | .congruence _ _ => []
  | .relationQuery rel _ => [rel]
  | .forAll _ _ body => relationRefs body

end Premise

namespace LanguageDef

private def mkValidationError (context message : String) : ValidationError :=
  { context, message }

private def duplicateErrors (context what : String) (names : List String) : List ValidationError :=
  let rec go (seen : List String) (remaining : List String) : List ValidationError :=
    match remaining with
    | [] => []
    | x :: xs =>
        let rest := go (x :: seen) xs
        if x ∈ seen then
          mkValidationError context s!"duplicate {what} `{x}`" :: rest
        else
          rest
  go [] names

private def validateTypeExpr (knownTypes : List String) (context : String) (ty : TypeExpr) :
    List ValidationError :=
  (TypeExpr.baseNames ty).flatMap fun name =>
    if name ∈ knownTypes then
      []
    else
      [mkValidationError context s!"unknown type `{name}`"]

mutual

private partial def validateSyntaxPatternOp
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

private partial def validateSyntaxPatternItem
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

private partial def validateSyntaxPatternItems
    (ctx : String)
    (bound : List String)
    (items : List SyntaxItem) : List ValidationError :=
  items.flatMap (validateSyntaxPatternItem ctx bound)

end

private def validateSyntaxPattern
    (ctx : String)
    (boundNames : List String)
    (items : List SyntaxItem) : List ValidationError :=
  validateSyntaxPatternItems ctx boundNames items

private def validatePatternConstructors
    (ctx : String)
    (knownConstructors : List String)
    (checkConstructors : Bool)
    (pat : Pattern) : List ValidationError :=
  if !checkConstructors then
    []
  else
    (Pattern.constructorRefs pat).flatMap fun (ctor, arity) =>
      if arity = 0 ∨ ctor ∈ knownConstructors then
        []
      else
        [mkValidationError ctx s!"unknown constructor `{ctor}`"]

private def validatePremises (ctx : String) (knownRelations : List String) (premises : List Premise) :
    List ValidationError :=
  premises.flatMap fun prem =>
    (Premise.relationRefs prem).flatMap fun rel =>
      if rel ∈ knownRelations then
        []
      else
        [mkValidationError ctx s!"unknown relation `{rel}`"]

/-- Generic semantic validation for an authored `LanguageDef`.
    This complements macro-time parsing checks with cross-reference checks on
    types, constructor names, relation names, and syntax-parameter usage. -/
def validate (lang : LanguageDef) : List ValidationError :=
  let knownTypes := lang.typeNames
  let knownConstructors := lang.terms.map (·.label)
  let knownRelations :=
    lang.logic.foldl
      (fun acc decl =>
        match decl with
        | .relation sig => sig.name :: acc
        | .ruleText _ => acc)
      []
  let checkConstructors := !knownConstructors.isEmpty
  let typeDupErrs := duplicateErrors lang.name "type" knownTypes
  let ctorDupErrs := duplicateErrors lang.name "constructor" knownConstructors
  let logicDupErrs :=
    duplicateErrors lang.name "logic relation"
      (lang.logic.foldl
        (fun acc decl =>
          match decl with
          | .relation sig => s!"{sig.name}/{sig.argTypes.length}" :: acc
          | .ruleText _ => acc)
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
      let lhsCtorErrs := validatePatternConstructors (ctx ++ " lhs") knownConstructors checkConstructors eqn.left
      let rhsCtorErrs := validatePatternConstructors (ctx ++ " rhs") knownConstructors checkConstructors eqn.right
      ctxTypeErrs ++ premiseErrs ++ lhsCtorErrs ++ rhsCtorErrs
  let rewriteErrs :=
    lang.rewrites.flatMap fun rw =>
      let ctx := s!"rewrite {rw.name}"
      let ctxTypeErrs := rw.typeContext.flatMap fun (_, ty) => validateTypeExpr knownTypes ctx ty
      let premiseErrs := validatePremises ctx knownRelations rw.premises
      let lhsCtorErrs := validatePatternConstructors (ctx ++ " lhs") knownConstructors checkConstructors rw.left
      let rhsCtorErrs := validatePatternConstructors (ctx ++ " rhs") knownConstructors checkConstructors rw.right
      ctxTypeErrs ++ premiseErrs ++ lhsCtorErrs ++ rhsCtorErrs
  let logicTypeErrs :=
    lang.logic.flatMap fun decl =>
      match decl with
      | .relation sig =>
          sig.argTypes.flatMap fun ty => validateTypeExpr knownTypes s!"logic relation {sig.name}" ty
      | .ruleText _ => []
  let oracleTypeErrs :=
    lang.oracles.flatMap fun oracle =>
      let ctx := s!"oracle {oracle.name}"
      (oracle.argTypes.flatMap fun ty => validateTypeExpr knownTypes ctx ty) ++
      validateTypeExpr knownTypes ctx oracle.resultType
  typeDupErrs ++ ctorDupErrs ++ logicDupErrs ++ oracleDupErrs ++
  termErrs ++ equationErrs ++ rewriteErrs ++ logicTypeErrs ++ oracleTypeErrs

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

end Mettapedia.OSLF.MeTTaIL.Syntax
