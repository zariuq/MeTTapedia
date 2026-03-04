namespace MeTTailCore.MeTTaIL.Syntax

inductive CollType where
  | vec
  | hashBag
  | hashSet
deriving Repr, DecidableEq, BEq

inductive TypeExpr where
  | base : String → TypeExpr
  | arrow : TypeExpr → TypeExpr → TypeExpr
  | multiBinder : TypeExpr → TypeExpr
  | collection : CollType → TypeExpr → TypeExpr
deriving Repr, DecidableEq, BEq

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

inductive TermParam where
  | simple : String → TypeExpr → TermParam
  | abstraction : String → TypeExpr → TermParam
  | multiAbstraction : String → TypeExpr → TermParam
deriving Repr, DecidableEq, BEq

inductive SyntaxItem where
  | terminal : String → SyntaxItem
  | nonTerminal : String → SyntaxItem
  | separator : String → SyntaxItem
  | delimiter : String → String → SyntaxItem
deriving Repr, DecidableEq, BEq

structure GrammarRule where
  label : String
  category : String
  params : List TermParam
  syntaxPattern : List SyntaxItem
deriving Repr, DecidableEq, BEq

inductive Pattern where
  | bvar : Nat → Pattern
  | fvar : String → Pattern
  | apply : String → List Pattern → Pattern
  | lambda : Pattern → Pattern
  | multiLambda : Nat → Pattern → Pattern
  | subst : Pattern → Pattern → Pattern
  | collection : CollType → List Pattern → Option String → Pattern
deriving Repr

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

@[match_pattern] abbrev var (name : String) : Pattern := .fvar name

def mkFVar (name : String) : Pattern := .fvar name

def mkBVar (n : Nat) : Pattern := .bvar n

def mkApp (constructor : String) (args : List Pattern) : Pattern :=
  .apply constructor args

def mkBag (elements : List Pattern) (rest : Option String := none) : Pattern :=
  .collection .hashBag elements rest

end Pattern

structure FreshnessCondition where
  varName : String
  term : Pattern
deriving Repr, DecidableEq, BEq

inductive Premise where
  | freshness : FreshnessCondition → Premise
  | congruence : Pattern → Pattern → Premise
  | relationQuery : String → List Pattern → Premise
deriving Repr, DecidableEq, BEq

structure Equation where
  name : String
  typeContext : List (String × TypeExpr)
  premises : List Premise
  left : Pattern
  right : Pattern
deriving Repr, DecidableEq, BEq

structure RewriteRule where
  name : String
  typeContext : List (String × TypeExpr)
  premises : List Premise
  left : Pattern
  right : Pattern
deriving Repr, DecidableEq, BEq

structure CongruenceCollection where
  collectionType : CollType
deriving Repr, DecidableEq, BEq

structure LanguageDef where
  name : String
  types : List String
  terms : List GrammarRule
  equations : List Equation
  rewrites : List RewriteRule
  congruenceCollections : List CongruenceCollection
deriving Repr

namespace LanguageDef

def allowsCongruenceIn (lang : LanguageDef) (ct : CollType) : Bool :=
  (lang.congruenceCollections.any (fun c => c.collectionType == ct))

end LanguageDef

end MeTTailCore.MeTTaIL.Syntax
