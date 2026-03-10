import Std.Data.HashMap
import Std.Data.HashSet

namespace Algorithms.GF.CompiledIR

abbrev CatId := String
abbrev FunId := String
abbrev Tok := String

inductive Symbol where
  | nonterminal : CatId → Symbol
  | terminal : Tok → Symbol
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

structure Production where
  lhs : CatId
  rhs : Array Symbol
  funName : FunId
  deriving Repr, DecidableEq, BEq, Inhabited

structure ConcreteSyntax where
  language : String
  startCats : Array CatId
  productions : Array Production
  deriving Repr, Inhabited

private def indexedArray {α} (xs : Array α) : List (Nat × α) :=
  xs.zipIdx.toList.map (fun (x, i) => (i, x))

namespace Production

def isLexical (p : Production) : Bool :=
  p.rhs.size = 1 &&
    match p.rhs[0]? with
    | some (Symbol.terminal _) => true
    | _ => false

end Production

namespace ConcreteSyntax

def indexedProductions (g : ConcreteSyntax) : List (Nat × Production) :=
  indexedArray g.productions

def productionsFor (g : ConcreteSyntax) (lhs : CatId) : List (Nat × Production) :=
  g.indexedProductions.filter (fun (_, p) => p.lhs == lhs)

def lexicalHeads (g : ConcreteSyntax) : Std.HashSet CatId := Id.run do
  let mut acc : Std.HashSet CatId := {}
  for p in g.productions do
    if p.isLexical then
      acc := acc.insert p.lhs
  return acc

end ConcreteSyntax

inductive ExportedTree where
  | node : FunId → List ExportedTree → ExportedTree
  deriving Repr

instance : Inhabited ExportedTree := ⟨.node "" []⟩

inductive SemExpr where
  | ref : Nat → SemExpr
  | node : FunId → List SemExpr → SemExpr
  deriving Repr

instance : Inhabited SemExpr := ⟨.ref 0⟩

mutual
  private def exportedTreeDecEq : (a b : ExportedTree) → Decidable (a = b)
    | .node f xs, .node g ys =>
        if hfg : f = g then
          match exportedTreeListDecEq xs ys with
          | isTrue hxy => isTrue (by cases hfg; cases hxy; rfl)
          | isFalse hxy => isFalse (by intro h; cases h; exact hxy rfl)
        else
          isFalse (by intro h; cases h; exact hfg rfl)

  private def exportedTreeListDecEq : (xs ys : List ExportedTree) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
        match exportedTreeDecEq x y, exportedTreeListDecEq xs ys with
        | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
        | isFalse h1, _ => isFalse (by intro h; cases h; exact h1 rfl)
        | _, isFalse h2 => isFalse (by intro h; cases h; exact h2 rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq ExportedTree := exportedTreeDecEq

namespace ExportedTree

mutual
  def beq : ExportedTree → ExportedTree → Bool
    | .node f xs, .node g ys => f == g && listBeq xs ys

  def listBeq : List ExportedTree → List ExportedTree → Bool
    | [], [] => true
    | x :: xs, y :: ys => beq x y && listBeq xs ys
    | _, _ => false
end

end ExportedTree

instance : BEq ExportedTree := ⟨ExportedTree.beq⟩

mutual
  private def semExprDecEq : (a b : SemExpr) → Decidable (a = b)
    | .ref i, .ref j =>
        if hij : i = j then
          isTrue (by cases hij; rfl)
        else
          isFalse (by intro h; cases h; exact hij rfl)
    | .node f xs, .node g ys =>
        if hfg : f = g then
          match semExprListDecEq xs ys with
          | isTrue hxy => isTrue (by cases hfg; cases hxy; rfl)
          | isFalse hxy => isFalse (by intro h; cases h; exact hxy rfl)
        else
          isFalse (by intro h; cases h; exact hfg rfl)
    | .ref _, .node _ _ => isFalse (by intro h; cases h)
    | .node _ _, .ref _ => isFalse (by intro h; cases h)

  private def semExprListDecEq : (xs ys : List SemExpr) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
        match semExprDecEq x y, semExprListDecEq xs ys with
        | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
        | isFalse h1, _ => isFalse (by intro h; cases h; exact h1 rfl)
        | _, isFalse h2 => isFalse (by intro h; cases h; exact h2 rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq SemExpr := semExprDecEq

namespace SemExpr

def eval : SemExpr → Array ExportedTree → Option ExportedTree
  | .ref i, env => env[i]?
  | .node f args, env => do
      let mut built : List ExportedTree := []
      for arg in args do
        built := built.concat (← eval arg env)
      pure (.node f built)

end SemExpr

inductive NormalizedRhs where
  | terminal : Tok → NormalizedRhs
  | unary : CatId → NormalizedRhs
  | binary : CatId → CatId → NormalizedRhs
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

structure NormalizedProduction where
  lhs : CatId
  rhs : NormalizedRhs
  funName : FunId
  sem : SemExpr
  deriving Repr, DecidableEq

instance : Inhabited NormalizedProduction :=
  ⟨{ lhs := "", rhs := .terminal "", funName := "", sem := .ref 0 }⟩

structure NormalizedGrammar where
  language : String
  startCats : Array CatId
  productions : Array NormalizedProduction
  deriving Repr, Inhabited

namespace NormalizedGrammar

def indexedProductions (g : NormalizedGrammar) : List (Nat × NormalizedProduction) :=
  indexedArray g.productions

def binaryProductions (g : NormalizedGrammar) : List (Nat × NormalizedProduction) :=
  g.indexedProductions.filter fun (_, p) =>
    match p.rhs with
    | NormalizedRhs.binary _ _ => true
    | _ => false

def unaryProductions (g : NormalizedGrammar) : List (Nat × NormalizedProduction) :=
  g.indexedProductions.filter fun (_, p) =>
    match p.rhs with
    | NormalizedRhs.unary _ => true
    | _ => false

def terminalProductions (g : NormalizedGrammar) : List (Nat × NormalizedProduction) :=
  g.indexedProductions.filter fun (_, p) =>
    match p.rhs with
    | NormalizedRhs.terminal _ => true
    | _ => false

def productionsFor (g : NormalizedGrammar) (lhs : CatId) : List (Nat × NormalizedProduction) :=
  g.indexedProductions.filter (fun (_, p) => p.lhs == lhs)

end NormalizedGrammar

end Algorithms.GF.CompiledIR
