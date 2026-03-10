import Algorithms.GF.CompiledIR
import Algorithms.GF.Tokenize
import Std.Data.HashMap

namespace Algorithms.GF.CYK

open Algorithms.GF.CompiledIR

structure SpanCatKey where
  cat : CatId
  startPos : Nat
  endPos : Nat
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

inductive ParseTree where
  | leaf : CatId → FunId → Tok → ParseTree
  | unary : CatId → FunId → ParseTree → ParseTree
  | node : CatId → FunId → ParseTree → ParseTree → ParseTree
  deriving Repr, DecidableEq, BEq, Inhabited

namespace ParseTree

def rootCat : ParseTree → CatId
  | .leaf cat _ _ => cat
  | .unary cat _ _ => cat
  | .node cat _ _ _ => cat

end ParseTree

structure Parsed where
  derivation : ParseTree
  recovered : ExportedTree
  deriving Repr, DecidableEq, Inhabited

abbrev ParseTable := Std.HashMap SpanCatKey (Array Parsed)

private def tableGet? (table : ParseTable) (key : SpanCatKey) : Option (Array Parsed) :=
  Std.HashMap.get? table key

private def tableGetD (table : ParseTable) (key : SpanCatKey) : Array Parsed :=
  Std.HashMap.getD table key #[]

private def containsParsed (xs : Array Parsed) (y : Parsed) : Bool :=
  xs.any (fun x => decide (x = y))

private def appendUnique (xs ys : Array Parsed) : Array Parsed :=
  ys.foldl (fun acc y => if containsParsed acc y then acc else acc.push y) xs

private def insertParses (table : ParseTable) (key : SpanCatKey) (newParses : Array Parsed) : ParseTable × Bool :=
  let old := tableGetD table key
  let merged := appendUnique old newParses
  if merged.size = old.size then
    (table, false)
  else
    (table.insert key merged, true)

private def singletonLeaf (lhs : CatId) (funName : FunId) (tok : Tok) (recovered : ExportedTree) : Array Parsed :=
  #[{ derivation := ParseTree.leaf lhs funName tok, recovered := recovered }]

private def singletonUnary (lhs : CatId) (funName : FunId) (child : Parsed) (recovered : ExportedTree) : Array Parsed :=
  #[{ derivation := ParseTree.unary lhs funName child.derivation, recovered := recovered }]

private def singletonNode (lhs : CatId) (funName : FunId) (left right : Parsed) (recovered : ExportedTree) : Array Parsed :=
  #[{ derivation := ParseTree.node lhs funName left.derivation right.derivation, recovered := recovered }]

private def unaryParents (g : NormalizedGrammar) (childCat : CatId) : List NormalizedProduction :=
  g.unaryProductions.foldr
    (fun (_, prod) acc =>
      match prod.rhs with
      | .unary rhsCat => if rhsCat == childCat then prod :: acc else acc
      | _ => acc)
    []

private partial def closeUnary (g : NormalizedGrammar) (table : ParseTable) (seedKeys : List SpanCatKey) : ParseTable := Id.run do
  let mut table := table
  let mut work := seedKeys
  while !work.isEmpty do
    let key := work.head!
    work := work.tail!
    let childParses := tableGetD table key
    for prod in unaryParents g key.cat do
      let mut built : Array Parsed := #[]
      for child in childParses do
        match SemExpr.eval prod.sem #[child.recovered] with
        | some recovered =>
            built := built ++ singletonUnary prod.lhs prod.funName child recovered
        | none =>
            pure ()
      let parentKey : SpanCatKey := { cat := prod.lhs, startPos := key.startPos, endPos := key.endPos }
      let (table', changed) := insertParses table parentKey built
      table := table'
      if changed then
        work := work ++ [parentKey]
  return table

def parseTable (g : NormalizedGrammar) (tokens : Array Tok) : ParseTable := Id.run do
  let n := tokens.size
  let mut table : ParseTable := {}

  for i in List.range n do
    let tok := tokens[i]!
    let mut inserted : List SpanCatKey := []
    for (_, prod) in g.terminalProductions do
      match prod.rhs with
      | .terminal t =>
          if t == tok then
            match SemExpr.eval prod.sem #[] with
            | some recovered =>
                let key : SpanCatKey := { cat := prod.lhs, startPos := i, endPos := i + 1 }
                let (table', changed) := insertParses table key (singletonLeaf prod.lhs prod.funName tok recovered)
                table := table'
                if changed then
                  inserted := key :: inserted
            | none =>
                pure ()
      | _ =>
          pure ()
    table := closeUnary g table inserted

  for spanLen in List.range (n + 1) do
    if spanLen ≥ 2 then
      for startPos in List.range (n - spanLen + 1) do
        let endPos := startPos + spanLen
        let mut inserted : List SpanCatKey := []
        for split in List.range (spanLen - 1) do
          let mid := startPos + split + 1
          for (_, prod) in g.binaryProductions do
            match prod.rhs with
            | .binary leftCat rightCat =>
                let leftKey : SpanCatKey := { cat := leftCat, startPos := startPos, endPos := mid }
                let rightKey : SpanCatKey := { cat := rightCat, startPos := mid, endPos := endPos }
                match tableGet? table leftKey, tableGet? table rightKey with
                | some leftTrees, some rightTrees =>
                    let mut built : Array Parsed := #[]
                    for lt in leftTrees.toList do
                      for rt in rightTrees.toList do
                        match SemExpr.eval prod.sem #[lt.recovered, rt.recovered] with
                        | some recovered =>
                            built := built ++ singletonNode prod.lhs prod.funName lt rt recovered
                        | none =>
                            pure ()
                    let key : SpanCatKey := { cat := prod.lhs, startPos := startPos, endPos := endPos }
                    let (table', changed) := insertParses table key built
                    table := table'
                    if changed then
                      inserted := key :: inserted
                | _, _ =>
                    pure ()
            | _ =>
                pure ()
        table := closeUnary g table inserted

  return table


def parsesFor (g : NormalizedGrammar) (tokens : Array Tok) (cat : CatId) (startPos endPos : Nat) : Array Parsed :=
  tableGetD (parseTable g tokens) { cat := cat, startPos := startPos, endPos := endPos }


def parsesForStart (g : NormalizedGrammar) (tokens : Array Tok) : Array Parsed :=
  let table := parseTable g tokens
  let keyFor (cat : CatId) : SpanCatKey := { cat := cat, startPos := 0, endPos := tokens.size }
  g.startCats.foldl (fun acc cat => acc ++ tableGetD table (keyFor cat)) #[]


def parseCount (g : NormalizedGrammar) (tokens : Array Tok) : Nat :=
  (parsesForStart g tokens).size

end Algorithms.GF.CYK
