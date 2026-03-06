import MeTTailCore

namespace Algorithms.MeTTa.Simple.Semantics.ConditionSolver

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

structure Interface (σ : Type) where
  eval : σ → Pattern → σ × List Pattern
  applyBindings : Bindings → Pattern → Pattern
  boolOfPattern? : Pattern → Option Bool
  dedupBindings : List Bindings → List Bindings
  leafBindings? : σ → Pattern → Option (List Bindings)

private def trueAtom : Pattern := .apply "True" []
private def falseAtom : Pattern := .apply "False" []

private def boolVarName? : Pattern → Option String
  | .fvar n =>
      if n.isEmpty then none else some n
  | .apply ctor [] =>
      if ctor.startsWith "$" then
        let n := (ctor.drop 1).toString
        if n.isEmpty then none else some n
      else
        none
  | _ => none

private def isBoolAtom : Pattern → Bool
  | .apply "True" [] => true
  | .apply "False" [] => true
  | .apply "true" [] => true
  | .apply "false" [] => true
  | p => (boolVarName? p).isSome

private def isBoolOp (op : String) : Bool :=
  op == "and" || op == "or" || op == "not" || op == "xor"

private def isCmpOp (op : String) : Bool :=
  op == "<" || op == ">" || op == "<=" || op == ">=" ||
  op == "==" || op == "!="

private partial def isBoolSolverCandidate : Pattern → Bool
  | p =>
      if isBoolAtom p then
        true
      else
        match p with
        | .apply op args =>
            if isBoolOp op then
              args.all isBoolSolverCandidate
            else if isCmpOp op && args.length == 2 then
              true
            else if op == "=" && args.length == 2 then
              true
            else
              false
        | _ => false

private def dedupStrings (xs : List String) : List String :=
  (xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).reverse

private partial def collectBoolVars : Pattern → List String
  | p =>
      if let some n := boolVarName? p then
        [n]
      else
        match p with
        | .apply op args =>
            if isBoolOp op then
              dedupStrings (args.foldl (fun acc a => acc ++ collectBoolVars a) [])
            else
              []
        | _ => []

private def dedupPatterns (xs : List Pattern) : List Pattern :=
  (xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).reverse

private partial def collectConstraintLeaves : Pattern → List Pattern
  | p =>
      if isBoolAtom p then
        []
      else
        match p with
        | .apply op args =>
            if isBoolOp op then
              dedupPatterns (args.foldl (fun acc a => acc ++ collectConstraintLeaves a) [])
            else if (isCmpOp op || op == "=") && args.length == 2 then
              [p]
            else
              []
        | _ => []

private partial def isConjOnlyFormula : Pattern → Bool
  | p =>
      if isBoolAtom p then
        true
      else
        match p with
        | .apply op args =>
            if op == "and" then
              !args.isEmpty && args.all isConjOnlyFormula
            else if (isCmpOp op || op == "=") && args.length == 2 then
              true
            else
              false
        | _ => false

private def allBoolAssignments : List String → List Bindings
  | [] => [[]]
  | n :: rest =>
      let tail := allBoolAssignments rest
      tail.flatMap (fun bs => [[(n, trueAtom)] ++ bs, [(n, falseAtom)] ++ bs])

def satisfyingBindingsForBoolCondition (I : Interface σ) (s : σ)
    (cond : Pattern) : Option (List Bindings) :=
  if !isBoolSolverCandidate cond then
    none
  else
    let mergeBindingSets : List Bindings → List Bindings → List Bindings := fun lhs rhs =>
      lhs.flatMap (fun b1 => rhs.filterMap (fun b2 => mergeBindings b1 b2))
    let leaves := collectConstraintLeaves cond
    let baseBindings :=
      if isConjOnlyFormula cond then
        leaves.foldl
          (fun acc leaf =>
            if acc.isEmpty then
              []
            else
              match I.leafBindings? s leaf with
              | some leafBs =>
                  if leafBs.isEmpty then
                    []
                  else
                    mergeBindingSets acc leafBs
              | none =>
                  let (_sLeaf, outLeaf) := I.eval s leaf
                  let okLeaf := outLeaf.any (fun p => I.boolOfPattern? p == some true)
                  if okLeaf then acc else [])
          ([[]] : List Bindings)
      else
        ([[]] : List Bindings)
    let sat :=
      baseBindings.flatMap (fun base =>
        let condBase := I.applyBindings base cond
        let vars := collectBoolVars condBase
        let envs := allBoolAssignments vars
        envs.filterMap (fun boolBs =>
          match mergeBindings base boolBs with
          | none => none
          | some bs =>
              let condSub := I.applyBindings bs cond
              let (_s1, out) := I.eval s condSub
              let ok := out.any (fun p => I.boolOfPattern? p == some true)
              if ok then some bs else none))
    some (I.dedupBindings sat)

end Algorithms.MeTTa.Simple.Semantics.ConditionSolver
