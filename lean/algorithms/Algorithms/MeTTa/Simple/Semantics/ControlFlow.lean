import MeTTailCore

namespace Algorithms.MeTTa.Simple.Semantics.ControlFlow

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

structure Interface (σ : Type) where
  eval : σ → Pattern → σ × List Pattern
  applyBindings : Bindings → Pattern → Pattern
  matchPattern : Pattern → Pattern → List Bindings
  evalCallableApply : σ → Pattern → List Pattern → σ × List Pattern
  evalGeneratorValues : σ → Pattern → σ × List Pattern
  isTruthy : Pattern → Bool
  patternOfBool : Bool → Pattern

private partial def decodeCasePair? : Pattern → Option (Pattern × Pattern)
  | .apply "Expr" [pat, value] => some (pat, value)
  | .apply ctor [value] =>
      let pat :=
        if ctor.startsWith "$" then
          let name := (ctor.drop 1).toString
          if name.isEmpty then .apply ctor [] else .fvar name
        else
          .apply ctor []
      some (pat, value)
  | _ => none

private partial def decodeCasePairs? : Pattern → Option (List (Pattern × Pattern))
  | .apply "Expr" elems => elems.mapM decodeCasePair?
  | .collection _ elems _ => elems.mapM decodeCasePair?
  | one =>
      match decodeCasePair? one with
      | some p => some [p]
      | none => none

private def isCaseDefaultPattern : Pattern → Bool
  | .apply "Empty" [] => true
  | .apply "empty" [] => true
  | _ => false

private partial def evalCaseValueForBindings (I : Interface σ) (s : σ)
    (value : Pattern) (subs : List Bindings) : σ × List Pattern :=
  subs.foldl
    (fun (acc : σ × List Pattern) bs =>
      let sess := acc.1
      let outAcc := acc.2
      let valueSub := I.applyBindings bs value
      let (sess', out) := I.eval sess valueSub
      let out' := if out.isEmpty then [valueSub] else out
      (sess', outAcc ++ out'))
    (s, [])

partial def evalCaseIntrinsic (I : Interface σ) (s : σ)
    (keyExpr branchesExpr : Pattern) : σ × List Pattern :=
  let (sK, keyOut) := I.eval s keyExpr
  let keys := if keyOut.isEmpty then [keyExpr] else keyOut
  let pairs := decodeCasePairs? branchesExpr
  match pairs with
  | none =>
      (sK, [.apply "case" [keyExpr, branchesExpr]])
  | some rawPairs =>
      let normalPairs := rawPairs.filter (fun kv => !isCaseDefaultPattern kv.1)
      let defaultPair? := rawPairs.find? (fun kv => isCaseDefaultPattern kv.1)
      keys.foldl
        (fun (acc : σ × List Pattern) key =>
          let sess := acc.1
          let outAcc := acc.2
          let rec tryBranches : List (Pattern × Pattern) → σ × List Pattern × Bool
            | [] =>
                match defaultPair? with
                | some (_, defaultVal) =>
                    let (sess', outDef) := I.eval sess defaultVal
                    let out' := if outDef.isEmpty then [defaultVal] else outDef
                    (sess', out', true)
                | none =>
                    (sess, [], false)
            | (pat, value) :: rest =>
                let subs := I.matchPattern pat key
                if subs.isEmpty then
                  tryBranches rest
                else
                  let (sess', outCase) := evalCaseValueForBindings I sess value subs
                  (sess', outCase, true)
          let (sess', outCase, _found) := tryBranches normalPairs
          (sess', outAcc ++ outCase))
        (sK, [])

partial def evalFoldallIntrinsic (I : Interface σ) (s : σ)
    (aggExpr genExpr initExpr : Pattern) : σ × List Pattern :=
  let (sA, aggVals0) := I.eval s aggExpr
  let aggVals :=
    match aggExpr with
    | .apply _ [] => [aggExpr]
    | _ => if aggVals0.isEmpty then [aggExpr] else aggVals0
  let (sG, genVals0) := I.evalGeneratorValues sA genExpr
  let genVals := genVals0
  let (sI, initVals0) := I.eval sG initExpr
  let initVals := if initVals0.isEmpty then [initExpr] else initVals0
  let (sOut, outRev) :=
    aggVals.foldl
      (fun (accOuter : σ × List Pattern) aggVal =>
        let sessOuter := accOuter.1
        let outOuter := accOuter.2
        let (sessAfterInit, foldedForAggRev) :=
          initVals.foldl
            (fun (accInit : σ × List Pattern) initVal =>
              let sessInit := accInit.1
              let outInitRev := accInit.2
              let rec foldGenerator (sessFold : σ) (accVals : List Pattern) :
                  List Pattern → σ × List Pattern
                | [] => (sessFold, accVals)
                | g :: gs =>
                    let (sessStep, nextRev) :=
                      accVals.foldl
                        (fun (accStep : σ × List Pattern) accVal =>
                          let sessStep0 := accStep.1
                          let nextAccRev := accStep.2
                          let (sessStep1, callOut) := I.evalCallableApply sessStep0 aggVal [accVal, g]
                          let nextVals := if callOut.isEmpty then [accVal] else callOut
                          (sessStep1, nextVals.reverse ++ nextAccRev))
                        (sessFold, [])
                    foldGenerator sessStep nextRev.reverse gs
              let (sessFolded, foldedVals) := foldGenerator sessInit [initVal] genVals
              (sessFolded, foldedVals.reverse ++ outInitRev))
            (sessOuter, [])
        (sessAfterInit, foldedForAggRev ++ outOuter))
      (sI, [])
  let out := outRev.reverse
  if out.isEmpty then
    (sOut, [initExpr])
  else
    (sOut, out)

partial def evalForallIntrinsic (I : Interface σ) (s : σ)
    (genExpr checkExpr : Pattern) : σ × List Pattern :=
  let (sG, genVals) := I.evalGeneratorValues s genExpr
  let vals := genVals
  let (sC, checkVals0) := I.eval sG checkExpr
  let checkVals :=
    match checkExpr with
    | .apply _ [] => [checkExpr]
    | _ => if checkVals0.isEmpty then [checkExpr] else checkVals0
  let rec checkAll (sess : σ) : List Pattern → σ × Bool
    | [] => (sess, true)
    | v :: rest =>
        let (sessV, passOne) :=
          checkVals.foldl
            (fun (acc : σ × Bool) checkVal =>
              let sess0 := acc.1
              let okAcc := acc.2
              if okAcc then
                (sess0, true)
              else
                let (sess1, out) := I.evalCallableApply sess0 checkVal [v]
                let ok := out.any I.isTruthy
                (sess1, ok))
            (sess, false)
        if passOne then
          checkAll sessV rest
        else
          (sessV, false)
  let (sF, ok) := checkAll sC vals
  (sF, [I.patternOfBool ok])

end Algorithms.MeTTa.Simple.Semantics.ControlFlow
