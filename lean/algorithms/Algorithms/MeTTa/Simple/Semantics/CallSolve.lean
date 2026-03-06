import MeTTailCore

namespace Algorithms.MeTTa.Simple.Semantics.CallSolve

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

structure Interface (σ : Type) where
  normalizePattern : Pattern → Pattern
  applyBindings : Bindings → Pattern → Pattern
  matchPattern : Pattern → Pattern → List Bindings
  dedupBindings : List Bindings → List Bindings
  hasCompatHeadConstraintRule : σ → String → Nat → Bool
  constrainedCallBindingsAndValues : σ → Pattern → σ × List (Bindings × Pattern)

private def isCallLikePattern : Pattern → Bool
  | .apply _ (_ :: _) => true
  | _ => false

private partial def patternVarNames : Pattern → List String
  | .fvar x => [x]
  | .bvar _ => []
  | .apply _ args =>
      args.foldl (fun acc a => acc ++ patternVarNames a) []
  | .lambda b => patternVarNames b
  | .multiLambda _ b => patternVarNames b
  | .subst b r => patternVarNames b ++ patternVarNames r
  | .collection _ elems _ =>
      elems.foldl (fun acc a => acc ++ patternVarNames a) []

private def dedupNames (xs : List String) : List String :=
  (xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).reverse

private partial def hasAnyFVar : Pattern → Bool
  | .fvar _ => true
  | .bvar _ => false
  | .apply _ args => args.any hasAnyFVar
  | .lambda b => hasAnyFVar b
  | .multiLambda _ b => hasAnyFVar b
  | .subst b r => hasAnyFVar b || hasAnyFVar r
  | .collection _ elems _ => elems.any hasAnyFVar

def shouldAttemptCallConstraintSolve (patTerm valTerm : Pattern) (vals : List Pattern) : Bool :=
  let patVars := dedupNames (patternVarNames patTerm)
  let patVarCount := patVars.length
  isCallLikePattern patTerm &&
    hasAnyFVar patTerm &&
    decide (patVarCount ≤ 3) &&
    !hasAnyFVar valTerm &&
    !vals.isEmpty &&
    decide (vals.length ≤ 8) &&
    vals.all (fun v => !hasAnyFVar v)

def recommendedSolveFuel (patTerm : Pattern) : Nat :=
  let patVars := dedupNames (patternVarNames patTerm)
  match patVars.length with
  | 0 => 16
  | 1 => 64
  | 2 => 96
  | _ => 128

private def resolvedPatternVars (I : Interface σ) (patVars : List String)
    (bs : Bindings) : Option Bindings :=
  let resolved :=
    patVars.filterMap (fun x =>
      let v := I.applyBindings bs (.fvar x)
      if hasAnyFVar v then none else some (x, v))
  if patVars.isEmpty then
    some []
  else if resolved.length == patVars.length then
    some resolved
  else
    none

private def mergeProducedWanted (I : Interface σ)
    (baseBs : Bindings) (produced wanted : Pattern) :
    List Bindings :=
  let byL := I.matchPattern produced wanted
  let byR := I.matchPattern wanted produced
  let byEq := if produced == wanted then ([[]] : List Bindings) else []
  (byL ++ byR ++ byEq).filterMap (fun extraBs =>
    match mergeBindings baseBs extraBs with
    | none => none
    | some merged => some merged)

mutual
  private partial def candidateBindings (I : Interface σ) (fuel : Nat)
      (s : σ) (baseBs : Bindings) (produced wanted : Pattern) :
      σ × List Bindings :=
    let producedN := I.normalizePattern produced
    let wantedN := I.normalizePattern wanted
    let direct := mergeProducedWanted I baseBs producedN wantedN
    if !direct.isEmpty then
      (s, I.dedupBindings direct)
    else if !(hasAnyFVar producedN || hasAnyFVar wantedN) then
      (s, [])
    else
      match fuel with
    | 0 =>
        (s, I.dedupBindings direct)
    | fuel + 1 =>
        let (sStruct, structBs) :=
          match producedN, wantedN with
          | .apply pCtor pArgs, .apply wCtor wArgs =>
              if pCtor == wCtor && pArgs.length == wArgs.length then
                solveArgPairs I fuel s [baseBs] (List.zip pArgs wArgs)
              else
                (s, [])
          | _, _ =>
              (s, [])
        let (sCall, callBs) :=
          match producedN with
          | .apply ctor args =>
              if I.hasCompatHeadConstraintRule sStruct ctor args.length then
                let (sPairs, pairs) := I.constrainedCallBindingsAndValues sStruct producedN
                pairs.foldl
                  (fun (acc : σ × List Bindings) pair =>
                    let sess := acc.1
                    let outAcc := acc.2
                    let stepBs := pair.1
                    let nextTerm := pair.2
                    match mergeBindings baseBs stepBs with
                    | none =>
                        (sess, outAcc)
                    | some merged =>
                        let nextSub := I.applyBindings merged nextTerm
                        let wantedSub := I.applyBindings merged wantedN
                        let (sess', solved) :=
                          candidateBindings I fuel sess merged nextSub wantedSub
                        (sess', outAcc ++ solved))
                  (sPairs, [])
              else
                (sStruct, [])
          | _ =>
              (sStruct, [])
        (sCall, I.dedupBindings (direct ++ structBs ++ callBs))

  private partial def solveArgPairs (I : Interface σ) (fuel : Nat)
      (s : σ) (states : List Bindings) (pairs : List (Pattern × Pattern)) :
      σ × List Bindings :=
    match pairs with
    | [] =>
        (s, states)
    | (pArg, wArg) :: rest =>
        let (sNext, nextStates) :=
          states.foldl
            (fun (acc : σ × List Bindings) bs =>
              let sess := acc.1
              let outAcc := acc.2
              let pSub := I.applyBindings bs pArg
              let wSub := I.applyBindings bs wArg
              let (sess', solved) := candidateBindings I fuel sess bs pSub wSub
              (sess', outAcc ++ solved))
            (s, [])
        solveArgPairs I fuel sNext (I.dedupBindings nextStates) rest
end

def solveCallConstraintBindings (I : Interface σ) (s : σ)
    (patTerm : Pattern) (vals : List Pattern) (fuel : Nat := 4) :
    σ × List Bindings :=
  match I.normalizePattern patTerm with
  | .apply ctor args =>
      if I.hasCompatHeadConstraintRule s ctor args.length then
        let patVars := dedupNames (patternVarNames (I.normalizePattern patTerm))
        let (s', pairs) := I.constrainedCallBindingsAndValues s patTerm
        let (sSolve, rawMerged) :=
          pairs.foldl
            (fun (acc : σ × List Bindings) pair =>
              let sess := acc.1
              let outAcc := acc.2
              let baseBs := pair.1
              let produced := pair.2
              vals.foldl
                (fun (accV : σ × List Bindings) wanted =>
                  let sessV := accV.1
                  let outV := accV.2
                  let producedSub := I.applyBindings baseBs produced
                  let wantedSub := I.applyBindings baseBs wanted
                  let (sessSolved, solved) :=
                    candidateBindings I fuel sessV baseBs producedSub wantedSub
                  (sessSolved, outV ++ solved))
                (sess, outAcc))
            (s', [])
        let projected :=
          rawMerged.filterMap (resolvedPatternVars I patVars)
        (sSolve, I.dedupBindings projected)
      else
        (s, [])
  | _ =>
      (s, [])

end Algorithms.MeTTa.Simple.Semantics.CallSolve
