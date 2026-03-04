import MeTTailCore

namespace Algorithms.MeTTa.Simple.Semantics.Dispatch

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

structure Interface (σ : Type) where
  rewrites : σ → List RewriteRule
  eval : σ → Pattern → σ × List Pattern
  evalForRuleEnumeration : σ → Pattern → σ × List Pattern
  applyBindings : Bindings → Pattern → Pattern
  matchPattern : Pattern → Pattern → List Bindings
  normalizePattern : Pattern → Pattern
  dedupBindings : List Bindings → List Bindings

structure CompatRewriteInterface (σ : Type) where
  rewrites : σ → List RewriteRule
  applyBindings : Bindings → Pattern → Pattern
  matchPattern : Pattern → Pattern → List Bindings

private partial def listConcatMap (f : Pattern → List String) :
    List Pattern → List String
  | [] => []
  | x :: xs => f x ++ listConcatMap f xs

private partial def listConcatMapP (f : Pattern → List (List Pattern)) :
    List Pattern → List (List Pattern)
  | [] => []
  | x :: xs => f x ++ listConcatMapP f xs

private partial def lambdaParamNames : Pattern → List String
  | .fvar x => [x]
  | .apply "Expr" elems =>
      listConcatMap lambdaParamNames elems
  | .apply ctor args =>
      let headNames :=
        if ctor.startsWith "$" then
          let name := (ctor.drop 1).toString
          if name.isEmpty then [] else [name]
        else
          []
      headNames ++ (listConcatMap lambdaParamNames args)
  | _ => []

private partial def hasFreeVar : Pattern → Bool
  | .fvar _ => true
  | .bvar _ => false
  | .apply _ args => args.any hasFreeVar
  | .lambda body => hasFreeVar body
  | .multiLambda _ body => hasFreeVar body
  | .subst body repl => hasFreeVar body || hasFreeVar repl
  | .collection _ elems _ => elems.any hasFreeVar

private partial def renameFVarsWith (tag : String) : Pattern → Pattern
  | .fvar x =>
      if x == "constraint" then
        .fvar x
      else
        .fvar (tag ++ x)
  | .bvar n => .bvar n
  | .apply ctor args =>
      let ctor' :=
        if ctor.startsWith "$" then
          let name := (ctor.drop 1).toString
          if name == "constraint" then
            ctor
          else
            "$" ++ tag ++ name
        else
          ctor
      .apply ctor' (args.map (renameFVarsWith tag))
  | .lambda body => .lambda (renameFVarsWith tag body)
  | .multiLambda n body => .multiLambda n (renameFVarsWith tag body)
  | .subst body repl => .subst (renameFVarsWith tag body) (renameFVarsWith tag repl)
  | .collection ct elems rest => .collection ct (elems.map (renameFVarsWith tag)) rest

def compatRewriteStep (I : CompatRewriteInterface σ) (s : σ) (term : Pattern) :
    List Pattern :=
  (I.rewrites s).flatMap fun rule =>
    if rule.premises.isEmpty then
      let tag := s!"__{rule.name}::"
      let leftFresh := renameFVarsWith tag rule.left
      let rightFresh := renameFVarsWith tag rule.right
      (I.matchPattern leftFresh term).map (fun bs => I.applyBindings bs rightFresh)
    else
      []

def enumerateCallByRules (I : Interface σ) (s : σ) (expr : Pattern) :
    σ × List Pattern :=
  match expr with
  | .apply rel _ =>
      (I.rewrites s).foldl
        (fun (acc : σ × List Pattern) rule =>
          let sess := acc.1
          let outAcc := acc.2
          match rule.left with
          | .apply relL _ =>
              if relL == rel then
                let subs := I.matchPattern expr rule.left
                subs.foldl
                  (fun (accBs : σ × List Pattern) bs =>
                    let sessBs := accBs.1
                    let outBs := accBs.2
                    let rhs := I.applyBindings bs rule.right
                    let (sessRhs, rhsOut) := I.evalForRuleEnumeration sessBs rhs
                    (sessRhs, outBs ++ rhsOut))
                  (sess, outAcc)
              else
                (sess, outAcc)
          | _ =>
              (sess, outAcc))
        (s, [])
  | _ =>
      (s, [])

private partial def enumerateArgCallVariants (I : Interface σ) (s : σ)
    (args : List Pattern) : σ × List (List Pattern) :=
  match args with
  | [] => (s, [[]])
  | a :: rest =>
      let (sA, aExtra) := enumerateCallByRules I s a
      let aVals := if aExtra.isEmpty then [a] else aExtra
      let (sR, tails) := enumerateArgCallVariants I sA rest
      let combos :=
        listConcatMapP (fun v => tails.map (fun t => v :: t)) aVals
      (sR, combos)

def refineCallableOutWithArgEnumeration (I : Interface σ) (s : σ)
    (expr : Pattern) (baseOut : List Pattern) : σ × List Pattern :=
  if !(baseOut.any hasFreeVar) then
    (s, baseOut)
  else
    match expr with
    | .apply ctor args =>
        let (sV, combos) := enumerateArgCallVariants I s args
        let variants := combos.map (fun xs => .apply ctor xs)
        let (sE, outAccRev) :=
          variants.foldl
            (fun (acc : σ × List Pattern) v =>
              let sess := acc.1
              let outRev := acc.2
              let (sess', outV0) := I.eval sess v
              let outV := if outV0.isEmpty then [v] else outV0
              (sess', outV.reverse ++ outRev))
            (sV, [])
        let out := outAccRev.reverse
        if out.isEmpty then
          (sE, baseOut)
        else
          (sE, out)
    | _ =>
        (s, baseOut)

partial def evalCallableApply (I : Interface σ) (s : σ)
    (callable : Pattern) (args : List Pattern) : σ × List Pattern :=
  match callable with
  | .apply "partial" [base, bound] =>
      let boundArgs := tupleElems bound
      evalCallableApply I s base (boundArgs ++ args)
  | .apply "|->" [params, body] =>
      let names := lambdaParamNames params
      if names.length != args.length then
        (s, [])
      else
        let env : Bindings := List.zip names args
        let bodySub := I.applyBindings env body
        let (sEval, out0) := I.eval s bodySub
        let (sEnum, extra) := enumerateCallByRules I sEval bodySub
        let out := if extra.isEmpty then out0 else extra
        refineCallableOutWithArgEnumeration I sEnum bodySub out
  | .apply name [] =>
      let call := .apply name args
      let (sEval, out0) := I.eval s call
      let (sEnum, extra) := enumerateCallByRules I sEval call
      let out := if extra.isEmpty then out0 else extra
      refineCallableOutWithArgEnumeration I sEnum call out
  | .apply name boundArgs =>
      evalCallableApply I s (.apply name []) (boundArgs ++ args)
  | .fvar name =>
      let call := .apply name args
      let (sEval, out0) := I.eval s call
      let (sEnum, extra) := enumerateCallByRules I sEval call
      let out := if extra.isEmpty then out0 else extra
      refineCallableOutWithArgEnumeration I sEnum call out
  | _ =>
      (s, [])

def evalGeneratorValues (I : Interface σ) (s : σ) (genExpr : Pattern) :
    σ × List Pattern :=
  let (s1, out0) := I.eval s genExpr
  let (sCall, callOut) :=
    match genExpr with
    | .apply "Expr" (callable :: args) =>
        evalCallableApply I s1 callable args
    | _ =>
        (s1, [])
  let baseOut := if callOut.isEmpty then out0 else callOut
  let (sEnum, extra) := enumerateCallByRules I sCall genExpr
  let out := if extra.isEmpty then baseOut else extra
  (sEnum, out)

def matchHeadArgWithEval (I : Interface σ) (s : σ)
    (patArg termArg : Pattern) : List Bindings :=
  let patN := I.normalizePattern patArg
  let direct := I.matchPattern patN termArg
  if !direct.isEmpty then
    direct
  else
    match patN with
    | .apply rel callArgs =>
        let (_sGen, genOut0) := I.eval s (.apply rel callArgs)
        if genOut0.isEmpty then
          []
        else
          let byOutput :=
            I.dedupBindings <|
            genOut0.flatMap (fun v =>
              (I.matchPattern termArg v) ++ (I.matchPattern v termArg))
          if byOutput.isEmpty then
            []
          else
            let firstArgBindings :=
              match callArgs with
              | outPat :: _ =>
                  match I.normalizePattern outPat with
                  | .fvar x => [[(x, termArg)]]
                  | _ => [[]]
              | [] => [[]]
            byOutput.flatMap
              (fun bOut =>
                firstArgBindings.filterMap (fun bFirst => mergeBindings bOut bFirst))
    | _ =>
        []

def matchHeadArgsWithEval (I : Interface σ) (s : σ)
    (patArgs termArgs : List Pattern) (states : List Bindings) : List Bindings :=
  match patArgs, termArgs with
  | [], [] => states
  | p :: ps, t :: ts =>
      let nextStates :=
        states.flatMap (fun bs =>
          let pSub := I.applyBindings bs p
          let cands := matchHeadArgWithEval I s pSub t
          cands.filterMap (fun b => mergeBindings bs b))
      matchHeadArgsWithEval I s ps ts nextStates
  | _, _ => []

def compatFunctionHeadRewrite (I : Interface σ) (s : σ) (term : Pattern) :
    List Pattern :=
  match term with
  | .apply ctor tArgs =>
      (I.rewrites s).foldl
        (fun acc rule =>
          if rule.premises.isEmpty then
            let tag := s!"__fh::{rule.name}::"
            let leftFresh := renameFVarsWith tag rule.left
            let rightFresh := renameFVarsWith tag rule.right
            match leftFresh with
            | .apply lCtor pArgs =>
                if lCtor == ctor && pArgs.length == tArgs.length then
                  let matchedBs := matchHeadArgsWithEval I s pArgs tArgs [[]]
                  let outs := matchedBs.map (fun bs => I.applyBindings bs rightFresh)
                  acc ++ outs
                else
                  acc
            | _ =>
                acc
          else
            acc)
        []
  | _ => []

private def hasCompatHeadConstraintArg : Pattern → Bool
  | .apply _ (_ :: _) => true
  | .collection _ (_ :: _) _ => true
  | _ => false

def hasCompatHeadConstraintRule (I : Interface σ) (s : σ) (ctor : String) (arity : Nat) : Bool :=
  (I.rewrites s).any (fun rule =>
    if rule.premises.isEmpty then
      match rule.left with
      | .apply lCtor pArgs =>
          lCtor == ctor &&
          pArgs.length == arity &&
          pArgs.any hasCompatHeadConstraintArg
      | _ => false
    else
      false)

def constrainedCallBindingsAndValues (I : Interface σ) (s : σ) (expr : Pattern) :
    σ × List (Bindings × Pattern) :=
  match expr with
  | .apply ctor tArgs =>
      (I.rewrites s).foldl
        (fun (acc : σ × List (Bindings × Pattern)) rule =>
          let sess := acc.1
          let outAcc := acc.2
          if rule.premises.isEmpty then
            let tag := s!"__fh::{rule.name}::"
            let leftFresh := renameFVarsWith tag rule.left
            let rightFresh := renameFVarsWith tag rule.right
            match leftFresh with
            | .apply lCtor pArgs =>
                if lCtor == ctor &&
                   pArgs.length == tArgs.length &&
                   pArgs.any hasCompatHeadConstraintArg then
                  let matchedBs := matchHeadArgsWithEval I sess pArgs tArgs [[]]
                  let (sess', out') :=
                    matchedBs.foldl
                      (fun (accBs : σ × List (Bindings × Pattern)) bs =>
                        let sessBs := accBs.1
                        let outBs := accBs.2
                        let rhs := I.applyBindings bs rightFresh
                        let (sessRhs, vals0) := I.eval sessBs rhs
                        (sessRhs, outBs ++ (vals0.map (fun v => (bs, v)))))
                      (sess, outAcc)
                  (sess', out')
                else
                  (sess, outAcc)
            | _ =>
                (sess, outAcc)
          else
            (sess, outAcc))
        (s, [])
  | _ =>
      (s, [])

end Algorithms.MeTTa.Simple.Semantics.Dispatch
