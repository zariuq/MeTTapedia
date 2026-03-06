import MeTTailCore
import Algorithms.MeTTa.Simple.Relations

namespace Algorithms.MeTTa.Simple.Semantics.PeTTaCore

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

private def trueAtom : Pattern := .apply "True" []
private def falseAtom : Pattern := .apply "False" []
private def boolAtom (b : Bool) : Pattern := if b then trueAtom else falseAtom

structure Interface (σ : Type) where
  eval : σ → Pattern → σ × List Pattern
  evalDeterministic : σ → Nat → Pattern → σ × Pattern
  evalCallableApply : σ → Pattern → List Pattern → σ × List Pattern
  applyBindings : Bindings → Pattern → Pattern
  matchPattern : Pattern → Pattern → List Bindings
  findBindingsInSpace : σ → Pattern → Pattern → List Bindings
  dedupPatterns : List Pattern → List Pattern
  typeCandidates : σ → Pattern → List Pattern

structure Preservation (I : Interface σ) (P : σ → Prop) where
  eval_preserves :
    ∀ {s : σ} {term : Pattern} {s' : σ} {out : List Pattern},
      I.eval s term = (s', out) →
      P s → P s'
  evalDeterministic_preserves :
    ∀ {s : σ} {fuel : Nat} {term : Pattern} {s' : σ} {out : Pattern},
      I.evalDeterministic s fuel term = (s', out) →
      P s → P s'
  evalCallableApply_preserves :
    ∀ {s : σ} {fn : Pattern} {args : List Pattern} {s' : σ} {out : List Pattern},
      I.evalCallableApply s fn args = (s', out) →
      P s → P s'

private def tupleAt? (xs : List Pattern) (n : Nat) : Option Pattern :=
  match xs.drop n with
  | [] => none
  | x :: _ => some x

mutual
  private partial def alphaEqGo (env : List (String × String)) : Pattern → Pattern → Option (List (String × String))
    | .fvar x, .fvar y =>
        match env.find? (fun p => p.1 == x) with
        | some (_, y') =>
            if y' == y then some env else none
        | none =>
            if env.any (fun p => p.2 == y) then
              none
            else
              some ((x, y) :: env)
    | .bvar n, .bvar m =>
        if n = m then some env else none
    | .apply ca as, .apply cb bs =>
        if ca == cb then
          alphaEqListGo env as bs
        else
          none
    | .lambda a, .lambda b =>
        alphaEqGo env a b
    | .multiLambda na a, .multiLambda nb b =>
        if na = nb then alphaEqGo env a b else none
    | .subst ab ar, .subst bb br =>
        match alphaEqGo env ab bb with
        | some env' => alphaEqGo env' ar br
        | none => none
    | .collection cta ea ra, .collection ctb eb rb =>
        if cta = ctb && ra = rb then
          alphaEqListGo env ea eb
        else
          none
    | _, _ => none

  private partial def alphaEqListGo (env : List (String × String)) :
      List Pattern → List Pattern → Option (List (String × String))
    | [], [] => some env
    | a :: as, b :: bs =>
        match alphaEqGo env a b with
        | some env' => alphaEqListGo env' as bs
        | none => none
    | _, _ => none
end

private def alphaEq (a b : Pattern) : Bool :=
  (alphaEqGo [] a b).isSome

private def isCompositeExpr : Pattern → Bool
  | .apply _ (_ :: _) => true
  | .collection _ (_ :: _) _ => true
  | .lambda _ => true
  | .multiLambda _ _ => true
  | .subst _ _ => true
  | _ => false

private def withQuoteFallback (target : Pattern) (vals : List Pattern) : List Pattern :=
  match vals with
  | [] => [.apply "quote" [target]]
  | [one] =>
      if one = target && isCompositeExpr target then
        [.apply "quote" [target]]
      else
        [one]
  | many => many

private def builtinTypeOf? : String → Option Pattern
  | "+" | "-" | "*" | "/" | "%" | "pow-math" | "log-math" | "min" | "max" =>
      some (.apply "->" [.apply "Number" [], .apply "Number" [], .apply "Number" []])
  | "sqrt-math" | "abs-math" | "trunc-math" | "ceil-math" | "floor-math" | "round-math"
  | "sin-math" | "asin-math" | "cos-math" | "acos-math" | "tan-math" | "atan-math" | "exp" =>
      some (.apply "->" [.apply "Number" [], .apply "Number" []])
  | "<" | "<=" | ">" | ">=" =>
      some (.apply "->" [.apply "Number" [], .apply "Number" [], .apply "Bool" []])
  | "==" | "!=" =>
      some (.apply "->" [.fvar "a", .fvar "b", .apply "Bool" []])
  | "isnan-math" | "isinf-math" =>
      some (.apply "->" [.apply "Number" [], .apply "Bool" []])
  | "and" | "or" | "xor" =>
      some (.apply "->" [.apply "Bool" [], .apply "Bool" [], .apply "Bool" []])
  | "not" =>
      some (.apply "->" [.apply "Bool" [], .apply "Bool" []])
  | "min-atom" | "max-atom" =>
      some (.apply "->" [.fvar "a", .apply "Number" []])
  | _ => none

private def lookupTypeFact (I : Interface σ) (s : σ) (x : Pattern) : Option Pattern :=
  (I.typeCandidates s x).head?

private def getTypeResult (I : Interface σ) (s : σ) (x : Pattern) : Pattern :=
  match x with
  | .fvar name => .fvar name
  | .apply ctor [] =>
      match builtinTypeOf? ctor with
      | some t => t
      | none =>
          if ctor.startsWith "\"" then
            .apply "String" []
          else if ctor == "True" || ctor == "False" || ctor == "true" || ctor == "false" then
            .apply "Bool" []
          else
            match numericOfPattern? x with
            | some _ => .apply "Number" []
            | none =>
                (lookupTypeFact I s x).getD (.apply "%Undefined%" [])
  | .apply _ _ =>
      (lookupTypeFact I s x).getD (.apply "%Undefined%" [])
  | _ =>
      (lookupTypeFact I s x).getD (.apply "%Undefined%" [])

private def evalChain (I : Interface σ) (s : σ) (val pat body : Pattern) : σ × List Pattern :=
  let (s1, vals0) := I.eval s val
  let vals := if vals0.isEmpty then [val] else vals0
  vals.foldl
    (fun (acc : σ × List Pattern) v =>
      let sess := acc.1
      let outAcc := acc.2
      let subs := I.matchPattern pat v
      let (sess', out) :=
        subs.foldl
          (fun (acc2 : σ × List Pattern) bs =>
            let sess2 := acc2.1
            let outAcc2 := acc2.2
            let bodySub := I.applyBindings bs body
            let (sess3, out3) := I.eval sess2 bodySub
            (sess3, outAcc2 ++ out3))
          (sess, [])
      (sess', outAcc ++ out))
    (s1, [])

private def applyFuncToElem (I : Interface σ) (s : σ) (func elem : Pattern) : σ × Pattern :=
  match func with
  | .apply "partial" [fn, bound] =>
      let args := tupleElems bound ++ [elem]
      match fn with
      | .apply name [] =>
          let (s1, out) := I.eval s (.apply name args)
          (s1, out.headD (.apply "quote" [.apply name args]))
      | _ =>
          let (s1, out) := I.evalCallableApply s fn args
          (s1, out.headD (.apply "quote" [.apply "Expr" (fn :: args)]))
  | .apply name boundArgs =>
      let (s1, out) := I.eval s (.apply name (boundArgs ++ [elem]))
      (s1, out.headD (.apply "quote" [.apply name (boundArgs ++ [elem])]))
  | _ =>
      let (s1, out) := I.evalCallableApply s func [elem]
      (s1, out.headD (.apply "quote" [.apply "Expr" [func, elem]]))

private def isVarLikePattern : Pattern → Bool
  | .fvar _ => true
  | .apply ctor [] =>
      ctor.startsWith "$" && !(ctor.drop 1).isEmpty
  | _ => false

private def isTruthy : Pattern → Bool
  | .apply "True" [] => true
  | .apply "true" [] => true
  | .apply "False" [] => false
  | .apply "false" [] => false
  | .apply "()" [] => false
  | .apply "empty" [] => false
  | .apply "Empty" [] => false
  | _ => true

private partial def consListLength? : Pattern → Option Nat
  | .apply "()" [] => some 0
  | .apply "cons" [_head, tail] =>
      (consListLength? tail).map (fun n => n + 1)
  | _ => none

private theorem foldlState_preserves
    (P : σ → Prop)
    (step : (σ × α) → β → (σ × α))
    (hStep : ∀ (st : σ × α) (x : β), P st.1 → P (step st x).1)
    (xs : List β) (st : σ × α) :
    P st.1 → P ((xs.foldl step st).1) := by
  intro hP
  induction xs generalizing st with
  | nil =>
      simpa
  | cons x xs ih =>
      have hStep' : P (step st x).1 := hStep st x hP
      simpa [List.foldl] using ih (step st x) hStep'

private theorem evalBindingsFold_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (bindings : List Bindings) (s : σ) (out0 : List Pattern)
    (bodyOf : Bindings → Pattern) :
    P s →
      P
        ((bindings.foldl
            (fun (acc : σ × List Pattern) bs =>
              let sess := acc.1
              let valsAcc := acc.2
              let bodySub := bodyOf bs
              let (sess', out3) := I.eval sess bodySub
              (sess', valsAcc ++ out3))
            (s, out0)).1) := by
  intro hP
  refine foldlState_preserves P
    (step := fun (acc : σ × List Pattern) bs =>
      let sess := acc.1
      let valsAcc := acc.2
      let bodySub := bodyOf bs
      let (sess', out3) := I.eval sess bodySub
      (sess', valsAcc ++ out3))
    ?_ bindings (s, out0) hP
  intro st bs hSt
  cases st with
  | mk sess valsAcc =>
      simpa using H.eval_preserves
        (s := sess) (term := bodyOf bs) rfl hSt

private theorem evalChain_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (val pat body : Pattern) :
    P s → P (evalChain I s val pat body).1 := by
  intro hP
  unfold evalChain
  have hVals : P (I.eval s val).1 := H.eval_preserves rfl hP
  cases hEval : I.eval s val with
  | mk s1 vals0 =>
      have hS1 : P s1 := by
        simpa [hEval] using hVals
      let vals := if vals0.isEmpty then [val] else vals0
      refine foldlState_preserves P
        (step := fun (acc : σ × List Pattern) v =>
          let sess := acc.1
          let outAcc := acc.2
          let subs := I.matchPattern pat v
          let (sess', out) :=
            subs.foldl
              (fun (acc2 : σ × List Pattern) bs =>
                let sess2 := acc2.1
                let outAcc2 := acc2.2
                let bodySub := I.applyBindings bs body
                let (sess3, out3) := I.eval sess2 bodySub
                (sess3, outAcc2 ++ out3))
              (sess, [])
          (sess', outAcc ++ out))
        ?_ vals (s1, []) hS1
      intro st v hSt
      cases st with
      | mk sess outAcc =>
          simpa using
            evalBindingsFold_preserves I P H (I.matchPattern pat v) sess [] (fun bs => I.applyBindings bs body) hSt

private theorem applyFuncToElem_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (func elem : Pattern) :
    P s → P (applyFuncToElem I s func elem).1 := by
  intro hP
  unfold applyFuncToElem
  cases func with
  | fvar x =>
      simpa using H.evalCallableApply_preserves
        (s := s) (fn := .fvar x) (args := [elem]) rfl hP
  | bvar n =>
      simpa using H.evalCallableApply_preserves
        (s := s) (fn := .bvar n) (args := [elem]) rfl hP
  | apply ctor args =>
      by_cases hPartial : ctor = "partial"
      · subst hPartial
        cases args with
        | nil =>
            simpa using H.eval_preserves
              (s := s) (term := .apply "partial" [elem]) rfl hP
        | cons fn rest =>
            cases rest with
            | nil =>
                simpa using H.eval_preserves
                  (s := s) (term := .apply "partial" [fn, elem]) rfl hP
            | cons bound rest2 =>
                cases rest2 with
                | nil =>
                    cases fn with
                    | apply name fnArgs =>
                        cases fnArgs with
                        | nil =>
                            simpa using H.eval_preserves
                              (s := s) (term := .apply name (tupleElems bound ++ [elem])) rfl hP
                        | cons a as =>
                            simpa using H.evalCallableApply_preserves
                              (s := s) (fn := .apply name (a :: as))
                              (args := tupleElems bound ++ [elem]) rfl hP
                    | fvar x =>
                        simpa using H.evalCallableApply_preserves
                          (s := s) (fn := .fvar x)
                          (args := tupleElems bound ++ [elem]) rfl hP
                    | bvar n =>
                        simpa using H.evalCallableApply_preserves
                          (s := s) (fn := .bvar n)
                          (args := tupleElems bound ++ [elem]) rfl hP
                    | lambda body =>
                        simpa using H.evalCallableApply_preserves
                          (s := s) (fn := .lambda body)
                          (args := tupleElems bound ++ [elem]) rfl hP
                    | multiLambda n body =>
                        simpa using H.evalCallableApply_preserves
                          (s := s) (fn := .multiLambda n body)
                          (args := tupleElems bound ++ [elem]) rfl hP
                    | subst body repl =>
                        simpa using H.evalCallableApply_preserves
                          (s := s) (fn := .subst body repl)
                          (args := tupleElems bound ++ [elem]) rfl hP
                    | collection ct elems rest =>
                        simpa using H.evalCallableApply_preserves
                          (s := s) (fn := .collection ct elems rest)
                          (args := tupleElems bound ++ [elem]) rfl hP
                | cons extra extras =>
                    simpa using H.eval_preserves
                      (s := s) (term := .apply "partial" (fn :: bound :: extra :: extras ++ [elem])) rfl hP
      · simpa [hPartial] using H.eval_preserves
          (s := s) (term := .apply ctor (args ++ [elem])) rfl hP
  | lambda body =>
      simpa using H.evalCallableApply_preserves
        (s := s) (fn := .lambda body) (args := [elem]) rfl hP
  | multiLambda n body =>
      simpa using H.evalCallableApply_preserves
        (s := s) (fn := .multiLambda n body) (args := [elem]) rfl hP
  | subst body repl =>
      simpa using H.evalCallableApply_preserves
        (s := s) (fn := .subst body repl) (args := [elem]) rfl hP
  | collection ct elems rest =>
      simpa using H.evalCallableApply_preserves
        (s := s) (fn := .collection ct elems rest) (args := [elem]) rfl hP

private theorem mapAtomCallable_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (xs func : Pattern) :
    P s →
      P
        ((tupleElems xs).foldl
          (fun (acc : σ × List Pattern) e =>
            let sess := acc.1
            let mappedRev := acc.2
            let (sess', v) := applyFuncToElem I sess func e
            (sess', v :: mappedRev))
          (s, [])).1 := by
  intro hP
  refine foldlState_preserves P
    (step := fun (acc : σ × List Pattern) e =>
      let sess := acc.1
      let mappedRev := acc.2
      let (sess', v) := applyFuncToElem I sess func e
      (sess', v :: mappedRev))
    ?_ (tupleElems xs) (s, []) hP
  intro st e hSt
  cases st with
  | mk sess mappedRev =>
      simpa using applyFuncToElem_preserves I P H sess func e hSt

private theorem mapAtomPattern_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (xs pat body : Pattern) :
    P s →
      P
        ((tupleElems xs).foldl
          (fun (acc : σ × List Pattern) e =>
            let sess := acc.1
            let mappedRev := acc.2
            let bindings := I.matchPattern pat e
            let (sess', vals) :=
              bindings.foldl
                (fun (acc2 : σ × List Pattern) bs =>
                  let sess2 := acc2.1
                  let valsAcc := acc2.2
                  let bodySub := I.applyBindings bs body
                  let (sess3, out3) := I.eval sess2 bodySub
                  (sess3, valsAcc ++ out3))
                (sess, [])
            let mapped :=
              match vals with
              | [] => e
              | _ => vals.headD e
            (sess', mapped :: mappedRev))
          (s, [])).1 := by
  intro hP
  refine foldlState_preserves P
    (step := fun (acc : σ × List Pattern) e =>
      let sess := acc.1
      let mappedRev := acc.2
      let bindings := I.matchPattern pat e
      let (sess', vals) :=
        bindings.foldl
          (fun (acc2 : σ × List Pattern) bs =>
            let sess2 := acc2.1
            let valsAcc := acc2.2
            let bodySub := I.applyBindings bs body
            let (sess3, out3) := I.eval sess2 bodySub
            (sess3, valsAcc ++ out3))
          (sess, [])
      let mapped :=
        match vals with
        | [] => e
        | _ => vals.headD e
      (sess', mapped :: mappedRev))
    ?_ (tupleElems xs) (s, []) hP
  intro st e hSt
  cases st with
  | mk sess mappedRev =>
      simpa using
        evalBindingsFold_preserves I P H (I.matchPattern pat e) sess [] (fun bs => I.applyBindings bs body) hSt

private theorem foldlAtomCallable_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (xs init func : Pattern) :
    P s →
      P
        ((let (sInit, initOut) := I.eval s init
          let initVal := initOut.headD init
          (tupleElems xs).foldl
            (fun (acc : σ × Pattern) e =>
              let sess := acc.1
              let curr := acc.2
              let (sess', out) := I.evalCallableApply sess func [curr, e]
              (sess', out.headD curr))
            (sInit, initVal)).1) := by
  intro hP
  have hInit : P (I.eval s init).1 := H.eval_preserves rfl hP
  cases hInitEval : I.eval s init with
  | mk sInit initOut =>
      have hSInit : P sInit := by
        simpa [hInitEval] using hInit
      refine foldlState_preserves P
        (step := fun (acc : σ × Pattern) e =>
          let sess := acc.1
          let curr := acc.2
          let (sess', out) := I.evalCallableApply sess func [curr, e]
          (sess', out.headD curr))
        ?_ (tupleElems xs) (sInit, initOut.headD init) ?_
      · intro st e hSt
        cases st with
        | mk sess curr =>
            simpa using H.evalCallableApply_preserves
              (s := sess) (fn := func) (args := [curr, e]) rfl hSt
      · simpa [hInitEval]

private theorem foldlAtomPattern_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (xs init accPat xPat body : Pattern) :
    P s →
      P
        ((let (sInit, initOut) := I.eval s init
          let initVal := initOut.headD init
          (tupleElems xs).foldl
            (fun (acc : σ × Pattern) e =>
              let sess := acc.1
              let curr := acc.2
              let bAcc := I.matchPattern accPat curr
              let bX := I.matchPattern xPat e
              let merged := bAcc.flatMap (fun a => bX.filterMap (fun x => mergeBindings a x))
              let (sess', vals) :=
                merged.foldl
                  (fun (acc2 : σ × List Pattern) bs =>
                    let sess2 := acc2.1
                    let valsAcc := acc2.2
                    let bodySub := I.applyBindings bs body
                    let (sess3, out3) := I.eval sess2 bodySub
                    (sess3, valsAcc ++ out3))
                  (sess, [])
              let next := vals.headD curr
              (sess', next))
            (sInit, initVal)).1) := by
  intro hP
  have hInit : P (I.eval s init).1 := H.eval_preserves rfl hP
  cases hInitEval : I.eval s init with
  | mk sInit initOut =>
      have hSInit : P sInit := by
        simpa [hInitEval] using hInit
      refine foldlState_preserves P
        (step := fun (acc : σ × Pattern) e =>
          let sess := acc.1
          let curr := acc.2
          let bAcc := I.matchPattern accPat curr
          let bX := I.matchPattern xPat e
          let merged := bAcc.flatMap (fun a => bX.filterMap (fun x => mergeBindings a x))
          let (sess', vals) :=
            merged.foldl
              (fun (acc2 : σ × List Pattern) bs =>
                let sess2 := acc2.1
                let valsAcc := acc2.2
                let bodySub := I.applyBindings bs body
                let (sess3, out3) := I.eval sess2 bodySub
                (sess3, valsAcc ++ out3))
              (sess, [])
          let next := vals.headD curr
          (sess', next))
        ?_ (tupleElems xs) (sInit, initOut.headD init) ?_
      · intro st e hSt
        cases st with
        | mk sess curr =>
            simpa using
              evalBindingsFold_preserves I P H
                ((I.matchPattern accPat curr).flatMap (fun a => (I.matchPattern xPat e).filterMap (fun x => mergeBindings a x)))
                sess [] (fun bs => I.applyBindings bs body) hSt
      · simpa [hInitEval]

private theorem filterAtomCallable_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (xs func : Pattern) :
    P s →
      P
        ((tupleElems xs).foldl
          (fun (acc : σ × List Pattern) e =>
            let sess := acc.1
            let keptRev := acc.2
            let (sess', out) := I.evalCallableApply sess func [e]
            let keep := out.any isTruthy
            if keep then (sess', e :: keptRev) else (sess', keptRev))
          (s, [])).1 := by
  intro hP
  refine foldlState_preserves P
    (step := fun (acc : σ × List Pattern) e =>
      let sess := acc.1
      let keptRev := acc.2
      let (sess', out) := I.evalCallableApply sess func [e]
      let keep := out.any isTruthy
      if keep then (sess', e :: keptRev) else (sess', keptRev))
    ?_ (tupleElems xs) (s, []) hP
  intro st e hSt
  cases st with
  | mk sess keptRev =>
      cases hStep : I.evalCallableApply sess func [e] with
      | mk s' out =>
          have hPres : P s' :=
            H.evalCallableApply_preserves (s := sess) (fn := func) (args := [e]) hStep hSt
          by_cases hKeep : out.any isTruthy
          · simpa [hStep, hKeep] using hPres
          · simpa [hStep, hKeep] using hPres

private theorem filterAtomPattern_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (xs pat predBody : Pattern) :
    P s →
      P
        ((tupleElems xs).foldl
          (fun (acc : σ × List Pattern) e =>
            let sess := acc.1
            let keptRev := acc.2
            let bindings := I.matchPattern pat e
            let (sess', out) :=
              bindings.foldl
                (fun (acc2 : σ × List Pattern) bs =>
                  let sess2 := acc2.1
                  let outAcc := acc2.2
                  let bodySub := I.applyBindings bs predBody
                  let (sess3, out3) := I.eval sess2 bodySub
                  (sess3, outAcc ++ out3))
                (sess, [])
            let keep := out.any isTruthy
            if keep then (sess', e :: keptRev) else (sess', keptRev))
          (s, [])).1 := by
  intro hP
  refine foldlState_preserves P
    (step := fun (acc : σ × List Pattern) e =>
      let sess := acc.1
      let keptRev := acc.2
      let bindings := I.matchPattern pat e
      let (sess', out) :=
        bindings.foldl
          (fun (acc2 : σ × List Pattern) bs =>
            let sess2 := acc2.1
            let outAcc := acc2.2
            let bodySub := I.applyBindings bs predBody
            let (sess3, out3) := I.eval sess2 bodySub
            (sess3, outAcc ++ out3))
          (sess, [])
      let keep := out.any isTruthy
      if keep then (sess', e :: keptRev) else (sess', keptRev))
    ?_ (tupleElems xs) (s, []) hP
  intro st e hSt
  cases st with
  | mk sess keptRev =>
      have hInner : P
          ((I.matchPattern pat e).foldl
            (fun (acc2 : σ × List Pattern) bs =>
              let sess2 := acc2.1
              let outAcc := acc2.2
              let bodySub := I.applyBindings bs predBody
              let (sess3, out3) := I.eval sess2 bodySub
              (sess3, outAcc ++ out3))
            (sess, [])).1 := by
        simpa using
          evalBindingsFold_preserves I P H (I.matchPattern pat e) sess [] (fun bs => I.applyBindings bs predBody) hSt
      cases hStep :
        (I.matchPattern pat e).foldl
          (fun (acc2 : σ × List Pattern) bs =>
            let sess2 := acc2.1
            let outAcc := acc2.2
            let bodySub := I.applyBindings bs predBody
            let (sess3, out3) := I.eval sess2 bodySub
            (sess3, outAcc ++ out3))
          (sess, []) with
      | mk s' out =>
          have hPres : P s' := by
            simpa [hStep] using hInner
          by_cases hKeep : out.any isTruthy
          · simpa [hStep, hKeep] using hPres
          · simpa [hStep, hKeep] using hPres

private theorem reduce_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (x : Pattern) :
    P s →
      P
        ((let target :=
            match x with
            | .apply "quote" [q] => q
            | other => other
          let (s1, _out) := I.evalDeterministic s 1024 target
          (s1, withQuoteFallback target [] )).1) := by
  intro hP
  simp
  exact H.evalDeterministic_preserves rfl hP

private theorem call_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (x : Pattern) :
    P s →
      P
        ((let target :=
            match x with
            | .apply "quote" [q] => q
            | other => other
          let (s1, _detOut) := I.evalDeterministic s 1024 target
          (s1, withQuoteFallback target [] )).1) := by
  intro hP
  simp
  exact H.evalDeterministic_preserves rfl hP

private theorem eval_preserves_via_det
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (x : Pattern) :
    P s →
      P
        (let target0 :=
            match x with
            | .apply "quote" [q] => q
            | other => other
          let stage := I.evalDeterministic s 1024 target0
          let target :=
            match stage.2 with
            | .apply "quote" [q] => q
            | other => other
          (I.evalDeterministic stage.1 1024 target).1) := by
  intro hP
  let target0 : Pattern :=
    match x with
    | .apply "quote" [q] => q
    | other => other
  let stage := I.evalDeterministic s 1024 target0
  have hStage : P stage.1 := by
    cases hStageEq : stage with
    | mk s1 stageVal =>
        have hDet :
            I.evalDeterministic s 1024 target0 = (s1, stageVal) := by
          simpa [stage] using hStageEq
        simpa [stage, hStageEq] using H.evalDeterministic_preserves hDet hP
  let target : Pattern :=
    match stage.2 with
    | .apply "quote" [q] => q
    | other => other
  cases hDet2 : I.evalDeterministic stage.1 1024 target with
  | mk s2 out2 =>
      have hS2 : P s2 := by
        exact H.evalDeterministic_preserves hDet2 hStage
      simpa [target0, stage, target, hDet2] using hS2

def evalIntrinsic (I : Interface σ) (s : σ) (term : Pattern) : Option (σ × List Pattern) :=
  match term with
  | .apply "unify" [spaceOrA, patOrB, thenExpr, elseExpr] =>
      let isSpace :=
        match spaceOrA with
        | .apply ctor [] => ctor.startsWith "&"
        | _ => false
      if isSpace then
        let bs := I.findBindingsInSpace s spaceOrA patOrB
        let branch := if bs.isEmpty then elseExpr else thenExpr
        let (s1, out0) := I.eval s branch
        let out := if out0.isEmpty then [branch] else out0
        some (s1, out)
      else
        let branch := if spaceOrA == patOrB then thenExpr else elseExpr
        let (s1, out0) := I.eval s branch
        let out := if out0.isEmpty then [branch] else out0
        some (s1, out)
  | .apply "id" [x] =>
      some (s, [x])
  | .apply "cons-atom" [h, t] =>
      some (s, [tupleOfElems (h :: tupleElems t)])
  | .apply "car-atom" [x] =>
      match tupleAt? (tupleElems x) 0 with
      | some h => some (s, [h])
      | none => some (s, [])
  | .apply "cdr-atom" [x] =>
      match tupleElems x with
      | [] => some (s, [])
      | _ :: tl => some (s, [tupleOfElems tl])
  | .apply "first-from-pair" [x] =>
      match tupleAt? (tupleElems x) 0 with
      | some h => some (s, [h])
      | none => some (s, [])
  | .apply "second-from-pair" [x] =>
      match tupleAt? (tupleElems x) 1 with
      | some h => some (s, [h])
      | none => some (s, [])
  | .apply "index-atom" [x, idx] =>
      match intOfPattern? idx with
      | some n =>
          if n < 0 then
            some (s, [])
          else
            match tupleAt? (tupleElems x) n.natAbs with
            | some v => some (s, [v])
            | none => some (s, [])
      | none => some (s, [])
  | .apply "=alpha" [a, b] =>
      some (s, [boolAtom (alphaEq a b)])
  | .apply "is-var" [a] =>
      let b :=
        match a with
        | .fvar _ => true
        | .apply ctor [] =>
            ctor.startsWith "$"
        | _ => false
      some (s, [boolAtom b])
  | .apply "is-space" [a] =>
      let b :=
        match a with
        | .apply ctor [] => ctor.startsWith "&"
        | _ => false
      some (s, [boolAtom b])
  | .apply "get-type" [x] =>
      some (s, [getTypeResult I s x])
  | .apply "map-atom" [xs, func] =>
      let elems := tupleElems xs
      let (s1, outRev) :=
        elems.foldl
          (fun (acc : σ × List Pattern) e =>
            let sess := acc.1
            let mappedRev := acc.2
            let (sess', v) := applyFuncToElem I sess func e
            (sess', v :: mappedRev))
          (s, [])
      some (s1, [tupleOfElems outRev.reverse])
  | .apply "map-atom" [xs, pat, body] =>
      let elems := tupleElems xs
      let (s1, outRev) :=
        elems.foldl
          (fun (acc : σ × List Pattern) e =>
            let sess := acc.1
            let mappedRev := acc.2
            let bindings := I.matchPattern pat e
            let (sess', vals) :=
              bindings.foldl
                (fun (acc2 : σ × List Pattern) bs =>
                  let sess2 := acc2.1
                  let valsAcc := acc2.2
                  let bodySub := I.applyBindings bs body
                  let (sess3, out3) := I.eval sess2 bodySub
                  (sess3, valsAcc ++ out3))
                (sess, [])
            let mapped :=
              match vals with
              | [] => e
              | _ => vals.headD e
            (sess', mapped :: mappedRev))
          (s, [])
      some (s1, [tupleOfElems outRev.reverse])
  | .apply "foldl-atom" [xs, init, func] =>
      let elems := tupleElems xs
      let (sInit, initOut) := I.eval s init
      let initVal := initOut.headD init
      let (s1, accVal) :=
        elems.foldl
          (fun (acc : σ × Pattern) e =>
            let sess := acc.1
            let curr := acc.2
            let (sess', out) := I.evalCallableApply sess func [curr, e]
            (sess', out.headD curr))
          (sInit, initVal)
      some (s1, [accVal])
  | .apply "foldl-atom" [xs, init, accPat, xPat, body] =>
      let elems := tupleElems xs
      let (sInit, initOut) := I.eval s init
      let initVal := initOut.headD init
      let (s1, accVal) :=
        elems.foldl
          (fun (acc : σ × Pattern) e =>
            let sess := acc.1
            let curr := acc.2
            let bAcc := I.matchPattern accPat curr
            let bX := I.matchPattern xPat e
            let merged :=
              bAcc.flatMap (fun a =>
                bX.filterMap (fun x => mergeBindings a x))
            let (sess', vals) :=
              merged.foldl
                (fun (acc2 : σ × List Pattern) bs =>
                  let sess2 := acc2.1
                  let valsAcc := acc2.2
                  let bodySub := I.applyBindings bs body
                  let (sess3, out3) := I.eval sess2 bodySub
                  (sess3, valsAcc ++ out3))
                (sess, [])
            let next := vals.headD curr
            (sess', next))
          (sInit, initVal)
      some (s1, [accVal])
  | .apply "filter-atom" [xs, func] =>
      let elems := tupleElems xs
      let (s1, keepRev) :=
        elems.foldl
          (fun (acc : σ × List Pattern) e =>
            let sess := acc.1
            let keptRev := acc.2
            let (sess', out) := I.evalCallableApply sess func [e]
            let keep := out.any isTruthy
            if keep then (sess', e :: keptRev) else (sess', keptRev))
          (s, [])
      some (s1, [tupleOfElems keepRev.reverse])
  | .apply "filter-atom" [xs, pat, predBody] =>
      let elems := tupleElems xs
      let (s1, keepRev) :=
        elems.foldl
          (fun (acc : σ × List Pattern) e =>
            let sess := acc.1
            let keptRev := acc.2
            let bindings := I.matchPattern pat e
            let (sess', out) :=
              bindings.foldl
                (fun (acc2 : σ × List Pattern) bs =>
                  let sess2 := acc2.1
                  let outAcc := acc2.2
                  let bodySub := I.applyBindings bs predBody
                  let (sess3, out3) := I.eval sess2 bodySub
                  (sess3, outAcc ++ out3))
                (sess, [])
            let keep := out.any isTruthy
            if keep then (sess', e :: keptRev) else (sess', keptRev))
          (s, [])
      some (s1, [tupleOfElems keepRev.reverse])
  | .apply "length" [xs] =>
      let n :=
        match consListLength? xs with
        | some k => k
        | none => (tupleElems xs).length
      some (s, [.apply (toString n) []])
  | .apply "is-expr" [x] =>
      let b := match tupleElems x with | _ :: _ :: _ => true | _ => false
      some (s, [boolAtom b])
  | .apply "quote" [x] =>
      some (s, [x])
  | .apply "reduce" [x] =>
      let target :=
        match x with
        | .apply "quote" [q] => q
        | other => other
      let (s1, out) := I.evalDeterministic s 1024 target
      let out0 := if out == target then [target] else [out]
      some (s1, withQuoteFallback target out0)
  | .apply "eval" [x] =>
      let target0 :=
        match x with
        | .apply "quote" [q] => q
        | other => other
      let (s1, stageVal) := I.evalDeterministic s 1024 target0
      let stage := [stageVal]
      let (s2, outRev) :=
        stage.foldl
          (fun (acc : σ × List Pattern) t =>
            let sess := acc.1
            let valsRev := acc.2
            let target :=
              match t with
              | .apply "quote" [q] => q
              | other => other
            let (sess', detOut) := I.evalDeterministic sess 1024 target
            let out0 := if detOut == target then [target] else [detOut]
            let out := withQuoteFallback target out0
            (sess', out.reverse ++ valsRev))
          (s1, [])
      some (s2, I.dedupPatterns outRev.reverse)
  | .apply "call" [x] =>
      let target :=
        match x with
        | .apply "quote" [q] => q
        | other => other
      let (s1, detOut) := I.evalDeterministic s 1024 target
      let out0 := if detOut == target then [target] else [detOut]
      some (s1, withQuoteFallback target out0)
  | .apply "chain" [val, pat, body] =>
      if isVarLikePattern pat then
        let (s1, out) := evalChain I s val pat body
        some (s1, I.dedupPatterns out)
      else
        none
  | .apply "import!" [_space, _path] =>
      some (s, [trueAtom])
  | .apply "import!" [_space, _path, _opts] =>
      some (s, [trueAtom])
  | _ => none

theorem evalIntrinsic_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (term : Pattern) :
    P s →
      match evalIntrinsic I s term with
      | some res => P res.1
      | none => True := by
  intro hP
  cases term with
  | fvar x =>
      simp [evalIntrinsic]
  | bvar n =>
      simp [evalIntrinsic]
  | lambda body =>
      simp [evalIntrinsic]
  | multiLambda n body =>
      simp [evalIntrinsic]
  | subst body repl =>
      simp [evalIntrinsic]
  | collection ct elems rest =>
      simp [evalIntrinsic]
  | apply ctor args =>
      cases args with
      | nil =>
          simp [evalIntrinsic]
      | cons a rest =>
          cases rest with
          | nil =>
              by_cases hId : ctor = "id"
              · subst hId; simp [evalIntrinsic, hP]
              · by_cases hCar : ctor = "car-atom"
                · subst hCar
                  cases hAt : tupleAt? (tupleElems a) 0 <;> simp [evalIntrinsic, hAt, hP]
                · by_cases hCdr : ctor = "cdr-atom"
                  · subst hCdr
                    cases hElems : tupleElems a <;> simp [evalIntrinsic, hElems, hP]
                  · by_cases hFirst : ctor = "first-from-pair"
                    · subst hFirst
                      cases hAt : tupleAt? (tupleElems a) 0 <;> simp [evalIntrinsic, hAt, hP]
                    · by_cases hSecond : ctor = "second-from-pair"
                      · subst hSecond
                        cases hAt : tupleAt? (tupleElems a) 1 <;> simp [evalIntrinsic, hAt, hP]
                      · by_cases hIsVar : ctor = "is-var"
                        · subst hIsVar; simp [evalIntrinsic, hP]
                        · by_cases hIsSpace : ctor = "is-space"
                          · subst hIsSpace; simp [evalIntrinsic, hP]
                          · by_cases hGetType : ctor = "get-type"
                            · subst hGetType; simp [evalIntrinsic, hP]
                            · by_cases hLength : ctor = "length"
                              · subst hLength; simp [evalIntrinsic, hP]
                              · by_cases hIsExpr : ctor = "is-expr"
                                · subst hIsExpr; simp [evalIntrinsic, hP]
                                · by_cases hQuote : ctor = "quote"
                                  · subst hQuote; simp [evalIntrinsic, hP]
                                  · by_cases hReduce : ctor = "reduce"
                                    · subst hReduce
                                      simpa [evalIntrinsic] using
                                        H.evalDeterministic_preserves
                                          (s := s) (fuel := 1024)
                                          (term := match a with | .apply "quote" [q] => q | other => other)
                                          rfl hP
                                    · by_cases hEval : ctor = "eval"
                                      · subst hEval
                                        simpa [evalIntrinsic] using
                                          eval_preserves_via_det I P H s a hP
                                      · by_cases hCall : ctor = "call"
                                        · subst hCall
                                          simpa [evalIntrinsic] using
                                            H.evalDeterministic_preserves
                                              (s := s) (fuel := 1024)
                                              (term := match a with | .apply "quote" [q] => q | other => other)
                                              rfl hP
                                        · simp [evalIntrinsic, hId, hCar, hCdr, hFirst, hSecond,
                                            hIsVar, hIsSpace, hGetType, hLength, hIsExpr, hQuote,
                                            hReduce, hEval, hCall]
          | cons b rest2 =>
              cases rest2 with
              | nil =>
                  by_cases hUnify : ctor = "unify"
                  · subst hUnify
                    by_cases hSpace :
                        (match a with
                        | .apply ctor [] => ctor.startsWith "&"
                        | _ => false)
                    · simpa [evalIntrinsic, hSpace] using H.eval_preserves rfl hP
                    · simpa [evalIntrinsic, hSpace] using H.eval_preserves rfl hP
                  · by_cases hCons : ctor = "cons-atom"
                    · subst hCons; simp [evalIntrinsic, hP]
                    · by_cases hIndex : ctor = "index-atom"
                      · subst hIndex
                        cases hInt : intOfPattern? b with
                        | none =>
                            simp [evalIntrinsic, hInt, hP]
                        | some n =>
                            by_cases hNeg : n < 0
                            · simp [evalIntrinsic, hInt, hNeg, hP]
                            · cases hAt : tupleAt? (tupleElems a) n.natAbs <;>
                                simp [evalIntrinsic, hInt, hNeg, hAt, hP]
                      · by_cases hAlpha : ctor = "=alpha"
                        · subst hAlpha; simp [evalIntrinsic, hP]
                        · by_cases hMap : ctor = "map-atom"
                          · subst hMap
                            simpa [evalIntrinsic] using
                              mapAtomCallable_preserves I P H s a b hP
                          · by_cases hFilter : ctor = "filter-atom"
                            · subst hFilter
                              simpa [evalIntrinsic] using
                                filterAtomCallable_preserves I P H s a b hP
                            · by_cases hImport : ctor = "import!"
                              · subst hImport; simp [evalIntrinsic, hP]
                              · simp [evalIntrinsic, hCons, hIndex, hAlpha, hMap,
                                  hFilter, hImport]
              | cons c rest3 =>
                  cases rest3 with
                  | nil =>
                      by_cases hMap : ctor = "map-atom"
                      · subst hMap
                        simpa [evalIntrinsic] using
                          mapAtomPattern_preserves I P H s a b c hP
                      · by_cases hChain : ctor = "chain"
                        · subst hChain
                          by_cases hVar : isVarLikePattern b
                          · simpa [evalIntrinsic, hVar] using
                              evalChain_preserves I P H s a b c hP
                          · simp [evalIntrinsic, hVar]
                        · by_cases hImport : ctor = "import!"
                          · subst hImport; simp [evalIntrinsic, hP]
                          · by_cases hFilter : ctor = "filter-atom"
                            · subst hFilter
                              simpa [evalIntrinsic] using
                                filterAtomPattern_preserves I P H s a b c hP
                            · by_cases hFold : ctor = "foldl-atom"
                              · subst hFold
                                simpa [evalIntrinsic] using
                                  foldlAtomCallable_preserves I P H s a b c hP
                              · simp [evalIntrinsic, hMap, hChain, hImport, hFilter, hFold]
                  | cons d rest4 =>
                      cases rest4 with
                      | nil =>
                          by_cases hUnify : ctor = "unify"
                          · subst hUnify
                            by_cases hSpace :
                                (match a with
                                | .apply ctor [] => ctor.startsWith "&"
                                | _ => false)
                            · simpa [evalIntrinsic, hSpace] using H.eval_preserves rfl hP
                            · simpa [evalIntrinsic, hSpace] using H.eval_preserves rfl hP
                          · by_cases hFold : ctor = "foldl-atom"
                            · subst hFold
                              simpa [evalIntrinsic] using
                                foldlAtomPattern_preserves I P H s a b c d hP
                            · simp [evalIntrinsic, hUnify, hFold]
                      | cons e es =>
                          cases es with
                          | nil =>
                              by_cases hFold : ctor = "foldl-atom"
                              · subst hFold
                                simpa [evalIntrinsic] using
                                  foldlAtomPattern_preserves I P H s a b c d e hP
                              · simp [evalIntrinsic, hFold]
                          | cons f fs =>
                              simp [evalIntrinsic]

end Algorithms.MeTTa.Simple.Semantics.PeTTaCore
