import MeTTailCore

namespace Algorithms.MeTTa.Simple.Semantics.PredicateControl

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

structure Interface (σ : Type) where
  eval : σ → Pattern → σ × List Pattern
  findBindingsInSpace : σ → Pattern → Pattern → List Bindings
  applyBindings : Bindings → Pattern → Pattern
  intrinsicStep : σ → Pattern → List Pattern

structure Policy where
  specialHeads : List String := []

def isSpecialHead (policy : Policy) (h : String) : Bool :=
  policy.specialHeads.contains h

private def selfSpaceAtom : Pattern := .apply "&self" []

partial def decodePredicateSpacePattern? (policy : Policy) : Pattern → Option (Pattern × Pattern)
  | .apply "Predicate" [inner] =>
      decodePredicateSpacePattern? policy inner
  | .apply "translatePredicate" [inner] =>
      decodePredicateSpacePattern? policy inner
  | .apply "quote" [inner] =>
      decodePredicateSpacePattern? policy inner
  | .apply "catch" [inner] =>
      decodePredicateSpacePattern? policy inner
  | .apply "catch" [inner, _handler, _fallback] =>
      decodePredicateSpacePattern? policy inner
  | .apply space (relHead :: args) =>
      if space.startsWith "&" then
        match relHead with
        | .apply rel [] =>
            some (.apply space [], .apply rel args)
        | _ => none
      else if isSpecialHead policy space then
        none
      else
        some (selfSpaceAtom, .apply space (relHead :: args))
  | .apply rel args =>
      if rel.startsWith "&" then
        none
      else if isSpecialHead policy rel then
        none
      else
        some (selfSpaceAtom, .apply rel args)
  | _ => none

def isFailurePattern : Pattern → Bool
  | .apply "fail" [] => true
  | .apply "False" [] => true
  | .apply "false" [] => true
  | .apply "empty" [] => true
  | .apply "Empty" [] => true
  | .apply "()" [] => true
  | .apply "Error" _ => true
  | _ => false

def isTruthy : Pattern → Bool
  | .apply "True" [] => true
  | .apply "true" [] => true
  | p => !isFailurePattern p

private def bindPatternValue (env : Bindings) (pat value : Pattern) : Option Bindings :=
  match pat with
  | .fvar x => mergeBindings env [(x, value)]
  | .apply ctor [] =>
      if ctor.startsWith "$" then
        let name := (ctor.drop 1).toString
        if name.isEmpty then
          none
        else
          mergeBindings env [(name, value)]
      else if pat = value then
        some env
      else
        none
  | _ =>
      let subs := matchPatternMeTTa pat value
      subs.findSome? (fun bs => mergeBindings env bs)

private def arithmeticPredicateOp : String → Bool
  | "+" | "-" | "*" | "/" | "%" | "==" | "!=" | "<" | ">" | "<=" | ">=" => true
  | _ => false

partial def evalTranslatePredicateWithEnv (I : Interface σ) (s : σ) (env : Bindings)
    (expr : Pattern) (policy : Policy := {}) : σ × List Pattern × Option Bindings :=
  let exprSub := I.applyBindings env expr
  match decodePredicateSpacePattern? policy exprSub with
  | some (space, pat) =>
      let bindings := I.findBindingsInSpace s space pat
      if bindings.isEmpty then
        (s, [.apply "fail" []], none)
      else
        let out :=
          bindings.foldl
            (fun acc bs =>
              if acc.contains (I.applyBindings bs pat) then acc else (I.applyBindings bs pat) :: acc)
            []
        let env? := bindings.findSome? (fun bs => mergeBindings env bs)
        let merged? := env?.orElse (fun _ => some env)
        (s, out.reverse, merged?)
  | none =>
      match exprSub with
      | .apply "is" [lhs, rhs] =>
          let (s1, rhsOut) := I.eval s rhs
          match rhsOut.head? with
          | none => (s1, [.apply "fail" []], none)
          | some v =>
              match bindPatternValue env lhs v with
              | some env' => (s1, [v], some env')
              | none => (s1, [.apply "fail" []], none)
      | .apply op [lhs, rhs, outPat] =>
          if arithmeticPredicateOp op then
            let lhs' := I.applyBindings env lhs
            let rhs' := I.applyBindings env rhs
            let vals := I.intrinsicStep s (.apply op [lhs', rhs'])
            match vals.head? with
            | none => (s, [.apply "fail" []], none)
            | some v =>
                match bindPatternValue env outPat v with
                | some env' => (s, [v], some env')
                | none => (s, [.apply "fail" []], none)
          else
            let (s1, out) := I.eval s exprSub
            if out.isEmpty || out.all isFailurePattern then
              (s1, out, none)
            else
              (s1, out, some env)
      | _ =>
          let (s1, out) := I.eval s exprSub
          if out.isEmpty || out.all isFailurePattern then
            (s1, out, none)
          else
            (s1, out, some env)

partial def evalPrognWithEnv (I : Interface σ) (s : σ) (env : Bindings)
    (exprs : List Pattern) (policy : Policy := {}) : σ × List Pattern × Bindings :=
  match exprs with
  | [] => (s, [.apply "()" []], env)
  | [last] =>
      let lastSub := I.applyBindings env last
      let (s1, out) := I.eval s lastSub
      (s1, out, env)
  | e :: rest =>
      let eSub := I.applyBindings env e
      match eSub with
      | .apply "translatePredicate" [pred] =>
          let (s1, out, env?) := evalTranslatePredicateWithEnv I s env pred policy
          match env? with
          | some env' => evalPrognWithEnv I s1 env' rest policy
          | none =>
              let failOut := if out.isEmpty then [.apply "fail" []] else out
              (s1, failOut, env)
      | .apply "catch" [inner, _handler, fallback] =>
          match inner with
          | .apply "translatePredicate" [pred] =>
              let (s1, _out, env?) := evalTranslatePredicateWithEnv I s env pred policy
              match env? with
              | some env' => evalPrognWithEnv I s1 env' rest policy
              | none =>
                  let fallbackSub := I.applyBindings env fallback
                  let (s2, outFb) := I.eval s1 fallbackSub
                  if outFb.isEmpty || outFb.all isFailurePattern then
                    let failOut := if outFb.isEmpty then [.apply "fail" []] else outFb
                    (s2, failOut, env)
                  else
                    evalPrognWithEnv I s2 env rest policy
          | _ =>
              let (s1, out) := I.eval s eSub
              if out.isEmpty || out.all isFailurePattern then
                let failOut := if out.isEmpty then [.apply "fail" []] else out
                (s1, failOut, env)
              else
                evalPrognWithEnv I s1 env rest policy
      | _ =>
          let (s1, out) := I.eval s eSub
          if out.isEmpty || out.all isFailurePattern then
            let failOut := if out.isEmpty then [.apply "fail" []] else out
            (s1, failOut, env)
            else
            evalPrognWithEnv I s1 env rest policy

partial def evalProg1WithEnv (I : Interface σ) (s : σ) (env : Bindings)
    (exprs : List Pattern) (policy : Policy := {}) : σ × List Pattern × Bindings :=
  match exprs with
  | [] => (s, [.apply "()" []], env)
  | first :: rest =>
      let firstSub := I.applyBindings env first
      let (s1, firstOut, env1) :=
        match firstSub with
        | .apply "translatePredicate" [pred] =>
            let (sT, outT, env?) := evalTranslatePredicateWithEnv I s env pred policy
            (sT, outT, env?.getD env)
        | _ =>
            let (sT, outT) := I.eval s firstSub
            (sT, outT, env)
      if rest.isEmpty then
        (s1, firstOut, env1)
      else
        let (s2, _restOut, env2) := evalPrognWithEnv I s1 env1 rest policy
        (s2, firstOut, env2)

end Algorithms.MeTTa.Simple.Semantics.PredicateControl
