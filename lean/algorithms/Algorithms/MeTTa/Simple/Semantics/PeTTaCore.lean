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
  dedupPatterns : List Pattern → List Pattern
  typeCandidates : σ → Pattern → List Pattern

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

def evalIntrinsic (I : Interface σ) (s : σ) (term : Pattern) : Option (σ × List Pattern) :=
  match term with
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

end Algorithms.MeTTa.Simple.Semantics.PeTTaCore
