import MeTTailCore

namespace Algorithms.MeTTa.Simple.Semantics.StreamOps

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

structure Interface (σ : Type) where
  evalValues : σ → Pattern → σ × List Pattern

structure Preservation (I : Interface σ) (P : σ → Prop) where
  evalValues_preserves :
    ∀ {s : σ} {expr : Pattern} {s' : σ} {out : List Pattern},
      I.evalValues s expr = (s', out) →
      P s → P s'

private def uniquePatterns (xs : List Pattern) : List Pattern :=
  (xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).reverse

private def removeFirstEq (x : Pattern) : List Pattern → Option (List Pattern)
  | [] => none
  | y :: ys =>
      if y == x then
        some ys
      else
        match removeFirstEq x ys with
        | none => none
        | some rest => some (y :: rest)

private def multisetIntersection : List Pattern → List Pattern → List Pattern
  | [], _ => []
  | x :: xs, ys =>
      match removeFirstEq x ys with
      | some ys' => x :: multisetIntersection xs ys'
      | none => multisetIntersection xs ys

private def multisetSubtract : List Pattern → List Pattern → List Pattern
  | [], _ => []
  | x :: xs, ys =>
      match removeFirstEq x ys with
      | some ys' => multisetSubtract xs ys'
      | none => x :: multisetSubtract xs ys

private def streamValues (I : Interface σ) (s : σ) (expr : Pattern) : σ × List Pattern :=
  let (s1, out0) := I.evalValues s expr
  let out := if out0.isEmpty then [expr] else out0
  let vals := out.flatMap tupleElems
  (s1, vals)

private theorem streamValues_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (expr : Pattern) :
    P s → P (streamValues I s expr).1 := by
  intro hP
  unfold streamValues
  exact H.evalValues_preserves rfl hP

def evalIntrinsic (I : Interface σ) (s : σ) (term : Pattern) : Option (σ × List Pattern) :=
  match term with
  | .apply "unique" [expr] =>
      let (s1, xs) := streamValues I s expr
      some (s1, uniquePatterns xs)
  | .apply "union" [a, b] =>
      let (s1, xs) := streamValues I s a
      let (s2, ys) := streamValues I s1 b
      some (s2, xs ++ ys)
  | .apply "intersection" [a, b] =>
      let (s1, xs) := streamValues I s a
      let (s2, ys) := streamValues I s1 b
      some (s2, multisetIntersection xs ys)
  | .apply "subtraction" [a, b] =>
      let (s1, xs) := streamValues I s a
      let (s2, ys) := streamValues I s1 b
      some (s2, multisetSubtract xs ys)
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
      | cons a as =>
          cases as with
          | nil =>
              by_cases hUnique : ctor = "unique"
              · subst hUnique
                simpa [evalIntrinsic] using
                  streamValues_preserves I P H s a hP
              · simp [evalIntrinsic, hUnique]
          | cons b bs =>
              cases bs with
              | nil =>
                  by_cases hUnion : ctor = "union"
                  · subst hUnion
                    have h1 : P (streamValues I s a).1 :=
                      streamValues_preserves I P H s a hP
                    cases hA : streamValues I s a with
                    | mk s1 xs =>
                        have h2 : P (streamValues I s1 b).1 := by
                          have h1' : P s1 := by simpa [hA] using h1
                          exact streamValues_preserves I P H s1 b h1'
                        simpa [evalIntrinsic, hA] using h2
                  · by_cases hIntersection : ctor = "intersection"
                    · subst hIntersection
                      have h1 : P (streamValues I s a).1 :=
                        streamValues_preserves I P H s a hP
                      cases hA : streamValues I s a with
                      | mk s1 xs =>
                          have h2 : P (streamValues I s1 b).1 := by
                            have h1' : P s1 := by simpa [hA] using h1
                            exact streamValues_preserves I P H s1 b h1'
                          simpa [evalIntrinsic, hA] using h2
                    · by_cases hSubtraction : ctor = "subtraction"
                      · subst hSubtraction
                        have h1 : P (streamValues I s a).1 :=
                          streamValues_preserves I P H s a hP
                        cases hA : streamValues I s a with
                        | mk s1 xs =>
                            have h2 : P (streamValues I s1 b).1 := by
                              have h1' : P s1 := by simpa [hA] using h1
                              exact streamValues_preserves I P H s1 b h1'
                            simpa [evalIntrinsic, hA] using h2
                      · simp [evalIntrinsic, hUnion, hIntersection, hSubtraction]
              | cons c cs =>
                  simp [evalIntrinsic]

section Contracts

theorem evalIntrinsic_unique
    (I : Interface σ) (s : σ) (expr : Pattern) :
    evalIntrinsic I s (.apply "unique" [expr]) =
      let (s1, xs) := streamValues I s expr
      some (s1, uniquePatterns xs) := rfl

theorem evalIntrinsic_union
    (I : Interface σ) (s : σ) (a b : Pattern) :
    evalIntrinsic I s (.apply "union" [a, b]) =
      let (s1, xs) := streamValues I s a
      let (s2, ys) := streamValues I s1 b
      some (s2, xs ++ ys) := rfl

theorem evalIntrinsic_intersection
    (I : Interface σ) (s : σ) (a b : Pattern) :
    evalIntrinsic I s (.apply "intersection" [a, b]) =
      let (s1, xs) := streamValues I s a
      let (s2, ys) := streamValues I s1 b
      some (s2, multisetIntersection xs ys) := rfl

theorem evalIntrinsic_subtraction
    (I : Interface σ) (s : σ) (a b : Pattern) :
    evalIntrinsic I s (.apply "subtraction" [a, b]) =
      let (s1, xs) := streamValues I s a
      let (s2, ys) := streamValues I s1 b
      some (s2, multisetSubtract xs ys) := rfl

theorem evalIntrinsic_other_none
    (I : Interface σ) (s : σ) (ctor : String) (args : List Pattern)
    (hUnique : ctor ≠ "unique")
    (hUnion : ctor ≠ "union")
    (hIntersection : ctor ≠ "intersection")
    (hSubtraction : ctor ≠ "subtraction") :
    evalIntrinsic I s (.apply ctor args) = none := by
  simp [evalIntrinsic, hUnique, hUnion, hIntersection, hSubtraction]

end Contracts

end Algorithms.MeTTa.Simple.Semantics.StreamOps
