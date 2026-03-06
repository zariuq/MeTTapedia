import MeTTailCore

namespace Algorithms.MeTTa.Simple.Backend.SpaceIndex

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

structure HeadFacts where
  ctor : String
  arity : Nat
  facts : List Pattern := []
deriving Repr

structure TypeHeadFacts where
  ctor : String
  arity : Nat
  entries : List (Pattern × Pattern) := []
deriving Repr

structure View where
  selfFacts : List Pattern := []
  nonApplyFacts : List Pattern := []
  byHeadArity : List HeadFacts := []
  typeFacts : List (Pattern × Pattern) := []
  typeFactsNonApplyHead : List (Pattern × Pattern) := []
  typeByHeadArity : List TypeHeadFacts := []
deriving Repr

def empty : View := {}

private def upsertHeadFact (rows : List HeadFacts)
    (ctor : String) (arity : Nat) (fact : Pattern) : List HeadFacts :=
  match rows with
  | [] => [{ ctor := ctor, arity := arity, facts := [fact] }]
  | r :: rs =>
      if r.ctor == ctor && r.arity == arity then
        { r with facts := r.facts ++ [fact] } :: rs
      else
        r :: upsertHeadFact rs ctor arity fact

private def upsertTypeHeadFact (rows : List TypeHeadFacts)
    (ctor : String) (arity : Nat) (entry : Pattern × Pattern) : List TypeHeadFacts :=
  match rows with
  | [] => [{ ctor := ctor, arity := arity, entries := [entry] }]
  | r :: rs =>
      if r.ctor == ctor && r.arity == arity then
        { r with entries := r.entries ++ [entry] } :: rs
      else
        r :: upsertTypeHeadFact rs ctor arity entry

private def findHeadFacts (rows : List HeadFacts) (ctor : String) (arity : Nat) : List Pattern :=
  match rows.find? (fun r => r.ctor == ctor && r.arity == arity) with
  | some r => r.facts
  | none => []

private def findTypeHeadFacts (rows : List TypeHeadFacts)
    (ctor : String) (arity : Nat) : List (Pattern × Pattern) :=
  match rows.find? (fun r => r.ctor == ctor && r.arity == arity) with
  | some r => r.entries
  | none => []

def headFactsFor (v : View) (ctor : String) (arity : Nat) : List Pattern :=
  findHeadFacts v.byHeadArity ctor arity

def typeHeadFactsFor (v : View) (ctor : String) (arity : Nat) : List (Pattern × Pattern) :=
  findTypeHeadFacts v.typeByHeadArity ctor arity

def build (selfFacts : List Pattern) : View :=
  selfFacts.foldl
    (fun v fact =>
      let v1 :=
        match fact with
        | .apply ctor args =>
            { v with byHeadArity := upsertHeadFact v.byHeadArity ctor args.length fact }
        | _ =>
            { v with nonApplyFacts := v.nonApplyFacts ++ [fact] }
      let v2 :=
        match fact with
        | .apply ":" [lhs, ty] =>
            let entry := (lhs, ty)
            let base :=
              { v1 with typeFacts := v1.typeFacts ++ [entry] }
            match lhs with
            | .apply lCtor lArgs =>
                { base with typeByHeadArity := upsertTypeHeadFact base.typeByHeadArity lCtor lArgs.length entry }
            | _ =>
                { base with typeFactsNonApplyHead := base.typeFactsNonApplyHead ++ [entry] }
        | _ => v1
      v2)
    { empty with selfFacts := selfFacts }

/-- Candidate self-space facts for a pattern. Always returns a semantic superset. -/
def candidateSelfFacts (v : View) (pat : Pattern) : List Pattern :=
  match pat with
  | .apply "," [_lhs, _rhs] => v.selfFacts
  | .fvar _ => v.selfFacts
  | .apply ctor args =>
      if ctor.startsWith "$" then
        v.selfFacts
      else
        let headFacts := headFactsFor v ctor args.length
        if headFacts.isEmpty then
          v.selfFacts
        else
          headFacts ++ v.nonApplyFacts
  | _ => v.selfFacts

private def dedupPatterns (xs : List Pattern) : List Pattern :=
  (xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) [])

/-- Candidate type annotations `(: lhs ty)` for a query term in self space. -/
def candidateSelfTypeEntries (v : View) (x : Pattern) : List (Pattern × Pattern) :=
  match x with
  | .apply ctor args =>
      let indexed := typeHeadFactsFor v ctor args.length
      if indexed.isEmpty then
        v.typeFacts
      else
        indexed ++ v.typeFactsNonApplyHead
  | _ =>
      v.typeFacts

/-- Resolve matching type candidates from indexed self-space type facts. -/
def typeCandidatesForSelf (v : View)
    (matchPattern : Pattern → Pattern → List Bindings)
    (x : Pattern) : List Pattern :=
  let entries := candidateSelfTypeEntries v x
  let outRev :=
    entries.foldl
      (fun acc e =>
        let lhs := e.1
        let ty := e.2
        if (matchPattern lhs x).isEmpty then
          acc
        else
          if acc.contains ty then acc else ty :: acc)
      []
  outRev.reverse

end Algorithms.MeTTa.Simple.Backend.SpaceIndex
