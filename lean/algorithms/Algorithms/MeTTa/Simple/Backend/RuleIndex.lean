import MeTTailCore

namespace Algorithms.MeTTa.Simple.Backend.RuleIndex

open MeTTailCore.MeTTaIL.Syntax

structure HeadEntry where
  ctor : String
  aritiesRev : List Nat := []
  premiseFreeCountByArity : List (Nat × Nat) := []
  compatConstraintArities : List Nat := []
deriving Repr

private def hasCompatHeadConstraintArg : Pattern → Bool
  | .apply _ [] => true
  | .apply _ (_ :: _) => true
  | .collection _ (_ :: _) _ => true
  | _ => false

private def bumpCount (counts : List (Nat × Nat)) (arity : Nat) : List (Nat × Nat) :=
  match counts with
  | [] => [(arity, 1)]
  | (n, c) :: rest =>
      if n == arity then
        (n, c + 1) :: rest
      else
        (n, c) :: bumpCount rest arity

private def addCompatArity (arities : List Nat) (arity : Nat) : List Nat :=
  if arities.contains arity then arities else arity :: arities

private def updateHeadEntry
    (entry : HeadEntry) (arity : Nat) (premiseFree hasCompat : Bool) : HeadEntry :=
  let counts :=
    if premiseFree then
      bumpCount entry.premiseFreeCountByArity arity
    else
      entry.premiseFreeCountByArity
  let compatArities :=
    if premiseFree && hasCompat then
      addCompatArity entry.compatConstraintArities arity
    else
      entry.compatConstraintArities
  { entry with
      aritiesRev := arity :: entry.aritiesRev
      premiseFreeCountByArity := counts
      compatConstraintArities := compatArities }

private def updateIndex
    (idx : List HeadEntry) (ctor : String) (arity : Nat)
    (premiseFree hasCompat : Bool) : List HeadEntry :=
  match idx with
  | [] =>
      let counts := if premiseFree then [(arity, 1)] else []
      let compatArities := if premiseFree && hasCompat then [arity] else []
      [{ ctor := ctor
         aritiesRev := [arity]
         premiseFreeCountByArity := counts
         compatConstraintArities := compatArities }]
  | e :: rest =>
      if e.ctor == ctor then
        updateHeadEntry e arity premiseFree hasCompat :: rest
      else
        e :: updateIndex rest ctor arity premiseFree hasCompat

private def updateFromRule (idx : List HeadEntry) (rule : RewriteRule) : List HeadEntry :=
  match rule.left with
  | .apply ctor args =>
      let arity := args.length
      let premiseFree := rule.premises.isEmpty
      let hasCompat := args.any hasCompatHeadConstraintArg
      updateIndex idx ctor arity premiseFree hasCompat
  | _ =>
      idx

def build (rewrites : List RewriteRule) : List HeadEntry :=
  rewrites.foldl updateFromRule []

private def findEntry? (idx : List HeadEntry) (ctor : String) : Option HeadEntry :=
  idx.find? (fun e => e.ctor == ctor)

def aritiesForHead (idx : List HeadEntry) (ctor : String) : List Nat :=
  match findEntry? idx ctor with
  | some e => e.aritiesRev
  | none => []

def rewriteCountForHeadArity (idx : List HeadEntry) (ctor : String) (arity : Nat) : Nat :=
  match findEntry? idx ctor with
  | none => 0
  | some e =>
      match e.premiseFreeCountByArity.find? (fun p => p.1 == arity) with
      | some (_, c) => c
      | none => 0

def hasHead (idx : List HeadEntry) (ctor : String) : Bool :=
  !(aritiesForHead idx ctor).isEmpty

def hasCompatHeadConstraintRule (idx : List HeadEntry) (ctor : String) (arity : Nat) : Bool :=
  match findEntry? idx ctor with
  | none => false
  | some e => e.compatConstraintArities.contains arity

end Algorithms.MeTTa.Simple.Backend.RuleIndex
