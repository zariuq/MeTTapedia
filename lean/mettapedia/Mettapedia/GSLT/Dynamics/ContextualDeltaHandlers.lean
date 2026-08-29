import Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
import Mettapedia.GSLT.Dynamics.MonotoneWorldHandler
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Contextual delta handlers

Branch-local state is most useful when a branch carries a composable delta,
not only a copied final world.  This module presents a free finite-choice
program with reads, delta updates, and deferred external intents.

One execution produces contextual worlds.  Three later operations remain
separate:

* retain every world without changing the parent;
* select one occurrence and expose only its delta and intents; or
* merge all deltas through an authored permutation-invariant resolver.

The resolver returns an `Option`: incompatible deltas remain unresolved.  A
join-semilattice supplies the monotone-union instance.  A first-occurrence
resolver is proved inadmissible for unordered alternatives.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.MonotoneWorldHandler

universe uState uDelta uAnswer uOtherAnswer uIntent

variable {State : Type uState} {Delta : Type uDelta}
variable {Answer : Type uAnswer} {Intent : Type uIntent}

/-! ## Delta actions -/

/-- A monoid action written explicitly so several delta algebras may coexist
on one state type.  Composition is chronological: `first` then `second`. -/
structure DeltaAlgebra (State : Type uState) (Delta : Type uDelta) where
  empty : Delta
  compose : Delta → Delta → Delta
  apply : State → Delta → State
  compose_assoc : ∀ first second third,
    compose (compose first second) third =
      compose first (compose second third)
  empty_compose : ∀ delta, compose empty delta = delta
  compose_empty : ∀ delta, compose delta empty = delta
  apply_empty : ∀ state, apply state empty = state
  apply_compose : ∀ state first second,
    apply state (compose first second) = apply (apply state first) second

/-! ## Free contextual delta program -/

inductive Program (State : Type uState) (Delta : Type uDelta)
    (Answer : Type uAnswer) (Intent : Type uIntent) where
  | pure (answer : Answer)
  | choose (left right : Program State Delta Answer Intent)
  | read (next : State → Program State Delta Answer Intent)
  | update (delta : Delta) (next : Program State Delta Answer Intent)
  | intent (request : Intent) (next : Program State Delta Answer Intent)

namespace Program

def bind {State : Type uState} {Delta : Type uDelta}
    {Answer : Type uAnswer} {OtherAnswer : Type uOtherAnswer}
    {Intent : Type uIntent}
    (program : Program State Delta Answer Intent)
    (next : Answer → Program State Delta OtherAnswer Intent) :
    Program State Delta OtherAnswer Intent :=
  match program with
  | .pure answer => next answer
  | .choose left right => .choose (bind left next) (bind right next)
  | .read continuation => .read fun state => bind (continuation state) next
  | .update delta continuation => .update delta (bind continuation next)
  | .intent request continuation => .intent request (bind continuation next)

end Program

/-- One contextual result retains occurrence identity, its delta, the state
obtained by applying it to the parent, and deferred external intents. -/
structure DeltaWorld (State : Type uState) (Delta : Type uDelta)
    (Answer : Type uAnswer) (Intent : Type uIntent) where
  branch : BranchTrace
  answer : Answer
  delta : Delta
  state : State
  intents : List Intent
deriving DecidableEq, Repr

/-- Evaluate each alternative from the same parent while accumulating its
own chronological delta. -/
def runWorldsAt
    {State : Type uState} {Delta : Type uDelta}
    {Answer : Type uAnswer} {Intent : Type uIntent}
    (algebra : DeltaAlgebra State Delta) :
    Program State Delta Answer Intent → State → Delta → BranchTrace →
      List (DeltaWorld State Delta Answer Intent)
  | .pure answer, parent, accumulated, branch =>
      [{ branch := branch
         answer := answer
         delta := accumulated
         state := algebra.apply parent accumulated
         intents := [] }]
  | .choose left right, parent, accumulated, branch =>
      runWorldsAt algebra left parent accumulated (false :: branch) ++
        runWorldsAt algebra right parent accumulated (true :: branch)
  | .read next, parent, accumulated, branch =>
      runWorldsAt algebra (next (algebra.apply parent accumulated)) parent
        accumulated branch
  | .update delta next, parent, accumulated, branch =>
      runWorldsAt algebra next parent (algebra.compose accumulated delta) branch
  | .intent request next, parent, accumulated, branch =>
      (runWorldsAt algebra next parent accumulated branch).map fun result =>
        { result with intents := request :: result.intents }

def runWorlds
    {State : Type uState} {Delta : Type uDelta}
    {Answer : Type uAnswer} {Intent : Type uIntent}
    (algebra : DeltaAlgebra State Delta)
    (program : Program State Delta Answer Intent) (parent : State) :
    List (DeltaWorld State Delta Answer Intent) :=
  runWorldsAt algebra program parent algebra.empty []

/-! ## Selection and order-free merging -/

/-- Selecting one alternative authorizes exactly one delta and intent batch. -/
structure Selected (State : Type uState) (Delta : Type uDelta)
    (Answer : Type uAnswer) (Intent : Type uIntent) where
  branch : BranchTrace
  answer : Answer
  delta : Delta
  state : State
  intents : List Intent
deriving DecidableEq, Repr

def DeltaWorld.select
    (world : DeltaWorld State Delta Answer Intent) :
    Selected State Delta Answer Intent where
  branch := world.branch
  answer := world.answer
  delta := world.delta
  state := world.state
  intents := world.intents

def selectCommit
    (worlds : List (DeltaWorld State Delta Answer Intent)) (index : Nat) :
    Option (Selected State Delta Answer Intent) :=
  (worlds[index]?).map DeltaWorld.select

/-- An unordered alternative merge must be invariant under permutation.  It
may refuse a conflict by returning `none`. -/
structure AlternativeMerge (Delta : Type uDelta) where
  merge : List Delta → Option Delta
  permutationInvariant : ∀ {first second}, first.Perm second →
    merge first = merge second

/-- Result of merging state deltas.  All worlds, including their answers and
intents, remain available; merging state is not authorization to perform all
external intents. -/
structure Merged (State : Type uState) (Delta : Type uDelta)
    (Answer : Type uAnswer) (Intent : Type uIntent) where
  worlds : List (DeltaWorld State Delta Answer Intent)
  delta : Delta
  state : State
deriving DecidableEq, Repr

def worldDeltas
    (worlds : List (DeltaWorld State Delta Answer Intent)) : List Delta :=
  worlds.map DeltaWorld.delta

/-- Attempt an authored merge.  Failure retains the original worlds outside
this result and commits no state. -/
def mergeWorlds
    (algebra : DeltaAlgebra State Delta) (parent : State)
    (resolver : AlternativeMerge Delta)
    (worlds : List (DeltaWorld State Delta Answer Intent)) :
    Option (Merged State Delta Answer Intent) :=
  (resolver.merge (worldDeltas worlds)).map fun delta =>
    { worlds := worlds, delta := delta, state := algebra.apply parent delta }

/-- Convert bare deltas to the generic join contribution carrier. -/
def deltaContributions (deltas : List Delta) :
    List (Contribution Unit Delta) :=
  deltas.map fun delta => ⟨(), delta⟩

/-- Monotone information deltas support an order-free join resolver. -/
def joinMerge (Delta : Type uDelta) [SemilatticeSup Delta] [OrderBot Delta] :
    AlternativeMerge Delta where
  merge deltas := some (joinDeltas (deltaContributions deltas))
  permutationInvariant := by
    intro first second permutation
    apply congrArg some
    apply joinDeltas_perm
    simpa [deltaContributions] using
      permutation.map fun delta =>
        (⟨(), delta⟩ : Contribution Unit Delta)

/-- Reordering worlds cannot change whether an order-free resolver succeeds
or which delta it returns. -/
theorem AlternativeMerge.merge_worldDeltas_perm
    (resolver : AlternativeMerge Delta)
    {first second : List (DeltaWorld State Delta Answer Intent)}
    (permutation : first.Perm second) :
    resolver.merge (worldDeltas first) =
      resolver.merge (worldDeltas second) :=
  resolver.permutationInvariant (permutation.map DeltaWorld.delta)

/-! ## Positive and negative controls -/

namespace Canary

def factAlgebra : DeltaAlgebra (Finset Nat) (Finset Nat) where
  empty := ∅
  compose := (· ∪ ·)
  apply := (· ∪ ·)
  compose_assoc := Finset.union_assoc
  empty_compose := Finset.empty_union
  compose_empty := Finset.union_empty
  apply_empty := Finset.union_empty
  apply_compose := fun state first second =>
    (Finset.union_assoc state first second).symm

def twoFacts : Program (Finset Nat) (Finset Nat) Bool Bool :=
  .choose
    (.update {1} (.intent false (.pure false)))
    (.update {2} (.intent true (.pure true)))

def duplicateFact : Program (Finset Nat) (Finset Nat) Bool Bool :=
  .choose (.update {1} (.pure false)) (.update {1} (.pure true))

def factWorlds := runWorlds factAlgebra twoFacts ({0} : Finset Nat)
def joinedFacts :=
  mergeWorlds factAlgebra ({0} : Finset Nat) (joinMerge (Finset Nat)) factWorlds

/-- Both alternatives remain contextual occurrences while their disjoint
facts coexist in the merged state. -/
theorem disjoint_alternatives_merge_without_erasure :
    joinedFacts.map Merged.state = some ({0, 1, 2} : Finset Nat) ∧
      factWorlds.map DeltaWorld.answer = [false, true] := by
  decide

/-- Selecting one world exposes only its state and deferred intent. -/
theorem selected_world_excludes_loser :
    (selectCommit factWorlds 0).map
        (fun selected => (selected.state, selected.intents)) =
      some (({0, 1} : Finset Nat), [false]) := by
  decide

/-- Duplicate monotone facts collapse in state, but the two answer
occurrences remain distinct. -/
theorem duplicate_state_not_duplicate_occurrence :
    let worlds := runWorlds factAlgebra duplicateFact ({0} : Finset Nat)
    (mergeWorlds factAlgebra ({0} : Finset Nat)
        (joinMerge (Finset Nat)) worlds).map Merged.state =
        some ({0, 1} : Finset Nat) ∧
      worlds.map DeltaWorld.answer = [false, true] := by
  decide

/-- Choosing the first delta is sensitive to enumeration order. -/
def firstMerge (deltas : List Bool) : Option Bool :=
  deltas.head?

/-- Negative control: a first-occurrence merge cannot implement an unordered
alternative merge. -/
theorem firstMerge_not_permutationInvariant :
    ¬ ∀ {first second : List Bool}, first.Perm second →
      firstMerge first = firstMerge second := by
  intro invariant
  have contradiction :
      firstMerge [true, false] = firstMerge [false, true] :=
    invariant (List.Perm.swap false true [])
  simp [firstMerge] at contradiction

end Canary

/-! ## Axiom audit -/

#print axioms AlternativeMerge.merge_worldDeltas_perm
#print axioms joinMerge
#print axioms Canary.disjoint_alternatives_merge_without_erasure
#print axioms Canary.selected_world_excludes_loser
#print axioms Canary.duplicate_state_not_duplicate_occurrence
#print axioms Canary.firstMerge_not_permutationInvariant

end Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers
