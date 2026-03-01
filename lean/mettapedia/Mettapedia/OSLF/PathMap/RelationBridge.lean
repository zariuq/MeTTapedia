import Mettapedia.OSLF.PathMap.Core
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# PathMap ↔ RelationEnv Bridge

Shows how the OSLF's `RelationEnv` can be viewed as an abstract "relational
space" interface, and how a PathMap-backed store provides the same semantics.

## Motivation

The current `RelationEnv` is a simple function:

```lean
structure RelationEnv where
  tuples : String → List Pattern → List (List Pattern)
```

This suffices for the OSLF formalization but couples us to a list-of-tuples
model.  PathMap replaces this with a trie-based lattice store that can:
- Answer prefix queries efficiently (restrict operation)
- Join/meet spaces algebraically
- Support the full MORK (MeTTa Optimal Reduction Kernel) interface

## Design

We introduce `RelationalSpace α`, a typeclass that generalises `RelationEnv`.
Any `α` satisfying `RelationalSpace` can be used wherever `RelationEnv` appears.

Key instances:
1. `RelationEnv` itself (trivial instance)
2. Abstract PathMap-backed space (via `PathMapQuantale`)

## References
- `Engine.lean`:    `Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv`
- PathMap MORK:     `/home/zar/claude/hyperon/MORK/`
-/

namespace Mettapedia.OSLF.PathMap

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-! ## Abstract Relational Space -/

/-- A relational space: a store that answers tuple queries.

    `query rel args` returns all tuples matching the relation `rel` with the
    given argument patterns.  This is the abstract counterpart of
    `RelationEnv.tuples`.

    Implemented by `RelationEnv` (list-of-tuples) and, prospectively, by
    PathMap-backed trie stores. -/
class RelationalSpace (α : Type*) where
  /-- Query the store for tuples of relation `rel` matching `args`. -/
  query : α → String → List Pattern → List (List Pattern)

/-! ## Instances -/

/-- `RelationEnv` is a `RelationalSpace` (trivially). -/
instance : RelationalSpace RelationEnv where
  query env rel args := env.tuples rel args

/-- Empty relational space: never produces any tuples. -/
def emptySpace : RelationEnv := RelationEnv.empty

/-! ## PathMap-backed Relational Space -/

/-- An abstract PathMap-backed relational space.

    In the full MORK implementation, the store is a `PathMap` trie where:
    - Outer keys are relation names (strings)
    - Inner structure is a trie over pattern sequences
    - Queries use `prestrict` to filter matching sub-tries

    Here we give the abstract specification: any type `σ` with a
    `PathMapQuantale` instance and a query function satisfying certain
    algebraic laws forms a valid relational space. -/
structure PathMapSpace (σ : Type*) [Mettapedia.PathMap.PathMapQuantale σ] where
  /-- The underlying store -/
  store : σ
  /-- Query function: extracts matching tuples from the store -/
  queryFn : σ → String → List Pattern → List (List Pattern)

/-- A `PathMapSpace` is a `RelationalSpace`. -/
instance {σ : Type*} [Mettapedia.PathMap.PathMapQuantale σ] :
    RelationalSpace (PathMapSpace σ) where
  query s rel args := s.queryFn s.store rel args

/-! ## Algebraic Properties of Spaces -/

/-- Two relational spaces agree on a query if they return the same tuples. -/
def SpacesAgreeOn (α β : Type*) [RelationalSpace α] [RelationalSpace β]
    (a : α) (b : β) (rel : String) (args : List Pattern) : Prop :=
  RelationalSpace.query a rel args = RelationalSpace.query b rel args

/-- A relational space is monotone under join if merging two stores via join
    produces a store that answers queries with the union of their results. -/
def JoinMonotone (σ : Type*) [RelationalSpace σ] [Mettapedia.PathMap.PathMapLattice σ] : Prop :=
  ∀ a b : σ, ∀ ab : σ,
    (Mettapedia.PathMap.PathMapLattice.pjoin a b).resolve a b = some ab →
    ∀ rel args,
      RelationalSpace.query ab rel args =
      RelationalSpace.query a rel args ++ RelationalSpace.query b rel args

/-- A relational space is monotone under meet if intersecting two stores via
    meet produces a store answering only queries that both stores answer. -/
def MeetMonotone (σ : Type*) [RelationalSpace σ] [Mettapedia.PathMap.PathMapLattice σ] : Prop :=
  ∀ a b : σ, ∀ ab : σ,
    (Mettapedia.PathMap.PathMapLattice.pmeet a b).resolve a b = some ab →
    ∀ rel args,
      RelationalSpace.query ab rel args =
      (RelationalSpace.query a rel args).filter
        (fun t => (RelationalSpace.query b rel args).contains t)

/-! ## Lifting `RelationEnv` operations to spaces -/

/-- Lift a `RelationEnv`-aware function to use any `RelationalSpace`. -/
def liftToSpace {α : Type*} [RelationalSpace α]
    (f : RelationEnv → β) (toEnv : α → RelationEnv) : α → β :=
  fun a => f (toEnv a)

/-- Canonical embedding: lift a `RelationalSpace` to a `RelationEnv` by
    packaging the query function. -/
def toRelationEnv {α : Type*} [RelationalSpace α] (a : α) : RelationEnv where
  tuples := RelationalSpace.query a

/-- `toRelationEnv` preserves queries. -/
theorem toRelationEnv_query {α : Type*} [RelationalSpace α] (a : α)
    (rel : String) (args : List Pattern) :
    (toRelationEnv a).tuples rel args = RelationalSpace.query a rel args := rfl

/-! ## Commutativity of the Bridge -/

/-- The embedding `toRelationEnv` commutes with query: using the embedded env
    gives the same tuples as using the space directly. -/
theorem query_comm_bridge {α : Type*} [RelationalSpace α] (a : α) :
    ∀ rel args,
      RelationalSpace.query (toRelationEnv a) rel args =
      RelationalSpace.query a rel args := fun _ _ => rfl

/-! ## Backend Preservation: RelationalSpace → OSLF Synthesis -/

open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef)
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises (DeclReducesWithPremises)

/-- Two `RelationEnv`s with equal `tuples` are equal. -/
theorem RelationEnv.ext_tuples {env₁ env₂ : RelationEnv}
    (h : env₁.tuples = env₂.tuples) : env₁ = env₂ := by
  cases env₁; cases env₂; simp at h; exact congrArg _ h

/-- If two relational spaces agree on all queries, their `toRelationEnv`
    embeddings are equal as `RelationEnv`s. -/
theorem toRelationEnv_eq_of_agree {α β : Type*}
    [RelationalSpace α] [RelationalSpace β]
    (a : α) (b : β)
    (hagree : ∀ rel args,
      RelationalSpace.query a rel args = RelationalSpace.query b rel args) :
    toRelationEnv a = toRelationEnv b :=
  RelationEnv.ext_tuples (funext fun rel => funext fun args => hagree rel args)

/-- If two relational spaces agree on all queries, they induce the same
    OSLF reduction relation. This is the key backend-equivalence theorem:
    swapping the store preserves semantics as long as queries agree. -/
theorem langReducesUsing_of_spacesAgree {α β : Type*}
    [RelationalSpace α] [RelationalSpace β]
    (a : α) (b : β)
    (hagree : ∀ rel args,
      RelationalSpace.query a rel args = RelationalSpace.query b rel args)
    (lang : LanguageDef) (p q : Pattern) :
    DeclReducesWithPremises (toRelationEnv a) lang p q ↔
    DeclReducesWithPremises (toRelationEnv b) lang p q := by
  rw [toRelationEnv_eq_of_agree a b hagree]

/-- Backend preservation for diamond: query-agreeing spaces produce
    the same step-future modality. -/
theorem langDiamondUsing_of_spacesAgree {α β : Type*}
    [RelationalSpace α] [RelationalSpace β]
    (a : α) (b : β)
    (hagree : ∀ rel args,
      RelationalSpace.query a rel args = RelationalSpace.query b rel args)
    (lang : LanguageDef) (φ : Pattern → Prop) (p : Pattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing (toRelationEnv a) lang φ p ↔
    Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing (toRelationEnv b) lang φ p := by
  rw [toRelationEnv_eq_of_agree a b hagree]

/-- Backend preservation for box: query-agreeing spaces produce
    the same step-past modality. -/
theorem langBoxUsing_of_spacesAgree {α β : Type*}
    [RelationalSpace α] [RelationalSpace β]
    (a : α) (b : β)
    (hagree : ∀ rel args,
      RelationalSpace.query a rel args = RelationalSpace.query b rel args)
    (lang : LanguageDef) (φ : Pattern → Prop) (p : Pattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langBoxUsing (toRelationEnv a) lang φ p ↔
    Mettapedia.OSLF.Framework.TypeSynthesis.langBoxUsing (toRelationEnv b) lang φ p := by
  rw [toRelationEnv_eq_of_agree a b hagree]

end Mettapedia.OSLF.PathMap
