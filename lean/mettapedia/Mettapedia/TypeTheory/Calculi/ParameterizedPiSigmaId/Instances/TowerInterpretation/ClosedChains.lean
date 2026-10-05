import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Consistency
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerLevelSubstitution

/-!
# The tower read by a chain of closed universes

The tower model (`Consistency`) reads the universe at a level as the least closed universe
around the earlier ones. The rules of the tower ask for less.

**A chain of closed universes** (`ClosedChain`) over a level order: a closed universe for
every level, each a member of every later one.

**The rules of the tower hold over every chain** (`chain_universeModel`), when the ground set
is a member of the first universe. The universe at a level expression is read as the universe
of the chain at the value of the expression (`chainHead`). So the tower has a set model over
every chain (`chain_setModel`).

With bounds on the level parameters, the rules hold at every valuation that respects the
bounds (`chain_universeModel_bounded`, `chain_setModel_bounded`).

The two are instances of one statement (`chain_universeModel_of`): a rule package that types
its heads and forms its types as the tower does holds over a chain as soon as its comparisons
of universes are inclusions of the chain's universes.

A chain need not consist of least universes. One of its universes may be closed under the
universe operation, which no least closed universe is (`univOf_not_closed_under_univOf`); the
tower inside the sets (`MegalodonHOTG.SetsModel`) is read by such a chain.

Positive example: the least closed universes of the tower model are a chain
(`universeSet_closedChain`), and the reading over it is the tower model's
(`chainHead_universeSet`). Negative example: one closed universe at every level is not a chain
(`constant_not_closedChain`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles Closed univOf mem_univOf)
open ZFSetInterpretation (universeSet universeSet_closed universeSet_mem_of_lt)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayInterpretation (UniverseModel)
open ZFSetTraceProducts (tracePiSet)
open ZFSetDependentProducts (sigmaSet)
open ZFSetTraceProofDecoding (truthCode)

universe u

variable {L : Type} [LevelOrder L]

/-- **A chain of closed universes** over a level order: a closed universe for every level,
each a member of every later one. -/
structure ClosedChain (V : L → ZFSet.{u}) : Prop where
  closed : ∀ a : L, Closed (V a)
  mem_of_lt : ∀ {a b : L}, a < b → V a ∈ V b

namespace ClosedChain

variable {V : L → ZFSet.{u}} (chain : ClosedChain V)

include chain

/-- A universe of a chain is a member of the next one. -/
theorem mem_succ (a : L) : V a ∈ V (LevelOrder.succ a) :=
  chain.mem_of_lt (LevelOrder.lt_succ a)

/-- A universe of a chain is a subset of every universe at a level above. -/
theorem mono {a b : L} (le : a ≤ b) : V a ⊆ V b := by
  rcases eq_or_lt_of_le le with rfl | lt
  · exact fun _ hx => hx
  · exact (chain.closed b).transitive _ (chain.mem_of_lt lt)

/-- The empty set is a member of every universe of a chain whose first universe has a
member. -/
theorem empty_mem {ground : ZFSet.{u}} (groundTyped : ground ∈ V LevelOrder.bot) (a : L) :
    (∅ : ZFSet.{u}) ∈ V a :=
  (chain.closed a).empty_mem (chain.mono (LevelOrder.bot_le a) groundTyped)

/-- A truth value is a member of every universe of a chain whose first universe has a
member. -/
theorem truthCode_mem {ground : ZFSet.{u}} (groundTyped : ground ∈ V LevelOrder.bot) (a : L)
    (P : Prop) : truthCode P ∈ V a :=
  (chain.closed a).separation_mem
    ((chain.closed a).singleton_mem (chain.empty_mem groundTyped a)) _

end ClosedChain

/-- **The reading of the heads of the tower over a family of sets**: the ground head as the
ground set, the universe at a level expression as the set at the value of the expression. -/
def chainHead (V : L → ZFSet.{u}) (ground : ZFSet.{u}) (ν : Nat → L) :
    LevelTower.Head L → ZFSet.{u}
  | .legacyGround => ground
  | .sort e => V (e.eval ν)

variable {V : L → ZFSet.{u}} {ground : ZFSet.{u}}

/-- **A rule package that types its heads and forms its types as the tower does holds over a
chain**, when its comparisons of universes are inclusions of the chain's universes. -/
theorem chain_universeModel_of (chain : ClosedChain V)
    (groundTyped : ground ∈ V LevelOrder.bot) (ν : Nat → L) {R : Rules (LevelTower.Head L)}
    (formation : LevelTower.TowerFormation R)
    (cumulative : ∀ {lower upper : LevelTower.Head L}, R.cumulative lower upper →
      chainHead V ground ν lower ⊆ chainHead V ground ν upper) :
    UniverseModel R (chainHead V ground ν) where
  headTyping_mem := by
    intro head level typed
    cases formation.headTyping.mp typed with
    | legacyGround => exact groundTyped
    | sort e => exact chain.mem_succ (e.eval ν)
  cumulative_subset := cumulative
  pi_mem := by
    intro domainLevel bodyLevel level joined A domainTyped B bodyTyped
    cases formation.join.mp joined with
    | sorts left right =>
      change tracePiSet A B ∈ V (max (left.eval ν) (right.eval ν))
      exact (chain.closed _).tracePiSet_mem (chain.mono (le_max_left _ _) domainTyped) B
        (fun x inside => chain.mono (le_max_right _ _) (bodyTyped x inside))
  sigma_mem := by
    intro domainLevel bodyLevel level joined A domainTyped B bodyTyped
    cases formation.join.mp joined with
    | sorts left right =>
      change sigmaSet A B ∈ V (max (left.eval ν) (right.eval ν))
      exact (chain.closed _).sigmaSet_mem (chain.mono (le_max_left _ _) domainTyped) B
        (fun x inside => chain.mono (le_max_right _ _) (bodyTyped x inside))
  identity_mem := by
    intro level isUniverse P
    cases formation.isUniverse.mp isUniverse with
    | sort e => exact chain.truthCode_mem groundTyped _ P

/-- **The rules of the tower hold over every chain of closed universes.** -/
theorem chain_universeModel (chain : ClosedChain V) (groundTyped : ground ∈ V LevelOrder.bot)
    (ν : Nat → L) : UniverseModel (LevelTower.rules L) (chainHead V ground ν) :=
  chain_universeModel_of chain groundTyped ν LevelTower.overTower_rules.toTowerFormation
    fun {lower upper} below => by
      have known : LevelTower.Cumulative lower upper := below
      cases lower with
      | legacyGround => exact False.elim known
      | sort l =>
        cases upper with
        | legacyGround => exact False.elim known
        | sort r => exact chain.mono (known ν)

/-- **With bounds on the level parameters, the rules of the tower hold over every chain** at
every valuation that respects the bounds. -/
theorem chain_universeModel_bounded (chain : ClosedChain V)
    (groundTyped : ground ∈ V LevelOrder.bot) {Δ : LevelBounds L} {ν : Nat → L}
    (valid : Δ.Valid ν) :
    UniverseModel (LevelTower.boundedRules (LevelTower.rules L) Δ) (chainHead V ground ν) :=
  chain_universeModel_of chain groundTyped ν
    (LevelTower.overTower_rules.toTowerFormation.bounded Δ)
    fun {lower upper} below => by
      have known : LevelTower.CumulativeUnder Δ lower upper := below
      cases lower with
      | legacyGround => exact False.elim known
      | sort l =>
        cases upper with
        | legacyGround => exact False.elim known
        | sort r => exact chain.mono (known ν valid)

/-- Equal heads of the tower have equal readings. -/
theorem chainHead_eq (V : L → ZFSet.{u}) (ground : ZFSet.{u}) (ν : Nat → L)
    {h h' : LevelTower.Head L} (same : LevelTower.HeadEq h h') :
    chainHead V ground ν h = chainHead V ground ν h' := by
  cases h with
  | legacyGround =>
    cases h' with
    | legacyGround => rfl
    | sort _ => exact False.elim same
  | sort l =>
    cases h' with
    | legacyGround => exact False.elim same
    | sort r => exact congrArg V (same ν)

/-- Heads of the tower that are equal under bounds on the level parameters have equal
readings at every valuation that respects the bounds. -/
theorem chainHead_eq_bounded (V : L → ZFSet.{u}) (ground : ZFSet.{u}) {Δ : LevelBounds L}
    {ν : Nat → L} (valid : Δ.Valid ν) {h h' : LevelTower.Head L}
    (same : LevelTower.HeadEqUnder Δ h h') :
    chainHead V ground ν h = chainHead V ground ν h' := by
  cases h with
  | legacyGround =>
    cases h' with
    | legacyGround => rfl
    | sort _ => exact False.elim same
  | sort l =>
    cases h' with
    | legacyGround => exact False.elim same
    | sort r => exact congrArg V (same ν valid)

/-- **The tower has a set model over every chain of closed universes.** -/
theorem chain_setModel (chain : ClosedChain V) (groundTyped : ground ∈ V LevelOrder.bot)
    (ν : Nat → L) (consts : DeclName → ZFSet.{u}) :
    SetModel (chainHead V ground ν) consts (towerPackage (L := L)) where
  universes := chain_universeModel chain groundTyped ν
  headEq same := chainHead_eq V ground ν same
  constants known := by cases known
  steps step := step.elim

/-- **The tower with bounded level parameters has a set model over every chain of closed
universes**, at every valuation that respects the bounds. -/
theorem chain_setModel_bounded (chain : ClosedChain V)
    (groundTyped : ground ∈ V LevelOrder.bot) {Δ : LevelBounds L} {ν : Nat → L}
    (valid : Δ.Valid ν) (consts : DeclName → ZFSet.{u}) :
    SetModel (chainHead V ground ν) consts
      (LevelTower.boundedChurch (towerPackage (L := L)) Δ) where
  universes := chain_universeModel_bounded chain groundTyped valid
  headEq same := chainHead_eq_bounded V ground valid same
  constants known := by cases known
  steps step := step.elim

/-! ## Examples -/

/-- Positive example: **the least closed universes of the tower model are a chain.** -/
theorem universeSet_closedChain (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    ClosedChain (universeSet h seed : L → ZFSet.{u}) where
  closed := universeSet_closed h seed
  mem_of_lt := fun lt => universeSet_mem_of_lt h seed lt

/-- The reading over the chain of least closed universes is the reading of the tower
model. -/
theorem chainHead_universeSet (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u})
    (ν : Nat → L) :
    chainHead (universeSet h seed) ground ν = interpretHead h seed ground ν := by
  funext head
  cases head <;> rfl

/-- Negative example: **one closed universe at every level is not a chain.** -/
theorem constant_not_closedChain (U : ZFSet.{u}) : ¬ ClosedChain (fun _ : L => U) := fun chain =>
  ZFSet.mem_irrefl U (chain.mem_succ LevelOrder.bot)

/-- **No least closed universe is closed under the universe operation**: the set it is the
least closed universe around is one of its members, and the least closed universe around that
member is not. -/
theorem univOf_not_closed_under_univOf (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    ¬ ∀ x ∈ univOf h N, univOf h x ∈ univOf h N := fun closed =>
  ZFSet.mem_irrefl _ (closed N (mem_univOf h N))

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
