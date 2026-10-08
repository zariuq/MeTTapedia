import Mettapedia.OSLF.Syntax.FiniteBranchingBehaviour
import Mettapedia.CategoryTheory.FinitePowersetWeakPullback
import Mathlib.Data.Fintype.EquivFin

/-!
# Branching, collision and finite-support boundaries

The examples use actual finite successor sets and actual family maps.
Two distinct branches may collide under direct image. Conversely, one
deterministic branch at every natural-number action has no finite enabled
action support. Complete matching pairs give a weak-pullback section, but
cannot recover the originally supplied matching relation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Controls

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.CategoryTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)

inductive Operator where
  | stopped
  | choose
  deriving DecidableEq

abbrev signature : Signature.{0} where
  Srt := Unit
  Operator := fun _ => Operator
  Position := fun operator => match operator with
    | .stopped => Empty
    | .choose => Fin 2
  argument := fun _ _ => ()
  finite operator := by cases operator <;> infer_instance

abbrev actions : signature.Srt → Type := fun _ => Nat
abbrev naturals : signature.Families := fun _ _ => Nat

def twoBranches : Behaviour signature actions naturals PUnit.unit () :=
  fun action => if action = 7 then {11, 21} else ∅

theorem actual_two_branches : twoBranches 7 = {11, 21} := by
  simp [twoBranches]

theorem cannot_be_deterministic :
    ¬ ∃ source : DeterministicGSOS.Behaviour signature actions naturals PUnit.unit (),
      (deterministicEmbedding signature actions).app naturals PUnit.unit () source =
        twoBranches := by
  rintro ⟨source, same⟩
  have exactSeven := congrArg (fun behaviour => behaviour 7) same
  change (source 7).toFinset = twoBranches 7 at exactSeven
  rw [actual_two_branches] at exactSeven
  cases offered : source 7 with
  | none =>
      have member : 11 ∈ (source 7).toFinset := by
        rw [exactSeven]
        simp
      simp [offered] at member
  | some value =>
      have first : 11 = value := by
        have member : 11 ∈ (source 7).toFinset := by
          rw [exactSeven]
          simp
        simpa [offered] using member
      have second : 21 = value := by
        have member : 21 ∈ (source 7).toFinset := by
          rw [exactSeven]
          simp
        simpa [offered] using member
      have impossible : (11 : Nat) = 21 := first.trans second.symm
      exact (by decide : (11 : Nat) ≠ 21) impossible

def collapse : naturals ⟶ naturals := fun _ _ => ↾(fun _ => 0)

theorem collision_readout :
    behaviourMap signature actions collapse PUnit.unit () twoBranches 7 = {0} := by
  change FinitePowerset.map (fun _ : Nat => 0) (twoBranches 7) = {0}
  rw [actual_two_branches]
  ext value
  simp [FinitePowerset.map]

theorem collision_changes_branch_count :
    (twoBranches 7).card = 2 ∧
      (behaviourMap signature actions collapse PUnit.unit () twoBranches 7).card = 1 := by
  rw [actual_two_branches, collision_readout]
  constructor <;> decide

def allActions : DeterministicGSOS.Behaviour signature actions naturals PUnit.unit () :=
  fun action => some (action + 1)

def embeddedAllActions : Behaviour signature actions naturals PUnit.unit () :=
  (deterministicEmbedding signature actions).app naturals PUnit.unit () allActions

theorem all_actions_readout (action : Nat) :
    embeddedAllActions action = {action + 1} := rfl

theorem all_actions_nonempty (action : Nat) : embeddedAllActions action ≠ ∅ := by
  rw [all_actions_readout]
  exact Finset.singleton_ne_empty _

theorem no_finite_enabled_action_support :
    ¬ ∃ support : Finset Nat,
      ∀ action, embeddedAllActions action ≠ ∅ → action ∈ support := by
  rintro ⟨support, covers⟩
  obtain ⟨action, missing⟩ := Infinite.exists_notMem_finset support
  exact missing (covers action (all_actions_nonempty action))

def eraseBool : Bool → Unit := fun _ => ()

abbrev MatchingPair := FinitePowersetWeakPullback.Pair eraseBool eraseBool

def ff : MatchingPair := ⟨(false, false), rfl⟩
def tt : MatchingPair := ⟨(true, true), rfl⟩
def ft : MatchingPair := ⟨(false, true), rfl⟩
def tf : MatchingPair := ⟨(true, false), rfl⟩

def diagonal : Finset MatchingPair := {ff, tt}
def crossed : Finset MatchingPair := {ft, tf}

theorem distinct_matching_relations : diagonal ≠ crossed := by
  intro same
  have member : ff ∈ crossed := by rw [← same]; simp [diagonal]
  simp [crossed, ff, ft, tf] at member

theorem same_complete_projection_readouts :
    FinitePowersetWeakPullback.comparison eraseBool eraseBool diagonal =
      FinitePowersetWeakPullback.comparison eraseBool eraseBool crossed := by
  apply Subtype.ext
  apply Prod.ext
  · ext value
    cases value <;>
      simp [FinitePowersetWeakPullback.comparison, FinitePowersetWeakPullback.first,
        FinitePowerset.map, diagonal, crossed, ff, tt, ft, tf]
  · ext value
    cases value <;>
      simp [FinitePowersetWeakPullback.comparison, FinitePowersetWeakPullback.second,
        FinitePowerset.map, diagonal, crossed, ff, tt, ft, tf]

theorem weak_comparison_is_not_injective :
    ¬ Function.Injective (FinitePowersetWeakPullback.comparison eraseBool eraseBool) :=
  fun injective => distinct_matching_relations
    (injective same_complete_projection_readouts)

theorem no_matching_receipt_decoder :
    ¬ ∃ decode : FinitePowersetWeakPullback.Pair
        (FinitePowerset.map eraseBool) (FinitePowerset.map eraseBool) → Finset MatchingPair,
      ∀ supplied, decode
        (FinitePowersetWeakPullback.comparison eraseBool eraseBool supplied) = supplied := by
  rintro ⟨decode, recovers⟩
  apply distinct_matching_relations
  exact (recovers diagonal).symm.trans
    ((congrArg decode same_complete_projection_readouts).trans (recovers crossed))

end Mettapedia.OSLF.FiniteBranching.Controls
