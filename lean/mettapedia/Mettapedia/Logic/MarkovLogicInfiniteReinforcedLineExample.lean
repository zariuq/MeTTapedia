import Mathlib.Logic.Equiv.Nat
import Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
import Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
import Mettapedia.Logic.MarkovLogicInfiniteWorldModel

/-!
# Reinforced Half-Line MLN

This file sets up a one-dimensional Ising-style infinite MLN on `Nat`, with
two implication clauses per edge.  The edge log-weights are allowed to vary with
the position; this is the small formal target for a domain-wall phase-splitting
argument where increasingly strong couplings can preserve boundary influence at
the origin.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteReinforcedLineExample

open scoped ENNReal BigOperators
open Filter
open MeasureTheory
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteCylinders
open Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
open Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel

/-- Countable half-line nodes. -/
abbrev LineNode := Nat

/-- The origin site for the reinforced-line observable. -/
def lineOrigin : LineNode := 0

/-- All-plus boundary condition for finite-volume limits. -/
def linePlusBoundary : BoundaryCondition LineNode := fun _ => true

/-- All-minus boundary condition for finite-volume limits. -/
def lineMinusBoundary : BoundaryCondition LineNode := fun _ => false

def lineSpinFlipWorld {Atom : Type*} (ω : InfiniteWorld Atom) :
    InfiniteWorld Atom :=
  fun a => !ω a

def lineSpinFlipLocalAssignment {Atom : Type*} {Λ : Region Atom}
    (x : LocalAssignment Atom Λ) : LocalAssignment Atom Λ :=
  fun a => !x a

@[simp] theorem lineSpinFlipWorld_apply {Atom : Type*}
    (ω : InfiniteWorld Atom) (a : Atom) :
    lineSpinFlipWorld ω a = !ω a := rfl

@[simp] theorem lineSpinFlipLocalAssignment_apply {Atom : Type*} {Λ : Region Atom}
    (x : LocalAssignment Atom Λ) (a : RegionAtom Atom Λ) :
    lineSpinFlipLocalAssignment x a = !x a := rfl

theorem lineSpinFlipWorld_involutive {Atom : Type*}
    (ω : InfiniteWorld Atom) :
    lineSpinFlipWorld (lineSpinFlipWorld ω) = ω := by
  funext a
  simp [lineSpinFlipWorld]

theorem lineSpinFlipLocalAssignment_involutive {Atom : Type*} {Λ : Region Atom}
    (x : LocalAssignment Atom Λ) :
    lineSpinFlipLocalAssignment (lineSpinFlipLocalAssignment x) = x := by
  funext a
  simp [lineSpinFlipLocalAssignment]

theorem lineSpinFlipLocalAssignment_bijective {Atom : Type*} {Λ : Region Atom} :
    Function.Bijective (@lineSpinFlipLocalAssignment Atom Λ) := by
  constructor
  · intro a b h
    have hflip := congrArg lineSpinFlipLocalAssignment h
    simpa [lineSpinFlipLocalAssignment_involutive] using hflip
  · intro a
    exact ⟨lineSpinFlipLocalAssignment a, by simp [lineSpinFlipLocalAssignment_involutive]⟩

theorem lineSpinFlipWorld_patch {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (x : LocalAssignment Atom Λ) (ξ : BoundaryCondition Atom) :
    lineSpinFlipWorld (patch Λ x ξ) =
      patch Λ (lineSpinFlipLocalAssignment x) (lineSpinFlipWorld ξ) := by
  funext a
  by_cases ha : a ∈ Λ <;> simp [lineSpinFlipWorld, lineSpinFlipLocalAssignment, patch, ha]

@[simp] theorem lineSpinFlipWorld_linePlusBoundary :
    lineSpinFlipWorld linePlusBoundary = lineMinusBoundary := by
  funext a
  simp [lineSpinFlipWorld, linePlusBoundary, lineMinusBoundary]

@[simp] theorem lineSpinFlipWorld_lineMinusBoundary :
    lineSpinFlipWorld lineMinusBoundary = linePlusBoundary := by
  funext a
  simp [lineSpinFlipWorld, linePlusBoundary, lineMinusBoundary]

/-- Global finite query: the origin spin is up/true. -/
def lineOriginSpinUpQuery : ConstraintQuery LineNode :=
  [⟨lineOrigin, true⟩]

/-- Local one-site query: the origin spin is up/true. -/
def lineOriginSpinUpLocalQuery :
    LocalConstraintQuery LineNode ({lineOrigin} : Region LineNode) :=
  [⟨⟨lineOrigin, by simp [lineOrigin]⟩, true⟩]

/-- The local origin-spin query denotes exactly the singleton true-assignment
set on the origin cylinder. -/
theorem lineOriginSpinUpLocalConstraintSet_eq :
    localConstraintSet ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery =
      singletonTrueAssignmentSet lineOrigin := by
  ext x
  constructor
  · intro hx
    have hmem :
        (⟨⟨lineOrigin, by simp [lineOrigin]⟩, true⟩ :
          Sigma fun _ : RegionAtom LineNode ({lineOrigin} : Region LineNode) => Bool) ∈
            lineOriginSpinUpLocalQuery := by
      simp [lineOriginSpinUpLocalQuery]
    have h := hx _ hmem
    simpa [singletonTrueAssignmentSet] using h
  · intro hx c hc
    simp [lineOriginSpinUpLocalQuery] at hc
    rcases hc with rfl
    simpa [singletonTrueAssignmentSet] using hx

theorem lineSpinFlipLocalAssignment_mem_originSpinUp_iff_not
    (x : LocalAssignment LineNode ({lineOrigin} : Region LineNode)) :
    lineSpinFlipLocalAssignment x ∈
        localConstraintSet ({lineOrigin} : Region LineNode)
          lineOriginSpinUpLocalQuery ↔
      x ∉
        localConstraintSet ({lineOrigin} : Region LineNode)
          lineOriginSpinUpLocalQuery := by
  rw [lineOriginSpinUpLocalConstraintSet_eq]
  simp [singletonTrueAssignmentSet, lineSpinFlipLocalAssignment]

/-- One-site origin-spin query viewed inside any finite region that contains
the origin. -/
def lineOriginSpinLocalQueryInRegion
    (Λ : Region LineNode) (hOrigin : lineOrigin ∈ Λ) (b : Bool) :
    LocalConstraintQuery LineNode Λ :=
  [⟨⟨lineOrigin, hOrigin⟩, b⟩]

theorem lineSpinFlipLocalAssignment_satisfies_originSpinInRegion_iff
    (Λ : Region LineNode) (hOrigin : lineOrigin ∈ Λ) (b : Bool)
    (x : LocalAssignment LineNode Λ) :
    satisfiesConstraints (lineSpinFlipLocalAssignment x)
        (lineOriginSpinLocalQueryInRegion Λ hOrigin b) ↔
      satisfiesConstraints x
        (lineOriginSpinLocalQueryInRegion Λ hOrigin (!b)) := by
  cases b <;> simp [satisfiesConstraints, lineOriginSpinLocalQueryInRegion,
    lineSpinFlipLocalAssignment]

/-- The global origin-spin event is the same cylinder event used by the local
DLR/Walley readout. -/
theorem lineOriginSpinUpEvent_eq_cylinder :
    infiniteQueryEvent lineOriginSpinUpQuery =
      MeasureTheory.cylinder ({lineOrigin} : Region LineNode)
        (singletonTrueAssignmentSet lineOrigin) := by
  ext ω
  simp [infiniteQueryEvent, lineOriginSpinUpQuery, satisfiesConstraints,
    MeasureTheory.mem_cylinder, singletonTrueAssignmentSet, lineOrigin]

/-- The local and global presentations of the origin-spin event are the same
measurable cylinder. -/
theorem lineOriginSpinUpLocalQueryEvent_eq_global :
    localQueryEvent ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery =
      infiniteQueryEvent lineOriginSpinUpQuery := by
  rw [localQueryEvent_eq_cylinder]
  rw [lineOriginSpinUpLocalConstraintSet_eq]
  rw [lineOriginSpinUpEvent_eq_cylinder]

theorem localQueryEvent_lineOriginSpinLocalQueryInRegion_eq_originSpinUp
    (Λ : Region LineNode) (hOrigin : lineOrigin ∈ Λ) :
    localQueryEvent Λ (lineOriginSpinLocalQueryInRegion Λ hOrigin true) =
      localQueryEvent ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery := by
  ext ω
  simp [localQueryEvent, worldRestriction, satisfiesConstraints,
    lineOriginSpinLocalQueryInRegion, lineOriginSpinUpLocalQuery]

/-- Clause ids for the reinforced half-line. -/
inductive ReinforcedLineClauseId where
  | forward : Nat → ReinforcedLineClauseId
  | backward : Nat → ReinforcedLineClauseId
deriving DecidableEq

/-- Forward implication on edge `n -- n+1`. -/
def lineForwardClause (n : Nat) : GroundClause LineNode :=
  {Literal.neg n, Literal.pos (n + 1)}

/-- Reverse implication on edge `n -- n+1`.  Together with `lineForwardClause`,
this rewards equal neighbouring spins and is spin-flip symmetric. -/
def lineBackwardClause (n : Nat) : GroundClause LineNode :=
  {Literal.pos n, Literal.neg (n + 1)}

/-- Underlying clause attached to a reinforced-line clause id. -/
def reinforcedLineClause : ReinforcedLineClauseId → GroundClause LineNode
  | .forward n => lineForwardClause n
  | .backward n => lineBackwardClause n

/-- Spin flip swaps the two implications on each edge. -/
def reinforcedLineClauseFlip : ReinforcedLineClauseId → ReinforcedLineClauseId
  | .forward n => .backward n
  | .backward n => .forward n

@[simp] theorem reinforcedLineClauseFlip_involutive
    (j : ReinforcedLineClauseId) :
    reinforcedLineClauseFlip (reinforcedLineClauseFlip j) = j := by
  cases j <;> rfl

theorem reinforcedLineClauseFlip_bijective :
    Function.Bijective reinforcedLineClauseFlip := by
  constructor
  · intro a b h
    have hflip := congrArg reinforcedLineClauseFlip h
    simpa using hflip
  · intro a
    exact ⟨reinforcedLineClauseFlip a, by simp⟩

@[simp] theorem lineForwardClause_atoms (n : Nat) :
    (lineForwardClause n).atoms = ({n, n + 1} : Finset LineNode) := by
  ext a
  simp [lineForwardClause, GroundClause.atoms, Literal.atom]

@[simp] theorem lineBackwardClause_atoms (n : Nat) :
    (lineBackwardClause n).atoms = ({n, n + 1} : Finset LineNode) := by
  ext a
  simp [lineBackwardClause, GroundClause.atoms, Literal.atom]

theorem lineForwardClause_holds_spinFlip_iff_backward
    (n : Nat) (W : InfiniteWorld LineNode) :
    (lineForwardClause n).holds (lineSpinFlipWorld W) ↔
      (lineBackwardClause n).holds W := by
  simp [lineForwardClause, lineBackwardClause, GroundClause.holds,
    Literal.holds, lineSpinFlipWorld]

theorem lineBackwardClause_holds_spinFlip_iff_forward
    (n : Nat) (W : InfiniteWorld LineNode) :
    (lineBackwardClause n).holds (lineSpinFlipWorld W) ↔
      (lineForwardClause n).holds W := by
  simp [lineForwardClause, lineBackwardClause, GroundClause.holds,
    Literal.holds, lineSpinFlipWorld]

theorem reinforcedLineEdgePair_eval_spinFlip_eq
    (w : ℝ) (n : Nat) (W : InfiniteWorld LineNode) :
    (classicalWeightedClause (lineForwardClause n) w).eval (lineSpinFlipWorld W) *
        (classicalWeightedClause (lineBackwardClause n) w).eval (lineSpinFlipWorld W) =
      (classicalWeightedClause (lineForwardClause n) w).eval W *
        (classicalWeightedClause (lineBackwardClause n) w).eval W := by
  by_cases hf : (lineForwardClause n).holds W <;>
    by_cases hb : (lineBackwardClause n).holds W <;>
      simp [WeightedGroundClause.eval, classicalWeightedClause,
        lineForwardClause_holds_spinFlip_iff_backward,
        lineBackwardClause_holds_spinFlip_iff_forward,
        hf, hb, mul_comm]

/-- Finite clause support for a finite half-line region.  For every site in the
region we include the edge to its right and the edge from its predecessor, with
both implications for each edge. -/
noncomputable def reinforcedLineRegionSupport
    (Λ : Region LineNode) : Finset ReinforcedLineClauseId :=
  (Λ.image ReinforcedLineClauseId.forward) ∪
    (((Λ.image Nat.pred).image ReinforcedLineClauseId.forward) ∪
      ((Λ.image ReinforcedLineClauseId.backward) ∪
        ((Λ.image Nat.pred).image ReinforcedLineClauseId.backward)))

theorem reinforcedLineClauseFlip_mem_regionSupport_iff
    (Λ : Region LineNode) (j : ReinforcedLineClauseId) :
    reinforcedLineClauseFlip j ∈ reinforcedLineRegionSupport Λ ↔
      j ∈ reinforcedLineRegionSupport Λ := by
  cases j <;>
    simp [reinforcedLineRegionSupport, reinforcedLineClauseFlip, or_comm]

theorem reinforcedLineRegionSupport_sound
    {Λ : Region LineNode} {j : ReinforcedLineClauseId}
    (hj : j ∈ reinforcedLineRegionSupport Λ) :
    clauseTouchesRegion (reinforcedLineClause j) Λ := by
  rw [reinforcedLineRegionSupport] at hj
  rcases Finset.mem_union.mp hj with hforwardOut | hrest
  · rcases Finset.mem_image.mp hforwardOut with ⟨n, hnΛ, rfl⟩
    refine ⟨n, ?_, hnΛ⟩
    simp [reinforcedLineClause]
  · rcases Finset.mem_union.mp hrest with hforwardIn | hrest
    · rcases Finset.mem_image.mp hforwardIn with ⟨p, hp, rfl⟩
      rcases Finset.mem_image.mp hp with ⟨a, haΛ, hpred⟩
      by_cases ha0 : a = 0
      · subst ha0
        have hp0 : p = 0 := by simpa using hpred.symm
        subst hp0
        refine ⟨0, ?_, by simpa using haΛ⟩
        simp [reinforcedLineClause]
      · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
        have hpEq : p = Nat.pred a := by simpa using hpred.symm
        subst hpEq
        refine ⟨a, ?_, haΛ⟩
        have hmem : a = Nat.pred a + 1 := (Nat.succ_pred_eq_of_pos ha_pos).symm
        simpa [reinforcedLineClause, lineForwardClause_atoms] using Or.inr hmem
    · rcases Finset.mem_union.mp hrest with hbackwardOut | hbackwardIn
      · rcases Finset.mem_image.mp hbackwardOut with ⟨n, hnΛ, rfl⟩
        refine ⟨n, ?_, hnΛ⟩
        simp [reinforcedLineClause]
      · rcases Finset.mem_image.mp hbackwardIn with ⟨p, hp, rfl⟩
        rcases Finset.mem_image.mp hp with ⟨a, haΛ, hpred⟩
        by_cases ha0 : a = 0
        · subst ha0
          have hp0 : p = 0 := by simpa using hpred.symm
          subst hp0
          refine ⟨0, ?_, by simpa using haΛ⟩
          simp [reinforcedLineClause]
        · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
          have hpEq : p = Nat.pred a := by simpa using hpred.symm
          subst hpEq
          refine ⟨a, ?_, haΛ⟩
          have hmem : a = Nat.pred a + 1 := (Nat.succ_pred_eq_of_pos ha_pos).symm
          simpa [reinforcedLineClause, lineBackwardClause_atoms] using Or.inr hmem

theorem reinforcedLineRegionSupport_complete
    {Λ : Region LineNode} {j : ReinforcedLineClauseId}
    (hj : clauseTouchesRegion (reinforcedLineClause j) Λ) :
    j ∈ reinforcedLineRegionSupport Λ := by
  cases j with
  | forward n =>
    rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = n ∨ a = n + 1 := by
      simpa [reinforcedLineClause] using haAtoms
    rw [reinforcedLineRegionSupport]
    rcases ha with haEq | haNext
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_image.mpr ⟨n, by simpa [haEq] using haΛ, rfl⟩
    · have hpredmem :
          Nat.pred (n + 1) ∈ Finset.image Nat.pred Λ :=
        Finset.mem_image.mpr ⟨n + 1, by simpa [haNext] using haΛ, rfl⟩
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_image.mpr ⟨Nat.pred (n + 1), hpredmem, by simp⟩
  | backward n =>
    rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = n ∨ a = n + 1 := by
      simpa [reinforcedLineClause] using haAtoms
    rw [reinforcedLineRegionSupport]
    rcases ha with haEq | haNext
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_image.mpr ⟨n, by simpa [haEq] using haΛ, rfl⟩
    · have hpredmem :
          Nat.pred (n + 1) ∈ Finset.image Nat.pred Λ :=
        Finset.mem_image.mpr ⟨n + 1, by simpa [haNext] using haΛ, rfl⟩
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_image.mpr ⟨Nat.pred (n + 1), hpredmem, by simp⟩

/-- Prefix exhaustion of the half-line. -/
def reinforcedLineExhaustion : RegionExhaustion LineNode where
  region n := Finset.range (n + 1)
  monotone := by
    intro m n hmn a ha
    exact Finset.mem_range.mpr <|
      lt_of_lt_of_le (Finset.mem_range.mp ha) (Nat.succ_le_succ hmn)
  exhaustive := by
    intro a
    exact ⟨a, Finset.mem_range.mpr (Nat.lt_succ_self a)⟩

theorem lineOrigin_mem_reinforcedLineExhaustion_region (n : ℕ) :
    lineOrigin ∈ reinforcedLineExhaustion.region n := by
  simp [reinforcedLineExhaustion, lineOrigin]

theorem reinforcedLine_mem_exhaustion_region_of_le
    {n k : Nat} (hk : k ≤ n) :
    k ∈ reinforcedLineExhaustion.region n := by
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)

theorem reinforcedLine_succ_not_mem_exhaustion_region (n : Nat) :
    n + 1 ∉ reinforcedLineExhaustion.region n := by
  simp [reinforcedLineExhaustion]

theorem reinforcedLine_pred_image_range_subset (n : Nat) :
    (Finset.range (n + 1)).image Nat.pred ⊆ Finset.range (n + 1) := by
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨a, ha, rfl⟩
  exact Finset.mem_range.mpr
    (lt_of_le_of_lt (Nat.pred_le a) (Finset.mem_range.mp ha))

/-- On the prefix volume `0..n`, the active clauses are exactly the two
implications on edges `0..n`; edge `n` talks to the boundary site `n+1`. -/
theorem reinforcedLineRegionSupport_exhaustion_region (n : Nat) :
    reinforcedLineRegionSupport (reinforcedLineExhaustion.region n) =
      ((Finset.range (n + 1)).image ReinforcedLineClauseId.forward ∪
        (Finset.range (n + 1)).image ReinforcedLineClauseId.backward) := by
  ext j
  cases j with
  | forward k =>
      simp [reinforcedLineRegionSupport, reinforcedLineExhaustion]
      intro x hx hk
      rw [← hk]
      exact le_trans (Nat.sub_le x 1) hx
  | backward k =>
      simp [reinforcedLineRegionSupport, reinforcedLineExhaustion]
      intro x hx hk
      rw [← hk]
      exact le_trans (Nat.sub_le x 1) hx

/-- If the origin is false while the plus boundary to the right is true, then
some edge in the prefix volume is the first false-to-true domain wall. -/
theorem exists_reinforcedLine_firstDomainWall_of_origin_false
    (n : Nat)
    (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n))
    (hOriginFalse :
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary lineOrigin = false) :
    ∃ k : Nat,
      k ≤ n ∧
        patch (reinforcedLineExhaustion.region n) x linePlusBoundary k = false ∧
          patch (reinforcedLineExhaustion.region n) x linePlusBoundary (k + 1) = true := by
  classical
  let W : InfiniteWorld LineNode :=
    patch (reinforcedLineExhaustion.region n) x linePlusBoundary
  have hBoundary : W (n + 1) = true := by
    simp [W, reinforcedLineExhaustion, linePlusBoundary]
  let P : Nat → Prop := fun m => W m = true
  have hExists : ∃ m : Nat, P m := ⟨n + 1, hBoundary⟩
  let j : Nat := Nat.find hExists
  have hjTrue : P j := by
    simpa [j] using Nat.find_spec hExists
  have hnot0 : ¬ P 0 := by
    simpa [P, W, lineOrigin] using hOriginFalse
  have hjPos : 0 < j := by
    exact Nat.pos_of_ne_zero (fun hj0 => hnot0 (by simpa [P, j, hj0] using hjTrue))
  have hjLe : j ≤ n + 1 := by
    exact Nat.find_min' hExists hBoundary
  let k : Nat := Nat.pred j
  have hkLtJ : k < j := by
    simpa [k] using Nat.pred_lt hjPos.ne'
  have hkFalse : W k = false := by
    have hnot : ¬ P k := Nat.find_min hExists hkLtJ
    cases hk : W k <;> simp [P, hk] at hnot ⊢
  have hkSucc : k + 1 = j := by
    simpa [k] using Nat.succ_pred_eq_of_pos hjPos
  have hkLe : k ≤ n := by
    omega
  refine ⟨k, hkLe, ?_, ?_⟩
  · simpa [W] using hkFalse
  · simpa [W, hkSucc] using hjTrue

def reinforcedLineOriginFalseDomainWallAt
    (n k : Nat)
    (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n)) : Prop :=
  patch (reinforcedLineExhaustion.region n) x linePlusBoundary lineOrigin = false ∧
    k ≤ n ∧
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary k = false ∧
        patch (reinforcedLineExhaustion.region n) x linePlusBoundary (k + 1) = true

/-- Flip the initial segment `0..k` of a local prefix assignment. -/
def reinforcedLineFlipPrefix (n k : Nat)
    (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n)) :
    LocalAssignment LineNode (reinforcedLineExhaustion.region n) :=
  fun a => if a.1 ≤ k then !x a else x a

@[simp] theorem reinforcedLineFlipPrefix_apply_le
    (n k : Nat) (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n))
    (a : RegionAtom LineNode (reinforcedLineExhaustion.region n))
    (ha : a.1 ≤ k) :
    reinforcedLineFlipPrefix n k x a = !x a := by
  simp [reinforcedLineFlipPrefix, ha]

@[simp] theorem reinforcedLineFlipPrefix_apply_gt
    (n k : Nat) (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n))
    (a : RegionAtom LineNode (reinforcedLineExhaustion.region n))
    (ha : k < a.1) :
    reinforcedLineFlipPrefix n k x a = x a := by
  simp [reinforcedLineFlipPrefix, not_le.mpr ha]

theorem reinforcedLineFlipPrefix_involutive
    (n k : Nat) (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n)) :
    reinforcedLineFlipPrefix n k (reinforcedLineFlipPrefix n k x) = x := by
  funext a
  by_cases ha : a.1 ≤ k <;> simp [reinforcedLineFlipPrefix, ha]

theorem reinforcedLineFlipPrefix_bijective
    (n k : Nat) :
    Function.Bijective (reinforcedLineFlipPrefix n k) := by
  constructor
  · intro a b h
    have hflip := congrArg (reinforcedLineFlipPrefix n k) h
    simpa [reinforcedLineFlipPrefix_involutive] using hflip
  · intro a
    exact ⟨reinforcedLineFlipPrefix n k a, by simp [reinforcedLineFlipPrefix_involutive]⟩

theorem reinforcedLineFlipPrefix_origin_of_origin_false
    {n k : Nat}
    (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n))
    (hOrigin : x ⟨lineOrigin, lineOrigin_mem_reinforcedLineExhaustion_region n⟩ = false) :
    reinforcedLineFlipPrefix n k x
        ⟨lineOrigin, lineOrigin_mem_reinforcedLineExhaustion_region n⟩ = true := by
  have hOrigin' :
      x ⟨0, lineOrigin_mem_reinforcedLineExhaustion_region n⟩ = false := by
    exact hOrigin
  simp [reinforcedLineFlipPrefix, lineOrigin, hOrigin']

theorem reinforcedLineFlipPrefix_patch_domainWall_left
    {n k : Nat}
    (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n))
    (hk : k ≤ n)
    (hleft :
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary k = false) :
    patch (reinforcedLineExhaustion.region n) (reinforcedLineFlipPrefix n k x)
        linePlusBoundary k = true := by
  have hkMem : k ∈ reinforcedLineExhaustion.region n :=
    reinforcedLine_mem_exhaustion_region_of_le hk
  have hxleft : x ⟨k, hkMem⟩ = false := by
    simpa [patch, hkMem] using hleft
  simp [patch, hkMem, reinforcedLineFlipPrefix, hxleft]

theorem reinforcedLineFlipPrefix_patch_domainWall_right
    {n k : Nat}
    (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n))
    (hright :
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary (k + 1) = true) :
    patch (reinforcedLineExhaustion.region n) (reinforcedLineFlipPrefix n k x)
        linePlusBoundary (k + 1) = true := by
  by_cases hmem : k + 1 ∈ reinforcedLineExhaustion.region n
  · have hxright : x ⟨k + 1, hmem⟩ = true := by
      simpa [patch, hmem] using hright
    simp [patch, hmem, reinforcedLineFlipPrefix, hxright]
  · simp [patch, hmem, linePlusBoundary]

theorem reinforcedLineFlipPrefix_patch_domainWall_edge
    {n k : Nat}
    (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n))
    (hk : k ≤ n)
    (hleft :
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary k = false)
    (hright :
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary (k + 1) = true) :
    patch (reinforcedLineExhaustion.region n) (reinforcedLineFlipPrefix n k x)
        linePlusBoundary k = true ∧
      patch (reinforcedLineExhaustion.region n) (reinforcedLineFlipPrefix n k x)
        linePlusBoundary (k + 1) = true := by
  exact ⟨reinforcedLineFlipPrefix_patch_domainWall_left x hk hleft,
    reinforcedLineFlipPrefix_patch_domainWall_right x hright⟩

theorem reinforcedLine_domainWall_edgePair_eval_flipPrefix
    (edgeLogWeight : Nat → ℝ) {n k : Nat}
    (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n))
    (hk : k ≤ n)
    (hleft :
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary k = false)
    (hright :
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary (k + 1) = true) :
    let W : InfiniteWorld LineNode :=
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary
    let W' : InfiniteWorld LineNode :=
      patch (reinforcedLineExhaustion.region n) (reinforcedLineFlipPrefix n k x)
        linePlusBoundary
    (classicalWeightedClause (lineForwardClause k) (edgeLogWeight k)).eval W' *
        (classicalWeightedClause (lineBackwardClause k) (edgeLogWeight k)).eval W' =
      ENNReal.ofReal (Real.exp (edgeLogWeight k)) *
        ((classicalWeightedClause (lineForwardClause k) (edgeLogWeight k)).eval W *
          (classicalWeightedClause (lineBackwardClause k) (edgeLogWeight k)).eval W) := by
  intro W W'
  have hflip :=
    reinforcedLineFlipPrefix_patch_domainWall_edge x hk hleft hright
  simp [W, W', WeightedGroundClause.eval, classicalWeightedClause,
    lineForwardClause, lineBackwardClause, GroundClause.holds, Literal.holds,
    hleft, hright, hflip.1, hflip.2]

/-- Classical reinforced-line MLN with position-dependent edge log-weights. -/
noncomputable def reinforcedLineClassicalSpec
    (edgeLogWeight : Nat → ℝ) :
    ClassicalInfiniteGroundMLNSpec LineNode ReinforcedLineClauseId where
  clause := reinforcedLineClause
  logWeight j := match j with
    | .forward n => edgeLogWeight n
    | .backward n => edgeLogWeight n
  regionSupport := reinforcedLineRegionSupport
  regionSupport_sound := fun hj => reinforcedLineRegionSupport_sound hj
  regionSupport_complete := fun hj => reinforcedLineRegionSupport_complete hj

@[simp] theorem reinforcedLineClassicalSpec_clause
    (edgeLogWeight : Nat → ℝ) (j : ReinforcedLineClauseId) :
    (reinforcedLineClassicalSpec edgeLogWeight).clause j =
      reinforcedLineClause j := rfl

@[simp] theorem reinforcedLineClassicalSpec_logWeight_forward
    (edgeLogWeight : Nat → ℝ) (n : Nat) :
    (reinforcedLineClassicalSpec edgeLogWeight).logWeight
      (ReinforcedLineClauseId.forward n) = edgeLogWeight n := rfl

@[simp] theorem reinforcedLineClassicalSpec_logWeight_backward
    (edgeLogWeight : Nat → ℝ) (n : Nat) :
    (reinforcedLineClassicalSpec edgeLogWeight).logWeight
      (ReinforcedLineClauseId.backward n) = edgeLogWeight n := rfl

@[simp] theorem reinforcedLineClassicalSpec_regionSupport
    (edgeLogWeight : Nat → ℝ) (Λ : Region LineNode) :
    (reinforcedLineClassicalSpec edgeLogWeight).regionSupport Λ =
      reinforcedLineRegionSupport Λ := rfl

noncomputable def reinforcedLineEdgePairWeight
    (edgeLogWeight : Nat → ℝ) (i : Nat) (W : InfiniteWorld LineNode) :
    ENNReal :=
  ((reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.clauseData
      (ReinforcedLineClauseId.forward i)).eval W *
    ((reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.clauseData
      (ReinforcedLineClauseId.backward i)).eval W

theorem lineForwardClause_holds_congr_edge
    {i : Nat} {W W' : InfiniteWorld LineNode}
    (hi : W i = W' i) (hsucc : W (i + 1) = W' (i + 1)) :
    (lineForwardClause i).holds W ↔ (lineForwardClause i).holds W' := by
  simp [lineForwardClause, GroundClause.holds, Literal.holds, hi, hsucc]

theorem lineBackwardClause_holds_congr_edge
    {i : Nat} {W W' : InfiniteWorld LineNode}
    (hi : W i = W' i) (hsucc : W (i + 1) = W' (i + 1)) :
    (lineBackwardClause i).holds W ↔ (lineBackwardClause i).holds W' := by
  simp [lineBackwardClause, GroundClause.holds, Literal.holds, hi, hsucc]

theorem reinforcedLineEdgePairWeight_congr_edge
    (edgeLogWeight : Nat → ℝ) {i : Nat} {W W' : InfiniteWorld LineNode}
    (hi : W i = W' i) (hsucc : W (i + 1) = W' (i + 1)) :
    reinforcedLineEdgePairWeight edgeLogWeight i W =
      reinforcedLineEdgePairWeight edgeLogWeight i W' := by
  have hForward :
      (classicalWeightedClause (lineForwardClause i) (edgeLogWeight i)).eval W =
        (classicalWeightedClause (lineForwardClause i) (edgeLogWeight i)).eval W' := by
    by_cases h : (lineForwardClause i).holds W
    · have h' : (lineForwardClause i).holds W' :=
        (lineForwardClause_holds_congr_edge hi hsucc).mp h
      simp [WeightedGroundClause.eval, classicalWeightedClause, h, h']
    · have h' : ¬ (lineForwardClause i).holds W' := by
        intro hW'
        exact h ((lineForwardClause_holds_congr_edge hi hsucc).mpr hW')
      simp [WeightedGroundClause.eval, classicalWeightedClause, h, h']
  have hBackward :
      (classicalWeightedClause (lineBackwardClause i) (edgeLogWeight i)).eval W =
        (classicalWeightedClause (lineBackwardClause i) (edgeLogWeight i)).eval W' := by
    by_cases h : (lineBackwardClause i).holds W
    · have h' : (lineBackwardClause i).holds W' :=
        (lineBackwardClause_holds_congr_edge hi hsucc).mp h
      simp [WeightedGroundClause.eval, classicalWeightedClause, h, h']
    · have h' : ¬ (lineBackwardClause i).holds W' := by
        intro hW'
        exact h ((lineBackwardClause_holds_congr_edge hi hsucc).mpr hW')
      simp [WeightedGroundClause.eval, classicalWeightedClause, h, h']
  change
    (classicalWeightedClause (lineForwardClause i) (edgeLogWeight i)).eval W *
        (classicalWeightedClause (lineBackwardClause i) (edgeLogWeight i)).eval W =
      (classicalWeightedClause (lineForwardClause i) (edgeLogWeight i)).eval W' *
        (classicalWeightedClause (lineBackwardClause i) (edgeLogWeight i)).eval W'
  rw [hForward, hBackward]

theorem reinforcedLineEdgePairWeight_spinFlip_eq
    (edgeLogWeight : Nat → ℝ) (i : Nat) (W : InfiniteWorld LineNode) :
    reinforcedLineEdgePairWeight edgeLogWeight i (lineSpinFlipWorld W) =
      reinforcedLineEdgePairWeight edgeLogWeight i W := by
  change
    (classicalWeightedClause (lineForwardClause i) (edgeLogWeight i)).eval (lineSpinFlipWorld W) *
        (classicalWeightedClause (lineBackwardClause i) (edgeLogWeight i)).eval (lineSpinFlipWorld W) =
      (classicalWeightedClause (lineForwardClause i) (edgeLogWeight i)).eval W *
        (classicalWeightedClause (lineBackwardClause i) (edgeLogWeight i)).eval W
  exact reinforcedLineEdgePair_eval_spinFlip_eq (edgeLogWeight i) i W

theorem reinforcedLineEdgePairWeight_flipPrefix_domainWall
    (edgeLogWeight : Nat → ℝ) {n k : Nat}
    (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n))
    (hk : k ≤ n)
    (hleft :
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary k = false)
    (hright :
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary (k + 1) = true) :
    let W : InfiniteWorld LineNode :=
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary
    let W' : InfiniteWorld LineNode :=
      patch (reinforcedLineExhaustion.region n) (reinforcedLineFlipPrefix n k x)
        linePlusBoundary
    reinforcedLineEdgePairWeight edgeLogWeight k W' =
      ENNReal.ofReal (Real.exp (edgeLogWeight k)) *
        reinforcedLineEdgePairWeight edgeLogWeight k W := by
  simpa [reinforcedLineEdgePairWeight,
    ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec,
    reinforcedLineClassicalSpec, reinforcedLineClause] using
    (reinforcedLine_domainWall_edgePair_eval_flipPrefix edgeLogWeight x hk hleft hright)

theorem reinforcedLineEdgePairWeight_flipPrefix_eq_of_ne
    (edgeLogWeight : Nat → ℝ) {n k i : Nat}
    (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n))
    (hk : k ≤ n) (hi : i ≤ n) (hne : i ≠ k) :
    reinforcedLineEdgePairWeight edgeLogWeight i
        (patch (reinforcedLineExhaustion.region n) (reinforcedLineFlipPrefix n k x)
          linePlusBoundary) =
      reinforcedLineEdgePairWeight edgeLogWeight i
        (patch (reinforcedLineExhaustion.region n) x linePlusBoundary) := by
  let W : InfiniteWorld LineNode :=
    patch (reinforcedLineExhaustion.region n) x linePlusBoundary
  let W' : InfiniteWorld LineNode :=
    patch (reinforcedLineExhaustion.region n) (reinforcedLineFlipPrefix n k x)
      linePlusBoundary
  rcases Nat.lt_or_gt_of_ne hne with hik | hki
  · have hiMem : i ∈ reinforcedLineExhaustion.region n :=
      reinforcedLine_mem_exhaustion_region_of_le hi
    have hisuccMem : i + 1 ∈ reinforcedLineExhaustion.region n :=
      reinforcedLine_mem_exhaustion_region_of_le
        (Nat.succ_le_of_lt (lt_of_lt_of_le hik hk))
    have hi_le_k : i ≤ k := le_of_lt hik
    have hisucc_le_k : i + 1 ≤ k := Nat.succ_le_of_lt hik
    have hW' :
        reinforcedLineEdgePairWeight edgeLogWeight i W' =
          reinforcedLineEdgePairWeight edgeLogWeight i (lineSpinFlipWorld W) := by
      refine reinforcedLineEdgePairWeight_congr_edge edgeLogWeight ?_ ?_
      · simp [W, W', hiMem, reinforcedLineFlipPrefix, hi_le_k,
          lineSpinFlipWorld]
      · simp [W, W', hisuccMem, reinforcedLineFlipPrefix, hisucc_le_k,
          lineSpinFlipWorld]
    have hSpin := reinforcedLineEdgePairWeight_spinFlip_eq edgeLogWeight i W
    simpa [W, W'] using hW'.trans hSpin
  · have hiMem : i ∈ reinforcedLineExhaustion.region n :=
      reinforcedLine_mem_exhaustion_region_of_le hi
    by_cases hisucc : i + 1 ∈ reinforcedLineExhaustion.region n
    · have hki' : k < i := hki
      have hksucc : k < i + 1 := Nat.lt_trans hki (Nat.lt_succ_self i)
      have hSame :
          reinforcedLineEdgePairWeight edgeLogWeight i W' =
            reinforcedLineEdgePairWeight edgeLogWeight i W := by
        refine reinforcedLineEdgePairWeight_congr_edge edgeLogWeight ?_ ?_
        · simp [W, W', hiMem, reinforcedLineFlipPrefix, not_le.mpr hki']
        · simp [W, W', hisucc, reinforcedLineFlipPrefix, not_le.mpr hksucc]
      simpa [W, W'] using hSame
    · have hki' : k < i := hki
      have hSame :
          reinforcedLineEdgePairWeight edgeLogWeight i W' =
            reinforcedLineEdgePairWeight edgeLogWeight i W := by
        refine reinforcedLineEdgePairWeight_congr_edge edgeLogWeight ?_ ?_
        · simp [W, W', hiMem, reinforcedLineFlipPrefix, not_le.mpr hki']
        · simp [W, W', hisucc, linePlusBoundary]
      simpa [W, W'] using hSame

theorem reinforcedLine_finiteVolumeWeight_prefix_eq_prod_edgePair
    (edgeLogWeight : Nat → ℝ) (n : Nat)
    (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n))
    (ξ : BoundaryCondition LineNode) :
    (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumeWeight
        (reinforcedLineExhaustion.region n) x ξ =
      ∏ i ∈ Finset.range (n + 1),
        reinforcedLineEdgePairWeight edgeLogWeight i
          (patch (reinforcedLineExhaustion.region n) x ξ) := by
  classical
  unfold Mettapedia.Logic.MarkovLogicInfiniteSpecification.InfiniteGroundMLNSpec.finiteVolumeWeight
  change
    (∏ j ∈ reinforcedLineRegionSupport (reinforcedLineExhaustion.region n),
      ((reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.clauseData j).eval
        (patch (reinforcedLineExhaustion.region n) x ξ)) =
      ∏ i ∈ Finset.range (n + 1),
        reinforcedLineEdgePairWeight edgeLogWeight i
          (patch (reinforcedLineExhaustion.region n) x ξ)
  rw [reinforcedLineRegionSupport_exhaustion_region]
  have hdisj :
      Disjoint
        ((Finset.range (n + 1)).image ReinforcedLineClauseId.forward)
        ((Finset.range (n + 1)).image ReinforcedLineClauseId.backward) := by
    rw [Finset.disjoint_left]
    intro j hjF hjB
    rcases Finset.mem_image.mp hjF with ⟨i, _hi, rfl⟩
    rcases Finset.mem_image.mp hjB with ⟨l, _hl, h⟩
    cases h
  rw [Finset.prod_union hdisj]
  rw [Finset.prod_image]
  · rw [Finset.prod_image]
    · rw [← Finset.prod_mul_distrib]
      rfl
    · intro a _ha b _hb h
      injection h
  · intro a _ha b _hb h
    injection h

theorem reinforcedLine_finiteVolumeWeight_flipPrefix_domainWall
    (edgeLogWeight : Nat → ℝ) {n k : Nat}
    (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n))
    (hk : k ≤ n)
    (hleft :
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary k = false)
    (hright :
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary (k + 1) = true) :
    (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumeWeight
        (reinforcedLineExhaustion.region n) (reinforcedLineFlipPrefix n k x)
        linePlusBoundary =
      ENNReal.ofReal (Real.exp (edgeLogWeight k)) *
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumeWeight
          (reinforcedLineExhaustion.region n) x linePlusBoundary := by
  classical
  let s := Finset.range (n + 1)
  let W : InfiniteWorld LineNode :=
    patch (reinforcedLineExhaustion.region n) x linePlusBoundary
  let W' : InfiniteWorld LineNode :=
    patch (reinforcedLineExhaustion.region n) (reinforcedLineFlipPrefix n k x)
      linePlusBoundary
  let factor : ENNReal := ENNReal.ofReal (Real.exp (edgeLogWeight k))
  have hkRange : k ∈ s := by
    simp [s, Finset.mem_range, Nat.lt_succ_of_le hk]
  rw [reinforcedLine_finiteVolumeWeight_prefix_eq_prod_edgePair]
  rw [reinforcedLine_finiteVolumeWeight_prefix_eq_prod_edgePair]
  change (∏ i ∈ s, reinforcedLineEdgePairWeight edgeLogWeight i W') =
    factor * ∏ i ∈ s, reinforcedLineEdgePairWeight edgeLogWeight i W
  let f : Nat → ENNReal := fun i => reinforcedLineEdgePairWeight edgeLogWeight i W'
  let g : Nat → ENNReal := fun i => reinforcedLineEdgePairWeight edgeLogWeight i W
  change (∏ i ∈ s, f i) = factor * ∏ i ∈ s, g i
  have hwall : f k = factor * g k := by
    simpa [f, g, W, W', factor] using
      (reinforcedLineEdgePairWeight_flipPrefix_domainWall
        edgeLogWeight x hk hleft hright)
  have hnonwall : ∀ i ∈ s.erase k, f i = g i := by
    intro i hiErase
    have hiS : i ∈ s := (Finset.mem_erase.mp hiErase).2
    have hne : i ≠ k := (Finset.mem_erase.mp hiErase).1
    have hiLe : i ≤ n := by
      have hlt : i < n + 1 := by
        simpa [s, Finset.mem_range] using hiS
      exact Nat.le_of_lt_succ hlt
    simpa [f, g, W, W'] using
      (reinforcedLineEdgePairWeight_flipPrefix_eq_of_ne
        edgeLogWeight x hk hiLe hne)
  have hprodErase : (∏ i ∈ s.erase k, f i) = ∏ i ∈ s.erase k, g i :=
    Finset.prod_congr rfl hnonwall
  calc
    ∏ i ∈ s, f i = f k * ∏ i ∈ s.erase k, f i := by
      rw [← Finset.mul_prod_erase s f hkRange]
    _ = (factor * g k) * ∏ i ∈ s.erase k, g i := by
      rw [hwall, hprodErase]
    _ = factor * (g k * ∏ i ∈ s.erase k, g i) := by
      rw [mul_assoc]
    _ = factor * ∏ i ∈ s, g i := by
      rw [Finset.mul_prod_erase s g hkRange]

theorem reinforcedLine_exists_weightBoost_of_origin_false
    (edgeLogWeight : Nat → ℝ) {n : Nat}
    (x : LocalAssignment LineNode (reinforcedLineExhaustion.region n))
    (hOriginFalse :
      patch (reinforcedLineExhaustion.region n) x linePlusBoundary lineOrigin = false) :
    ∃ k : Nat,
      k ≤ n ∧
        patch (reinforcedLineExhaustion.region n) x linePlusBoundary k = false ∧
          patch (reinforcedLineExhaustion.region n) x linePlusBoundary (k + 1) = true ∧
            (reinforcedLineFlipPrefix n k x)
                ⟨lineOrigin, lineOrigin_mem_reinforcedLineExhaustion_region n⟩ = true ∧
              (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumeWeight
                  (reinforcedLineExhaustion.region n) (reinforcedLineFlipPrefix n k x)
                  linePlusBoundary =
                ENNReal.ofReal (Real.exp (edgeLogWeight k)) *
                  (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumeWeight
                    (reinforcedLineExhaustion.region n) x linePlusBoundary := by
  rcases exists_reinforcedLine_firstDomainWall_of_origin_false n x hOriginFalse with
    ⟨k, hk, hleft, hright⟩
  refine ⟨k, hk, hleft, hright, ?_, ?_⟩
  · have hxOrigin :
        x ⟨lineOrigin, lineOrigin_mem_reinforcedLineExhaustion_region n⟩ = false := by
      simpa [patch, lineOrigin_mem_reinforcedLineExhaustion_region n] using hOriginFalse
    exact reinforcedLineFlipPrefix_origin_of_origin_false x hxOrigin
  · exact reinforcedLine_finiteVolumeWeight_flipPrefix_domainWall
      edgeLogWeight x hk hleft hright

noncomputable def reinforcedLineOriginFalseDomainWallMass
    (edgeLogWeight : Nat → ℝ) (n k : Nat) : ENNReal :=
  by
    classical
    exact Finset.sum Finset.univ
      (fun x : LocalAssignment LineNode (reinforcedLineExhaustion.region n) =>
        if reinforcedLineOriginFalseDomainWallAt n k x then
          (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumeWeight
            (reinforcedLineExhaustion.region n) x linePlusBoundary
        else 0)

theorem reinforcedLine_originFalseDomainWallMass_le_invFactor_mul_originTrueQueryMass
    (edgeLogWeight : Nat → ℝ) (n k : Nat) :
    reinforcedLineOriginFalseDomainWallMass edgeLogWeight n k ≤
      (ENNReal.ofReal (Real.exp (edgeLogWeight k)))⁻¹ *
        finiteVolumeQueryMass
          (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          (reinforcedLineExhaustion.region n) linePlusBoundary
          (lineOriginSpinLocalQueryInRegion (reinforcedLineExhaustion.region n)
            (lineOrigin_mem_reinforcedLineExhaustion_region n) true) := by
  classical
  let M :=
    (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
  let Λ := reinforcedLineExhaustion.region n
  let qTrue := lineOriginSpinLocalQueryInRegion Λ
    (lineOrigin_mem_reinforcedLineExhaustion_region n) true
  let factor : ENNReal := ENNReal.ofReal (Real.exp (edgeLogWeight k))
  have hfactor_ne_zero : factor ≠ 0 := by
    simpa [factor] using
      (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos (edgeLogWeight k)))
  have hfactor_ne_top : factor ≠ ⊤ := by
    simp [factor]
  have hsumReindex :
      (∑ x : LocalAssignment LineNode Λ,
        if satisfiesConstraints (reinforcedLineFlipPrefix n k x) qTrue then
          M.finiteVolumeWeight Λ (reinforcedLineFlipPrefix n k x) linePlusBoundary
        else 0) =
        finiteVolumeQueryMass M Λ linePlusBoundary qTrue := by
    unfold finiteVolumeQueryMass
    refine Finset.sum_bijective (reinforcedLineFlipPrefix n k)
      (reinforcedLineFlipPrefix_bijective n k) ?_ ?_
    · intro x
      simp
    · intro x _hx
      rfl
  unfold reinforcedLineOriginFalseDomainWallMass
  change
    (∑ x : LocalAssignment LineNode Λ,
      if reinforcedLineOriginFalseDomainWallAt n k x then
        M.finiteVolumeWeight Λ x linePlusBoundary
      else 0) ≤
        factor⁻¹ * finiteVolumeQueryMass M Λ linePlusBoundary qTrue
  calc
    (∑ x : LocalAssignment LineNode Λ,
      if reinforcedLineOriginFalseDomainWallAt n k x then
        M.finiteVolumeWeight Λ x linePlusBoundary
      else 0)
        ≤ ∑ x : LocalAssignment LineNode Λ,
            factor⁻¹ *
              (if satisfiesConstraints (reinforcedLineFlipPrefix n k x) qTrue then
                M.finiteVolumeWeight Λ (reinforcedLineFlipPrefix n k x) linePlusBoundary
              else 0) := by
          refine Finset.sum_le_sum ?_
          intro x _hx
          by_cases hwall : reinforcedLineOriginFalseDomainWallAt n k x
          · have hwallTrue : reinforcedLineOriginFalseDomainWallAt n k x := hwall
            rcases hwall with ⟨hOriginFalse, hk, hleft, hright⟩
            have hxOrigin :
                x ⟨lineOrigin, lineOrigin_mem_reinforcedLineExhaustion_region n⟩ = false := by
              simpa [Λ, patch, lineOrigin_mem_reinforcedLineExhaustion_region n] using
                hOriginFalse
            have hflipOrigin :
                (reinforcedLineFlipPrefix n k x)
                    ⟨lineOrigin, lineOrigin_mem_reinforcedLineExhaustion_region n⟩ = true :=
              reinforcedLineFlipPrefix_origin_of_origin_false x hxOrigin
            have hsatTrue :
                satisfiesConstraints (reinforcedLineFlipPrefix n k x) qTrue := by
              unfold satisfiesConstraints
              intro c hc
              simp [qTrue, lineOriginSpinLocalQueryInRegion] at hc
              rcases hc with rfl
              exact hflipOrigin
            have hboost :
                M.finiteVolumeWeight Λ (reinforcedLineFlipPrefix n k x) linePlusBoundary =
                  factor * M.finiteVolumeWeight Λ x linePlusBoundary := by
              simpa [M, Λ, factor] using
                (reinforcedLine_finiteVolumeWeight_flipPrefix_domainWall
                  edgeLogWeight x hk hleft hright)
            have hweightInv :
                M.finiteVolumeWeight Λ x linePlusBoundary =
                  factor⁻¹ *
                    M.finiteVolumeWeight Λ (reinforcedLineFlipPrefix n k x)
                      linePlusBoundary := by
              calc
                M.finiteVolumeWeight Λ x linePlusBoundary =
                    factor⁻¹ * (factor * M.finiteVolumeWeight Λ x linePlusBoundary) := by
                  rw [ENNReal.inv_mul_cancel_left hfactor_ne_zero hfactor_ne_top]
                _ = factor⁻¹ *
                    M.finiteVolumeWeight Λ (reinforcedLineFlipPrefix n k x)
                      linePlusBoundary := by
                  rw [← hboost]
            simp [hwallTrue, hsatTrue, hweightInv]
          · simp [hwall]
    _ = factor⁻¹ *
        (∑ x : LocalAssignment LineNode Λ,
          if satisfiesConstraints (reinforcedLineFlipPrefix n k x) qTrue then
            M.finiteVolumeWeight Λ (reinforcedLineFlipPrefix n k x) linePlusBoundary
          else 0) := by
        rw [← Finset.mul_sum]
    _ = factor⁻¹ * finiteVolumeQueryMass M Λ linePlusBoundary qTrue := by
        rw [hsumReindex]

theorem reinforcedLine_originFalseQueryMass_le_sum_domainWallMass
    (edgeLogWeight : Nat → ℝ) (n : Nat) :
    finiteVolumeQueryMass
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        (reinforcedLineExhaustion.region n) linePlusBoundary
        (lineOriginSpinLocalQueryInRegion (reinforcedLineExhaustion.region n)
          (lineOrigin_mem_reinforcedLineExhaustion_region n) false) ≤
      ∑ k ∈ Finset.range (n + 1),
        reinforcedLineOriginFalseDomainWallMass edgeLogWeight n k := by
  classical
  let M :=
    (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
  let Λ := reinforcedLineExhaustion.region n
  let qFalse := lineOriginSpinLocalQueryInRegion Λ
    (lineOrigin_mem_reinforcedLineExhaustion_region n) false
  unfold finiteVolumeQueryMass reinforcedLineOriginFalseDomainWallMass
  change
    (∑ x : LocalAssignment LineNode Λ,
      if satisfiesConstraints x qFalse then
        M.finiteVolumeWeight Λ x linePlusBoundary
      else 0) ≤
      ∑ k ∈ Finset.range (n + 1),
        ∑ x : LocalAssignment LineNode Λ,
          if reinforcedLineOriginFalseDomainWallAt n k x then
            M.finiteVolumeWeight Λ x linePlusBoundary
          else 0
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum ?_
  intro x _hx
  by_cases hsatFalse : satisfiesConstraints x qFalse
  · have hmem :
        (⟨⟨lineOrigin, lineOrigin_mem_reinforcedLineExhaustion_region n⟩, false⟩ :
          Sigma fun _ : RegionAtom LineNode Λ => Bool) ∈ qFalse := by
      simp [qFalse, lineOriginSpinLocalQueryInRegion]
    have hxOrigin :
        x ⟨lineOrigin, lineOrigin_mem_reinforcedLineExhaustion_region n⟩ = false :=
      hsatFalse _ hmem
    have hPatchOrigin :
        patch (reinforcedLineExhaustion.region n) x linePlusBoundary lineOrigin = false := by
      simpa [Λ, patch, lineOrigin_mem_reinforcedLineExhaustion_region n] using hxOrigin
    rcases exists_reinforcedLine_firstDomainWall_of_origin_false n x hPatchOrigin with
      ⟨k, hk, hleft, hright⟩
    have hkRange : k ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    let term : Nat → ENNReal := fun j =>
      if reinforcedLineOriginFalseDomainWallAt n j x then
        M.finiteVolumeWeight Λ x linePlusBoundary
      else 0
    have hwallAt : reinforcedLineOriginFalseDomainWallAt n k x :=
      ⟨hPatchOrigin, hk, hleft, hright⟩
    have hnonneg : ∀ j ∈ Finset.range (n + 1), 0 ≤ term j := by
      intro j hj
      exact zero_le
    have hsingle : term k ≤ ∑ j ∈ Finset.range (n + 1), term j :=
      Finset.single_le_sum hnonneg hkRange
    have htermk : term k = M.finiteVolumeWeight Λ x linePlusBoundary := by
      simp [term, hwallAt]
    simpa [hsatFalse, term, htermk] using hsingle
  · simp [hsatFalse]

theorem reinforcedLine_originFalseQueryMass_le_wallFactorSum_mul_originTrueQueryMass
    (edgeLogWeight : Nat → ℝ) (n : Nat) :
    finiteVolumeQueryMass
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        (reinforcedLineExhaustion.region n) linePlusBoundary
        (lineOriginSpinLocalQueryInRegion (reinforcedLineExhaustion.region n)
          (lineOrigin_mem_reinforcedLineExhaustion_region n) false) ≤
      (∑ k ∈ Finset.range (n + 1),
        (ENNReal.ofReal (Real.exp (edgeLogWeight k)))⁻¹) *
        finiteVolumeQueryMass
          (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          (reinforcedLineExhaustion.region n) linePlusBoundary
          (lineOriginSpinLocalQueryInRegion (reinforcedLineExhaustion.region n)
            (lineOrigin_mem_reinforcedLineExhaustion_region n) true) := by
  classical
  let M :=
    (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
  let Λ := reinforcedLineExhaustion.region n
  let qFalse := lineOriginSpinLocalQueryInRegion Λ
    (lineOrigin_mem_reinforcedLineExhaustion_region n) false
  let qTrue := lineOriginSpinLocalQueryInRegion Λ
    (lineOrigin_mem_reinforcedLineExhaustion_region n) true
  calc
    finiteVolumeQueryMass M Λ linePlusBoundary qFalse
        ≤ ∑ k ∈ Finset.range (n + 1),
            reinforcedLineOriginFalseDomainWallMass edgeLogWeight n k := by
          simpa [M, Λ, qFalse] using
            reinforcedLine_originFalseQueryMass_le_sum_domainWallMass edgeLogWeight n
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          (ENNReal.ofReal (Real.exp (edgeLogWeight k)))⁻¹ *
            finiteVolumeQueryMass M Λ linePlusBoundary qTrue := by
        refine Finset.sum_le_sum ?_
        intro k hk
        simpa [M, Λ, qTrue] using
          reinforcedLine_originFalseDomainWallMass_le_invFactor_mul_originTrueQueryMass
            edgeLogWeight n k
    _ = (∑ k ∈ Finset.range (n + 1),
          (ENNReal.ofReal (Real.exp (edgeLogWeight k)))⁻¹) *
          finiteVolumeQueryMass M Λ linePlusBoundary qTrue := by
        rw [Finset.sum_mul]

theorem reinforcedLine_clauseData_eval_spinFlip_eq_flip
    (edgeLogWeight : Nat → ℝ) (k : ReinforcedLineClauseId)
    (W : InfiniteWorld LineNode) :
    ((reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.clauseData k).eval
        (lineSpinFlipWorld W) =
      ((reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.clauseData
        (reinforcedLineClauseFlip k)).eval W := by
  cases k <;>
    simp [ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec,
      reinforcedLineClauseFlip, reinforcedLineClassicalSpec,
      reinforcedLineClause, WeightedGroundClause.eval,
      classicalWeightedClause, lineForwardClause_holds_spinFlip_iff_backward,
      lineBackwardClause_holds_spinFlip_iff_forward]

theorem reinforcedLine_finiteVolumeWeight_spinFlip
    (edgeLogWeight : Nat → ℝ) (Λ : Region LineNode)
    (x : LocalAssignment LineNode Λ) (ξ : BoundaryCondition LineNode) :
    (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumeWeight
        Λ (lineSpinFlipLocalAssignment x) (lineSpinFlipWorld ξ) =
      (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumeWeight
        Λ x ξ := by
  classical
  unfold Mettapedia.Logic.MarkovLogicInfiniteSpecification.InfiniteGroundMLNSpec.finiteVolumeWeight
  rw [← lineSpinFlipWorld_patch]
  refine Finset.prod_bijective reinforcedLineClauseFlip reinforcedLineClauseFlip_bijective ?_ ?_
  · intro k
    simpa [reinforcedLineClassicalSpec,
      ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec] using
      (reinforcedLineClauseFlip_mem_regionSupport_iff Λ k).symm
  · intro k _hk
    simpa using reinforcedLine_clauseData_eval_spinFlip_eq_flip edgeLogWeight k (patch Λ x ξ)

theorem reinforcedLine_finiteVolumePartition_spinFlip
    (edgeLogWeight : Nat → ℝ) (Λ : Region LineNode)
    (ξ : BoundaryCondition LineNode) :
    (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumePartition
        Λ (lineSpinFlipWorld ξ) =
      (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumePartition
        Λ ξ := by
  classical
  unfold Mettapedia.Logic.MarkovLogicInfiniteSpecification.InfiniteGroundMLNSpec.finiteVolumePartition
  refine Finset.sum_bijective lineSpinFlipLocalAssignment lineSpinFlipLocalAssignment_bijective ?_ ?_
  · intro x
    simp
  · intro x _hx
    simpa [lineSpinFlipLocalAssignment_involutive] using
      (reinforcedLine_finiteVolumeWeight_spinFlip
        edgeLogWeight Λ (lineSpinFlipLocalAssignment x) ξ)

theorem reinforcedLine_originSpin_queryMass_spinFlip
    (edgeLogWeight : Nat → ℝ) (Λ : Region LineNode)
    (hOrigin : lineOrigin ∈ Λ) (ξ : BoundaryCondition LineNode) (b : Bool) :
    finiteVolumeQueryMass
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ (lineSpinFlipWorld ξ)
        (lineOriginSpinLocalQueryInRegion Λ hOrigin b) =
      finiteVolumeQueryMass
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ ξ
        (lineOriginSpinLocalQueryInRegion Λ hOrigin (!b)) := by
  classical
  unfold finiteVolumeQueryMass
  refine Finset.sum_bijective lineSpinFlipLocalAssignment lineSpinFlipLocalAssignment_bijective ?_ ?_
  · intro x
    simp
  · intro x _hx
    have hsat : satisfiesConstraints x
          (lineOriginSpinLocalQueryInRegion Λ hOrigin b) ↔
        satisfiesConstraints (lineSpinFlipLocalAssignment x)
          (lineOriginSpinLocalQueryInRegion Λ hOrigin (!b)) := by
      simpa using
        (lineSpinFlipLocalAssignment_satisfies_originSpinInRegion_iff
          Λ hOrigin (!b) x).symm
    by_cases hxSat : satisfiesConstraints x
        (lineOriginSpinLocalQueryInRegion Λ hOrigin b)
    · have hxFlipSat : satisfiesConstraints (lineSpinFlipLocalAssignment x)
          (lineOriginSpinLocalQueryInRegion Λ hOrigin (!b)) := hsat.1 hxSat
      simp [hxSat, hxFlipSat]
      simpa [lineSpinFlipLocalAssignment_involutive] using
        (reinforcedLine_finiteVolumeWeight_spinFlip
          edgeLogWeight Λ (lineSpinFlipLocalAssignment x) ξ)
    · have hxFlipNotSat : ¬ satisfiesConstraints (lineSpinFlipLocalAssignment x)
          (lineOriginSpinLocalQueryInRegion Λ hOrigin (!b)) := by
        intro hxFlipSat
        exact hxSat (hsat.2 hxFlipSat)
      simp [hxSat, hxFlipNotSat]

theorem reinforcedLine_originSpin_queryProb_spinFlip
    (edgeLogWeight : Nat → ℝ) (Λ : Region LineNode)
    (hOrigin : lineOrigin ∈ Λ) (ξ : BoundaryCondition LineNode) (b : Bool) :
    (finiteVolumeMassSemantics
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ (lineSpinFlipWorld ξ)).queryProb
        (lineOriginSpinLocalQueryInRegion Λ hOrigin b) =
      (finiteVolumeMassSemantics
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ ξ).queryProb
        (lineOriginSpinLocalQueryInRegion Λ hOrigin (!b)) := by
  unfold finiteVolumeMassSemantics MassSemantics.queryProb
  simp [reinforcedLine_originSpin_queryMass_spinFlip,
    reinforcedLine_finiteVolumePartition_spinFlip]

theorem reinforcedLine_originSpin_queryMass_add_complement
    (edgeLogWeight : Nat → ℝ) (Λ : Region LineNode)
    (hOrigin : lineOrigin ∈ Λ) (ξ : BoundaryCondition LineNode) (b : Bool) :
    finiteVolumeQueryMass
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ ξ (lineOriginSpinLocalQueryInRegion Λ hOrigin b) +
      finiteVolumeQueryMass
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ ξ (lineOriginSpinLocalQueryInRegion Λ hOrigin (!b)) =
      (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumePartition
        Λ ξ := by
  classical
  unfold finiteVolumeQueryMass
  unfold Mettapedia.Logic.MarkovLogicInfiniteSpecification.InfiniteGroundMLNSpec.finiteVolumePartition
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  cases b <;>
    by_cases hxOrigin : x ⟨lineOrigin, hOrigin⟩ = true <;>
      simp [satisfiesConstraints, lineOriginSpinLocalQueryInRegion, hxOrigin] at *

theorem reinforcedLine_originSpin_queryProb_add_complement
    (edgeLogWeight : Nat → ℝ) (Λ : Region LineNode)
    (hOrigin : lineOrigin ∈ Λ) (ξ : BoundaryCondition LineNode) (b : Bool) :
    (finiteVolumeMassSemantics
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ ξ).queryProb
        (lineOriginSpinLocalQueryInRegion Λ hOrigin b) +
      (finiteVolumeMassSemantics
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ ξ).queryProb
        (lineOriginSpinLocalQueryInRegion Λ hOrigin (!b)) = 1 := by
  let Msp := (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
  have hZ : Msp.finiteVolumePartition Λ ξ ≠ 0 := by
    exact Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
      Msp Λ ξ
  have htop : Msp.finiteVolumePartition Λ ξ ≠ ⊤ := by
    simpa using finiteVolumePartition_ne_top Msp.toInfiniteGroundMLNSpec Λ ξ
  unfold finiteVolumeMassSemantics MassSemantics.queryProb
  simp [Msp, hZ]
  rw [ENNReal.div_add_div_same]
  rw [reinforcedLine_originSpin_queryMass_add_complement]
  exact ENNReal.div_self hZ htop

theorem reinforcedLine_originSpinUp_queryProb_toReal_ge_three_quarters_of_wallFactorSum_le
    (edgeLogWeight : Nat → ℝ) (n : Nat)
    (hsum :
      (∑ k ∈ Finset.range (n + 1),
        (ENNReal.ofReal (Real.exp (edgeLogWeight k)))⁻¹) ≤
        (3 : ENNReal)⁻¹) :
    (3 / 4 : ℝ) ≤
      ENNReal.toReal
        ((finiteVolumeMassSemantics
          (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          (reinforcedLineExhaustion.region n) linePlusBoundary).queryProb
          (lineOriginSpinLocalQueryInRegion (reinforcedLineExhaustion.region n)
            (lineOrigin_mem_reinforcedLineExhaustion_region n) true)) := by
  classical
  let Msp := (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
  let M := Msp.toInfiniteGroundMLNSpec
  let Λ := reinforcedLineExhaustion.region n
  let qTrue := lineOriginSpinLocalQueryInRegion Λ
    (lineOrigin_mem_reinforcedLineExhaustion_region n) true
  let qFalse := lineOriginSpinLocalQueryInRegion Λ
    (lineOrigin_mem_reinforcedLineExhaustion_region n) false
  let S := finiteVolumeMassSemantics M Λ linePlusBoundary
  have hZ : M.finiteVolumePartition Λ linePlusBoundary ≠ 0 := by
    simpa [M, Msp] using
      Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
        Msp Λ linePlusBoundary
  have hmass :
      finiteVolumeQueryMass M Λ linePlusBoundary qFalse ≤
        (3 : ENNReal)⁻¹ * finiteVolumeQueryMass M Λ linePlusBoundary qTrue := by
    calc
      finiteVolumeQueryMass M Λ linePlusBoundary qFalse
          ≤ (∑ k ∈ Finset.range (n + 1),
              (ENNReal.ofReal (Real.exp (edgeLogWeight k)))⁻¹) *
              finiteVolumeQueryMass M Λ linePlusBoundary qTrue := by
            simpa [M, Msp, Λ, qFalse, qTrue] using
              reinforcedLine_originFalseQueryMass_le_wallFactorSum_mul_originTrueQueryMass
                edgeLogWeight n
      _ ≤ (3 : ENNReal)⁻¹ * finiteVolumeQueryMass M Λ linePlusBoundary qTrue :=
            mul_le_mul' hsum le_rfl
  have hprobFalse_le_pre :
      finiteVolumeQueryMass M Λ linePlusBoundary qFalse /
          M.finiteVolumePartition Λ linePlusBoundary ≤
        ((3 : ENNReal)⁻¹ * finiteVolumeQueryMass M Λ linePlusBoundary qTrue) /
          M.finiteVolumePartition Λ linePlusBoundary :=
    ENNReal.div_le_div_right hmass _
  have hprobFalse_le :
      S.queryProb qFalse ≤ (3 : ENNReal)⁻¹ * S.queryProb qTrue := by
    simpa [S, finiteVolumeMassSemantics, MassSemantics.queryProb, hZ,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hprobFalse_le_pre
  have hprobSum : S.queryProb qTrue + S.queryProb qFalse = 1 := by
    simpa [S, M, Msp, Λ, qTrue, qFalse] using
      reinforcedLine_originSpin_queryProb_add_complement edgeLogWeight Λ
        (lineOrigin_mem_reinforcedLineExhaustion_region n) linePlusBoundary true
  have hsum_ne_top : S.queryProb qTrue + S.queryProb qFalse ≠ ⊤ := by
    rw [hprobSum]
    simp
  have hqTrue_ne_top : S.queryProb qTrue ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hsum_ne_top).1
  have hqFalse_ne_top : S.queryProb qFalse ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hsum_ne_top).2
  have hrealSum :
      ENNReal.toReal (S.queryProb qTrue) +
        ENNReal.toReal (S.queryProb qFalse) = 1 := by
    have hto := congrArg ENNReal.toReal hprobSum
    rw [ENNReal.toReal_add hqTrue_ne_top hqFalse_ne_top, ENNReal.toReal_one] at hto
    exact hto
  have hrealFalseLe :
      ENNReal.toReal (S.queryProb qFalse) ≤
        (1 / 3 : ℝ) * ENNReal.toReal (S.queryProb qTrue) := by
    have hright_ne_top :
        (3 : ENNReal)⁻¹ * S.queryProb qTrue ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) hqTrue_ne_top
    have hto := ENNReal.toReal_mono hright_ne_top hprobFalse_le
    simpa [ENNReal.toReal_mul, one_div] using hto
  linarith

theorem reinforcedLine_originSpin_queryProb_toReal_spinFlip
    (edgeLogWeight : Nat → ℝ) (Λ : Region LineNode)
    (hOrigin : lineOrigin ∈ Λ) (ξ : BoundaryCondition LineNode) (b : Bool) :
    ENNReal.toReal
      ((finiteVolumeMassSemantics
          (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          Λ (lineSpinFlipWorld ξ)).queryProb
          (lineOriginSpinLocalQueryInRegion Λ hOrigin b)) =
      1 - ENNReal.toReal
        ((finiteVolumeMassSemantics
          (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          Λ ξ).queryProb
          (lineOriginSpinLocalQueryInRegion Λ hOrigin b)) := by
  let S := finiteVolumeMassSemantics
    (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
    Λ ξ
  let q := lineOriginSpinLocalQueryInRegion Λ hOrigin b
  let qC := lineOriginSpinLocalQueryInRegion Λ hOrigin (!b)
  have htransport :
      (finiteVolumeMassSemantics
          (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          Λ (lineSpinFlipWorld ξ)).queryProb q = S.queryProb qC := by
    simpa [S, q, qC] using
      reinforcedLine_originSpin_queryProb_spinFlip edgeLogWeight Λ hOrigin ξ b
  have hsum : S.queryProb q + S.queryProb qC = 1 := by
    simpa [S, q, qC] using
      reinforcedLine_originSpin_queryProb_add_complement edgeLogWeight Λ hOrigin ξ b
  have hsum_ne_top : S.queryProb q + S.queryProb qC ≠ ⊤ := by
    rw [hsum]
    simp
  have hq_ne_top : S.queryProb q ≠ ⊤ := (ENNReal.add_ne_top.mp hsum_ne_top).1
  have hqC_ne_top : S.queryProb qC ≠ ⊤ := (ENNReal.add_ne_top.mp hsum_ne_top).2
  have hreal_sum : ENNReal.toReal (S.queryProb q) + ENNReal.toReal (S.queryProb qC) = 1 := by
    have hto := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add hq_ne_top hqC_ne_top, ENNReal.toReal_one] at hto
    exact hto
  rw [htransport]
  linarith

theorem reinforcedLine_finiteVolumeKernel_originSpinUp_eq_queryProb
    (edgeLogWeight : Nat → ℝ) (n : ℕ) (ξ : BoundaryCondition LineNode) :
    reinforcedLineExhaustion.finiteVolumeKernelSequence
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
        ξ n
        (localQueryEvent ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery) =
      (finiteVolumeMassSemantics
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        (reinforcedLineExhaustion.region n) ξ).queryProb
        (lineOriginSpinLocalQueryInRegion (reinforcedLineExhaustion.region n)
          (lineOrigin_mem_reinforcedLineExhaustion_region n) true) := by
  rw [← localQueryEvent_lineOriginSpinLocalQueryInRegion_eq_originSpinUp
    (reinforcedLineExhaustion.region n) (lineOrigin_mem_reinforcedLineExhaustion_region n)]
  rw [Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion.finiteVolumeKernelSequence]
  simpa [Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure] using
    (finiteVolumeWorldMeasure_localQueryEvent
      (M := (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec)
      (Λ := reinforcedLineExhaustion.region n) (ξ := ξ)
      (hZ := Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
        (reinforcedLineExhaustion.region n) ξ)
      (q := lineOriginSpinLocalQueryInRegion (reinforcedLineExhaustion.region n)
        (lineOrigin_mem_reinforcedLineExhaustion_region n) true))

theorem reinforcedLine_originSpinUp_finiteVolumeKernel_plus_ge_three_quarters_of_wallFactorSum_le
    (edgeLogWeight : Nat → ℝ) (n : Nat)
    (hsum :
      (∑ k ∈ Finset.range (n + 1),
        (ENNReal.ofReal (Real.exp (edgeLogWeight k)))⁻¹) ≤
        (3 : ENNReal)⁻¹) :
    (3 / 4 : ℝ) ≤
      ENNReal.toReal
        (reinforcedLineExhaustion.finiteVolumeKernelSequence
          (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
          linePlusBoundary n
          (localQueryEvent ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery)) := by
  rw [reinforcedLine_finiteVolumeKernel_originSpinUp_eq_queryProb]
  exact reinforcedLine_originSpinUp_queryProb_toReal_ge_three_quarters_of_wallFactorSum_le
    edgeLogWeight n hsum

theorem reinforcedLine_originSpinUp_finiteVolumeKernel_spinFlip
    (edgeLogWeight : Nat → ℝ) (n : ℕ) (ξ : BoundaryCondition LineNode) :
    ENNReal.toReal
      (reinforcedLineExhaustion.finiteVolumeKernelSequence
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
        (lineSpinFlipWorld ξ) n
        (localQueryEvent ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery)) =
      1 - ENNReal.toReal
        (reinforcedLineExhaustion.finiteVolumeKernelSequence
          (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ n
          (localQueryEvent ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery)) := by
  rw [reinforcedLine_finiteVolumeKernel_originSpinUp_eq_queryProb]
  rw [reinforcedLine_finiteVolumeKernel_originSpinUp_eq_queryProb]
  exact reinforcedLine_originSpin_queryProb_toReal_spinFlip
    edgeLogWeight (reinforcedLineExhaustion.region n)
    (lineOrigin_mem_reinforcedLineExhaustion_region n) ξ true

theorem reinforcedLine_originSpinUp_finiteVolumeKernel_minus_eq_one_sub_plus
    (edgeLogWeight : Nat → ℝ) (n : ℕ) :
    ENNReal.toReal
      (reinforcedLineExhaustion.finiteVolumeKernelSequence
        (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
        lineMinusBoundary n
        (localQueryEvent ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery)) =
      1 - ENNReal.toReal
        (reinforcedLineExhaustion.finiteVolumeKernelSequence
          (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
          linePlusBoundary n
          (localQueryEvent ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery)) := by
  simpa using
    (reinforcedLine_originSpinUp_finiteVolumeKernel_spinFlip
      edgeLogWeight n linePlusBoundary)

theorem reinforcedLine_originSpinUp_strictWidth_of_stageMarginalLimitSeparation
    {edgeLogWeight : Nat → ℝ}
    (Pminus Pplus :
      ∀ I : Finset LineNode, Measure (LocalAssignment LineNode I))
    [∀ I, IsProbabilityMeasure (Pminus I)]
    [∀ I, IsProbabilityMeasure (Pplus I)]
    (hPminus :
      MeasureTheory.IsProjectiveMeasureFamily
        (ι := LineNode)
        (α := Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord LineNode)
        Pminus)
    (hPplus :
      MeasureTheory.IsProjectiveMeasureFamily
        (ι := LineNode)
        (α := Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord LineNode)
        Pplus)
    (hconvMinus :
      ∀ (I : Finset LineNode) (S : Set (LocalAssignment LineNode I)),
        MeasurableSet S →
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                reinforcedLineExhaustion
                (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
                lineMinusBoundary n I S)
            atTop (nhds (Pminus I S)))
    (hconvPlus :
      ∀ (I : Finset LineNode) (S : Set (LocalAssignment LineNode I)),
        MeasurableSet S →
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                reinforcedLineExhaustion
                (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
                linePlusBoundary n I S)
            atTop (nhds (Pplus I S)))
    (hsep :
      ENNReal.toReal
          (Pminus ({lineOrigin} : Region LineNode)
            (localConstraintSet ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery)) <
        ENNReal.toReal
          (Pplus ({lineOrigin} : Region LineNode)
            (localConstraintSet ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery))) :
    dlrQueryHasStrictWidth
      (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery := by
  let e : ℕ ≃ LineNode := Equiv.refl Nat
  let μminus : DLRCompletion (reinforcedLineClassicalSpec edgeLogWeight) :=
    projectiveLimitDLRCompletion_of_stageMarginal_tendsto
      (reinforcedLineClassicalSpec edgeLogWeight) reinforcedLineExhaustion lineMinusBoundary
      e Pminus hPminus hconvMinus
  let μplus : DLRCompletion (reinforcedLineClassicalSpec edgeLogWeight) :=
    projectiveLimitDLRCompletion_of_stageMarginal_tendsto
      (reinforcedLineClassicalSpec edgeLogWeight) reinforcedLineExhaustion linePlusBoundary
      e Pplus hPplus hconvPlus
  refine ⟨μminus, μplus, ?_⟩
  have hminusLocal :
      dlrCompletionLocalQueryProb (reinforcedLineClassicalSpec edgeLogWeight)
          ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery μminus =
        ENNReal.toReal
          (Pminus ({lineOrigin} : Region LineNode)
            (localConstraintSet ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery)) := by
    simp [dlrCompletionLocalQueryProb, μminus,
      projectiveLimitDLRCompletion_of_stageMarginal_tendsto,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.projectiveLimitMeasure_localQueryEvent]
  have hplusLocal :
      dlrCompletionLocalQueryProb (reinforcedLineClassicalSpec edgeLogWeight)
          ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery μplus =
        ENNReal.toReal
          (Pplus ({lineOrigin} : Region LineNode)
            (localConstraintSet ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery)) := by
    simp [dlrCompletionLocalQueryProb, μplus,
      projectiveLimitDLRCompletion_of_stageMarginal_tendsto,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.projectiveLimitMeasure_localQueryEvent]
  have hminusQuery :
      dlrCompletionQueryProb (reinforcedLineClassicalSpec edgeLogWeight)
          lineOriginSpinUpQuery μminus =
        ENNReal.toReal
          (Pminus ({lineOrigin} : Region LineNode)
            (localConstraintSet ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery)) := by
    rw [dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent]
    rw [← lineOriginSpinUpLocalQueryEvent_eq_global]
    simpa [dlrCompletionLocalQueryProb] using hminusLocal
  have hplusQuery :
      dlrCompletionQueryProb (reinforcedLineClassicalSpec edgeLogWeight)
          lineOriginSpinUpQuery μplus =
        ENNReal.toReal
          (Pplus ({lineOrigin} : Region LineNode)
            (localConstraintSet ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery)) := by
    rw [dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent]
    rw [← lineOriginSpinUpLocalQueryEvent_eq_global]
    simpa [dlrCompletionLocalQueryProb] using hplusLocal
  rw [hminusQuery, hplusQuery]
  exact hsep

theorem reinforcedLine_originSpinUp_plnStrictInterval_of_stageMarginalLimitSeparation
    {edgeLogWeight : Nat → ℝ}
    (Pminus Pplus :
      ∀ I : Finset LineNode, Measure (LocalAssignment LineNode I))
    [∀ I, IsProbabilityMeasure (Pminus I)]
    [∀ I, IsProbabilityMeasure (Pplus I)]
    (hPminus :
      MeasureTheory.IsProjectiveMeasureFamily
        (ι := LineNode)
        (α := Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord LineNode)
        Pminus)
    (hPplus :
      MeasureTheory.IsProjectiveMeasureFamily
        (ι := LineNode)
        (α := Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord LineNode)
        Pplus)
    (hconvMinus :
      ∀ (I : Finset LineNode) (S : Set (LocalAssignment LineNode I)),
        MeasurableSet S →
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                reinforcedLineExhaustion
                (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
                lineMinusBoundary n I S)
            atTop (nhds (Pminus I S)))
    (hconvPlus :
      ∀ (I : Finset LineNode) (S : Set (LocalAssignment LineNode I)),
        MeasurableSet S →
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                reinforcedLineExhaustion
                (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
                linePlusBoundary n I S)
            atTop (nhds (Pplus I S)))
    (hsep :
      ENNReal.toReal
          (Pminus ({lineOrigin} : Region LineNode)
            (localConstraintSet ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery)) <
        ENNReal.toReal
          (Pplus ({lineOrigin} : Region LineNode)
            (localConstraintSet ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery))) :
    0 < infiniteMLNQueryEnvelopeWidth
          (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery ∧
      infiniteMLNQueryEnvelopeWidthComplement
          (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery < 1 ∧
        0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
          (dlrQueryOutcomeCredalSet
            (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  have hWidth :
      dlrQueryHasStrictWidth
        (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery :=
    reinforcedLine_originSpinUp_strictWidth_of_stageMarginalLimitSeparation
      Pminus Pplus hPminus hPplus hconvMinus hconvPlus hsep
  refine ⟨?_, ?_, ?_⟩
  · exact infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth
      (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery hWidth
  · have hpos : 0 < infiniteMLNQueryEnvelopeWidth
        (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery :=
      infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth
        (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery hWidth
    unfold infiniteMLNQueryEnvelopeWidthComplement
    linarith
  · exact dlrQueryOutcomeCredalSet_true_atom_width_pos_of_queryStrictWidth
      (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery hWidth

theorem reinforcedLine_originSpinUp_plnStrictInterval_of_uniformFiniteVolumeBounds
    {edgeLogWeight : Nat → ℝ} {lo hi : ℝ}
    (hlohi : lo < hi)
    (hminus :
      ∀ n,
        ENNReal.toReal
          (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
            reinforcedLineExhaustion
            (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
            lineMinusBoundary n ({lineOrigin} : Region LineNode)
            (localConstraintSet ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery)) ≤ lo)
    (hplus :
      ∀ n,
        hi ≤ ENNReal.toReal
          (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
            reinforcedLineExhaustion
            (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
            linePlusBoundary n ({lineOrigin} : Region LineNode)
            (localConstraintSet ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery))) :
    0 < infiniteMLNQueryEnvelopeWidth
          (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery ∧
      infiniteMLNQueryEnvelopeWidthComplement
          (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery < 1 ∧
        0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
          (dlrQueryOutcomeCredalSet
            (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  let M := (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
  let e : ℕ ≃ LineNode := Equiv.refl Nat
  rcases
      Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.exists_stageProbabilityFamily_tendsto_subseq_of_equiv
        (E := reinforcedLineExhaustion) (M := M) (ξ := lineMinusBoundary) e with
    ⟨PminusFamily, φminus, hmonoMinus, hφminus⟩
  rcases
      Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.exists_stageProbabilityFamily_tendsto_subseq_of_equiv
        (E := reinforcedLineExhaustion) (M := M) (ξ := linePlusBoundary) e with
    ⟨PplusFamily, φplus, hmonoPlus, hφplus⟩
  let Pminus : ∀ I : Finset LineNode, Measure (LocalAssignment LineNode I) :=
    fun I =>
      ((PminusFamily I : ProbabilityMeasure (LocalAssignment LineNode I)) :
        Measure (LocalAssignment LineNode I))
  let Pplus : ∀ I : Finset LineNode, Measure (LocalAssignment LineNode I) :=
    fun I =>
      ((PplusFamily I : ProbabilityMeasure (LocalAssignment LineNode I)) :
        Measure (LocalAssignment LineNode I))
  haveI hPminusProb : ∀ I : Finset LineNode, IsProbabilityMeasure (Pminus I) := by
    intro I
    dsimp [Pminus]
    infer_instance
  haveI hPplusProb : ∀ I : Finset LineNode, IsProbabilityMeasure (Pplus I) := by
    intro I
    dsimp [Pplus]
    infer_instance
  have hPminus :
      MeasureTheory.IsProjectiveMeasureFamily
        (ι := LineNode)
        (α := Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord LineNode)
        Pminus := by
    simpa [Pminus] using
      (Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.isProjectiveMeasureFamily_of_tendsto_stageProbabilityFamily
        (E := reinforcedLineExhaustion) (M := M) (ξ := lineMinusBoundary)
        (P := PminusFamily) (φ := φminus) hφminus)
  have hPplus :
      MeasureTheory.IsProjectiveMeasureFamily
        (ι := LineNode)
        (α := Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord LineNode)
        Pplus := by
    simpa [Pplus] using
      (Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.isProjectiveMeasureFamily_of_tendsto_stageProbabilityFamily
        (E := reinforcedLineExhaustion) (M := M) (ξ := linePlusBoundary)
        (P := PplusFamily) (φ := φplus) hφplus)
  let Eminus := reinforcedLineExhaustion.reindex φminus hmonoMinus
  let Eplus := reinforcedLineExhaustion.reindex φplus hmonoPlus
  have hconvMinus :
      ∀ (I : Finset LineNode) (S : Set (LocalAssignment LineNode I)),
        MeasurableSet S →
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                Eminus M lineMinusBoundary n I S)
            atTop (nhds (Pminus I S)) := by
    intro I S _hS
    simpa [Eminus, Pminus,
      Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal_reindex] using
      (Mettapedia.Logic.MarkovLogicInfiniteExistence.RegionExhaustion.tendsto_stageMarginal_apply_of_tendsto_stageProbabilityFamily
        (E := reinforcedLineExhaustion) (M := M) (ξ := lineMinusBoundary)
        (P := PminusFamily) (φ := φminus) hφminus I S)
  have hconvPlus :
      ∀ (I : Finset LineNode) (S : Set (LocalAssignment LineNode I)),
        MeasurableSet S →
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                Eplus M linePlusBoundary n I S)
            atTop (nhds (Pplus I S)) := by
    intro I S _hS
    simpa [Eplus, Pplus,
      Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal_reindex] using
      (Mettapedia.Logic.MarkovLogicInfiniteExistence.RegionExhaustion.tendsto_stageMarginal_apply_of_tendsto_stageProbabilityFamily
        (E := reinforcedLineExhaustion) (M := M) (ξ := linePlusBoundary)
        (P := PplusFamily) (φ := φplus) hφplus I S)
  let originRegion : Region LineNode := {lineOrigin}
  let originEvent : Set (LocalAssignment LineNode originRegion) :=
    localConstraintSet originRegion lineOriginSpinUpLocalQuery
  have hmeasOrigin : MeasurableSet originEvent := by
    simpa [originRegion, originEvent] using
      measurableSet_localConstraintSet
        ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery
  have hminusLimit_le :
      ENNReal.toReal (Pminus originRegion originEvent) ≤ lo := by
    have hconvENN :
        Tendsto
          (fun n =>
            Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
              Eminus M lineMinusBoundary n originRegion originEvent)
          atTop (nhds (Pminus originRegion originEvent)) :=
      hconvMinus originRegion originEvent hmeasOrigin
    have hconvReal :
        Tendsto
          (fun n =>
            ENNReal.toReal
              (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                Eminus M lineMinusBoundary n originRegion originEvent))
          atTop (nhds (ENNReal.toReal (Pminus originRegion originEvent))) :=
      (ENNReal.continuousAt_toReal
        (MeasureTheory.measure_ne_top (μ := Pminus originRegion) (s := originEvent))).tendsto.comp hconvENN
    have hsubseqBound :
        (fun n =>
          ENNReal.toReal
            (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
              Eminus M lineMinusBoundary n originRegion originEvent)) ≤ᶠ[atTop]
            fun _ => lo := by
      exact Eventually.of_forall (fun n => by
        simpa [Eminus, M, originRegion, originEvent,
          Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal_reindex] using
          hminus (φminus n))
    exact le_of_tendsto_of_tendsto hconvReal tendsto_const_nhds hsubseqBound
  have hplusLimit_ge :
      hi ≤ ENNReal.toReal (Pplus originRegion originEvent) := by
    have hconvENN :
        Tendsto
          (fun n =>
            Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
              Eplus M linePlusBoundary n originRegion originEvent)
          atTop (nhds (Pplus originRegion originEvent)) :=
      hconvPlus originRegion originEvent hmeasOrigin
    have hconvReal :
        Tendsto
          (fun n =>
            ENNReal.toReal
              (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                Eplus M linePlusBoundary n originRegion originEvent))
          atTop (nhds (ENNReal.toReal (Pplus originRegion originEvent))) :=
      (ENNReal.continuousAt_toReal
        (MeasureTheory.measure_ne_top (μ := Pplus originRegion) (s := originEvent))).tendsto.comp hconvENN
    have hsubseqBound :
        (fun _ => hi) ≤ᶠ[atTop]
          fun n =>
            ENNReal.toReal
              (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                Eplus M linePlusBoundary n originRegion originEvent) := by
      exact Eventually.of_forall (fun n => by
        simpa [Eplus, M, originRegion, originEvent,
          Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal_reindex] using
          hplus (φplus n))
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hconvReal hsubseqBound
  have hsep :
      ENNReal.toReal
          (Pminus ({lineOrigin} : Region LineNode)
            (localConstraintSet ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery)) <
        ENNReal.toReal
          (Pplus ({lineOrigin} : Region LineNode)
            (localConstraintSet ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery)) := by
    simpa [originRegion, originEvent] using
      lt_of_le_of_lt hminusLimit_le (lt_of_lt_of_le hlohi hplusLimit_ge)
  let μminus : DLRCompletion (reinforcedLineClassicalSpec edgeLogWeight) :=
    projectiveLimitDLRCompletion_of_stageMarginal_tendsto
      (reinforcedLineClassicalSpec edgeLogWeight) Eminus lineMinusBoundary
      e Pminus hPminus hconvMinus
  let μplus : DLRCompletion (reinforcedLineClassicalSpec edgeLogWeight) :=
    projectiveLimitDLRCompletion_of_stageMarginal_tendsto
      (reinforcedLineClassicalSpec edgeLogWeight) Eplus linePlusBoundary
      e Pplus hPplus hconvPlus
  have hStrictWidth :
      dlrQueryHasStrictWidth
        (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery := by
    refine ⟨μminus, μplus, ?_⟩
    have hminusLocal :
        dlrCompletionLocalQueryProb (reinforcedLineClassicalSpec edgeLogWeight)
            ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery μminus =
          ENNReal.toReal
            (Pminus ({lineOrigin} : Region LineNode)
              (localConstraintSet ({lineOrigin} : Region LineNode)
                lineOriginSpinUpLocalQuery)) := by
      simp [dlrCompletionLocalQueryProb, μminus,
        projectiveLimitDLRCompletion_of_stageMarginal_tendsto,
        Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.projectiveLimitMeasure_localQueryEvent]
    have hplusLocal :
        dlrCompletionLocalQueryProb (reinforcedLineClassicalSpec edgeLogWeight)
            ({lineOrigin} : Region LineNode) lineOriginSpinUpLocalQuery μplus =
          ENNReal.toReal
            (Pplus ({lineOrigin} : Region LineNode)
              (localConstraintSet ({lineOrigin} : Region LineNode)
                lineOriginSpinUpLocalQuery)) := by
      simp [dlrCompletionLocalQueryProb, μplus,
        projectiveLimitDLRCompletion_of_stageMarginal_tendsto,
        Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.projectiveLimitMeasure_localQueryEvent]
    have hminusQuery :
        dlrCompletionQueryProb (reinforcedLineClassicalSpec edgeLogWeight)
            lineOriginSpinUpQuery μminus =
          ENNReal.toReal
            (Pminus ({lineOrigin} : Region LineNode)
              (localConstraintSet ({lineOrigin} : Region LineNode)
                lineOriginSpinUpLocalQuery)) := by
      rw [dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent]
      rw [← lineOriginSpinUpLocalQueryEvent_eq_global]
      simpa [dlrCompletionLocalQueryProb] using hminusLocal
    have hplusQuery :
        dlrCompletionQueryProb (reinforcedLineClassicalSpec edgeLogWeight)
            lineOriginSpinUpQuery μplus =
          ENNReal.toReal
            (Pplus ({lineOrigin} : Region LineNode)
              (localConstraintSet ({lineOrigin} : Region LineNode)
                lineOriginSpinUpLocalQuery)) := by
      rw [dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent]
      rw [← lineOriginSpinUpLocalQueryEvent_eq_global]
      simpa [dlrCompletionLocalQueryProb] using hplusLocal
    rw [hminusQuery, hplusQuery]
    exact hsep
  refine ⟨?_, ?_, ?_⟩
  · exact infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth
      (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery hStrictWidth
  · have hpos : 0 < infiniteMLNQueryEnvelopeWidth
        (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery :=
      infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth
        (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery hStrictWidth
    unfold infiniteMLNQueryEnvelopeWidthComplement
    linarith
  · exact dlrQueryOutcomeCredalSet_true_atom_width_pos_of_queryStrictWidth
      (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery hStrictWidth

theorem reinforcedLine_originSpinUp_plnStrictInterval_of_uniformKernelBounds
    {edgeLogWeight : Nat → ℝ} {lo hi : ℝ}
    (hlohi : lo < hi)
    (hminus :
      ∀ n,
        ENNReal.toReal
          (reinforcedLineExhaustion.finiteVolumeKernelSequence
            (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
            lineMinusBoundary n
            (localQueryEvent ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery)) ≤ lo)
    (hplus :
      ∀ n,
        hi ≤ ENNReal.toReal
          (reinforcedLineExhaustion.finiteVolumeKernelSequence
            (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
            linePlusBoundary n
            (localQueryEvent ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery))) :
    0 < infiniteMLNQueryEnvelopeWidth
          (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery ∧
      infiniteMLNQueryEnvelopeWidthComplement
          (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery < 1 ∧
        0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
          (dlrQueryOutcomeCredalSet
            (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  refine
    reinforcedLine_originSpinUp_plnStrictInterval_of_uniformFiniteVolumeBounds
      (edgeLogWeight := edgeLogWeight) (lo := lo) (hi := hi) hlohi ?_ ?_
  · intro n
    rw [Mettapedia.Logic.MarkovLogicInfiniteGlobalDLR.RegionExhaustion.stageMarginal_apply_localConstraintSet]
    exact hminus n
  · intro n
    rw [Mettapedia.Logic.MarkovLogicInfiniteGlobalDLR.RegionExhaustion.stageMarginal_apply_localConstraintSet]
    exact hplus n

theorem reinforcedLine_originSpinUp_plnStrictInterval_of_spinFlipHalfGap
    {edgeLogWeight : Nat → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hflip :
      ∀ n,
        ENNReal.toReal
          (reinforcedLineExhaustion.finiteVolumeKernelSequence
            (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
            lineMinusBoundary n
            (localQueryEvent ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery)) =
          1 - ENNReal.toReal
            (reinforcedLineExhaustion.finiteVolumeKernelSequence
              (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
              linePlusBoundary n
              (localQueryEvent ({lineOrigin} : Region LineNode)
                lineOriginSpinUpLocalQuery)))
    (hplus :
      ∀ n,
        (1 / 2 : ℝ) + δ ≤ ENNReal.toReal
          (reinforcedLineExhaustion.finiteVolumeKernelSequence
            (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
            linePlusBoundary n
            (localQueryEvent ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery))) :
    0 < infiniteMLNQueryEnvelopeWidth
          (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery ∧
      infiniteMLNQueryEnvelopeWidthComplement
          (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery < 1 ∧
        0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
          (dlrQueryOutcomeCredalSet
            (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  refine
    reinforcedLine_originSpinUp_plnStrictInterval_of_uniformKernelBounds
      (edgeLogWeight := edgeLogWeight) (lo := (1 / 2 : ℝ) - δ) (hi := (1 / 2 : ℝ) + δ)
      (by linarith) ?_ hplus
  intro n
  rw [hflip n]
  linarith [hplus n]

theorem reinforcedLine_originSpinUp_plnStrictInterval_of_plusHalfGap
    {edgeLogWeight : Nat → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hplus :
      ∀ n,
        (1 / 2 : ℝ) + δ ≤ ENNReal.toReal
          (reinforcedLineExhaustion.finiteVolumeKernelSequence
            (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec
            linePlusBoundary n
            (localQueryEvent ({lineOrigin} : Region LineNode)
              lineOriginSpinUpLocalQuery))) :
    0 < infiniteMLNQueryEnvelopeWidth
          (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery ∧
      infiniteMLNQueryEnvelopeWidthComplement
          (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery < 1 ∧
        0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
          (dlrQueryOutcomeCredalSet
            (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  refine reinforcedLine_originSpinUp_plnStrictInterval_of_spinFlipHalfGap
    (edgeLogWeight := edgeLogWeight) (δ := δ) hδ ?_ hplus
  intro n
  exact reinforcedLine_originSpinUp_finiteVolumeKernel_minus_eq_one_sub_plus edgeLogWeight n

theorem reinforcedLine_originSpinUp_plnStrictInterval_of_uniformWallFactorSum_le_third
    {edgeLogWeight : Nat → ℝ}
    (hsum :
      ∀ n,
        (∑ k ∈ Finset.range (n + 1),
          (ENNReal.ofReal (Real.exp (edgeLogWeight k)))⁻¹) ≤
          (3 : ENNReal)⁻¹) :
    0 < infiniteMLNQueryEnvelopeWidth
          (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery ∧
      infiniteMLNQueryEnvelopeWidthComplement
          (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery < 1 ∧
        0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
          (dlrQueryOutcomeCredalSet
            (reinforcedLineClassicalSpec edgeLogWeight) lineOriginSpinUpQuery)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  refine reinforcedLine_originSpinUp_plnStrictInterval_of_plusHalfGap
    (edgeLogWeight := edgeLogWeight) (δ := (1 / 4 : ℝ)) ?_ ?_
  · norm_num
  · intro n
    have h :=
      reinforcedLine_originSpinUp_finiteVolumeKernel_plus_ge_three_quarters_of_wallFactorSum_le
        edgeLogWeight n (hsum n)
    have hleft : (1 / 2 : ℝ) + 1 / 4 = 3 / 4 := by norm_num
    rw [hleft]
    exact h

/-- A concrete reinforcement schedule whose wall costs grow geometrically. -/
noncomputable def reinforcedLineGeometricEdgeLogWeight (k : Nat) : ℝ :=
  Real.log ((3 : ℝ) * (2 : ℝ) ^ (k + 1))

theorem reinforcedLineGeometric_inverseWallFactor (k : Nat) :
    (ENNReal.ofReal (Real.exp (reinforcedLineGeometricEdgeLogWeight k)))⁻¹ =
      (3 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ ^ (k + 1) := by
  have hpos : 0 < (3 : ℝ) * (2 : ℝ) ^ (k + 1) := by positivity
  rw [reinforcedLineGeometricEdgeLogWeight, Real.exp_log hpos]
  rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (3 : ℝ))]
  rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 : ℝ))]
  norm_num
  rw [ENNReal.mul_inv]
  · simp [ENNReal.inv_pow]
  · left
    norm_num
  · left
    norm_num

theorem reinforcedLineGeometric_wallFactorSum_le_third (n : Nat) :
    (∑ k ∈ Finset.range (n + 1),
      (ENNReal.ofReal (Real.exp (reinforcedLineGeometricEdgeLogWeight k)))⁻¹) ≤
      (3 : ENNReal)⁻¹ := by
  calc
    (∑ k ∈ Finset.range (n + 1),
      (ENNReal.ofReal (Real.exp (reinforcedLineGeometricEdgeLogWeight k)))⁻¹)
        = ∑ k ∈ Finset.range (n + 1),
            (3 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ ^ (k + 1) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          exact reinforcedLineGeometric_inverseWallFactor k
    _ ≤ ∑' k : Nat, (3 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ ^ (k + 1) := by
          exact ENNReal.sum_le_tsum (Finset.range (n + 1))
    _ = (3 : ENNReal)⁻¹ * (∑' k : Nat, (2 : ENNReal)⁻¹ ^ (k + 1)) := by
          rw [ENNReal.tsum_mul_left]
    _ = (3 : ENNReal)⁻¹ := by
          rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
          rw [ENNReal.inv_mul_cancel]
          · simp
          · norm_num
          · exact ENNReal.ofNat_ne_top

theorem reinforcedLineGeometric_originSpinUp_plnStrictInterval :
    0 < infiniteMLNQueryEnvelopeWidth
          (reinforcedLineClassicalSpec reinforcedLineGeometricEdgeLogWeight)
          lineOriginSpinUpQuery ∧
      infiniteMLNQueryEnvelopeWidthComplement
          (reinforcedLineClassicalSpec reinforcedLineGeometricEdgeLogWeight)
          lineOriginSpinUpQuery < 1 ∧
        0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
          (dlrQueryOutcomeCredalSet
            (reinforcedLineClassicalSpec reinforcedLineGeometricEdgeLogWeight)
            lineOriginSpinUpQuery)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  exact
    reinforcedLine_originSpinUp_plnStrictInterval_of_uniformWallFactorSum_le_third
      (edgeLogWeight := reinforcedLineGeometricEdgeLogWeight)
      reinforcedLineGeometric_wallFactorSum_le_third

/-- Existence for the reinforced infinite half-line MLN. -/
theorem exists_reinforcedLine_fixedRegionCylinderDLR
    (edgeLogWeight : Nat → ℝ) (ξ : BoundaryCondition LineNode) :
    ∃ μ : Measure (InfiniteWorld LineNode),
      ∃ _ : IsProbabilityMeasure μ,
        FixedRegionCylinderDLR
          (reinforcedLineClassicalSpec edgeLogWeight).toStrictlyPositiveInfiniteGroundMLNSpec μ := by
  simpa using
    (reinforcedLineClassicalSpec edgeLogWeight).exists_fixedRegionCylinderDLR_of_equiv
      reinforcedLineExhaustion ξ (Equiv.refl Nat)

/-- The reinforced half-line has at least one DLR completion. -/
theorem reinforcedLine_dlrCompletion_nonempty
    (edgeLogWeight : Nat → ℝ) :
    Nonempty (DLRCompletion (reinforcedLineClassicalSpec edgeLogWeight)) := by
  rcases exists_reinforcedLine_fixedRegionCylinderDLR edgeLogWeight linePlusBoundary with
    ⟨μ, hμprob, hμdlr⟩
  exact ⟨⟨⟨μ, hμprob⟩, hμdlr⟩⟩

end Mettapedia.Logic.MarkovLogicInfiniteReinforcedLineExample
