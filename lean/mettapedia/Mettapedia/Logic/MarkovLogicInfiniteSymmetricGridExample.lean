import Mettapedia.Logic.MarkovLogicInfiniteGridExample
import Mettapedia.Logic.MarkovLogicInfiniteExistence

/-!
# Symmetric 2D Grid MLN

This file adds the spin-flip-symmetric nearest-neighbour grid target that the
low-temperature Ising/phase-coexistence crown should use.  Each unoriented edge
is represented by two implication clauses, so equal neighbouring spins satisfy
both clauses while unequal spins satisfy exactly one.  The support proof reuses
the oriented grid support by expanding each oriented edge id into its two
symmetric clauses.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteSymmetricGridExample

open scoped ENNReal
open Filter
open MeasureTheory
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteCylinders
open Mettapedia.Logic.MarkovLogicInfiniteExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicInfiniteGridExample

def spinFlipWorld {Atom : Type*} (ω : InfiniteWorld Atom) : InfiniteWorld Atom :=
  fun a => !ω a

def spinFlipLocalAssignment {Atom : Type*} {Λ : Region Atom}
    (x : LocalAssignment Atom Λ) : LocalAssignment Atom Λ :=
  fun a => !x a

@[simp] theorem spinFlipWorld_apply {Atom : Type*}
    (ω : InfiniteWorld Atom) (a : Atom) :
    spinFlipWorld ω a = !ω a := rfl

@[simp] theorem spinFlipLocalAssignment_apply {Atom : Type*} {Λ : Region Atom}
    (x : LocalAssignment Atom Λ) (a : RegionAtom Atom Λ) :
    spinFlipLocalAssignment x a = !x a := rfl

theorem spinFlipWorld_involutive {Atom : Type*}
    (ω : InfiniteWorld Atom) :
    spinFlipWorld (spinFlipWorld ω) = ω := by
  funext a
  simp [spinFlipWorld]

theorem spinFlipLocalAssignment_involutive {Atom : Type*} {Λ : Region Atom}
    (x : LocalAssignment Atom Λ) :
    spinFlipLocalAssignment (spinFlipLocalAssignment x) = x := by
  funext a
  simp [spinFlipLocalAssignment]

theorem spinFlipLocalAssignment_bijective {Atom : Type*} {Λ : Region Atom} :
    Function.Bijective (@spinFlipLocalAssignment Atom Λ) := by
  constructor
  · intro a b h
    have hflip := congrArg spinFlipLocalAssignment h
    simpa [spinFlipLocalAssignment_involutive] using hflip
  · intro a
    exact ⟨spinFlipLocalAssignment a, by simp [spinFlipLocalAssignment_involutive]⟩

theorem spinFlipWorld_patch {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (x : LocalAssignment Atom Λ) (ξ : BoundaryCondition Atom) :
    spinFlipWorld (patch Λ x ξ) =
      patch Λ (spinFlipLocalAssignment x) (spinFlipWorld ξ) := by
  funext a
  by_cases ha : a ∈ Λ <;> simp [spinFlipWorld, spinFlipLocalAssignment, patch, ha]

@[simp] theorem spinFlipWorld_gridPlusBoundary :
    spinFlipWorld gridPlusBoundary = gridMinusBoundary := by
  funext a
  simp [spinFlipWorld, gridPlusBoundary, gridMinusBoundary]

@[simp] theorem spinFlipWorld_gridMinusBoundary :
    spinFlipWorld gridMinusBoundary = gridPlusBoundary := by
  funext a
  simp [spinFlipWorld, gridPlusBoundary, gridMinusBoundary]

theorem spinFlipLocalAssignment_mem_originSpinUp_iff_not
    (x : LocalAssignment GridNode ({gridOrigin} : Region GridNode)) :
    spinFlipLocalAssignment x ∈
        localConstraintSet ({gridOrigin} : Region GridNode)
          gridOriginSpinUpLocalQuery ↔
      x ∉
        localConstraintSet ({gridOrigin} : Region GridNode)
          gridOriginSpinUpLocalQuery := by
  rw [gridOriginSpinUpLocalConstraintSet_eq]
  simp [singletonTrueAssignmentSet, spinFlipLocalAssignment]

/-- One-site origin-spin query viewed inside any finite region that contains
the origin.  The `true` instance is the positive/up event; the `false` instance
is its negative/down companion. -/
def gridOriginSpinLocalQueryInRegion
    (Λ : Region GridNode) (hOrigin : gridOrigin ∈ Λ) (b : Bool) :
    LocalConstraintQuery GridNode Λ :=
  [⟨⟨gridOrigin, hOrigin⟩, b⟩]

theorem spinFlipLocalAssignment_satisfies_originSpinInRegion_iff
    (Λ : Region GridNode) (hOrigin : gridOrigin ∈ Λ) (b : Bool)
    (x : LocalAssignment GridNode Λ) :
    satisfiesConstraints (spinFlipLocalAssignment x)
        (gridOriginSpinLocalQueryInRegion Λ hOrigin b) ↔
      satisfiesConstraints x
        (gridOriginSpinLocalQueryInRegion Λ hOrigin (!b)) := by
  cases b <;> simp [satisfiesConstraints, gridOriginSpinLocalQueryInRegion,
    spinFlipLocalAssignment]

theorem gridOrigin_mem_gridExhaustion_region (n : ℕ) :
    gridOrigin ∈ gridExhaustion.region n := by
  simp [gridExhaustion, gridOrigin]

theorem localQueryEvent_gridOriginSpinLocalQueryInRegion_eq_originSpinUp
    (Λ : Region GridNode) (hOrigin : gridOrigin ∈ Λ) :
    localQueryEvent Λ (gridOriginSpinLocalQueryInRegion Λ hOrigin true) =
      localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery := by
  ext ω
  simp [localQueryEvent, worldRestriction, satisfiesConstraints,
    gridOriginSpinLocalQueryInRegion, gridOriginSpinUpLocalQuery]

/-- The eastern nearest neighbour of the origin in the quarter-plane grid. -/
def gridOriginEast : GridNode := (1, 0)

/-- The northern nearest neighbour of the origin in the quarter-plane grid. -/
def gridOriginNorth : GridNode := (0, 1)

/-- The two boundary-support neighbours of the corner origin. -/
def gridOriginNeighborPairRegion : Region GridNode :=
  ({gridOriginEast, gridOriginNorth} : Finset GridNode)

@[simp] theorem gridOriginEast_mem_neighborPairRegion :
    gridOriginEast ∈ gridOriginNeighborPairRegion := by
  simp [gridOriginNeighborPairRegion]

@[simp] theorem gridOriginNorth_mem_neighborPairRegion :
    gridOriginNorth ∈ gridOriginNeighborPairRegion := by
  simp [gridOriginNeighborPairRegion]

/-- The local assignment on the east/north origin-neighbour pair with the
prescribed truth values. -/
def gridOriginNeighborPairAssignment (bEast bNorth : Bool) :
    LocalAssignment GridNode gridOriginNeighborPairRegion :=
  fun a => if a.1 = gridOriginEast then bEast else bNorth

@[simp] theorem gridOriginNeighborPairAssignment_apply_east
    (bEast bNorth : Bool) :
    gridOriginNeighborPairAssignment bEast bNorth
      ⟨gridOriginEast, gridOriginEast_mem_neighborPairRegion⟩ = bEast := by
  simp [gridOriginNeighborPairAssignment, gridOriginEast]

@[simp] theorem gridOriginNeighborPairAssignment_apply_north
    (bEast bNorth : Bool) :
    gridOriginNeighborPairAssignment bEast bNorth
      ⟨gridOriginNorth, gridOriginNorth_mem_neighborPairRegion⟩ = bNorth := by
  simp [gridOriginNeighborPairAssignment, gridOriginEast, gridOriginNorth]

@[simp] theorem gridOriginNeighborPairAssignment_eta
    (x : LocalAssignment GridNode gridOriginNeighborPairRegion) :
    gridOriginNeighborPairAssignment
        (x ⟨gridOriginEast, gridOriginEast_mem_neighborPairRegion⟩)
        (x ⟨gridOriginNorth, gridOriginNorth_mem_neighborPairRegion⟩) =
      x := by
  funext a
  rcases a with ⟨a, ha⟩
  have haCases : a = gridOriginEast ∨ a = gridOriginNorth := by
    simpa [gridOriginNeighborPairRegion, gridOriginEast, gridOriginNorth] using ha
  rcases haCases with rfl | rfl
  · simp [gridOriginNeighborPairAssignment]
  · simp [gridOriginNeighborPairAssignment, gridOriginEast, gridOriginNorth]

def gridOriginNeighborPairFF : LocalAssignment GridNode gridOriginNeighborPairRegion :=
  gridOriginNeighborPairAssignment false false

def gridOriginNeighborPairFT : LocalAssignment GridNode gridOriginNeighborPairRegion :=
  gridOriginNeighborPairAssignment false true

def gridOriginNeighborPairTF : LocalAssignment GridNode gridOriginNeighborPairRegion :=
  gridOriginNeighborPairAssignment true false

def gridOriginNeighborPairTT : LocalAssignment GridNode gridOriginNeighborPairRegion :=
  gridOriginNeighborPairAssignment true true

@[simp] theorem gridOriginNeighborPairAssignment_univ :
    (Finset.univ : Finset (LocalAssignment GridNode gridOriginNeighborPairRegion)) =
      ({gridOriginNeighborPairFF, gridOriginNeighborPairFT,
        gridOriginNeighborPairTF, gridOriginNeighborPairTT} :
          Finset (LocalAssignment GridNode gridOriginNeighborPairRegion)) := by
  ext x
  constructor
  · intro _hx
    rw [← gridOriginNeighborPairAssignment_eta x]
    cases hEast : x ⟨gridOriginEast, gridOriginEast_mem_neighborPairRegion⟩ <;>
      cases hNorth : x ⟨gridOriginNorth, gridOriginNorth_mem_neighborPairRegion⟩ <;>
      simp [gridOriginNeighborPairFF, gridOriginNeighborPairFT,
        gridOriginNeighborPairTF, gridOriginNeighborPairTT]
  · intro hx
    simp at hx
    simp

/-- Clause ids for the symmetric two-clause-per-edge grid. -/
inductive SymmetricGridClauseId where
  | prior : Nat → Nat → SymmetricGridClauseId
  | horizontalForward : Nat → Nat → SymmetricGridClauseId
  | horizontalBackward : Nat → Nat → SymmetricGridClauseId
  | verticalForward : Nat → Nat → SymmetricGridClauseId
  | verticalBackward : Nat → Nat → SymmetricGridClauseId
deriving DecidableEq

/-- Reverse horizontal implication, paired with `gridHorizontalClause` to reward
spin equality on a horizontal edge. -/
def gridHorizontalReverseClause (i j : Nat) : GroundClause GridNode :=
  {Literal.pos (i, j), Literal.neg (i + 1, j)}

/-- Reverse vertical implication, paired with `gridVerticalClause` to reward
spin equality on a vertical edge. -/
def gridVerticalReverseClause (i j : Nat) : GroundClause GridNode :=
  {Literal.pos (i, j), Literal.neg (i, j + 1)}

@[simp] theorem gridHorizontalReverseClause_atoms (i j : Nat) :
    (gridHorizontalReverseClause i j).atoms =
      ({(i, j), (i + 1, j)} : Finset GridNode) := by
  ext a
  simp [gridHorizontalReverseClause, GroundClause.atoms, Literal.atom]

@[simp] theorem gridVerticalReverseClause_atoms (i j : Nat) :
    (gridVerticalReverseClause i j).atoms =
      ({(i, j), (i, j + 1)} : Finset GridNode) := by
  ext a
  simp [gridVerticalReverseClause, GroundClause.atoms, Literal.atom]

theorem gridHorizontalClause_holds_spinFlip_iff_reverse
    (i j : Nat) (W : InfiniteWorld GridNode) :
    (gridHorizontalClause i j).holds (spinFlipWorld W) ↔
      (gridHorizontalReverseClause i j).holds W := by
  simp [gridHorizontalClause, gridHorizontalReverseClause, GroundClause.holds,
    Literal.holds, spinFlipWorld]

theorem gridHorizontalReverseClause_holds_spinFlip_iff_forward
    (i j : Nat) (W : InfiniteWorld GridNode) :
    (gridHorizontalReverseClause i j).holds (spinFlipWorld W) ↔
      (gridHorizontalClause i j).holds W := by
  simp [gridHorizontalClause, gridHorizontalReverseClause, GroundClause.holds,
    Literal.holds, spinFlipWorld]

theorem gridVerticalClause_holds_spinFlip_iff_reverse
    (i j : Nat) (W : InfiniteWorld GridNode) :
    (gridVerticalClause i j).holds (spinFlipWorld W) ↔
      (gridVerticalReverseClause i j).holds W := by
  simp [gridVerticalClause, gridVerticalReverseClause, GroundClause.holds,
    Literal.holds, spinFlipWorld]

theorem gridVerticalReverseClause_holds_spinFlip_iff_forward
    (i j : Nat) (W : InfiniteWorld GridNode) :
    (gridVerticalReverseClause i j).holds (spinFlipWorld W) ↔
      (gridVerticalClause i j).holds W := by
  simp [gridVerticalClause, gridVerticalReverseClause, GroundClause.holds,
    Literal.holds, spinFlipWorld]

theorem gridHorizontalPair_eval_spinFlip_eq
    (w : ℝ) (i j : Nat) (W : InfiniteWorld GridNode) :
    (classicalWeightedClause (gridHorizontalClause i j) w).eval (spinFlipWorld W) *
        (classicalWeightedClause (gridHorizontalReverseClause i j) w).eval (spinFlipWorld W) =
      (classicalWeightedClause (gridHorizontalClause i j) w).eval W *
        (classicalWeightedClause (gridHorizontalReverseClause i j) w).eval W := by
  by_cases hf : (gridHorizontalClause i j).holds W <;>
    by_cases hr : (gridHorizontalReverseClause i j).holds W <;>
      simp [WeightedGroundClause.eval, classicalWeightedClause,
        gridHorizontalClause_holds_spinFlip_iff_reverse,
        gridHorizontalReverseClause_holds_spinFlip_iff_forward,
        hf, hr, mul_comm]

theorem gridVerticalPair_eval_spinFlip_eq
    (w : ℝ) (i j : Nat) (W : InfiniteWorld GridNode) :
    (classicalWeightedClause (gridVerticalClause i j) w).eval (spinFlipWorld W) *
        (classicalWeightedClause (gridVerticalReverseClause i j) w).eval (spinFlipWorld W) =
      (classicalWeightedClause (gridVerticalClause i j) w).eval W *
        (classicalWeightedClause (gridVerticalReverseClause i j) w).eval W := by
  by_cases hf : (gridVerticalClause i j).holds W <;>
    by_cases hr : (gridVerticalReverseClause i j).holds W <;>
      simp [WeightedGroundClause.eval, classicalWeightedClause,
        gridVerticalClause_holds_spinFlip_iff_reverse,
        gridVerticalReverseClause_holds_spinFlip_iff_forward,
        hf, hr, mul_comm]

/-- Product of the two symmetric clause potentials on a horizontal grid edge. -/
noncomputable def symmetricGridHorizontalEdgePairWeight
    (w : ℝ) (i j : Nat) (W : InfiniteWorld GridNode) : ENNReal :=
  (classicalWeightedClause (gridHorizontalClause i j) w).eval W *
    (classicalWeightedClause (gridHorizontalReverseClause i j) w).eval W

/-- Product of the two symmetric clause potentials on a vertical grid edge. -/
noncomputable def symmetricGridVerticalEdgePairWeight
    (w : ℝ) (i j : Nat) (W : InfiniteWorld GridNode) : ENNReal :=
  (classicalWeightedClause (gridVerticalClause i j) w).eval W *
    (classicalWeightedClause (gridVerticalReverseClause i j) w).eval W

/-- Every symmetric horizontal edge contributes a base factor `exp(w)`, with an
additional factor `exp(w)` exactly when the endpoint spins agree. -/
theorem symmetricGridHorizontalEdgePairWeight_eq_alignmentBonus
    (w : ℝ) (i j : Nat) (W : InfiniteWorld GridNode) :
    symmetricGridHorizontalEdgePairWeight w i j W =
      ENNReal.ofReal (Real.exp w) *
        (if W (i, j) = W (i + 1, j) then ENNReal.ofReal (Real.exp w) else 1) := by
  cases hLeft : W (i, j) <;> cases hRight : W (i + 1, j) <;>
    simp [symmetricGridHorizontalEdgePairWeight, WeightedGroundClause.eval,
      classicalWeightedClause, gridHorizontalClause, gridHorizontalReverseClause,
      GroundClause.holds, Literal.holds, hLeft, hRight]

/-- Every symmetric vertical edge contributes a base factor `exp(w)`, with an
additional factor `exp(w)` exactly when the endpoint spins agree. -/
theorem symmetricGridVerticalEdgePairWeight_eq_alignmentBonus
    (w : ℝ) (i j : Nat) (W : InfiniteWorld GridNode) :
    symmetricGridVerticalEdgePairWeight w i j W =
      ENNReal.ofReal (Real.exp w) *
        (if W (i, j) = W (i, j + 1) then ENNReal.ofReal (Real.exp w) else 1) := by
  cases hDown : W (i, j) <;> cases hUp : W (i, j + 1) <;>
    simp [symmetricGridVerticalEdgePairWeight, WeightedGroundClause.eval,
      classicalWeightedClause, gridVerticalClause, gridVerticalReverseClause,
      GroundClause.holds, Literal.holds, hDown, hUp]

theorem symmetricGridHorizontalEdgePairWeight_eq_of_eq
    (w : ℝ) (i j : Nat) (W : InfiniteWorld GridNode)
    (hEq : W (i, j) = W (i + 1, j)) :
    symmetricGridHorizontalEdgePairWeight w i j W =
      ENNReal.ofReal (Real.exp w) * ENNReal.ofReal (Real.exp w) := by
  simp [symmetricGridHorizontalEdgePairWeight_eq_alignmentBonus, hEq]

theorem symmetricGridVerticalEdgePairWeight_eq_of_eq
    (w : ℝ) (i j : Nat) (W : InfiniteWorld GridNode)
    (hEq : W (i, j) = W (i, j + 1)) :
    symmetricGridVerticalEdgePairWeight w i j W =
      ENNReal.ofReal (Real.exp w) * ENNReal.ofReal (Real.exp w) := by
  simp [symmetricGridVerticalEdgePairWeight_eq_alignmentBonus, hEq]

theorem symmetricGridHorizontalEdgePairWeight_eq_of_ne
    (w : ℝ) (i j : Nat) (W : InfiniteWorld GridNode)
    (hNe : W (i, j) ≠ W (i + 1, j)) :
    symmetricGridHorizontalEdgePairWeight w i j W =
      ENNReal.ofReal (Real.exp w) := by
  simp [symmetricGridHorizontalEdgePairWeight_eq_alignmentBonus, hNe]

theorem symmetricGridVerticalEdgePairWeight_eq_of_ne
    (w : ℝ) (i j : Nat) (W : InfiniteWorld GridNode)
    (hNe : W (i, j) ≠ W (i, j + 1)) :
    symmetricGridVerticalEdgePairWeight w i j W =
      ENNReal.ofReal (Real.exp w) := by
  simp [symmetricGridVerticalEdgePairWeight_eq_alignmentBonus, hNe]

/-- Correcting a horizontal disagreement to an agreement gains exactly one
additional factor `exp(w)` in the symmetric two-clause-per-edge encoding. -/
theorem symmetricGridHorizontalEdgePairWeight_gain_of_eq_over_ne
    (w : ℝ) (i j : Nat) (W W' : InfiniteWorld GridNode)
    (hEq : W' (i, j) = W' (i + 1, j))
    (hNe : W (i, j) ≠ W (i + 1, j)) :
    symmetricGridHorizontalEdgePairWeight w i j W' =
      ENNReal.ofReal (Real.exp w) *
        symmetricGridHorizontalEdgePairWeight w i j W := by
  simp [symmetricGridHorizontalEdgePairWeight_eq_of_eq, hEq,
    symmetricGridHorizontalEdgePairWeight_eq_of_ne, hNe]

/-- Correcting a vertical disagreement to an agreement gains exactly one
additional factor `exp(w)` in the symmetric two-clause-per-edge encoding. -/
theorem symmetricGridVerticalEdgePairWeight_gain_of_eq_over_ne
    (w : ℝ) (i j : Nat) (W W' : InfiniteWorld GridNode)
    (hEq : W' (i, j) = W' (i, j + 1))
    (hNe : W (i, j) ≠ W (i, j + 1)) :
    symmetricGridVerticalEdgePairWeight w i j W' =
      ENNReal.ofReal (Real.exp w) *
        symmetricGridVerticalEdgePairWeight w i j W := by
  simp [symmetricGridVerticalEdgePairWeight_eq_of_eq, hEq,
    symmetricGridVerticalEdgePairWeight_eq_of_ne, hNe]

/-- Underlying clause attached to a symmetric grid clause id. -/
def symmetricGridClause : SymmetricGridClauseId → GroundClause GridNode
  | .prior i j => gridPriorClause i j
  | .horizontalForward i j => gridHorizontalClause i j
  | .horizontalBackward i j => gridHorizontalReverseClause i j
  | .verticalForward i j => gridVerticalClause i j
  | .verticalBackward i j => gridVerticalReverseClause i j

/-- Forget the reverse/forward distinction, retaining the underlying oriented
support id whose atoms are touched. -/
def symmetricGridBaseClauseId : SymmetricGridClauseId → GridClauseId
  | .prior i j => GridClauseId.prior i j
  | .horizontalForward i j => GridClauseId.horizontal i j
  | .horizontalBackward i j => GridClauseId.horizontal i j
  | .verticalForward i j => GridClauseId.vertical i j
  | .verticalBackward i j => GridClauseId.vertical i j

/-- Expand one oriented support id into the symmetric clauses it contributes. -/
def symmetricGridExpansion : GridClauseId → Finset SymmetricGridClauseId
  | .prior i j => {SymmetricGridClauseId.prior i j}
  | .horizontal i j =>
      {SymmetricGridClauseId.horizontalForward i j,
        SymmetricGridClauseId.horizontalBackward i j}
  | .vertical i j =>
      {SymmetricGridClauseId.verticalForward i j,
        SymmetricGridClauseId.verticalBackward i j}

/-- Spin-flip swaps the two oriented implications on every edge and fixes the
zero-field one-site prior ids. -/
def symmetricGridClauseFlip : SymmetricGridClauseId → SymmetricGridClauseId
  | .prior i j => .prior i j
  | .horizontalForward i j => .horizontalBackward i j
  | .horizontalBackward i j => .horizontalForward i j
  | .verticalForward i j => .verticalBackward i j
  | .verticalBackward i j => .verticalForward i j

@[simp] theorem symmetricGridClauseFlip_involutive
    (k : SymmetricGridClauseId) :
    symmetricGridClauseFlip (symmetricGridClauseFlip k) = k := by
  cases k <;> rfl

@[simp] theorem symmetricGridBaseClauseId_flip
    (k : SymmetricGridClauseId) :
    symmetricGridBaseClauseId (symmetricGridClauseFlip k) =
      symmetricGridBaseClauseId k := by
  cases k <;> rfl

theorem symmetricGridClauseFlip_bijective :
    Function.Bijective symmetricGridClauseFlip := by
  constructor
  · intro a b h
    have hflip := congrArg symmetricGridClauseFlip h
    simpa using hflip
  · intro a
    exact ⟨symmetricGridClauseFlip a, by simp⟩

theorem symmetricGridClauseFlip_mem_expansion_iff
    (j : GridClauseId) (k : SymmetricGridClauseId) :
    symmetricGridClauseFlip k ∈ symmetricGridExpansion j ↔
      k ∈ symmetricGridExpansion j := by
  cases j <;> cases k <;>
    simp [symmetricGridExpansion, symmetricGridClauseFlip]

/-- Symmetric clauses touch exactly the same atom set as their base oriented
support id. -/
theorem symmetricGridClause_atoms_eq_base (k : SymmetricGridClauseId) :
    (symmetricGridClause k).atoms =
      (gridClause (symmetricGridBaseClauseId k)).atoms := by
  cases k <;> simp [symmetricGridClause, symmetricGridBaseClauseId, gridClause]

theorem symmetricGridBase_mem_expansion (k : SymmetricGridClauseId) :
    k ∈ symmetricGridExpansion (symmetricGridBaseClauseId k) := by
  cases k <;> simp [symmetricGridExpansion, symmetricGridBaseClauseId]

theorem symmetricGridBaseClauseId_eq_of_mem_expansion
    {j : GridClauseId} {k : SymmetricGridClauseId}
    (hk : k ∈ symmetricGridExpansion j) :
    symmetricGridBaseClauseId k = j := by
  cases j <;> cases k <;>
    simp [symmetricGridExpansion, symmetricGridBaseClauseId] at hk ⊢ <;>
    simpa using hk

theorem symmetricGridExpansion_pairwiseDisjoint
    (s : Finset GridClauseId) :
    Set.PairwiseDisjoint (↑s) symmetricGridExpansion := by
  intro j _hj k _hk hjk
  change Disjoint (symmetricGridExpansion j) (symmetricGridExpansion k)
  rw [Finset.disjoint_left]
  intro x hxj hxk
  have hbasej : symmetricGridBaseClauseId x = j :=
    symmetricGridBaseClauseId_eq_of_mem_expansion hxj
  have hbasek : symmetricGridBaseClauseId x = k :=
    symmetricGridBaseClauseId_eq_of_mem_expansion hxk
  exact hjk (hbasej.symm.trans hbasek)

/-- Finite clause support for the symmetric grid, obtained by expanding the
already-proved oriented grid support. -/
noncomputable def symmetricGridRegionSupport
    (Λ : Region GridNode) : Finset SymmetricGridClauseId :=
  (gridRegionSupport Λ).biUnion symmetricGridExpansion

theorem symmetricGridClauseFlip_mem_regionSupport_iff
    (Λ : Region GridNode) (k : SymmetricGridClauseId) :
    symmetricGridClauseFlip k ∈ symmetricGridRegionSupport Λ ↔
      k ∈ symmetricGridRegionSupport Λ := by
  rw [symmetricGridRegionSupport]
  constructor
  · intro hk
    rcases Finset.mem_biUnion.mp hk with ⟨j, hj, hkj⟩
    exact Finset.mem_biUnion.mpr
      ⟨j, hj, (symmetricGridClauseFlip_mem_expansion_iff j k).1 hkj⟩
  · intro hk
    rcases Finset.mem_biUnion.mp hk with ⟨j, hj, hkj⟩
    exact Finset.mem_biUnion.mpr
      ⟨j, hj, (symmetricGridClauseFlip_mem_expansion_iff j k).2 hkj⟩

theorem symmetricGridRegionSupport_sound
    {Λ : Region GridNode} {k : SymmetricGridClauseId}
    (hk : k ∈ symmetricGridRegionSupport Λ) :
    clauseTouchesRegion (symmetricGridClause k) Λ := by
  rw [symmetricGridRegionSupport] at hk
  rcases Finset.mem_biUnion.mp hk with ⟨j, hj, hkj⟩
  rcases gridRegionSupport_sound (Λ := Λ) (j := j) hj with ⟨a, ha, haΛ⟩
  refine ⟨a, ?_, haΛ⟩
  have hatoms : (symmetricGridClause k).atoms = (gridClause j).atoms := by
    cases j <;> simp [symmetricGridExpansion] at hkj <;> rcases hkj with rfl | rfl <;>
      simp [symmetricGridClause_atoms_eq_base, symmetricGridBaseClauseId, gridClause]
  simpa [hatoms] using ha

theorem symmetricGridRegionSupport_complete
    {Λ : Region GridNode} {k : SymmetricGridClauseId}
    (hk : clauseTouchesRegion (symmetricGridClause k) Λ) :
    k ∈ symmetricGridRegionSupport Λ := by
  rw [symmetricGridRegionSupport]
  refine Finset.mem_biUnion.mpr
    ⟨symmetricGridBaseClauseId k, ?_, symmetricGridBase_mem_expansion k⟩
  apply gridRegionSupport_complete
  rcases hk with ⟨a, ha, haΛ⟩
  refine ⟨a, ?_, haΛ⟩
  simpa [symmetricGridClause_atoms_eq_base k] using ha

/-- Symmetric 2D grid MLN with uniform external field `h` and equality-reward
interaction weight `w`. -/
noncomputable def symmetricGridClassicalSpecWithField (h w : ℝ) :
    ClassicalInfiniteGroundMLNSpec GridNode SymmetricGridClauseId where
  clause := symmetricGridClause
  logWeight k := match k with
    | .prior _ _ => h
    | .horizontalForward _ _ => w
    | .horizontalBackward _ _ => w
    | .verticalForward _ _ => w
    | .verticalBackward _ _ => w
  regionSupport := symmetricGridRegionSupport
  regionSupport_sound := fun hk => symmetricGridRegionSupport_sound hk
  regionSupport_complete := fun hk => symmetricGridRegionSupport_complete hk

/-- Zero-field symmetric 2D grid MLN: the classical plus/minus Ising-style
target for low-temperature phase coexistence. -/
noncomputable def symmetricGridZeroFieldClassicalSpec
    (w : ℝ) : ClassicalInfiniteGroundMLNSpec GridNode SymmetricGridClauseId :=
  symmetricGridClassicalSpecWithField 0 w

/-- The zero-field weight contributed by one oriented support id: priors are
trivial, while horizontal and vertical ids contribute the paired symmetric edge
weights. -/
noncomputable def symmetricGridBaseClauseWeight
    (w : ℝ) (j : GridClauseId) (W : InfiniteWorld GridNode) : ENNReal :=
  match j with
  | .prior _ _ => 1
  | .horizontal i j => symmetricGridHorizontalEdgePairWeight w i j W
  | .vertical i j => symmetricGridVerticalEdgePairWeight w i j W

theorem symmetricGridExpansion_prod_clauseEval_eq_baseClauseWeight
    (w : ℝ) (j : GridClauseId) (W : InfiniteWorld GridNode) :
    ∏ k ∈ symmetricGridExpansion j,
      ((symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.clauseData k).eval W =
        symmetricGridBaseClauseWeight w j W := by
  cases j <;>
    simp [symmetricGridExpansion, symmetricGridBaseClauseWeight,
      symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
      ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec,
      symmetricGridClause, symmetricGridHorizontalEdgePairWeight,
      symmetricGridVerticalEdgePairWeight, classicalWeightedClause,
      WeightedGroundClause.eval, Real.exp_zero]

theorem symmetricGridZeroField_finiteVolumeWeight_eq_prod_baseClauseWeight
    (w : ℝ) (Λ : Region GridNode) (x : LocalAssignment GridNode Λ)
    (ξ : BoundaryCondition GridNode) :
    (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumeWeight
        Λ x ξ =
      ∏ j ∈ gridRegionSupport Λ,
        symmetricGridBaseClauseWeight w j (patch Λ x ξ) := by
  classical
  let W : InfiniteWorld GridNode := patch Λ x ξ
  unfold Mettapedia.Logic.MarkovLogicInfiniteSpecification.InfiniteGroundMLNSpec.finiteVolumeWeight
  change
    (∏ k ∈ symmetricGridRegionSupport Λ,
      ((symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.clauseData k).eval W) =
      ∏ j ∈ gridRegionSupport Λ, symmetricGridBaseClauseWeight w j W
  rw [symmetricGridRegionSupport, Finset.prod_biUnion
    (symmetricGridExpansion_pairwiseDisjoint (gridRegionSupport Λ))]
  refine Finset.prod_congr rfl ?_
  intro j hj
  simpa [W] using symmetricGridExpansion_prod_clauseEval_eq_baseClauseWeight w j W

theorem symmetricGridZeroField_clauseData_eval_spinFlip_eq_flip
    (w : ℝ) (k : SymmetricGridClauseId) (W : InfiniteWorld GridNode) :
    ((symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.clauseData k).eval
        (spinFlipWorld W) =
      ((symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.clauseData
        (symmetricGridClauseFlip k)).eval W := by
  cases k <;>
    simp [ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec,
      symmetricGridClauseFlip, symmetricGridZeroFieldClassicalSpec,
      symmetricGridClassicalSpecWithField, symmetricGridClause, WeightedGroundClause.eval,
      classicalWeightedClause, gridHorizontalClause_holds_spinFlip_iff_reverse,
      gridHorizontalReverseClause_holds_spinFlip_iff_forward,
      gridVerticalClause_holds_spinFlip_iff_reverse,
      gridVerticalReverseClause_holds_spinFlip_iff_forward]

theorem symmetricGridZeroField_finiteVolumeWeight_spinFlip
    (w : ℝ) (Λ : Region GridNode) (x : LocalAssignment GridNode Λ)
    (ξ : BoundaryCondition GridNode) :
    (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumeWeight
        Λ (spinFlipLocalAssignment x) (spinFlipWorld ξ) =
      (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumeWeight
        Λ x ξ := by
  classical
  unfold Mettapedia.Logic.MarkovLogicInfiniteSpecification.InfiniteGroundMLNSpec.finiteVolumeWeight
  rw [← spinFlipWorld_patch]
  refine Finset.prod_bijective symmetricGridClauseFlip symmetricGridClauseFlip_bijective ?_ ?_
  · intro k
    simpa [symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
      ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec] using
      (symmetricGridClauseFlip_mem_regionSupport_iff Λ k).symm
  · intro k _hk
    simpa using symmetricGridZeroField_clauseData_eval_spinFlip_eq_flip w k (patch Λ x ξ)

theorem symmetricGridZeroField_finiteVolumePartition_spinFlip
    (w : ℝ) (Λ : Region GridNode) (ξ : BoundaryCondition GridNode) :
    (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumePartition
        Λ (spinFlipWorld ξ) =
      (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumePartition
        Λ ξ := by
  classical
  unfold Mettapedia.Logic.MarkovLogicInfiniteSpecification.InfiniteGroundMLNSpec.finiteVolumePartition
  refine Finset.sum_bijective spinFlipLocalAssignment spinFlipLocalAssignment_bijective ?_ ?_
  · intro x
    simp
  · intro x _hx
    simpa [spinFlipLocalAssignment_involutive] using
      (symmetricGridZeroField_finiteVolumeWeight_spinFlip w Λ (spinFlipLocalAssignment x) ξ)

theorem symmetricGridZeroField_finiteVolumeAssignmentPMF_spinFlip
    (w : ℝ) (Λ : Region GridNode) (x : LocalAssignment GridNode Λ)
    (ξ : BoundaryCondition GridNode) :
    finiteVolumeAssignmentPMF
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ (spinFlipWorld ξ)
        (Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          Λ (spinFlipWorld ξ))
        (spinFlipLocalAssignment x) =
      finiteVolumeAssignmentPMF
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ ξ
        (Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          Λ ξ)
        x := by
  simp [finiteVolumeAssignmentPMF_apply,
    symmetricGridZeroField_finiteVolumeWeight_spinFlip,
    symmetricGridZeroField_finiteVolumePartition_spinFlip]

theorem symmetricGridZeroField_originSpin_queryMass_spinFlip
    (w : ℝ) (Λ : Region GridNode) (hOrigin : gridOrigin ∈ Λ)
    (ξ : BoundaryCondition GridNode) (b : Bool) :
    finiteVolumeQueryMass
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ (spinFlipWorld ξ)
        (gridOriginSpinLocalQueryInRegion Λ hOrigin b) =
      finiteVolumeQueryMass
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ ξ
        (gridOriginSpinLocalQueryInRegion Λ hOrigin (!b)) := by
  classical
  unfold finiteVolumeQueryMass
  refine Finset.sum_bijective spinFlipLocalAssignment spinFlipLocalAssignment_bijective ?_ ?_
  · intro x
    simp
  · intro x _hx
    have hsat : satisfiesConstraints x
          (gridOriginSpinLocalQueryInRegion Λ hOrigin b) ↔
        satisfiesConstraints (spinFlipLocalAssignment x)
          (gridOriginSpinLocalQueryInRegion Λ hOrigin (!b)) := by
      simpa using
        (spinFlipLocalAssignment_satisfies_originSpinInRegion_iff
          Λ hOrigin (!b) x).symm
    by_cases hxSat : satisfiesConstraints x
        (gridOriginSpinLocalQueryInRegion Λ hOrigin b)
    · have hxFlipSat : satisfiesConstraints (spinFlipLocalAssignment x)
          (gridOriginSpinLocalQueryInRegion Λ hOrigin (!b)) := hsat.1 hxSat
      simp [hxSat, hxFlipSat]
      simpa [spinFlipLocalAssignment_involutive] using
        (symmetricGridZeroField_finiteVolumeWeight_spinFlip w Λ (spinFlipLocalAssignment x) ξ)
    · have hxFlipNotSat : ¬ satisfiesConstraints (spinFlipLocalAssignment x)
          (gridOriginSpinLocalQueryInRegion Λ hOrigin (!b)) := by
        intro hxFlipSat
        exact hxSat (hsat.2 hxFlipSat)
      simp [hxSat, hxFlipNotSat]

theorem symmetricGridZeroField_originSpin_queryProb_spinFlip
    (w : ℝ) (Λ : Region GridNode) (hOrigin : gridOrigin ∈ Λ)
    (ξ : BoundaryCondition GridNode) (b : Bool) :
    (finiteVolumeMassSemantics
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ (spinFlipWorld ξ)).queryProb
        (gridOriginSpinLocalQueryInRegion Λ hOrigin b) =
      (finiteVolumeMassSemantics
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ ξ).queryProb
        (gridOriginSpinLocalQueryInRegion Λ hOrigin (!b)) := by
  unfold finiteVolumeMassSemantics MassSemantics.queryProb
  simp [symmetricGridZeroField_originSpin_queryMass_spinFlip,
    symmetricGridZeroField_finiteVolumePartition_spinFlip]

theorem symmetricGridZeroField_originSpin_queryMass_add_complement
    (w : ℝ) (Λ : Region GridNode) (hOrigin : gridOrigin ∈ Λ)
    (ξ : BoundaryCondition GridNode) (b : Bool) :
    finiteVolumeQueryMass
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ ξ (gridOriginSpinLocalQueryInRegion Λ hOrigin b) +
      finiteVolumeQueryMass
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ ξ (gridOriginSpinLocalQueryInRegion Λ hOrigin (!b)) =
      (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec.finiteVolumePartition
        Λ ξ := by
  classical
  unfold finiteVolumeQueryMass
  unfold Mettapedia.Logic.MarkovLogicInfiniteSpecification.InfiniteGroundMLNSpec.finiteVolumePartition
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  cases b <;>
    by_cases hxOrigin : x ⟨gridOrigin, hOrigin⟩ = true <;>
      simp [satisfiesConstraints, gridOriginSpinLocalQueryInRegion, hxOrigin] at *

theorem symmetricGridZeroField_originSpin_queryProb_add_complement
    (w : ℝ) (Λ : Region GridNode) (hOrigin : gridOrigin ∈ Λ)
    (ξ : BoundaryCondition GridNode) (b : Bool) :
    (finiteVolumeMassSemantics
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ ξ).queryProb
        (gridOriginSpinLocalQueryInRegion Λ hOrigin b) +
      (finiteVolumeMassSemantics
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        Λ ξ).queryProb
        (gridOriginSpinLocalQueryInRegion Λ hOrigin (!b)) = 1 := by
  let Msp := (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
  have hZ : Msp.finiteVolumePartition Λ ξ ≠ 0 := by
    exact Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
      Msp Λ ξ
  have htop : Msp.finiteVolumePartition Λ ξ ≠ ⊤ := by
    simpa using finiteVolumePartition_ne_top Msp.toInfiniteGroundMLNSpec Λ ξ
  unfold finiteVolumeMassSemantics MassSemantics.queryProb
  simp [Msp, hZ]
  rw [ENNReal.div_add_div_same]
  rw [symmetricGridZeroField_originSpin_queryMass_add_complement]
  exact ENNReal.div_self hZ htop

theorem symmetricGridZeroField_originSpin_queryProb_toReal_spinFlip
    (w : ℝ) (Λ : Region GridNode) (hOrigin : gridOrigin ∈ Λ)
    (ξ : BoundaryCondition GridNode) (b : Bool) :
    ENNReal.toReal
      ((finiteVolumeMassSemantics
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          Λ (spinFlipWorld ξ)).queryProb
          (gridOriginSpinLocalQueryInRegion Λ hOrigin b)) =
      1 - ENNReal.toReal
        ((finiteVolumeMassSemantics
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          Λ ξ).queryProb
          (gridOriginSpinLocalQueryInRegion Λ hOrigin b)) := by
  let S := finiteVolumeMassSemantics
    (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
    Λ ξ
  let q := gridOriginSpinLocalQueryInRegion Λ hOrigin b
  let qC := gridOriginSpinLocalQueryInRegion Λ hOrigin (!b)
  have htransport :
      (finiteVolumeMassSemantics
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          Λ (spinFlipWorld ξ)).queryProb q = S.queryProb qC := by
    simpa [S, q, qC] using
      symmetricGridZeroField_originSpin_queryProb_spinFlip w Λ hOrigin ξ b
  have hsum : S.queryProb q + S.queryProb qC = 1 := by
    simpa [S, q, qC] using
      symmetricGridZeroField_originSpin_queryProb_add_complement w Λ hOrigin ξ b
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

theorem symmetricGridZeroField_finiteVolumeKernel_originSpinUp_eq_queryProb
    (w : ℝ) (n : ℕ) (ξ : BoundaryCondition GridNode) :
    gridExhaustion.finiteVolumeKernelSequence
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        ξ n
        (localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery) =
      (finiteVolumeMassSemantics
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        (gridExhaustion.region n) ξ).queryProb
        (gridOriginSpinLocalQueryInRegion (gridExhaustion.region n)
          (gridOrigin_mem_gridExhaustion_region n) true) := by
  rw [← localQueryEvent_gridOriginSpinLocalQueryInRegion_eq_originSpinUp
    (gridExhaustion.region n) (gridOrigin_mem_gridExhaustion_region n)]
  rw [Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion.finiteVolumeKernelSequence]
  simpa [Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure] using
    (finiteVolumeWorldMeasure_localQueryEvent
      (M := (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec)
      (Λ := gridExhaustion.region n) (ξ := ξ)
      (hZ := Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        (gridExhaustion.region n) ξ)
      (q := gridOriginSpinLocalQueryInRegion (gridExhaustion.region n)
        (gridOrigin_mem_gridExhaustion_region n) true))

theorem symmetricGridZeroField_originSpinUp_finiteVolumeKernel_spinFlip
    (w : ℝ) (n : ℕ) (ξ : BoundaryCondition GridNode) :
    ENNReal.toReal
      (gridExhaustion.finiteVolumeKernelSequence
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        (spinFlipWorld ξ) n
        (localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery)) =
      1 - ENNReal.toReal
        (gridExhaustion.finiteVolumeKernelSequence
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ n
          (localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery)) := by
  rw [symmetricGridZeroField_finiteVolumeKernel_originSpinUp_eq_queryProb]
  rw [symmetricGridZeroField_finiteVolumeKernel_originSpinUp_eq_queryProb]
  exact symmetricGridZeroField_originSpin_queryProb_toReal_spinFlip
    w (gridExhaustion.region n) (gridOrigin_mem_gridExhaustion_region n) ξ true

theorem symmetricGridZeroField_originSpinUp_finiteVolumeKernel_minus_eq_one_sub_plus
    (w : ℝ) (n : ℕ) :
    ENNReal.toReal
      (gridExhaustion.finiteVolumeKernelSequence
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        gridMinusBoundary n
        (localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery)) =
      1 - ENNReal.toReal
        (gridExhaustion.finiteVolumeKernelSequence
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          gridPlusBoundary n
          (localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery)) := by
  simpa using
    (symmetricGridZeroField_originSpinUp_finiteVolumeKernel_spinFlip w n gridPlusBoundary)

private theorem symmetricGridZeroField_verticalPairInfluence_sum
    (w : ℝ) (i j : Nat) :
    ({SymmetricGridClauseId.verticalForward i j,
      SymmetricGridClauseId.verticalBackward i j} : Finset SymmetricGridClauseId).sum
        (fun x => (symmetricGridZeroFieldClassicalSpec w).clauseInfluenceContribution x) =
      |w| + |w| := by
  rw [Finset.sum_pair]
  · simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
      symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
      symmetricGridClause]
  · intro h
    cases h

private theorem symmetricGridZeroField_verticalTwoPairInfluence_sum
    (w : ℝ) {i j : Nat} (hj0 : j ≠ 0) :
    ({SymmetricGridClauseId.verticalForward i j,
      SymmetricGridClauseId.verticalBackward i j,
      SymmetricGridClauseId.verticalForward i (Nat.pred j),
      SymmetricGridClauseId.verticalBackward i (Nat.pred j)} :
        Finset SymmetricGridClauseId).sum
        (fun x => (symmetricGridZeroFieldClassicalSpec w).clauseInfluenceContribution x) =
      |w| + |w| + |w| + |w| := by
  rw [Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
          symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
          symmetricGridClause]
        ring_nf
      · simp
    · simp
      omega
  · simp
    omega

/-- The symmetric zero-field grid has Dobrushin row sum at most `4 * |w|`.
Each interior site touches four unoriented neighbours, represented by two
implication clauses per edge; boundary sites touch fewer clauses. -/
theorem symmetricGridZeroField_uniformSmallTotalInfluence
    {w : ℝ} (hbudget : 4 * |w| < 1) :
    (symmetricGridZeroFieldClassicalSpec w).PaperUniformSmallTotalInfluence := by
  refine ⟨4 * |w|, by positivity, hbudget, ?_⟩
  intro a
  rcases a with ⟨i, j⟩
  have hrow :
      Finset.sum ((symmetricGridZeroFieldClassicalSpec w).atomInteractionNeighborhood (i, j))
        (fun b => (symmetricGridZeroFieldClassicalSpec w).pairwiseDobrushinCoefficient (i, j) b) =
        (1 / 2 : ℝ) * (symmetricGridZeroFieldClassicalSpec w).atomTotalInfluence (i, j) := by
    rw [(symmetricGridZeroFieldClassicalSpec w).atomTotalInfluence_eq_sum_pairwiseInfluence]
    simp [ClassicalInfiniteGroundMLNSpec.pairwiseDobrushinCoefficient, Finset.mul_sum]
  rw [hrow]
  by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
  · subst hi0; subst hj0
    have hsupp00 :
        (symmetricGridZeroFieldClassicalSpec w).regionSupport ({(0, 0)} : Finset GridNode) =
          ({SymmetricGridClauseId.prior 0 0,
            SymmetricGridClauseId.horizontalForward 0 0,
            SymmetricGridClauseId.horizontalBackward 0 0,
            SymmetricGridClauseId.verticalForward 0 0,
            SymmetricGridClauseId.verticalBackward 0 0} : Finset SymmetricGridClauseId) := by
      ext k
      cases k <;> simp [symmetricGridZeroFieldClassicalSpec,
        symmetricGridClassicalSpecWithField, symmetricGridRegionSupport,
        symmetricGridExpansion, gridRegionSupport]
    have htot :
        (symmetricGridZeroFieldClassicalSpec w).atomTotalInfluence (0, 0) = 4 * |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp00]
      simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
        symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
        symmetricGridClause, gridHorizontalClause_atoms, gridVerticalClause_atoms]
      ring_nf
    rw [htot]
    nlinarith [abs_nonneg w]
  · subst hi0
    have hsupp0j :
        (symmetricGridZeroFieldClassicalSpec w).regionSupport ({(0, j)} : Finset GridNode) =
          ({SymmetricGridClauseId.prior 0 j,
            SymmetricGridClauseId.horizontalForward 0 j,
            SymmetricGridClauseId.horizontalBackward 0 j,
            SymmetricGridClauseId.verticalForward 0 j,
            SymmetricGridClauseId.verticalBackward 0 j,
            SymmetricGridClauseId.verticalForward 0 (Nat.pred j),
            SymmetricGridClauseId.verticalBackward 0 (Nat.pred j)} :
              Finset SymmetricGridClauseId) := by
      ext k
      cases k <;> simp [symmetricGridZeroFieldClassicalSpec,
        symmetricGridClassicalSpecWithField, symmetricGridRegionSupport,
        symmetricGridExpansion, gridRegionSupport, or_comm]
    have htot :
        (symmetricGridZeroFieldClassicalSpec w).atomTotalInfluence (0, j) = 6 * |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp0j]
      rw [Finset.sum_insert]
      · rw [Finset.sum_insert]
        · rw [Finset.sum_insert]
          · rw [symmetricGridZeroField_verticalTwoPairInfluence_sum w hj0]
            simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
              symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
              symmetricGridClause]
            ring_nf
          · simp
        · simp
      · simp
    rw [htot]
    nlinarith [abs_nonneg w]
  · subst hj0
    have hsuppi0 :
        (symmetricGridZeroFieldClassicalSpec w).regionSupport ({(i, 0)} : Finset GridNode) =
          ({SymmetricGridClauseId.prior i 0,
            SymmetricGridClauseId.horizontalForward i 0,
            SymmetricGridClauseId.horizontalBackward i 0,
            SymmetricGridClauseId.horizontalForward (Nat.pred i) 0,
            SymmetricGridClauseId.horizontalBackward (Nat.pred i) 0,
            SymmetricGridClauseId.verticalForward i 0,
            SymmetricGridClauseId.verticalBackward i 0} :
              Finset SymmetricGridClauseId) := by
      ext k
      cases k <;> simp [symmetricGridZeroFieldClassicalSpec,
        symmetricGridClassicalSpecWithField, symmetricGridRegionSupport,
        symmetricGridExpansion, gridRegionSupport, or_comm]
    have htot :
        (symmetricGridZeroFieldClassicalSpec w).atomTotalInfluence (i, 0) = 6 * |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsuppi0]
      rw [Finset.sum_insert]
      · rw [Finset.sum_insert]
        · rw [Finset.sum_insert]
          · rw [Finset.sum_insert]
            · rw [Finset.sum_insert]
              · rw [symmetricGridZeroField_verticalPairInfluence_sum]
                simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
                  symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
                  symmetricGridClause]
                ring_nf
              · simp
            · simp
          · simp
            omega
        · simp
          omega
      · simp
    rw [htot]
    nlinarith [abs_nonneg w]
  · have hsuppij :
        (symmetricGridZeroFieldClassicalSpec w).regionSupport ({(i, j)} : Finset GridNode) =
          ({SymmetricGridClauseId.prior i j,
            SymmetricGridClauseId.horizontalForward i j,
            SymmetricGridClauseId.horizontalBackward i j,
            SymmetricGridClauseId.horizontalForward (Nat.pred i) j,
            SymmetricGridClauseId.horizontalBackward (Nat.pred i) j,
            SymmetricGridClauseId.verticalForward i j,
            SymmetricGridClauseId.verticalBackward i j,
            SymmetricGridClauseId.verticalForward i (Nat.pred j),
            SymmetricGridClauseId.verticalBackward i (Nat.pred j)} :
              Finset SymmetricGridClauseId) := by
      ext k
      cases k <;> simp [symmetricGridZeroFieldClassicalSpec,
        symmetricGridClassicalSpecWithField, symmetricGridRegionSupport,
        symmetricGridExpansion, gridRegionSupport, or_comm]
    have htot :
        (symmetricGridZeroFieldClassicalSpec w).atomTotalInfluence (i, j) = 8 * |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsuppij]
      rw [Finset.sum_insert]
      · rw [Finset.sum_insert]
        · rw [Finset.sum_insert]
          · rw [Finset.sum_insert]
            · rw [Finset.sum_insert]
              · rw [symmetricGridZeroField_verticalTwoPairInfluence_sum w hj0]
                simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
                  symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
                  symmetricGridClause]
                ring_nf
              · simp
            · simp
          · simp
            omega
        · simp
          omega
      · simp
    rw [htot]
    nlinarith [abs_nonneg w]

@[simp] theorem symmetricGridZeroField_regionSupport_origin
    (w : ℝ) :
    (symmetricGridZeroFieldClassicalSpec w).regionSupport ({gridOrigin} : Region GridNode) =
      ({SymmetricGridClauseId.prior 0 0,
        SymmetricGridClauseId.horizontalForward 0 0,
        SymmetricGridClauseId.horizontalBackward 0 0,
        SymmetricGridClauseId.verticalForward 0 0,
        SymmetricGridClauseId.verticalBackward 0 0} : Finset SymmetricGridClauseId) := by
  ext k
  cases k <;> simp [symmetricGridZeroFieldClassicalSpec,
    symmetricGridClassicalSpecWithField, symmetricGridRegionSupport,
    symmetricGridExpansion, gridRegionSupport, gridOrigin]

@[simp] theorem symmetricGridZeroField_boundaryClauseSupportRegion_origin
    (w : ℝ) :
    Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR.boundaryClauseSupportRegion
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        ({gridOrigin} : Region GridNode) =
      gridOriginNeighborPairRegion := by
  have hsupport :
      (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.regionSupport
          ({gridOrigin} : Region GridNode) =
        ({SymmetricGridClauseId.prior 0 0,
          SymmetricGridClauseId.horizontalForward 0 0,
          SymmetricGridClauseId.horizontalBackward 0 0,
          SymmetricGridClauseId.verticalForward 0 0,
          SymmetricGridClauseId.verticalBackward 0 0} : Finset SymmetricGridClauseId) := by
    change (symmetricGridZeroFieldClassicalSpec w).regionSupport ({gridOrigin} : Region GridNode) =
      ({SymmetricGridClauseId.prior 0 0,
        SymmetricGridClauseId.horizontalForward 0 0,
        SymmetricGridClauseId.horizontalBackward 0 0,
        SymmetricGridClauseId.verticalForward 0 0,
        SymmetricGridClauseId.verticalBackward 0 0} : Finset SymmetricGridClauseId)
    exact symmetricGridZeroField_regionSupport_origin w
  ext a
  constructor
  · intro ha
    rw [Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR.boundaryClauseSupportRegion,
      hsupport] at ha
    rcases Finset.mem_biUnion.mp ha with ⟨j, hj, ha⟩
    rcases Finset.mem_sdiff.mp ha with ⟨haAtom, hnotOrigin⟩
    have hcases :
        j = SymmetricGridClauseId.prior 0 0 ∨
          j = SymmetricGridClauseId.horizontalForward 0 0 ∨
          j = SymmetricGridClauseId.horizontalBackward 0 0 ∨
          j = SymmetricGridClauseId.verticalForward 0 0 ∨
          j = SymmetricGridClauseId.verticalBackward 0 0 := by
      simp at hj
      exact hj
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · have haOrigin : a = gridOrigin := by
        simpa [ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec,
          classicalWeightedClause, symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
          symmetricGridClause, gridPriorClause_atoms, gridOrigin] using haAtom
      exact False.elim (hnotOrigin (by simp [haOrigin]))
    · have haCases : a = gridOrigin ∨ a = gridOriginEast := by
        simpa [ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec,
          classicalWeightedClause, symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
          symmetricGridClause, gridHorizontalClause_atoms, gridOrigin, gridOriginEast] using haAtom
      have haEast : a = gridOriginEast := by
        rcases haCases with haOrigin | haEast
        · exfalso
          exact hnotOrigin (by simp [haOrigin])
        · exact haEast
      simp [gridOriginNeighborPairRegion, gridOriginEast, gridOriginNorth, haEast]
    · have haCases : a = gridOrigin ∨ a = gridOriginEast := by
        simpa [ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec,
          classicalWeightedClause, symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
          symmetricGridClause, gridHorizontalReverseClause_atoms, gridOrigin, gridOriginEast] using haAtom
      have haEast : a = gridOriginEast := by
        rcases haCases with haOrigin | haEast
        · exfalso
          exact hnotOrigin (by simp [haOrigin])
        · exact haEast
      simp [gridOriginNeighborPairRegion, gridOriginEast, gridOriginNorth, haEast]
    · have haCases : a = gridOrigin ∨ a = gridOriginNorth := by
        simpa [ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec,
          classicalWeightedClause, symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
          symmetricGridClause, gridVerticalClause_atoms, gridOrigin, gridOriginNorth] using haAtom
      have haNorth : a = gridOriginNorth := by
        rcases haCases with haOrigin | haNorth
        · exfalso
          exact hnotOrigin (by simp [haOrigin])
        · exact haNorth
      simp [gridOriginNeighborPairRegion, gridOriginEast, gridOriginNorth, haNorth]
    · have haCases : a = gridOrigin ∨ a = gridOriginNorth := by
        simpa [ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec,
          classicalWeightedClause, symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
          symmetricGridClause, gridVerticalReverseClause_atoms, gridOrigin, gridOriginNorth] using haAtom
      have haNorth : a = gridOriginNorth := by
        rcases haCases with haOrigin | haNorth
        · exfalso
          exact hnotOrigin (by simp [haOrigin])
        · exact haNorth
      simp [gridOriginNeighborPairRegion, gridOriginEast, gridOriginNorth, haNorth]
  · intro ha
    rw [Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR.boundaryClauseSupportRegion,
      hsupport]
    simp [gridOriginNeighborPairRegion, gridOriginEast, gridOriginNorth] at ha
    rcases ha with rfl | rfl
    · refine Finset.mem_biUnion.mpr ?_
      refine ⟨SymmetricGridClauseId.horizontalForward 0 0, ?_, ?_⟩
      · simp
      · simp [ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec,
          classicalWeightedClause, symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
          symmetricGridClause, gridHorizontalClause_atoms, gridOrigin]
    · refine Finset.mem_biUnion.mpr ?_
      refine ⟨SymmetricGridClauseId.verticalForward 0 0, ?_, ?_⟩
      · simp
      · simp [ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec,
          classicalWeightedClause, symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
          symmetricGridClause, gridVerticalClause_atoms, gridOrigin]

@[simp] theorem symmetricGridZeroField_cylinderBoundarySupportRegion_origin
    (w : ℝ) :
    Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR.cylinderBoundarySupportRegion
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        ({gridOrigin} : Region GridNode)
        ({gridOrigin} : Region GridNode) =
      gridOriginNeighborPairRegion := by
  rw [Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR.cylinderBoundarySupportRegion,
    Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR.outsideRegion,
    symmetricGridZeroField_boundaryClauseSupportRegion_origin]
  ext a
  simp [gridOrigin, gridOriginNeighborPairRegion]

theorem symmetricGridZeroField_origin_singletonLogOdds_plusBoundary
    (w : ℝ) :
    (symmetricGridZeroFieldClassicalSpec w).singletonLogOdds gridOrigin gridPlusBoundary =
      2 * w := by
  rw [(symmetricGridZeroFieldClassicalSpec w).singletonLogOdds_eq_sum_clauseContribution
    gridOrigin gridPlusBoundary]
  rw [symmetricGridZeroField_regionSupport_origin]
  simp [ClassicalInfiniteGroundMLNSpec.singletonLogOddsClauseContribution,
    GroundClause.holds, Literal.holds,
    symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
    symmetricGridClause, gridOrigin, gridPlusBoundary, gridPriorClause,
    gridHorizontalClause, gridHorizontalReverseClause, gridVerticalClause,
    gridVerticalReverseClause, patch, singletonAssignment]
  ring_nf

theorem symmetricGridZeroField_origin_singletonLogOdds_minusBoundary
    (w : ℝ) :
    (symmetricGridZeroFieldClassicalSpec w).singletonLogOdds gridOrigin gridMinusBoundary =
      -2 * w := by
  rw [(symmetricGridZeroFieldClassicalSpec w).singletonLogOdds_eq_sum_clauseContribution
    gridOrigin gridMinusBoundary]
  rw [symmetricGridZeroField_regionSupport_origin]
  simp [ClassicalInfiniteGroundMLNSpec.singletonLogOddsClauseContribution,
    GroundClause.holds, Literal.holds,
    symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
    symmetricGridClause, gridOrigin, gridMinusBoundary, gridPriorClause,
    gridHorizontalClause, gridHorizontalReverseClause, gridVerticalClause,
    gridVerticalReverseClause, patch, singletonAssignment]
  ring_nf

theorem symmetricGridZeroField_origin_singletonLogOdds_eq_neighborBoundarySum
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    (symmetricGridZeroFieldClassicalSpec w).singletonLogOdds gridOrigin ξ =
      (if ξ gridOriginEast then w else -w) +
        (if ξ gridOriginNorth then w else -w) := by
  rw [(symmetricGridZeroFieldClassicalSpec w).singletonLogOdds_eq_sum_clauseContribution
    gridOrigin ξ]
  rw [symmetricGridZeroField_regionSupport_origin]
  cases hEast : ξ gridOriginEast <;> cases hNorth : ξ gridOriginNorth <;>
    simp [gridOriginEast, gridOriginNorth] at hEast hNorth <;>
    simp [ClassicalInfiniteGroundMLNSpec.singletonLogOddsClauseContribution,
      GroundClause.holds, Literal.holds,
      symmetricGridZeroFieldClassicalSpec, symmetricGridClassicalSpecWithField,
      symmetricGridClause, gridOrigin,
      gridPriorClause, gridHorizontalClause, gridHorizontalReverseClause,
      gridVerticalClause, gridVerticalReverseClause, patch, singletonAssignment,
      hEast, hNorth]

theorem symmetricGridZeroField_origin_singletonKernelTrueProb_eq_sigmoid_neighborBoundarySum
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    (symmetricGridZeroFieldClassicalSpec w).singletonKernelTrueProb gridOrigin ξ =
      Real.sigmoid
        ((if ξ gridOriginEast then w else -w) +
          (if ξ gridOriginNorth then w else -w)) := by
  rw [(symmetricGridZeroFieldClassicalSpec w).singletonKernelTrueProb_eq_sigmoid_singletonLogOdds]
  rw [symmetricGridZeroField_origin_singletonLogOdds_eq_neighborBoundarySum]

theorem symmetricGridZeroField_origin_cylinderBoundaryKernelValue_toReal_eq_neighborSigmoid
    (w : ℝ)
    (x : LocalAssignment GridNode gridOriginNeighborPairRegion) :
    ENNReal.toReal
      (StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        ({gridOrigin} : Region GridNode)
        ({gridOrigin} : Region GridNode)
        (singletonTrueAssignmentSet gridOrigin)
        x) =
      Real.sigmoid
        ((if x ⟨gridOriginEast, by simp [gridOriginNeighborPairRegion, gridOriginEast, gridOriginNorth]⟩
            then w else -w) +
          (if x ⟨gridOriginNorth, by simp [gridOriginNeighborPairRegion, gridOriginEast, gridOriginNorth]⟩
            then w else -w)) := by
  simpa [StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue,
    symmetricGridZeroField_cylinderBoundarySupportRegion_origin,
    gridOriginNeighborPairRegion, gridOriginEast, gridOriginNorth] using
    (symmetricGridZeroField_origin_singletonKernelTrueProb_eq_sigmoid_neighborBoundarySum
      w
      (patch gridOriginNeighborPairRegion x (fun _ => false)))

theorem symmetricGridZeroField_originSpinUp_finiteVolumeKernel_eq_neighborPairBoundaryIntegral
    (w : ℝ) (n : ℕ) (ξ : BoundaryCondition GridNode) :
    gridExhaustion.finiteVolumeKernelSequence
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        ξ n
        (localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery) =
      ∫⁻ x,
        StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ({gridOrigin} : Region GridNode)
          ({gridOrigin} : Region GridNode)
          (singletonTrueAssignmentSet gridOrigin)
          x
        ∂ Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
          gridExhaustion
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ n
          gridOriginNeighborPairRegion := by
  have hsub : ({gridOrigin} : Region GridNode) ⊆ gridExhaustion.region n := by
    intro a ha
    rcases Finset.mem_singleton.mp ha with rfl
    exact gridOrigin_mem_gridExhaustion_region n
  have hdlr :
      ∫⁻ ω,
        Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ({gridOrigin} : Region GridNode) ω
          (MeasureTheory.cylinder ({gridOrigin} : Region GridNode)
            (singletonTrueAssignmentSet gridOrigin))
        ∂ gridExhaustion.finiteVolumeKernelSequence
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ n =
      gridExhaustion.finiteVolumeKernelSequence
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        ξ n
        (MeasureTheory.cylinder ({gridOrigin} : Region GridNode)
          (singletonTrueAssignmentSet gridOrigin)) := by
    simpa [Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion.finiteVolumeKernelSequence] using
      (Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR.finiteVolumeWorldMeasure_subregion_cylinder_dlr
        (M := (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec)
        (Λ := ({gridOrigin} : Region GridNode))
        (Δ := gridExhaustion.region n)
        hsub
        (ξ := ξ)
        (I := ({gridOrigin} : Region GridNode))
        (S := singletonTrueAssignmentSet gridOrigin)
        (hS := measurableSet_singletonTrueAssignmentSet gridOrigin))
  have hstage :
      ∫⁻ x,
        StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ({gridOrigin} : Region GridNode)
          ({gridOrigin} : Region GridNode)
          (singletonTrueAssignmentSet gridOrigin)
          x
        ∂ Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
          gridExhaustion
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ n
          gridOriginNeighborPairRegion =
      ∫⁻ ω,
        Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ({gridOrigin} : Region GridNode) ω
          (MeasureTheory.cylinder ({gridOrigin} : Region GridNode)
            (singletonTrueAssignmentSet gridOrigin))
        ∂ gridExhaustion.finiteVolumeKernelSequence
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ n := by
    simpa [symmetricGridZeroField_cylinderBoundarySupportRegion_origin] using
      (Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR.RegionExhaustion.stageMarginal_lintegral_cylinderBoundaryKernelValue
        (E := gridExhaustion)
        (M := (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec)
        (ξ := ξ)
        (n := n)
        (Λ := ({gridOrigin} : Region GridNode))
        (I := ({gridOrigin} : Region GridNode))
        (S := singletonTrueAssignmentSet gridOrigin)
        (hS := measurableSet_singletonTrueAssignmentSet gridOrigin))
  calc
    gridExhaustion.finiteVolumeKernelSequence
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        ξ n
        (localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery) =
      ∫⁻ ω,
        Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ({gridOrigin} : Region GridNode) ω
          (MeasureTheory.cylinder ({gridOrigin} : Region GridNode)
            (singletonTrueAssignmentSet gridOrigin))
        ∂ gridExhaustion.finiteVolumeKernelSequence
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ n := by
            simpa [localQueryEvent_eq_cylinder, gridOriginSpinUpLocalConstraintSet_eq] using
              hdlr.symm
    _ =
      ∫⁻ x,
        StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ({gridOrigin} : Region GridNode)
          ({gridOrigin} : Region GridNode)
          (singletonTrueAssignmentSet gridOrigin)
          x
        ∂ Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
          gridExhaustion
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ n
          gridOriginNeighborPairRegion := by
            simpa using hstage.symm

/-- The stage marginal on the two-neighbour boundary support of the origin
query. -/
noncomputable def symmetricGridZeroFieldOriginNeighborPairStagePMF
    (w : ℝ) (ξ : BoundaryCondition GridNode) (n : ℕ) :
    PMF (LocalAssignment GridNode gridOriginNeighborPairRegion) :=
  (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
    gridExhaustion
    (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
    ξ n
    gridOriginNeighborPairRegion).toPMF

theorem symmetricGridZeroField_originSpinUp_finiteVolumeKernel_toReal_eq_neighborPairMixture
    (w : ℝ) (n : ℕ) (ξ : BoundaryCondition GridNode) :
    ENNReal.toReal
      (gridExhaustion.finiteVolumeKernelSequence
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        ξ n
        (localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery)) =
      Real.sigmoid (-2 * w) *
          ENNReal.toReal
            (symmetricGridZeroFieldOriginNeighborPairStagePMF w ξ n
              gridOriginNeighborPairFF) +
        (1 / 2 : ℝ) *
          ENNReal.toReal
            (symmetricGridZeroFieldOriginNeighborPairStagePMF w ξ n
              gridOriginNeighborPairFT) +
        (1 / 2 : ℝ) *
          ENNReal.toReal
            (symmetricGridZeroFieldOriginNeighborPairStagePMF w ξ n
              gridOriginNeighborPairTF) +
        Real.sigmoid (2 * w) *
          ENNReal.toReal
            (symmetricGridZeroFieldOriginNeighborPairStagePMF w ξ n
              gridOriginNeighborPairTT) := by
  classical
  let q := symmetricGridZeroFieldOriginNeighborPairStagePMF w ξ n
  let K : LocalAssignment GridNode gridOriginNeighborPairRegion → ENNReal := fun x =>
    StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue
      (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      ({gridOrigin} : Region GridNode)
      ({gridOrigin} : Region GridNode)
      (singletonTrueAssignmentSet gridOrigin)
      x
  have hEq :
      gridExhaustion.finiteVolumeKernelSequence
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ n
          (localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery) =
        ∑ x : LocalAssignment GridNode gridOriginNeighborPairRegion,
          K x * q x := by
    calc
      gridExhaustion.finiteVolumeKernelSequence
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ n
          (localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery) =
        ∫⁻ x, K x
          ∂ Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
            gridExhaustion
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            ξ n
            gridOriginNeighborPairRegion := by
              simpa [K] using
                symmetricGridZeroField_originSpinUp_finiteVolumeKernel_eq_neighborPairBoundaryIntegral
                  w n ξ
      _ = ∑ x : LocalAssignment GridNode gridOriginNeighborPairRegion, K x * q x := by
            rw [MeasureTheory.lintegral_fintype]
            simp [K, q, symmetricGridZeroFieldOriginNeighborPairStagePMF, Measure.toPMF_apply]
  have hne_top :
      ∀ x : LocalAssignment GridNode gridOriginNeighborPairRegion,
        K x * q x ≠ (⊤ : ENNReal) := by
    intro x
    exact ENNReal.mul_ne_top
      (StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue_ne_top
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        ({gridOrigin} : Region GridNode)
        ({gridOrigin} : Region GridNode)
        (singletonTrueAssignmentSet gridOrigin)
        x)
      (q.apply_ne_top x)
  calc
    ENNReal.toReal
        (gridExhaustion.finiteVolumeKernelSequence
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ n
          (localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery)) =
      ∑ x : LocalAssignment GridNode gridOriginNeighborPairRegion,
        ENNReal.toReal (K x * q x) := by
          rw [hEq, ENNReal.toReal_sum]
          intro x hx
          exact hne_top x
    _ =
      ∑ x : LocalAssignment GridNode gridOriginNeighborPairRegion,
        ENNReal.toReal (K x) * ENNReal.toReal (q x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [ENNReal.toReal_mul]
    _ =
      Finset.sum
          ({gridOriginNeighborPairFF, gridOriginNeighborPairFT,
            gridOriginNeighborPairTF, gridOriginNeighborPairTT} :
              Finset (LocalAssignment GridNode gridOriginNeighborPairRegion))
          (fun x => ENNReal.toReal (K x) * ENNReal.toReal (q x)) := by
          rw [gridOriginNeighborPairAssignment_univ]
    _ =
      Real.sigmoid (-2 * w) * ENNReal.toReal (q gridOriginNeighborPairFF) +
        (1 / 2 : ℝ) * ENNReal.toReal (q gridOriginNeighborPairFT) +
        (1 / 2 : ℝ) * ENNReal.toReal (q gridOriginNeighborPairTF) +
        Real.sigmoid (2 * w) * ENNReal.toReal (q gridOriginNeighborPairTT) := by
          have hFF :
              gridOriginNeighborPairFF ∉
                ({gridOriginNeighborPairFT, gridOriginNeighborPairTF,
                  gridOriginNeighborPairTT} :
                    Finset (LocalAssignment GridNode gridOriginNeighborPairRegion)) := by
            decide
          have hFT :
              gridOriginNeighborPairFT ∉
                ({gridOriginNeighborPairTF, gridOriginNeighborPairTT} :
                    Finset (LocalAssignment GridNode gridOriginNeighborPairRegion)) := by
            decide
          have hTF :
              gridOriginNeighborPairTF ∉
                ({gridOriginNeighborPairTT} :
                    Finset (LocalAssignment GridNode gridOriginNeighborPairRegion)) := by
            decide
          rw [Finset.sum_insert hFF, Finset.sum_insert hFT, Finset.sum_insert hTF,
            Finset.sum_singleton]
          simp [K, q, gridOriginNeighborPairFF, gridOriginNeighborPairFT,
            gridOriginNeighborPairTF, gridOriginNeighborPairTT,
            symmetricGridZeroField_origin_cylinderBoundaryKernelValue_toReal_eq_neighborSigmoid]
          ring_nf

theorem symmetricGridZeroField_originSpinUp_finiteVolumeKernel_toReal_eq_half_add_neighborPairGap
    (w : ℝ) (n : ℕ) (ξ : BoundaryCondition GridNode) :
    ENNReal.toReal
      (gridExhaustion.finiteVolumeKernelSequence
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        ξ n
        (localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery)) =
      (1 / 2 : ℝ) +
        (Real.sigmoid (2 * w) - (1 / 2 : ℝ)) *
          (ENNReal.toReal
              (symmetricGridZeroFieldOriginNeighborPairStagePMF w ξ n
                gridOriginNeighborPairTT) -
            ENNReal.toReal
              (symmetricGridZeroFieldOriginNeighborPairStagePMF w ξ n
                gridOriginNeighborPairFF)) := by
  classical
  let q := symmetricGridZeroFieldOriginNeighborPairStagePMF w ξ n
  have hmix :=
    symmetricGridZeroField_originSpinUp_finiteVolumeKernel_toReal_eq_neighborPairMixture
      w n ξ
  have hsumq' : ∑ x : LocalAssignment GridNode gridOriginNeighborPairRegion,
      ENNReal.toReal (q x) = 1 :=
    sum_toReal_eq_one_of_pmf q
  rw [gridOriginNeighborPairAssignment_univ] at hsumq'
  have hsumq :
      ENNReal.toReal (q gridOriginNeighborPairFF) +
          ENNReal.toReal (q gridOriginNeighborPairFT) +
          ENNReal.toReal (q gridOriginNeighborPairTF) +
          ENNReal.toReal (q gridOriginNeighborPairTT) = 1 := by
    have hFF :
        gridOriginNeighborPairFF ∉
          ({gridOriginNeighborPairFT, gridOriginNeighborPairTF,
            gridOriginNeighborPairTT} :
              Finset (LocalAssignment GridNode gridOriginNeighborPairRegion)) := by
      decide
    have hFT :
        gridOriginNeighborPairFT ∉
          ({gridOriginNeighborPairTF, gridOriginNeighborPairTT} :
              Finset (LocalAssignment GridNode gridOriginNeighborPairRegion)) := by
      decide
    have hTF :
        gridOriginNeighborPairTF ∉
          ({gridOriginNeighborPairTT} :
              Finset (LocalAssignment GridNode gridOriginNeighborPairRegion)) := by
      decide
    rw [Finset.sum_insert hFF, Finset.sum_insert hFT, Finset.sum_insert hTF,
      Finset.sum_singleton] at hsumq'
    simpa [q, gridOriginNeighborPairFF, gridOriginNeighborPairFT,
      gridOriginNeighborPairTF, gridOriginNeighborPairTT, add_assoc] using hsumq'
  have hsigNeg : Real.sigmoid (-2 * w) = 1 - Real.sigmoid (2 * w) := by
    simpa [neg_mul] using Real.sigmoid_neg (2 * w)
  calc
    ENNReal.toReal
        (gridExhaustion.finiteVolumeKernelSequence
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ n
          (localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery)) =
      Real.sigmoid (-2 * w) * ENNReal.toReal (q gridOriginNeighborPairFF) +
        (1 / 2 : ℝ) * ENNReal.toReal (q gridOriginNeighborPairFT) +
        (1 / 2 : ℝ) * ENNReal.toReal (q gridOriginNeighborPairTF) +
        Real.sigmoid (2 * w) * ENNReal.toReal (q gridOriginNeighborPairTT) := by
          simpa [q] using hmix
    _ =
      Real.sigmoid (-2 * w) * ENNReal.toReal (q gridOriginNeighborPairFF) +
        (1 / 2 : ℝ) *
            (ENNReal.toReal (q gridOriginNeighborPairFT) +
              ENNReal.toReal (q gridOriginNeighborPairTF)) +
        Real.sigmoid (2 * w) * ENNReal.toReal (q gridOriginNeighborPairTT) := by
          ring
    _ =
      Real.sigmoid (-2 * w) * ENNReal.toReal (q gridOriginNeighborPairFF) +
        (1 / 2 : ℝ) *
            (1 - ENNReal.toReal (q gridOriginNeighborPairFF) -
              ENNReal.toReal (q gridOriginNeighborPairTT)) +
        Real.sigmoid (2 * w) * ENNReal.toReal (q gridOriginNeighborPairTT) := by
          linarith
    _ =
      (1 / 2 : ℝ) +
        (Real.sigmoid (2 * w) - (1 / 2 : ℝ)) *
          (ENNReal.toReal (q gridOriginNeighborPairTT) -
            ENNReal.toReal (q gridOriginNeighborPairFF)) := by
          rw [hsigNeg]
          ring

/-- Any stagewise bound on the failure of the corner-neighbour `TT` event
forces a quantitative lower bound on the `TT - FF` pair gap. -/
theorem symmetricGridZeroFieldOriginNeighborPairStage_gap_ge_of_notTTBound
    {w η : ℝ} (n : ℕ) (ξ : BoundaryCondition GridNode)
    (hbad :
      1 -
          ENNReal.toReal
            (symmetricGridZeroFieldOriginNeighborPairStagePMF w ξ n
              gridOriginNeighborPairTT) ≤
        η) :
    1 - 2 * η ≤
      ENNReal.toReal
          (symmetricGridZeroFieldOriginNeighborPairStagePMF w ξ n
            gridOriginNeighborPairTT) -
        ENNReal.toReal
          (symmetricGridZeroFieldOriginNeighborPairStagePMF w ξ n
            gridOriginNeighborPairFF) := by
  let q := symmetricGridZeroFieldOriginNeighborPairStagePMF w ξ n
  have hsum' : ∑ x : LocalAssignment GridNode gridOriginNeighborPairRegion,
      ENNReal.toReal (q x) = 1 :=
    sum_toReal_eq_one_of_pmf q
  rw [gridOriginNeighborPairAssignment_univ] at hsum'
  have hsum :
      ENNReal.toReal (q gridOriginNeighborPairFF) +
          ENNReal.toReal (q gridOriginNeighborPairFT) +
          ENNReal.toReal (q gridOriginNeighborPairTF) +
          ENNReal.toReal (q gridOriginNeighborPairTT) = 1 := by
    have hFF :
        gridOriginNeighborPairFF ∉
          ({gridOriginNeighborPairFT, gridOriginNeighborPairTF,
            gridOriginNeighborPairTT} :
              Finset (LocalAssignment GridNode gridOriginNeighborPairRegion)) := by
      decide
    have hFT :
        gridOriginNeighborPairFT ∉
          ({gridOriginNeighborPairTF, gridOriginNeighborPairTT} :
              Finset (LocalAssignment GridNode gridOriginNeighborPairRegion)) := by
      decide
    have hTF :
        gridOriginNeighborPairTF ∉
          ({gridOriginNeighborPairTT} :
              Finset (LocalAssignment GridNode gridOriginNeighborPairRegion)) := by
      decide
    rw [Finset.sum_insert hFF, Finset.sum_insert hFT, Finset.sum_insert hTF,
      Finset.sum_singleton] at hsum'
    simpa [q, gridOriginNeighborPairFF, gridOriginNeighborPairFT,
      gridOriginNeighborPairTF, gridOriginNeighborPairTT, add_assoc] using hsum'
  have hft_nonneg : 0 ≤ ENNReal.toReal (q gridOriginNeighborPairFT) :=
    ENNReal.toReal_nonneg
  have htf_nonneg : 0 ≤ ENNReal.toReal (q gridOriginNeighborPairTF) :=
    ENNReal.toReal_nonneg
  have hff_le :
      ENNReal.toReal (q gridOriginNeighborPairFF) ≤
        1 - ENNReal.toReal (q gridOriginNeighborPairTT) := by
    linarith
  have htt_ge :
      1 - η ≤ ENNReal.toReal (q gridOriginNeighborPairTT) := by
    linarith
  linarith

theorem symmetricGridZeroField_origin_singletonKernelTrueProb_plusBoundary_eq_sigmoid
    (w : ℝ) :
    (symmetricGridZeroFieldClassicalSpec w).singletonKernelTrueProb
        gridOrigin gridPlusBoundary =
      Real.sigmoid (2 * w) := by
  rw [(symmetricGridZeroFieldClassicalSpec w).singletonKernelTrueProb_eq_sigmoid_singletonLogOdds]
  rw [symmetricGridZeroField_origin_singletonLogOdds_plusBoundary]

theorem symmetricGridZeroField_origin_singletonKernelTrueProb_minusBoundary_eq_sigmoid
    (w : ℝ) :
    (symmetricGridZeroFieldClassicalSpec w).singletonKernelTrueProb
        gridOrigin gridMinusBoundary =
      Real.sigmoid (-2 * w) := by
  rw [(symmetricGridZeroFieldClassicalSpec w).singletonKernelTrueProb_eq_sigmoid_singletonLogOdds]
  rw [symmetricGridZeroField_origin_singletonLogOdds_minusBoundary]

theorem symmetricGridZeroField_origin_singletonKernelTrueProb_plus_gt_minus
    {w : ℝ} (hw : 0 < w) :
    (symmetricGridZeroFieldClassicalSpec w).singletonKernelTrueProb
        gridOrigin gridMinusBoundary <
      (symmetricGridZeroFieldClassicalSpec w).singletonKernelTrueProb
        gridOrigin gridPlusBoundary := by
  rw [symmetricGridZeroField_origin_singletonKernelTrueProb_minusBoundary_eq_sigmoid,
    symmetricGridZeroField_origin_singletonKernelTrueProb_plusBoundary_eq_sigmoid]
  exact Real.sigmoid_lt (by nlinarith)

theorem symmetricGridZeroField_originSpinUp_stage0_plusBoundary_eq_sigmoid
    (w : ℝ) :
    ENNReal.toReal
      (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
        gridExhaustion
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        gridPlusBoundary 0 ({gridOrigin} : Region GridNode)
        (localConstraintSet ({gridOrigin} : Region GridNode)
          gridOriginSpinUpLocalQuery)) = Real.sigmoid (2 * w) := by
  rw [Mettapedia.Logic.MarkovLogicInfiniteGlobalDLR.RegionExhaustion.stageMarginal_apply_localConstraintSet]
  have hregion : gridExhaustion.region 0 = ({gridOrigin} : Region GridNode) := by
    ext a
    rcases a with ⟨i, j⟩
    simp [gridExhaustion, gridOrigin]
  rw [Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion.finiteVolumeKernelSequence]
  rw [hregion]
  rw [localQueryEvent_eq_cylinder]
  rw [gridOriginSpinUpLocalConstraintSet_eq]
  exact symmetricGridZeroField_origin_singletonKernelTrueProb_plusBoundary_eq_sigmoid w

theorem symmetricGridZeroField_originSpinUp_stage0_minusBoundary_eq_sigmoid
    (w : ℝ) :
    ENNReal.toReal
      (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
        gridExhaustion
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        gridMinusBoundary 0 ({gridOrigin} : Region GridNode)
        (localConstraintSet ({gridOrigin} : Region GridNode)
          gridOriginSpinUpLocalQuery)) = Real.sigmoid (-2 * w) := by
  rw [Mettapedia.Logic.MarkovLogicInfiniteGlobalDLR.RegionExhaustion.stageMarginal_apply_localConstraintSet]
  have hregion : gridExhaustion.region 0 = ({gridOrigin} : Region GridNode) := by
    ext a
    rcases a with ⟨i, j⟩
    simp [gridExhaustion, gridOrigin]
  rw [Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion.finiteVolumeKernelSequence]
  rw [hregion]
  rw [localQueryEvent_eq_cylinder]
  rw [gridOriginSpinUpLocalConstraintSet_eq]
  exact symmetricGridZeroField_origin_singletonKernelTrueProb_minusBoundary_eq_sigmoid w

theorem symmetricGridZeroField_originSpinUp_stage0_plus_gt_minus
    {w : ℝ} (hw : 0 < w) :
    ENNReal.toReal
      (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
        gridExhaustion
        (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
        gridMinusBoundary 0 ({gridOrigin} : Region GridNode)
        (localConstraintSet ({gridOrigin} : Region GridNode)
          gridOriginSpinUpLocalQuery)) <
      ENNReal.toReal
        (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
          gridExhaustion
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          gridPlusBoundary 0 ({gridOrigin} : Region GridNode)
          (localConstraintSet ({gridOrigin} : Region GridNode)
            gridOriginSpinUpLocalQuery)) := by
  rw [symmetricGridZeroField_originSpinUp_stage0_minusBoundary_eq_sigmoid,
    symmetricGridZeroField_originSpinUp_stage0_plusBoundary_eq_sigmoid]
  exact Real.sigmoid_lt (by nlinarith)

/-- A fixed enumeration of the countable grid nodes. -/
noncomputable def gridNodeNatEquiv : ℕ ≃ GridNode :=
  (Equiv.prodEquivOfEquivNat (Equiv.refl Nat)).symm

private theorem symmetricGridZeroFieldBoundary_exists_stageProbabilityFamily_tendsto_subseq
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    ∃ P :
        Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.StageProbabilityFamily
          GridNode,
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.stageProbabilityFamily
                gridExhaustion
                (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
                ξ (φ n))
            atTop
            (nhds P) := by
  exact
    Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.exists_stageProbabilityFamily_tendsto_subseq_of_equiv
      (E := gridExhaustion)
      (M := (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec)
      (ξ := ξ)
      gridNodeNatEquiv

/-- The compactness-extracted subsequential stage marginal family for the
zero-field symmetric grid under boundary condition `ξ`. -/
noncomputable def symmetricGridZeroFieldBoundaryStageProbabilityFamily
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.StageProbabilityFamily
      GridNode :=
  Classical.choose
    (symmetricGridZeroFieldBoundary_exists_stageProbabilityFamily_tendsto_subseq
      w ξ)

/-- The extracted subsequence along which the stage marginal family converges
for boundary condition `ξ`. -/
noncomputable def symmetricGridZeroFieldBoundaryStageSubseq
    (w : ℝ) (ξ : BoundaryCondition GridNode) : ℕ → ℕ :=
  Classical.choose
    (Classical.choose_spec
      (symmetricGridZeroFieldBoundary_exists_stageProbabilityFamily_tendsto_subseq
        w ξ))

theorem symmetricGridZeroFieldBoundaryStageSubseq_strictMono
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    StrictMono (symmetricGridZeroFieldBoundaryStageSubseq w ξ) := by
  unfold symmetricGridZeroFieldBoundaryStageSubseq
  simpa using
    (Classical.choose_spec
      (Classical.choose_spec
        (symmetricGridZeroFieldBoundary_exists_stageProbabilityFamily_tendsto_subseq
          w ξ))).1

theorem symmetricGridZeroFieldBoundaryStageProbabilityFamily_tendsto
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    Tendsto
      (fun n =>
        Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.stageProbabilityFamily
          gridExhaustion
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ
          (symmetricGridZeroFieldBoundaryStageSubseq w ξ n))
      atTop
      (nhds (symmetricGridZeroFieldBoundaryStageProbabilityFamily w ξ)) := by
  unfold symmetricGridZeroFieldBoundaryStageSubseq
    symmetricGridZeroFieldBoundaryStageProbabilityFamily
  simpa using
    (Classical.choose_spec
      (Classical.choose_spec
        (symmetricGridZeroFieldBoundary_exists_stageProbabilityFamily_tendsto_subseq
          w ξ))).2

/-- The compactness-extracted limiting marginal family, viewed as raw measures
rather than `ProbabilityMeasure`s. -/
noncomputable def symmetricGridZeroFieldBoundaryMarginalFamily
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    ∀ I : Finset GridNode, Measure (LocalAssignment GridNode I) :=
  fun I =>
    ((symmetricGridZeroFieldBoundaryStageProbabilityFamily w ξ I :
      ProbabilityMeasure (LocalAssignment GridNode I)) :
        Measure (LocalAssignment GridNode I))

theorem symmetricGridZeroFieldBoundaryMarginalFamily_projective
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    MeasureTheory.IsProjectiveMeasureFamily
      (ι := GridNode)
      (α := Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord GridNode)
      (symmetricGridZeroFieldBoundaryMarginalFamily w ξ) := by
  simpa [symmetricGridZeroFieldBoundaryMarginalFamily] using
    (Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.isProjectiveMeasureFamily_of_tendsto_stageProbabilityFamily
      (E := gridExhaustion)
      (M := (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec)
      (ξ := ξ)
      (P := symmetricGridZeroFieldBoundaryStageProbabilityFamily w ξ)
      (φ := symmetricGridZeroFieldBoundaryStageSubseq w ξ)
      (symmetricGridZeroFieldBoundaryStageProbabilityFamily_tendsto w ξ))

/-- The reindexed exhaustion following the extracted convergent subsequence for
boundary condition `ξ`. -/
noncomputable def symmetricGridZeroFieldBoundaryExhaustion
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion GridNode :=
  gridExhaustion.reindex
    (symmetricGridZeroFieldBoundaryStageSubseq w ξ)
    (symmetricGridZeroFieldBoundaryStageSubseq_strictMono w ξ)

theorem symmetricGridZeroFieldBoundaryStageMarginal_tendsto
    (w : ℝ) (ξ : BoundaryCondition GridNode)
    (I : Finset GridNode) (S : Set (LocalAssignment GridNode I))
    (_hS : MeasurableSet S) :
    Tendsto
      (fun n =>
        Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
          (symmetricGridZeroFieldBoundaryExhaustion w ξ)
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          ξ n I S)
      atTop
      (nhds ((symmetricGridZeroFieldBoundaryMarginalFamily w ξ) I S)) := by
  simpa [symmetricGridZeroFieldBoundaryExhaustion,
    symmetricGridZeroFieldBoundaryMarginalFamily,
    Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal_reindex] using
    (Mettapedia.Logic.MarkovLogicInfiniteExistence.RegionExhaustion.tendsto_stageMarginal_apply_of_tendsto_stageProbabilityFamily
      (E := gridExhaustion)
      (M := (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec)
      (ξ := ξ)
      (P := symmetricGridZeroFieldBoundaryStageProbabilityFamily w ξ)
      (φ := symmetricGridZeroFieldBoundaryStageSubseq w ξ)
      (symmetricGridZeroFieldBoundaryStageProbabilityFamily_tendsto w ξ)
      I S)

theorem symmetricGridZeroField_originSpinUp_strictWidth_of_stageMarginalLimitSeparation
    {w : ℝ}
    (Pminus Pplus :
      ∀ I : Finset GridNode, Measure (LocalAssignment GridNode I))
    [∀ I, IsProbabilityMeasure (Pminus I)]
    [∀ I, IsProbabilityMeasure (Pplus I)]
    (hPminus :
      MeasureTheory.IsProjectiveMeasureFamily
        (ι := GridNode)
        (α := Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord GridNode)
        Pminus)
    (hPplus :
      MeasureTheory.IsProjectiveMeasureFamily
        (ι := GridNode)
        (α := Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord GridNode)
        Pplus)
    (hconvMinus :
      ∀ (I : Finset GridNode) (S : Set (LocalAssignment GridNode I)),
        MeasurableSet S →
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                gridExhaustion
                (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
                gridMinusBoundary n I S)
            atTop (nhds (Pminus I S)))
    (hconvPlus :
      ∀ (I : Finset GridNode) (S : Set (LocalAssignment GridNode I)),
        MeasurableSet S →
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                gridExhaustion
                (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
                gridPlusBoundary n I S)
            atTop (nhds (Pplus I S)))
    (hsep :
      ENNReal.toReal
          (Pminus ({gridOrigin} : Region GridNode)
            (localConstraintSet ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) <
        ENNReal.toReal
          (Pplus ({gridOrigin} : Region GridNode)
            (localConstraintSet ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery))) :
    dlrQueryHasStrictWidth
      (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery := by
  let e : ℕ ≃ GridNode :=
    (Equiv.prodEquivOfEquivNat (Equiv.refl Nat)).symm
  let μminus : DLRCompletion (symmetricGridZeroFieldClassicalSpec w) :=
    projectiveLimitDLRCompletion_of_stageMarginal_tendsto
      (symmetricGridZeroFieldClassicalSpec w) gridExhaustion gridMinusBoundary
      e Pminus hPminus hconvMinus
  let μplus : DLRCompletion (symmetricGridZeroFieldClassicalSpec w) :=
    projectiveLimitDLRCompletion_of_stageMarginal_tendsto
      (symmetricGridZeroFieldClassicalSpec w) gridExhaustion gridPlusBoundary
      e Pplus hPplus hconvPlus
  refine ⟨μminus, μplus, ?_⟩
  have hminusLocal :
      dlrCompletionLocalQueryProb (symmetricGridZeroFieldClassicalSpec w)
          ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery μminus =
        ENNReal.toReal
          (Pminus ({gridOrigin} : Region GridNode)
            (localConstraintSet ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) := by
    simp [dlrCompletionLocalQueryProb, μminus,
      projectiveLimitDLRCompletion_of_stageMarginal_tendsto,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.projectiveLimitMeasure_localQueryEvent]
  have hplusLocal :
      dlrCompletionLocalQueryProb (symmetricGridZeroFieldClassicalSpec w)
          ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery μplus =
        ENNReal.toReal
          (Pplus ({gridOrigin} : Region GridNode)
            (localConstraintSet ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) := by
    simp [dlrCompletionLocalQueryProb, μplus,
      projectiveLimitDLRCompletion_of_stageMarginal_tendsto,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.projectiveLimitMeasure_localQueryEvent]
  have hminusQuery :
      dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w)
          gridOriginSpinUpQuery μminus =
        ENNReal.toReal
          (Pminus ({gridOrigin} : Region GridNode)
            (localConstraintSet ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) := by
    rw [dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent]
    rw [← gridOriginSpinUpLocalQueryEvent_eq_global]
    simpa [dlrCompletionLocalQueryProb] using hminusLocal
  have hplusQuery :
      dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w)
          gridOriginSpinUpQuery μplus =
        ENNReal.toReal
          (Pplus ({gridOrigin} : Region GridNode)
            (localConstraintSet ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) := by
    rw [dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent]
    rw [← gridOriginSpinUpLocalQueryEvent_eq_global]
    simpa [dlrCompletionLocalQueryProb] using hplusLocal
  rw [hminusQuery, hplusQuery]
  exact hsep

theorem symmetricGridZeroField_originSpinUp_plnStrictInterval_of_stageMarginalLimitSeparation
    {w : ℝ}
    (Pminus Pplus :
      ∀ I : Finset GridNode, Measure (LocalAssignment GridNode I))
    [∀ I, IsProbabilityMeasure (Pminus I)]
    [∀ I, IsProbabilityMeasure (Pplus I)]
    (hPminus :
      MeasureTheory.IsProjectiveMeasureFamily
        (ι := GridNode)
        (α := Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord GridNode)
        Pminus)
    (hPplus :
      MeasureTheory.IsProjectiveMeasureFamily
        (ι := GridNode)
        (α := Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord GridNode)
        Pplus)
    (hconvMinus :
      ∀ (I : Finset GridNode) (S : Set (LocalAssignment GridNode I)),
        MeasurableSet S →
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                gridExhaustion
                (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
                gridMinusBoundary n I S)
            atTop (nhds (Pminus I S)))
    (hconvPlus :
      ∀ (I : Finset GridNode) (S : Set (LocalAssignment GridNode I)),
        MeasurableSet S →
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                gridExhaustion
                (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
                gridPlusBoundary n I S)
            atTop (nhds (Pplus I S)))
    (hsep :
      ENNReal.toReal
          (Pminus ({gridOrigin} : Region GridNode)
            (localConstraintSet ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) <
        ENNReal.toReal
          (Pplus ({gridOrigin} : Region GridNode)
            (localConstraintSet ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery))) :
    0 < infiniteMLNQueryEnvelopeWidth
          (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery ∧
      infiniteMLNQueryEnvelopeWidthComplement
          (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery < 1 ∧
        0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
          (dlrQueryOutcomeCredalSet
            (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  have hWidth :
      dlrQueryHasStrictWidth
        (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery :=
    symmetricGridZeroField_originSpinUp_strictWidth_of_stageMarginalLimitSeparation
      Pminus Pplus hPminus hPplus hconvMinus hconvPlus hsep
  refine ⟨?_, ?_, ?_⟩
  · exact infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth
      (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery hWidth
  · have hpos : 0 < infiniteMLNQueryEnvelopeWidth
        (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery :=
      infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth
        (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery hWidth
    unfold infiniteMLNQueryEnvelopeWidthComplement
    linarith
  · exact dlrQueryOutcomeCredalSet_true_atom_width_pos_of_queryStrictWidth
      (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery hWidth

theorem symmetricGridZeroField_originSpinUp_plnStrictInterval_of_uniformFiniteVolumeBounds
    {w lo hi : ℝ}
    (hlohi : lo < hi)
    (hminus :
      ∀ n,
        ENNReal.toReal
          (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
            gridExhaustion
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            gridMinusBoundary n ({gridOrigin} : Region GridNode)
            (localConstraintSet ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) ≤ lo)
    (hplus :
      ∀ n,
        hi ≤ ENNReal.toReal
          (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
            gridExhaustion
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            gridPlusBoundary n ({gridOrigin} : Region GridNode)
            (localConstraintSet ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery))) :
    0 < infiniteMLNQueryEnvelopeWidth
          (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery ∧
      infiniteMLNQueryEnvelopeWidthComplement
          (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery < 1 ∧
        0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
          (dlrQueryOutcomeCredalSet
            (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  let M := (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
  let e : ℕ ≃ GridNode :=
    (Equiv.prodEquivOfEquivNat (Equiv.refl Nat)).symm
  rcases
      Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.exists_stageProbabilityFamily_tendsto_subseq_of_equiv
        (E := gridExhaustion) (M := M) (ξ := gridMinusBoundary) e with
    ⟨PminusFamily, φminus, hmonoMinus, hφminus⟩
  rcases
      Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.exists_stageProbabilityFamily_tendsto_subseq_of_equiv
        (E := gridExhaustion) (M := M) (ξ := gridPlusBoundary) e with
    ⟨PplusFamily, φplus, hmonoPlus, hφplus⟩
  let Pminus : ∀ I : Finset GridNode, Measure (LocalAssignment GridNode I) :=
    fun I =>
      ((PminusFamily I : ProbabilityMeasure (LocalAssignment GridNode I)) :
        Measure (LocalAssignment GridNode I))
  let Pplus : ∀ I : Finset GridNode, Measure (LocalAssignment GridNode I) :=
    fun I =>
      ((PplusFamily I : ProbabilityMeasure (LocalAssignment GridNode I)) :
        Measure (LocalAssignment GridNode I))
  haveI hPminusProb : ∀ I : Finset GridNode, IsProbabilityMeasure (Pminus I) := by
    intro I
    dsimp [Pminus]
    infer_instance
  haveI hPplusProb : ∀ I : Finset GridNode, IsProbabilityMeasure (Pplus I) := by
    intro I
    dsimp [Pplus]
    infer_instance
  have hPminus :
      MeasureTheory.IsProjectiveMeasureFamily
        (ι := GridNode)
        (α := Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord GridNode)
        Pminus := by
    simpa [Pminus] using
      (Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.isProjectiveMeasureFamily_of_tendsto_stageProbabilityFamily
        (E := gridExhaustion) (M := M) (ξ := gridMinusBoundary)
        (P := PminusFamily) (φ := φminus) hφminus)
  have hPplus :
      MeasureTheory.IsProjectiveMeasureFamily
        (ι := GridNode)
        (α := Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord GridNode)
        Pplus := by
    simpa [Pplus] using
      (Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion.isProjectiveMeasureFamily_of_tendsto_stageProbabilityFamily
        (E := gridExhaustion) (M := M) (ξ := gridPlusBoundary)
        (P := PplusFamily) (φ := φplus) hφplus)
  let Eminus := gridExhaustion.reindex φminus hmonoMinus
  let Eplus := gridExhaustion.reindex φplus hmonoPlus
  have hconvMinus :
      ∀ (I : Finset GridNode) (S : Set (LocalAssignment GridNode I)),
        MeasurableSet S →
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                Eminus M gridMinusBoundary n I S)
            atTop (nhds (Pminus I S)) := by
    intro I S _hS
    simpa [Eminus, Pminus,
      Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal_reindex] using
      (Mettapedia.Logic.MarkovLogicInfiniteExistence.RegionExhaustion.tendsto_stageMarginal_apply_of_tendsto_stageProbabilityFamily
        (E := gridExhaustion) (M := M) (ξ := gridMinusBoundary)
        (P := PminusFamily) (φ := φminus) hφminus I S)
  have hconvPlus :
      ∀ (I : Finset GridNode) (S : Set (LocalAssignment GridNode I)),
        MeasurableSet S →
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                Eplus M gridPlusBoundary n I S)
            atTop (nhds (Pplus I S)) := by
    intro I S _hS
    simpa [Eplus, Pplus,
      Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal_reindex] using
      (Mettapedia.Logic.MarkovLogicInfiniteExistence.RegionExhaustion.tendsto_stageMarginal_apply_of_tendsto_stageProbabilityFamily
        (E := gridExhaustion) (M := M) (ξ := gridPlusBoundary)
        (P := PplusFamily) (φ := φplus) hφplus I S)
  let originRegion : Region GridNode := {gridOrigin}
  let originEvent : Set (LocalAssignment GridNode originRegion) :=
    localConstraintSet originRegion gridOriginSpinUpLocalQuery
  have hmeasOrigin : MeasurableSet originEvent := by
    simpa [originRegion, originEvent] using
      measurableSet_localConstraintSet
        ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery
  have hminusLimit_le :
      ENNReal.toReal (Pminus originRegion originEvent) ≤ lo := by
    have hconvENN :
        Tendsto
          (fun n =>
            Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
              Eminus M gridMinusBoundary n originRegion originEvent)
          atTop (nhds (Pminus originRegion originEvent)) :=
      hconvMinus originRegion originEvent hmeasOrigin
    have hconvReal :
        Tendsto
          (fun n =>
            ENNReal.toReal
              (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                Eminus M gridMinusBoundary n originRegion originEvent))
          atTop (nhds (ENNReal.toReal (Pminus originRegion originEvent))) :=
      (ENNReal.continuousAt_toReal
        (MeasureTheory.measure_ne_top (μ := Pminus originRegion) (s := originEvent))).tendsto.comp hconvENN
    have hsubseqBound :
        (fun n =>
          ENNReal.toReal
            (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
              Eminus M gridMinusBoundary n originRegion originEvent)) ≤ᶠ[atTop]
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
              Eplus M gridPlusBoundary n originRegion originEvent)
          atTop (nhds (Pplus originRegion originEvent)) :=
      hconvPlus originRegion originEvent hmeasOrigin
    have hconvReal :
        Tendsto
          (fun n =>
            ENNReal.toReal
              (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                Eplus M gridPlusBoundary n originRegion originEvent))
          atTop (nhds (ENNReal.toReal (Pplus originRegion originEvent))) :=
      (ENNReal.continuousAt_toReal
        (MeasureTheory.measure_ne_top (μ := Pplus originRegion) (s := originEvent))).tendsto.comp hconvENN
    have hsubseqBound :
        (fun _ => hi) ≤ᶠ[atTop]
          fun n =>
            ENNReal.toReal
              (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                Eplus M gridPlusBoundary n originRegion originEvent) := by
      exact Eventually.of_forall (fun n => by
        simpa [Eplus, M, originRegion, originEvent,
          Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal_reindex] using
          hplus (φplus n))
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hconvReal hsubseqBound
  have hsep :
      ENNReal.toReal
          (Pminus ({gridOrigin} : Region GridNode)
            (localConstraintSet ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) <
        ENNReal.toReal
          (Pplus ({gridOrigin} : Region GridNode)
            (localConstraintSet ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) := by
    simpa [originRegion, originEvent] using
      lt_of_le_of_lt hminusLimit_le (lt_of_lt_of_le hlohi hplusLimit_ge)
  let μminus : DLRCompletion (symmetricGridZeroFieldClassicalSpec w) :=
    projectiveLimitDLRCompletion_of_stageMarginal_tendsto
      (symmetricGridZeroFieldClassicalSpec w) Eminus gridMinusBoundary
      e Pminus hPminus hconvMinus
  let μplus : DLRCompletion (symmetricGridZeroFieldClassicalSpec w) :=
    projectiveLimitDLRCompletion_of_stageMarginal_tendsto
      (symmetricGridZeroFieldClassicalSpec w) Eplus gridPlusBoundary
      e Pplus hPplus hconvPlus
  have hStrictWidth :
      dlrQueryHasStrictWidth
        (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery := by
    refine ⟨μminus, μplus, ?_⟩
    have hminusLocal :
        dlrCompletionLocalQueryProb (symmetricGridZeroFieldClassicalSpec w)
            ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery μminus =
          ENNReal.toReal
            (Pminus ({gridOrigin} : Region GridNode)
              (localConstraintSet ({gridOrigin} : Region GridNode)
                gridOriginSpinUpLocalQuery)) := by
      simp [dlrCompletionLocalQueryProb, μminus,
        projectiveLimitDLRCompletion_of_stageMarginal_tendsto,
        Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.projectiveLimitMeasure_localQueryEvent]
    have hplusLocal :
        dlrCompletionLocalQueryProb (symmetricGridZeroFieldClassicalSpec w)
            ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery μplus =
          ENNReal.toReal
            (Pplus ({gridOrigin} : Region GridNode)
              (localConstraintSet ({gridOrigin} : Region GridNode)
                gridOriginSpinUpLocalQuery)) := by
      simp [dlrCompletionLocalQueryProb, μplus,
        projectiveLimitDLRCompletion_of_stageMarginal_tendsto,
        Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.projectiveLimitMeasure_localQueryEvent]
    have hminusQuery :
        dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w)
            gridOriginSpinUpQuery μminus =
          ENNReal.toReal
            (Pminus ({gridOrigin} : Region GridNode)
              (localConstraintSet ({gridOrigin} : Region GridNode)
                gridOriginSpinUpLocalQuery)) := by
      rw [dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent]
      rw [← gridOriginSpinUpLocalQueryEvent_eq_global]
      simpa [dlrCompletionLocalQueryProb] using hminusLocal
    have hplusQuery :
        dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w)
            gridOriginSpinUpQuery μplus =
          ENNReal.toReal
            (Pplus ({gridOrigin} : Region GridNode)
              (localConstraintSet ({gridOrigin} : Region GridNode)
                gridOriginSpinUpLocalQuery)) := by
      rw [dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent]
      rw [← gridOriginSpinUpLocalQueryEvent_eq_global]
      simpa [dlrCompletionLocalQueryProb] using hplusLocal
    rw [hminusQuery, hplusQuery]
    exact hsep
  refine ⟨?_, ?_, ?_⟩
  · exact infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth
      (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery hStrictWidth
  · have hpos : 0 < infiniteMLNQueryEnvelopeWidth
        (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery :=
      infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth
        (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery hStrictWidth
    unfold infiniteMLNQueryEnvelopeWidthComplement
    linarith
  · exact dlrQueryOutcomeCredalSet_true_atom_width_pos_of_queryStrictWidth
      (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery hStrictWidth

theorem symmetricGridZeroField_originSpinUp_plnStrictInterval_of_uniformKernelBounds
    {w lo hi : ℝ}
    (hlohi : lo < hi)
    (hminus :
      ∀ n,
        ENNReal.toReal
          (gridExhaustion.finiteVolumeKernelSequence
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            gridMinusBoundary n
            (localQueryEvent ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) ≤ lo)
    (hplus :
      ∀ n,
        hi ≤ ENNReal.toReal
          (gridExhaustion.finiteVolumeKernelSequence
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            gridPlusBoundary n
            (localQueryEvent ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery))) :
    0 < infiniteMLNQueryEnvelopeWidth
          (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery ∧
      infiniteMLNQueryEnvelopeWidthComplement
          (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery < 1 ∧
        0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
          (dlrQueryOutcomeCredalSet
            (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  refine
    symmetricGridZeroField_originSpinUp_plnStrictInterval_of_uniformFiniteVolumeBounds
      (w := w) (lo := lo) (hi := hi) hlohi ?_ ?_
  · intro n
    rw [Mettapedia.Logic.MarkovLogicInfiniteGlobalDLR.RegionExhaustion.stageMarginal_apply_localConstraintSet]
    exact hminus n
  · intro n
    rw [Mettapedia.Logic.MarkovLogicInfiniteGlobalDLR.RegionExhaustion.stageMarginal_apply_localConstraintSet]
    exact hplus n

theorem symmetricGridZeroField_originSpinUp_plnStrictInterval_of_spinFlipHalfGap
    {w δ : ℝ}
    (hδ : 0 < δ)
    (hflip :
      ∀ n,
        ENNReal.toReal
          (gridExhaustion.finiteVolumeKernelSequence
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            gridMinusBoundary n
            (localQueryEvent ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) =
          1 - ENNReal.toReal
            (gridExhaustion.finiteVolumeKernelSequence
              (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
              gridPlusBoundary n
              (localQueryEvent ({gridOrigin} : Region GridNode)
                gridOriginSpinUpLocalQuery)))
    (hplus :
      ∀ n,
        (1 / 2 : ℝ) + δ ≤ ENNReal.toReal
          (gridExhaustion.finiteVolumeKernelSequence
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            gridPlusBoundary n
            (localQueryEvent ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery))) :
    0 < infiniteMLNQueryEnvelopeWidth
          (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery ∧
      infiniteMLNQueryEnvelopeWidthComplement
          (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery < 1 ∧
        0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
          (dlrQueryOutcomeCredalSet
            (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  refine
    symmetricGridZeroField_originSpinUp_plnStrictInterval_of_uniformKernelBounds
      (w := w) (lo := (1 / 2 : ℝ) - δ) (hi := (1 / 2 : ℝ) + δ)
      (by linarith) ?_ hplus
  intro n
  rw [hflip n]
  linarith [hplus n]

theorem symmetricGridZeroField_originSpinUp_plnStrictInterval_of_plusHalfGap
    {w δ : ℝ}
    (hδ : 0 < δ)
    (hplus :
      ∀ n,
        (1 / 2 : ℝ) + δ ≤ ENNReal.toReal
          (gridExhaustion.finiteVolumeKernelSequence
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            gridPlusBoundary n
            (localQueryEvent ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery))) :
    0 < infiniteMLNQueryEnvelopeWidth
          (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery ∧
      infiniteMLNQueryEnvelopeWidthComplement
          (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery < 1 ∧
        0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
          (dlrQueryOutcomeCredalSet
            (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  refine symmetricGridZeroField_originSpinUp_plnStrictInterval_of_spinFlipHalfGap
    (w := w) (δ := δ) hδ ?_ hplus
  intro n
  exact symmetricGridZeroField_originSpinUp_finiteVolumeKernel_minus_eq_one_sub_plus w n

/-- Existence for the zero-field symmetric infinite 2D grid MLN. -/
theorem exists_symmetricGridZeroField_fixedRegionCylinderDLR
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    ∃ μ : Measure (InfiniteWorld GridNode),
      ∃ _ : IsProbabilityMeasure μ,
        FixedRegionCylinderDLR
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec μ := by
  simpa using
    (symmetricGridZeroFieldClassicalSpec w).exists_fixedRegionCylinderDLR_of_equiv
      gridExhaustion ξ (Equiv.prodEquivOfEquivNat (Equiv.refl Nat)).symm

/-- The zero-field symmetric grid has at least one DLR completion. -/
theorem symmetricGridZeroField_dlrCompletion_nonempty
    (w : ℝ) :
    Nonempty (DLRCompletion (symmetricGridZeroFieldClassicalSpec w)) := by
  rcases exists_symmetricGridZeroField_fixedRegionCylinderDLR w gridMinusBoundary with
    ⟨μ, hμprob, hμdlr⟩
  exact ⟨⟨⟨μ, hμprob⟩, hμdlr⟩⟩

/-- A zero-field symmetric-grid DLR completion selected from finite-volume
construction with boundary `ξ`, built from the compactness-extracted
subsequential projective-limit measure for that boundary condition. -/
noncomputable def symmetricGridZeroFieldBoundaryCompletion
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    DLRCompletion (symmetricGridZeroFieldClassicalSpec w) := by
  letI :
      ∀ I : Finset GridNode,
        IsProbabilityMeasure
          ((symmetricGridZeroFieldBoundaryMarginalFamily w ξ) I) := by
    intro I
    dsimp [symmetricGridZeroFieldBoundaryMarginalFamily]
    infer_instance
  exact
    projectiveLimitDLRCompletion_of_stageMarginal_tendsto
      (symmetricGridZeroFieldClassicalSpec w)
      (symmetricGridZeroFieldBoundaryExhaustion w ξ)
      ξ
      gridNodeNatEquiv
      (symmetricGridZeroFieldBoundaryMarginalFamily w ξ)
      (symmetricGridZeroFieldBoundaryMarginalFamily_projective w ξ)
      (symmetricGridZeroFieldBoundaryStageMarginal_tendsto w ξ)

/-- The zero-field symmetric completion selected from all-plus finite-volume
boundary conditions. -/
noncomputable def symmetricGridZeroFieldPlusBoundaryCompletion
    (w : ℝ) : DLRCompletion (symmetricGridZeroFieldClassicalSpec w) :=
  symmetricGridZeroFieldBoundaryCompletion w gridPlusBoundary

/-- The zero-field symmetric completion selected from all-minus finite-volume
boundary conditions. -/
noncomputable def symmetricGridZeroFieldMinusBoundaryCompletion
    (w : ℝ) : DLRCompletion (symmetricGridZeroFieldClassicalSpec w) :=
  symmetricGridZeroFieldBoundaryCompletion w gridMinusBoundary

theorem symmetricGridZeroFieldBoundaryCompletion_originSpinUp_queryProb_eq_limit
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w)
        gridOriginSpinUpQuery
        (symmetricGridZeroFieldBoundaryCompletion w ξ) =
      ENNReal.toReal
        ((symmetricGridZeroFieldBoundaryMarginalFamily w ξ)
          ({gridOrigin} : Region GridNode)
          (localConstraintSet ({gridOrigin} : Region GridNode)
            gridOriginSpinUpLocalQuery)) := by
  have hlocal :
      dlrCompletionLocalQueryProb (symmetricGridZeroFieldClassicalSpec w)
          ({gridOrigin} : Region GridNode)
          gridOriginSpinUpLocalQuery
          (symmetricGridZeroFieldBoundaryCompletion w ξ) =
        ENNReal.toReal
          ((symmetricGridZeroFieldBoundaryMarginalFamily w ξ)
            ({gridOrigin} : Region GridNode)
            (localConstraintSet ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) := by
    simp [dlrCompletionLocalQueryProb, symmetricGridZeroFieldBoundaryCompletion,
      symmetricGridZeroFieldBoundaryMarginalFamily,
      projectiveLimitDLRCompletion_of_stageMarginal_tendsto,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.projectiveLimitMeasure_localQueryEvent]
  rw [dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent]
  rw [← gridOriginSpinUpLocalQueryEvent_eq_global]
  simpa [dlrCompletionLocalQueryProb] using hlocal

theorem symmetricGridZeroFieldBoundaryCompletion_originSpinUp_queryProb_le_of_uniformKernelUpperBound
    {w b : ℝ} (ξ : BoundaryCondition GridNode)
    (hbound :
      ∀ n,
        ENNReal.toReal
          (gridExhaustion.finiteVolumeKernelSequence
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            ξ n
            (localQueryEvent ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) ≤ b) :
    dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w)
        gridOriginSpinUpQuery
        (symmetricGridZeroFieldBoundaryCompletion w ξ) ≤ b := by
  let originRegion : Region GridNode := {gridOrigin}
  let originEvent : Set (LocalAssignment GridNode originRegion) :=
    localConstraintSet originRegion gridOriginSpinUpLocalQuery
  have hmeasOrigin : MeasurableSet originEvent := by
    simpa [originRegion, originEvent] using
      measurableSet_localConstraintSet
        ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery
  have hconvENN :
      Tendsto
        (fun n =>
          Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
            (symmetricGridZeroFieldBoundaryExhaustion w ξ)
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            ξ n originRegion originEvent)
        atTop
        (nhds
          ((symmetricGridZeroFieldBoundaryMarginalFamily w ξ)
            originRegion originEvent)) :=
    symmetricGridZeroFieldBoundaryStageMarginal_tendsto w ξ originRegion originEvent hmeasOrigin
  letI :
      IsProbabilityMeasure
        ((symmetricGridZeroFieldBoundaryMarginalFamily w ξ) originRegion) := by
    dsimp [symmetricGridZeroFieldBoundaryMarginalFamily]
    infer_instance
  have hconvReal :
      Tendsto
        (fun n =>
          ENNReal.toReal
            (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
              (symmetricGridZeroFieldBoundaryExhaustion w ξ)
              (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
              ξ n originRegion originEvent))
        atTop
        (nhds
          (ENNReal.toReal
            (((symmetricGridZeroFieldBoundaryMarginalFamily w ξ)
              originRegion originEvent)))) :=
    (ENNReal.continuousAt_toReal
      (MeasureTheory.measure_ne_top
        (μ := (symmetricGridZeroFieldBoundaryMarginalFamily w ξ) originRegion)
        (s := originEvent))).tendsto.comp hconvENN
  have hsubseqBound :
      (fun n =>
        ENNReal.toReal
          (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
            (symmetricGridZeroFieldBoundaryExhaustion w ξ)
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            ξ n originRegion originEvent)) ≤ᶠ[atTop]
        fun _ => b := by
    exact Eventually.of_forall (fun n => by
      simpa [symmetricGridZeroFieldBoundaryExhaustion, originRegion, originEvent,
        Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal_reindex,
        Mettapedia.Logic.MarkovLogicInfiniteGlobalDLR.RegionExhaustion.stageMarginal_apply_localConstraintSet] using
        hbound (symmetricGridZeroFieldBoundaryStageSubseq w ξ n))
  have hlimit :
      ENNReal.toReal
        (((symmetricGridZeroFieldBoundaryMarginalFamily w ξ)
          originRegion originEvent)) ≤ b :=
    le_of_tendsto_of_tendsto hconvReal tendsto_const_nhds hsubseqBound
  rw [symmetricGridZeroFieldBoundaryCompletion_originSpinUp_queryProb_eq_limit]
  simpa [originRegion, originEvent] using hlimit

theorem symmetricGridZeroFieldBoundaryCompletion_originSpinUp_queryProb_ge_of_uniformKernelLowerBound
    {w b : ℝ} (ξ : BoundaryCondition GridNode)
    (hbound :
      ∀ n,
        b ≤ ENNReal.toReal
          (gridExhaustion.finiteVolumeKernelSequence
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            ξ n
            (localQueryEvent ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery))) :
    b ≤ dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w)
        gridOriginSpinUpQuery
        (symmetricGridZeroFieldBoundaryCompletion w ξ) := by
  let originRegion : Region GridNode := {gridOrigin}
  let originEvent : Set (LocalAssignment GridNode originRegion) :=
    localConstraintSet originRegion gridOriginSpinUpLocalQuery
  have hmeasOrigin : MeasurableSet originEvent := by
    simpa [originRegion, originEvent] using
      measurableSet_localConstraintSet
        ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery
  have hconvENN :
      Tendsto
        (fun n =>
          Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
            (symmetricGridZeroFieldBoundaryExhaustion w ξ)
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            ξ n originRegion originEvent)
        atTop
        (nhds
          ((symmetricGridZeroFieldBoundaryMarginalFamily w ξ)
            originRegion originEvent)) :=
    symmetricGridZeroFieldBoundaryStageMarginal_tendsto w ξ originRegion originEvent hmeasOrigin
  letI :
      IsProbabilityMeasure
        ((symmetricGridZeroFieldBoundaryMarginalFamily w ξ) originRegion) := by
    dsimp [symmetricGridZeroFieldBoundaryMarginalFamily]
    infer_instance
  have hconvReal :
      Tendsto
        (fun n =>
          ENNReal.toReal
            (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
              (symmetricGridZeroFieldBoundaryExhaustion w ξ)
              (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
              ξ n originRegion originEvent))
        atTop
        (nhds
          (ENNReal.toReal
            (((symmetricGridZeroFieldBoundaryMarginalFamily w ξ)
              originRegion originEvent)))) :=
    (ENNReal.continuousAt_toReal
      (MeasureTheory.measure_ne_top
        (μ := (symmetricGridZeroFieldBoundaryMarginalFamily w ξ) originRegion)
        (s := originEvent))).tendsto.comp hconvENN
  have hsubseqBound :
      (fun _ => b) ≤ᶠ[atTop]
        (fun n =>
          ENNReal.toReal
            (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
              (symmetricGridZeroFieldBoundaryExhaustion w ξ)
              (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
              ξ n originRegion originEvent)) := by
    exact Eventually.of_forall (fun n => by
      simpa [symmetricGridZeroFieldBoundaryExhaustion, originRegion, originEvent,
        Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal_reindex,
        Mettapedia.Logic.MarkovLogicInfiniteGlobalDLR.RegionExhaustion.stageMarginal_apply_localConstraintSet] using
        hbound (symmetricGridZeroFieldBoundaryStageSubseq w ξ n))
  have hlimit :
      b ≤ ENNReal.toReal
        (((symmetricGridZeroFieldBoundaryMarginalFamily w ξ)
          originRegion originEvent)) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hconvReal hsubseqBound
  rw [symmetricGridZeroFieldBoundaryCompletion_originSpinUp_queryProb_eq_limit]
  simpa [originRegion, originEvent] using hlimit

/-- The local and global origin-spin probabilities agree for every zero-field
symmetric-grid DLR completion. -/
theorem symmetricGridZeroField_originSpinUp_localQueryProb_eq_queryProb
    (w : ℝ) (μ : DLRCompletion (symmetricGridZeroFieldClassicalSpec w)) :
    dlrCompletionLocalQueryProb (symmetricGridZeroFieldClassicalSpec w)
        ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery μ =
      dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery μ := by
  rw [dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent]
  unfold dlrCompletionLocalQueryProb
  rw [gridOriginSpinUpLocalQueryEvent_eq_global]

/-- Under the generic Dobrushin hypothesis, the symmetric zero-field grid has
precise lower/upper PLN/Walley query envelopes. -/
theorem symmetricGridZeroField_queryEnvelope_precise_of_dobrushin
    {w : ℝ}
    (hM : (symmetricGridZeroFieldClassicalSpec w).PaperUniformSmallTotalInfluence)
    (q : ConstraintQuery GridNode) :
    infiniteMLNLowerQueryEnvelope (symmetricGridZeroFieldClassicalSpec w) q =
      infiniteMLNUpperQueryEnvelope (symmetricGridZeroFieldClassicalSpec w) q := by
  letI : Nonempty (DLRCompletion (symmetricGridZeroFieldClassicalSpec w)) :=
    symmetricGridZeroField_dlrCompletion_nonempty w
  exact infiniteMLN_queryEnvelope_precise_of_uniform
    (symmetricGridZeroFieldClassicalSpec w) hM q

/-- Concrete high-temperature collapse: if `4 * |w| < 1`, every PLN/Walley
query envelope of the symmetric zero-field grid is precise. -/
theorem symmetricGridZeroField_queryEnvelope_precise_of_smallWeight
    {w : ℝ} (hbudget : 4 * |w| < 1) (q : ConstraintQuery GridNode) :
    infiniteMLNLowerQueryEnvelope (symmetricGridZeroFieldClassicalSpec w) q =
      infiniteMLNUpperQueryEnvelope (symmetricGridZeroFieldClassicalSpec w) q := by
  exact symmetricGridZeroField_queryEnvelope_precise_of_dobrushin
    (symmetricGridZeroField_uniformSmallTotalInfluence hbudget) q

/-- Dobrushin collapse for the concrete origin-spin query in the symmetric
zero-field grid. -/
theorem symmetricGridZeroField_originSpinUp_queryEnvelope_precise_of_dobrushin
    {w : ℝ}
    (hM : (symmetricGridZeroFieldClassicalSpec w).PaperUniformSmallTotalInfluence) :
    infiniteMLNLowerQueryEnvelope
        (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery =
      infiniteMLNUpperQueryEnvelope
        (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery := by
  exact symmetricGridZeroField_queryEnvelope_precise_of_dobrushin hM gridOriginSpinUpQuery

/-- Concrete high-temperature collapse for the origin-spin PLN query in the
symmetric zero-field grid. -/
theorem symmetricGridZeroField_originSpinUp_queryEnvelope_precise_of_smallWeight
    {w : ℝ} (hbudget : 4 * |w| < 1) :
    infiniteMLNLowerQueryEnvelope
        (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery =
      infiniteMLNUpperQueryEnvelope
        (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery := by
  exact symmetricGridZeroField_queryEnvelope_precise_of_smallWeight hbudget gridOriginSpinUpQuery

/-- If the plus/minus symmetric-grid boundary completions separate the
origin-spin query, then the symmetric grid has strict DLR width for that PLN
query. -/
theorem symmetricGridZeroField_originSpinUp_strictWidth_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldPlusBoundaryCompletion w)) :
    dlrQueryHasStrictWidth (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery := by
  exact ⟨symmetricGridZeroFieldMinusBoundaryCompletion w,
    symmetricGridZeroFieldPlusBoundaryCompletion w, hsep⟩

/-- The same plus/minus separation gives strict width for the one-site local
cylinder presentation of the origin-spin observable. -/
theorem symmetricGridZeroField_originSpinUp_localQueryStrictWidth_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldPlusBoundaryCompletion w)) :
    dlrLocalQueryHasStrictWidth (symmetricGridZeroFieldClassicalSpec w)
      ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery := by
  refine ⟨symmetricGridZeroFieldMinusBoundaryCompletion w,
    symmetricGridZeroFieldPlusBoundaryCompletion w, ?_⟩
  simpa [symmetricGridZeroField_originSpinUp_localQueryProb_eq_queryProb] using hsep

/-- Plus/minus origin-spin separation forces a nontrivial scalar PLN/Walley
query envelope for the symmetric grid. -/
theorem symmetricGridZeroField_originSpinUp_queryEnvelope_nontrivial_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldPlusBoundaryCompletion w)) :
    infiniteMLNLowerQueryEnvelope (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery <
      infiniteMLNUpperQueryEnvelope (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery := by
  exact infiniteMLN_queryEnvelope_nontrivial_of_strictWidth_bounded
    (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
    (symmetricGridZeroField_originSpinUp_strictWidth_of_plusMinusBoundarySeparation hsep)

/-- Plus/minus origin-spin separation forces positive scalar PLN/Walley query
width for the symmetric grid. -/
theorem symmetricGridZeroField_originSpinUp_queryEnvelopeWidth_pos_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldPlusBoundaryCompletion w)) :
    0 < infiniteMLNQueryEnvelopeWidth
      (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery := by
  exact infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth
    (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
    (symmetricGridZeroField_originSpinUp_strictWidth_of_plusMinusBoundarySeparation hsep)

/-- Plus/minus origin-spin separation drops the scalar PLN confidence coordinate
below one for the symmetric grid. -/
theorem symmetricGridZeroField_originSpinUp_queryEnvelopeWidthComplement_lt_one_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldPlusBoundaryCompletion w)) :
    infiniteMLNQueryEnvelopeWidthComplement
      (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery < 1 := by
  have hpos :=
    symmetricGridZeroField_originSpinUp_queryEnvelopeWidth_pos_of_plusMinusBoundarySeparation hsep
  unfold infiniteMLNQueryEnvelopeWidthComplement
  linarith

/-- Plus/minus origin-spin separation gives positive width in the concrete
binary query-outcome credal set read by PLN. -/
theorem symmetricGridZeroField_originSpinUp_queryOutcomeCredalSet_width_pos_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldPlusBoundaryCompletion w)) :
    0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
      (dlrQueryOutcomeCredalSet (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery)
      (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  exact dlrQueryOutcomeCredalSet_true_atom_width_pos_of_queryStrictWidth
    (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
    (symmetricGridZeroField_originSpinUp_strictWidth_of_plusMinusBoundarySeparation hsep)

/-- Plus/minus origin-spin separation forces positive width for the local
one-site cylinder envelope in the symmetric grid. -/
theorem symmetricGridZeroField_originSpinUp_localQueryEnvelopeWidth_pos_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldPlusBoundaryCompletion w)) :
    0 < dlrLocalQueryEnvelopeWidth (symmetricGridZeroFieldClassicalSpec w)
      ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery := by
  exact dlrLocalQueryEnvelopeWidth_pos_of_localQueryStrictWidth
    (symmetricGridZeroFieldClassicalSpec w) ({gridOrigin} : Region GridNode)
    gridOriginSpinUpLocalQuery
    (symmetricGridZeroField_originSpinUp_localQueryStrictWidth_of_plusMinusBoundarySeparation hsep)

/-- Plus/minus origin-spin separation drops the local one-site cylinder
confidence coordinate below one in the symmetric grid. -/
theorem symmetricGridZeroField_originSpinUp_localQueryEnvelopeWidthComplement_lt_one_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (symmetricGridZeroFieldPlusBoundaryCompletion w)) :
    dlrLocalQueryEnvelopeWidthComplement (symmetricGridZeroFieldClassicalSpec w)
      ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery < 1 := by
  exact dlrLocalQueryEnvelopeWidthComplement_lt_one_of_localQueryStrictWidth
    (symmetricGridZeroFieldClassicalSpec w) ({gridOrigin} : Region GridNode)
    gridOriginSpinUpLocalQuery
    (symmetricGridZeroField_originSpinUp_localQueryStrictWidth_of_plusMinusBoundarySeparation hsep)

/-- The remaining low-temperature phase-coexistence input, stated directly at
the origin-spin PLN query: the symmetric plus-boundary and minus-boundary DLR
completions have separated origin marginals. -/
abbrev symmetricGridZeroFieldOriginPlusMinusBoundarySeparation
    (w : ℝ) : Prop :=
  dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
      (symmetricGridZeroFieldMinusBoundaryCompletion w) <
    dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
      (symmetricGridZeroFieldPlusBoundaryCompletion w)

/-- A finite-volume half-gap input for the plus boundary: every exhaustion
stage has origin-spin-up probability at least `1/2 + δ`.  Spin-flip symmetry
then supplies the matching minus-boundary upper bound. -/
abbrev symmetricGridZeroFieldOriginPlusHalfGap
    (w δ : ℝ) : Prop :=
  0 < δ ∧
    ∀ n,
      (1 / 2 : ℝ) + δ ≤ ENNReal.toReal
        (gridExhaustion.finiteVolumeKernelSequence
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          gridPlusBoundary n
          (localQueryEvent ({gridOrigin} : Region GridNode)
            gridOriginSpinUpLocalQuery))

/-- Peierls-style finite-volume error input for the plus boundary: the
probability that the origin fails to align with the plus boundary is bounded
by an error `ε < 1/2` at every exhaustion stage.  A contour estimate at low
temperature is expected to instantiate this predicate. -/
abbrev symmetricGridZeroFieldOriginPeierlsErrorBound
    (w ε : ℝ) : Prop :=
  0 ≤ ε ∧ ε < (1 / 2 : ℝ) ∧
    ∀ n,
      1 - ENNReal.toReal
        (gridExhaustion.finiteVolumeKernelSequence
          (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
          gridPlusBoundary n
          (localQueryEvent ({gridOrigin} : Region GridNode)
            gridOriginSpinUpLocalQuery)) ≤ ε

/-- A Peierls error bound gives an explicit finite-volume plus/minus separation
window at every stage: the minus-boundary origin-up probability is at most
`ε`, while the plus-boundary origin-up probability is at least `1 - ε`. -/
theorem symmetricGridZeroField_originSpinUp_finiteVolumeKernel_separated_of_peierlsErrorBound
    {w ε : ℝ}
    (hPeierls : symmetricGridZeroFieldOriginPeierlsErrorBound w ε) :
    ∀ n,
      ENNReal.toReal
          (gridExhaustion.finiteVolumeKernelSequence
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            gridMinusBoundary n
            (localQueryEvent ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) ≤ ε ∧
        1 - ε ≤ ENNReal.toReal
          (gridExhaustion.finiteVolumeKernelSequence
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            gridPlusBoundary n
            (localQueryEvent ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) := by
  rcases hPeierls with ⟨_hε_nonneg, _hε_lt_half, hbound⟩
  intro n
  have hminus :=
    symmetricGridZeroField_originSpinUp_finiteVolumeKernel_minus_eq_one_sub_plus
      w n
  have hb := hbound n
  constructor
  · rw [hminus]
    exact hb
  · linarith

/-- A Peierls error bound gives strict finite-volume plus/minus separation at
the origin for every exhaustion stage. -/
theorem symmetricGridZeroField_originSpinUp_finiteVolumeKernel_lt_of_peierlsErrorBound
    {w ε : ℝ}
    (hPeierls : symmetricGridZeroFieldOriginPeierlsErrorBound w ε) :
    ∀ n,
      ENNReal.toReal
          (gridExhaustion.finiteVolumeKernelSequence
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            gridMinusBoundary n
            (localQueryEvent ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) <
        ENNReal.toReal
          (gridExhaustion.finiteVolumeKernelSequence
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            gridPlusBoundary n
            (localQueryEvent ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) := by
  rcases hPeierls with ⟨hε_nonneg, hε_lt_half, hbound⟩
  intro n
  have hsep :=
    symmetricGridZeroField_originSpinUp_finiteVolumeKernel_separated_of_peierlsErrorBound
      (w := w) (ε := ε) ⟨hε_nonneg, hε_lt_half, hbound⟩ n
  linarith

/-- A Peierls error bound instantiates the plus-boundary half-gap required by
the existing strict-interval bridge. -/
theorem symmetricGridZeroFieldOriginPlusHalfGap_of_peierlsErrorBound
    {w ε : ℝ}
    (hPeierls : symmetricGridZeroFieldOriginPeierlsErrorBound w ε) :
    symmetricGridZeroFieldOriginPlusHalfGap w ((1 / 2 : ℝ) - ε) := by
  rcases hPeierls with ⟨hε_nonneg, hε_lt_half, hbound⟩
  refine ⟨by linarith, ?_⟩
  intro n
  have hb := hbound n
  linarith

theorem symmetricGridZeroFieldOriginPlusHalfGap_of_neighborPairGap
    {w γ : ℝ}
    (hw : 0 < w)
    (hγ : 0 < γ)
    (hpair :
      ∀ n,
        γ ≤
          ENNReal.toReal
            (symmetricGridZeroFieldOriginNeighborPairStagePMF w gridPlusBoundary n
              gridOriginNeighborPairTT) -
            ENNReal.toReal
              (symmetricGridZeroFieldOriginNeighborPairStagePMF w gridPlusBoundary n
                gridOriginNeighborPairFF)) :
    symmetricGridZeroFieldOriginPlusHalfGap w
      ((Real.sigmoid (2 * w) - (1 / 2 : ℝ)) * γ) := by
  have hsigHalf : (1 / 2 : ℝ) < Real.sigmoid (2 * w) := by
    have hlt : Real.sigmoid 0 < Real.sigmoid (2 * w) := by
      exact Real.sigmoid_lt (by nlinarith)
    simpa [Real.sigmoid_zero] using hlt
  refine ⟨by nlinarith, ?_⟩
  intro n
  have hcoef_nonneg : 0 ≤ Real.sigmoid (2 * w) - (1 / 2 : ℝ) := by
    linarith
  have hmul :
      (Real.sigmoid (2 * w) - (1 / 2 : ℝ)) * γ ≤
        (Real.sigmoid (2 * w) - (1 / 2 : ℝ)) *
          (ENNReal.toReal
              (symmetricGridZeroFieldOriginNeighborPairStagePMF w gridPlusBoundary n
                gridOriginNeighborPairTT) -
            ENNReal.toReal
              (symmetricGridZeroFieldOriginNeighborPairStagePMF w gridPlusBoundary n
                gridOriginNeighborPairFF)) := by
    exact mul_le_mul_of_nonneg_left (hpair n) hcoef_nonneg
  rw [symmetricGridZeroField_originSpinUp_finiteVolumeKernel_toReal_eq_half_add_neighborPairGap
    w n gridPlusBoundary]
  linarith

/-- A uniform plus-boundary bound on the failure of the corner-neighbour `TT`
event is enough to instantiate the existing pair-gap half-gap bridge. -/
theorem symmetricGridZeroFieldOriginPlusHalfGap_of_notTTBound
    {w η : ℝ}
    (hw : 0 < w)
    (hη_lt_half : η < (1 / 2 : ℝ))
    (hbad :
      ∀ n,
        1 -
            ENNReal.toReal
              (symmetricGridZeroFieldOriginNeighborPairStagePMF w gridPlusBoundary n
                gridOriginNeighborPairTT) ≤
          η) :
    symmetricGridZeroFieldOriginPlusHalfGap w
      ((Real.sigmoid (2 * w) - (1 / 2 : ℝ)) * (1 - 2 * η)) := by
  have hgap_pos : 0 < 1 - 2 * η := by
    linarith
  exact symmetricGridZeroFieldOriginPlusHalfGap_of_neighborPairGap hw hgap_pos
    (fun n =>
      symmetricGridZeroFieldOriginNeighborPairStage_gap_ge_of_notTTBound
        (w := w) (η := η) n gridPlusBoundary (hbad n))

/-- A uniform plus-boundary half-gap forces the compactness-extracted
plus/minus DLR completions to separate at the origin-spin query. -/
theorem symmetricGridZeroFieldOriginPlusMinusBoundarySeparation_of_plusHalfGap
    {w δ : ℝ}
    (hgap : symmetricGridZeroFieldOriginPlusHalfGap w δ) :
    symmetricGridZeroFieldOriginPlusMinusBoundarySeparation w := by
  rcases hgap with ⟨hδ, hplus⟩
  have hminus :
      ∀ n,
        ENNReal.toReal
          (gridExhaustion.finiteVolumeKernelSequence
            (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
            gridMinusBoundary n
            (localQueryEvent ({gridOrigin} : Region GridNode)
              gridOriginSpinUpLocalQuery)) ≤ (1 / 2 : ℝ) - δ := by
    intro n
    rw [symmetricGridZeroField_originSpinUp_finiteVolumeKernel_minus_eq_one_sub_plus w n]
    linarith [hplus n]
  have hminus_le :
      dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w)
          gridOriginSpinUpQuery
          (symmetricGridZeroFieldMinusBoundaryCompletion w) ≤
        (1 / 2 : ℝ) - δ :=
    symmetricGridZeroFieldBoundaryCompletion_originSpinUp_queryProb_le_of_uniformKernelUpperBound
      (w := w) (b := (1 / 2 : ℝ) - δ) gridMinusBoundary hminus
  have hplus_ge :
      (1 / 2 : ℝ) + δ ≤
        dlrCompletionQueryProb (symmetricGridZeroFieldClassicalSpec w)
          gridOriginSpinUpQuery
          (symmetricGridZeroFieldPlusBoundaryCompletion w) :=
    symmetricGridZeroFieldBoundaryCompletion_originSpinUp_queryProb_ge_of_uniformKernelLowerBound
      (w := w) (b := (1 / 2 : ℝ) + δ) gridPlusBoundary hplus
  linarith

/-- A Peierls-style finite-volume error bound therefore also separates the
compactness-extracted plus/minus DLR completions at the origin-spin query. -/
theorem symmetricGridZeroFieldOriginPlusMinusBoundarySeparation_of_peierlsErrorBound
    {w ε : ℝ}
    (hPeierls : symmetricGridZeroFieldOriginPeierlsErrorBound w ε) :
    symmetricGridZeroFieldOriginPlusMinusBoundarySeparation w :=
  symmetricGridZeroFieldOriginPlusMinusBoundarySeparation_of_plusHalfGap
    (symmetricGridZeroFieldOriginPlusHalfGap_of_peierlsErrorBound hPeierls)

/-- The review-facing strict-interval package for the symmetric zero-field
origin-spin query: positive scalar envelope width, confidence complement below
one, and positive binary query-outcome credal width. -/
structure SymmetricGridZeroFieldOriginPLNStrictIntervalCrown
    (w : ℝ) : Prop where
  queryEnvelopeWidth_pos :
    0 < infiniteMLNQueryEnvelopeWidth
      (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
  queryEnvelopeWidthComplement_lt_one :
    infiniteMLNQueryEnvelopeWidthComplement
      (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery < 1
  queryOutcomeCredalSet_width_pos :
    0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
      (dlrQueryOutcomeCredalSet
        (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery)
      (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true)

/-- A plus-boundary finite-volume half-gap is enough to obtain the strict PLN
interval package for the symmetric zero-field origin-spin query. -/
theorem symmetricGridZeroField_originPLNStrictIntervalCrown_of_plusHalfGap
    {w δ : ℝ}
    (hgap : symmetricGridZeroFieldOriginPlusHalfGap w δ) :
    SymmetricGridZeroFieldOriginPLNStrictIntervalCrown w := by
  rcases hgap with ⟨hδ, hplus⟩
  rcases symmetricGridZeroField_originSpinUp_plnStrictInterval_of_plusHalfGap
      (w := w) (δ := δ) hδ hplus with
    ⟨hwidth, hcomp, houtcome⟩
  exact ⟨hwidth, hcomp, houtcome⟩

/-- A Peierls-style finite-volume origin-error bound is enough to obtain the
strict PLN interval package for the symmetric zero-field origin-spin query. -/
theorem symmetricGridZeroField_originPLNStrictIntervalCrown_of_peierlsErrorBound
    {w ε : ℝ}
    (hPeierls : symmetricGridZeroFieldOriginPeierlsErrorBound w ε) :
    SymmetricGridZeroFieldOriginPLNStrictIntervalCrown w :=
  symmetricGridZeroField_originPLNStrictIntervalCrown_of_plusHalfGap
    (symmetricGridZeroFieldOriginPlusHalfGap_of_peierlsErrorBound hPeierls)

/-- Plus/minus boundary separation is enough to obtain the strict PLN interval
package for the symmetric zero-field origin-spin query. -/
theorem symmetricGridZeroField_originPLNStrictIntervalCrown_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep : symmetricGridZeroFieldOriginPlusMinusBoundarySeparation w) :
    SymmetricGridZeroFieldOriginPLNStrictIntervalCrown w where
  queryEnvelopeWidth_pos :=
    symmetricGridZeroField_originSpinUp_queryEnvelopeWidth_pos_of_plusMinusBoundarySeparation hsep
  queryEnvelopeWidthComplement_lt_one :=
    symmetricGridZeroField_originSpinUp_queryEnvelopeWidthComplement_lt_one_of_plusMinusBoundarySeparation hsep
  queryOutcomeCredalSet_width_pos :=
    symmetricGridZeroField_originSpinUp_queryOutcomeCredalSet_width_pos_of_plusMinusBoundarySeparation hsep

/-- The present formal phase-coexistence reduction for the symmetric zero-field
grid: high temperature gives a precise origin-spin envelope, while either a
plus half-gap or direct plus/minus boundary separation gives the strict PLN
interval package.  A Peierls error bound is exposed as an intermediate
finite-volume route through the plus half-gap.  The low-temperature
Peierls/coexistence theorem is exactly the remaining mathematical input needed
to instantiate one of the low-temperature fields. -/
structure SymmetricGridZeroFieldOriginPhaseCoexistenceReductionCrown : Prop where
  highTemperaturePrecise :
    ∀ {w : ℝ}, 4 * |w| < 1 →
      infiniteMLNLowerQueryEnvelope
          (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery =
        infiniteMLNUpperQueryEnvelope
          (symmetricGridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
  plusHalfGapStrictInterval :
    ∀ {w δ : ℝ},
      symmetricGridZeroFieldOriginPlusHalfGap w δ →
        SymmetricGridZeroFieldOriginPLNStrictIntervalCrown w
  plusHalfGapBoundarySeparation :
    ∀ {w δ : ℝ},
      symmetricGridZeroFieldOriginPlusHalfGap w δ →
        symmetricGridZeroFieldOriginPlusMinusBoundarySeparation w
  peierlsErrorBoundPlusHalfGap :
    ∀ {w ε : ℝ},
      symmetricGridZeroFieldOriginPeierlsErrorBound w ε →
        symmetricGridZeroFieldOriginPlusHalfGap w ((1 / 2 : ℝ) - ε)
  peierlsErrorBoundFiniteVolumeSeparation :
    ∀ {w ε : ℝ},
      symmetricGridZeroFieldOriginPeierlsErrorBound w ε →
        ∀ n,
          ENNReal.toReal
              (gridExhaustion.finiteVolumeKernelSequence
                (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
                gridMinusBoundary n
                (localQueryEvent ({gridOrigin} : Region GridNode)
                  gridOriginSpinUpLocalQuery)) <
            ENNReal.toReal
              (gridExhaustion.finiteVolumeKernelSequence
                (symmetricGridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
                gridPlusBoundary n
                (localQueryEvent ({gridOrigin} : Region GridNode)
                  gridOriginSpinUpLocalQuery))
  peierlsErrorBoundBoundarySeparation :
    ∀ {w ε : ℝ},
      symmetricGridZeroFieldOriginPeierlsErrorBound w ε →
        symmetricGridZeroFieldOriginPlusMinusBoundarySeparation w
  peierlsErrorBoundStrictInterval :
    ∀ {w ε : ℝ},
      symmetricGridZeroFieldOriginPeierlsErrorBound w ε →
        SymmetricGridZeroFieldOriginPLNStrictIntervalCrown w
  plusMinusBoundarySeparationStrictInterval :
    ∀ {w : ℝ},
      symmetricGridZeroFieldOriginPlusMinusBoundarySeparation w →
        SymmetricGridZeroFieldOriginPLNStrictIntervalCrown w

/-- The symmetric zero-field Ising/MLN crown reduced to a precise
low-temperature input: prove a plus half-gap or plus/minus boundary separation,
and the PLN strict interval follows without additional assumptions. -/
theorem symmetricGridZeroField_originPhaseCoexistenceReductionCrown :
    SymmetricGridZeroFieldOriginPhaseCoexistenceReductionCrown where
  highTemperaturePrecise := by
    intro w hbudget
    exact symmetricGridZeroField_originSpinUp_queryEnvelope_precise_of_smallWeight hbudget
  plusHalfGapStrictInterval := by
    intro w δ hgap
    exact symmetricGridZeroField_originPLNStrictIntervalCrown_of_plusHalfGap hgap
  plusHalfGapBoundarySeparation := by
    intro w δ hgap
    exact symmetricGridZeroFieldOriginPlusMinusBoundarySeparation_of_plusHalfGap hgap
  peierlsErrorBoundPlusHalfGap := by
    intro w ε hPeierls
    exact symmetricGridZeroFieldOriginPlusHalfGap_of_peierlsErrorBound hPeierls
  peierlsErrorBoundFiniteVolumeSeparation := by
    intro w ε hPeierls n
    exact
      symmetricGridZeroField_originSpinUp_finiteVolumeKernel_lt_of_peierlsErrorBound
        hPeierls n
  peierlsErrorBoundBoundarySeparation := by
    intro w ε hPeierls
    exact symmetricGridZeroFieldOriginPlusMinusBoundarySeparation_of_peierlsErrorBound hPeierls
  peierlsErrorBoundStrictInterval := by
    intro w ε hPeierls
    exact symmetricGridZeroField_originPLNStrictIntervalCrown_of_peierlsErrorBound hPeierls
  plusMinusBoundarySeparationStrictInterval := by
    intro w hsep
    exact symmetricGridZeroField_originPLNStrictIntervalCrown_of_plusMinusBoundarySeparation hsep

end Mettapedia.Logic.MarkovLogicInfiniteSymmetricGridExample
