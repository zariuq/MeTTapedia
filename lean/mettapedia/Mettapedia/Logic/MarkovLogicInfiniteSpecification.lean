import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mettapedia.Logic.MarkovLogicClauseSemantics
import Mettapedia.Logic.MarkovLogicClauseFactorGraph

/-!
# Infinite MLN Specification Layer

This module starts the literature-backed infinite-domain MLN lane.

It does **not** yet construct global Gibbs measures. Instead it defines the
load-bearing semantic objects that appear in Singla and Domingos,
*Markov Logic in Infinite Domains* (UAI 2007; Dagstuhl 2008):

- infinite Boolean worlds `Atom → Bool`,
- finite regions and boundary conditions,
- patching a finite-region assignment into a boundary condition,
- region-local clause support,
- finite-volume weights and partitions.

This is intentionally kept separate from the existing finite/countable MLN
files so the infinite semantics can be built at the right abstraction layer and
then connected back cleanly.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteSpecification

open scoped ENNReal BigOperators
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph

/-- An infinite Boolean world over ground atoms. -/
abbrev InfiniteWorld (Atom : Type*) := Atom → Bool

/-- Finite regions of an infinite atom space. -/
abbrev Region (Atom : Type*) := Finset Atom

/-- Atom type restricted to a finite region. -/
abbrev RegionAtom (Atom : Type*) (Λ : Region Atom) := {a // a ∈ Λ}

/-- Boundary conditions are full infinite worlds. -/
abbrev BoundaryCondition (Atom : Type*) := InfiniteWorld Atom

/-- A local assignment only specifies truth values on a finite region. -/
abbrev LocalAssignment (Atom : Type*) (Λ : Region Atom) := RegionAtom Atom Λ → Bool

/-- Two infinite worlds agree outside a finite region. -/
def agreesOnOutside {Atom : Type*} (Λ : Region Atom)
    (ω ξ : InfiniteWorld Atom) : Prop :=
  ∀ a, a ∉ Λ → ω a = ξ a

/-- Patch a local assignment into a boundary condition, producing a full world. -/
def patch {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (x : LocalAssignment Atom Λ) (ξ : BoundaryCondition Atom) :
    InfiniteWorld Atom :=
  fun a => if h : a ∈ Λ then x ⟨a, h⟩ else ξ a

@[simp] theorem patch_on_region {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (x : LocalAssignment Atom Λ) (ξ : BoundaryCondition Atom)
    {a : Atom} (ha : a ∈ Λ) :
    patch Λ x ξ a = x ⟨a, ha⟩ := by
  simp [patch, ha]

@[simp] theorem patch_outside_region {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (x : LocalAssignment Atom Λ) (ξ : BoundaryCondition Atom)
    {a : Atom} (ha : a ∉ Λ) :
    patch Λ x ξ a = ξ a := by
  simp [patch, ha]

theorem patch_agreesOnOutside {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (x : LocalAssignment Atom Λ) (ξ : BoundaryCondition Atom) :
    agreesOnOutside Λ (patch Λ x ξ) ξ := by
  intro a ha
  simp [patch, ha]

/-- A clause touches a region when one of its atoms lies in that region. -/
def clauseTouchesRegion {Atom : Type*} [DecidableEq Atom]
    (C : GroundClause Atom) (Λ : Region Atom) : Prop :=
  ∃ a, a ∈ C.atoms ∧ a ∈ Λ

/-- Infinite MLN specification with explicit finite support for each region.

`regionSupport Λ` is the finite set of clause ids whose clauses touch the
region `Λ`.  This packages the local-finiteness data in a computationally
usable form for Lean.
-/
structure InfiniteGroundMLNSpec (Atom ClauseId : Type*)
    [DecidableEq Atom] [DecidableEq ClauseId] where
  clauseData : ClauseId → WeightedGroundClause Atom
  regionSupport : Region Atom → Finset ClauseId
  regionSupport_sound :
    ∀ {Λ : Region Atom} {j : ClauseId},
      j ∈ regionSupport Λ → clauseTouchesRegion (clauseData j).clause Λ
  regionSupport_complete :
    ∀ {Λ : Region Atom} {j : ClauseId},
      clauseTouchesRegion (clauseData j).clause Λ → j ∈ regionSupport Λ

namespace InfiniteGroundMLNSpec

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Finite-volume weight of a local assignment against a boundary condition. -/
noncomputable def finiteVolumeWeight
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (x : LocalAssignment Atom Λ) (ξ : BoundaryCondition Atom) :
    ENNReal :=
  Finset.prod (M.regionSupport Λ) (fun j => (M.clauseData j).eval (patch Λ x ξ))

theorem finiteVolumeWeight_ne_top
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (x : LocalAssignment Atom Λ) (ξ : BoundaryCondition Atom) :
    M.finiteVolumeWeight Λ x ξ ≠ ⊤ := by
  classical
  unfold finiteVolumeWeight
  exact ENNReal.prod_ne_top (by
    intro j hj
    exact WeightedGroundClause.eval_ne_top (M.clauseData j) (patch Λ x ξ))

/-- Partition function on a finite region with a fixed boundary condition. -/
noncomputable def finiteVolumePartition
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom) : ENNReal :=
  by
    classical
    exact Finset.sum Finset.univ (fun x => M.finiteVolumeWeight Λ x ξ)

/-- Infinite MLNs use the same finite conjunction query shape as the existing
finite MLN factor-graph bridge. -/
abbrev InfiniteConstraintQuery (Atom : Type*) := ConstraintQuery Atom

/-- Query interpretation for infinite worlds: finite atom-value constraints. -/
def infiniteConstraintQueryHolds {Atom : Type*} :
    InfiniteConstraintQuery Atom → InfiniteWorld Atom → Prop :=
  constraintQueryHolds

end InfiniteGroundMLNSpec

end Mettapedia.Logic.MarkovLogicInfiniteSpecification
