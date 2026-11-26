import Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures

/-! # Change of variables for finite-volume distributions -/

set_option autoImplicit false

namespace Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume

open MarkovLogicAbstract MarkovLogicClauseFactorGraph MarkovLogicInfiniteSpecification
open MarkovLogicInfiniteWorldMeasures

/-- A recoding of local assignments which preserves the weight of each assignment. -/
structure AssignmentTransport {A B C D : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (M : InfiniteGroundMLNSpec A C) (Λ : Region A) (ξ : BoundaryCondition A)
    (N : InfiniteGroundMLNSpec B D) (Δ : Region B) (η : BoundaryCondition B) where
  assignments : LocalAssignment A Λ ≃ LocalAssignment B Δ
  weight_eq : ∀ x, N.finiteVolumeWeight Δ (assignments x) η = M.finiteVolumeWeight Λ x ξ

namespace AssignmentTransport

variable {A B C D : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
variable {M : InfiniteGroundMLNSpec A C} {Λ : Region A} {ξ : BoundaryCondition A}
variable {N : InfiniteGroundMLNSpec B D} {Δ : Region B} {η : BoundaryCondition B}

/-- A pullback of clause indices establishes transport when the active supports
and all potentials on those supports agree. -/
def ofClauseReindex (assignments : LocalAssignment A Λ ≃ LocalAssignment B Δ)
    (clauses : D ≃ C) (support : ∀ c, c ∈ N.regionSupport Δ ↔ clauses c ∈ M.regionSupport Λ)
    (potential : ∀ x c, c ∈ N.regionSupport Δ →
      (N.clauseData c).eval (patch Δ (assignments x) η) =
        (M.clauseData (clauses c)).eval (patch Λ x ξ)) : AssignmentTransport M Λ ξ N Δ η where
  assignments := assignments
  weight_eq x := by
    unfold InfiniteGroundMLNSpec.finiteVolumeWeight
    exact Finset.prod_equiv clauses support (potential x)

theorem partition_eq (t : AssignmentTransport M Λ ξ N Δ η) :
    N.finiteVolumePartition Δ η = M.finiteVolumePartition Λ ξ := by
  classical
  unfold InfiniteGroundMLNSpec.finiteVolumePartition
  exact (Fintype.sum_equiv t.assignments _ _ (fun x => (t.weight_eq x).symm)).symm

/-- Query events must be transported along with assignment weights. -/
theorem queryMass_eq (t : AssignmentTransport M Λ ξ N Δ η)
    {q : LocalConstraintQuery A Λ} {r : LocalConstraintQuery B Δ}
    (event : ∀ x, satisfiesConstraints (t.assignments x) r ↔ satisfiesConstraints x q) :
    finiteVolumeQueryMass N Δ η r = finiteVolumeQueryMass M Λ ξ q := by
  classical
  unfold finiteVolumeQueryMass
  symm
  refine Fintype.sum_equiv t.assignments _ _ (fun x => ?_)
  simp only [event x, t.weight_eq x]

theorem queryProb_eq (t : AssignmentTransport M Λ ξ N Δ η)
    {q : LocalConstraintQuery A Λ} {r : LocalConstraintQuery B Δ}
    (event : ∀ x, satisfiesConstraints (t.assignments x) r ↔ satisfiesConstraints x q) :
    (finiteVolumeMassSemantics N Δ η).queryProb r =
      (finiteVolumeMassSemantics M Λ ξ).queryProb q := by
  unfold Mettapedia.ProbabilityTheory.MassSemantics.queryProb finiteVolumeMassSemantics
  dsimp only
  simp only [t.queryMass_eq event, t.partition_eq]

theorem assignmentPMF_apply (t : AssignmentTransport M Λ ξ N Δ η)
    (source_nonzero : M.finiteVolumePartition Λ ξ ≠ 0)
    (target_nonzero : N.finiteVolumePartition Δ η ≠ 0) (x : LocalAssignment A Λ) :
    finiteVolumeAssignmentPMF N Δ η target_nonzero (t.assignments x) =
      finiteVolumeAssignmentPMF M Λ ξ source_nonzero x := by
  simp only [finiteVolumeAssignmentPMF_apply, t.weight_eq x, t.partition_eq]

end AssignmentTransport

theorem toReal_eq_one_sub_of_add_eq_one {a b : ENNReal} (h : a + b = 1) :
    b.toReal = 1 - a.toReal := by
  have finite : a + b ≠ ⊤ := by simp [h]
  obtain ⟨ha, hb⟩ := ENNReal.add_ne_top.mp finite
  have sum : a.toReal + b.toReal = 1 := by
    simpa only [ENNReal.toReal_add ha hb, ENNReal.toReal_one] using congrArg ENNReal.toReal h
  linarith

end Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
