import Mettapedia.Algebra.MatrixAffineSummary
import Mettapedia.GSLT.Dynamics.LinearBoundaryReduction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Compiling equilibrium boundaries into existing affine summaries

Forward affine composition and solving an implicit affine feedback equation
are different operations. This module admits feedback only when its internal
coefficient has an inverse, and compiles the resulting boundary function into
the existing affine algebra. The general linear reduction is also realized
as an `AffineAction`, rather than introducing another summary representation.

The source observation is the equilibrium relation. Finite trajectories are
not identified with equilibrium, and a unique equilibrium does not imply
convergence of iteration. Exact rational controls include a coupled internal
system, singular feedback and a divergent iteration.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.AffineBoundaryFeedback

open Mettapedia.Algebra
open LinearBoundaryReduction

variable {K : Type*} [Field K]
variable {Boundary : Type*} [AddCommGroup Boundary] [Module K Boundary]
variable {Interior : Type*} [AddCommGroup Interior] [Module K Interior]

/-- A reduced linear region uses the same additive affine action as folds. -/
def boundaryAction (system : System K Boundary Interior) (forcing : Interior) :
    AffineAction Boundary where
  linear := system.schur.toAddMonoidHom
  offset := system.outward (system.internalBlock.symm forcing)

theorem boundaryAction_exact (system : System K Boundary Interior)
    (forcing : Interior) (input response : Boundary) :
    system.fullRelation input response forcing ↔
      (boundaryAction system forcing).act input = response := by
  exact system.fullRelation_iff input response forcing

/-- An implicit one-port region: its output feeds back into its own equation. -/
structure Feedback (K : Type*) where
  loopGain : K
  inputGain : K
  bias : K
  deriving DecidableEq, Repr

namespace Feedback

def relation (region : Feedback K) (input output : K) : Prop :=
  output = region.loopGain * output + region.inputGain * input + region.bias

/-- The coefficients of the eliminated boundary; admission is separate. -/
def summary (region : Feedback K) : AffineSummary K :=
  ⟨region.inputGain / (1 - region.loopGain), region.bias / (1 - region.loopGain)⟩

def compile? [DecidableEq K] (region : Feedback K) : Option (AffineSummary K) :=
  if region.loopGain = 1 then none else some region.summary

theorem relation_iff (region : Feedback K) (admitted : region.loopGain ≠ 1)
    (input output : K) :
    region.relation input output ↔ region.summary.act input = output := by
  have denominator : 1 - region.loopGain ≠ 0 := sub_ne_zero.mpr (Ne.symm admitted)
  simp only [relation, summary, AffineSummary.act]
  constructor
  · intro solves
    field_simp [denominator]
    linear_combination -solves
  · intro solved
    field_simp [denominator] at solved
    linear_combination -solved

theorem compile_sound [DecidableEq K] (region : Feedback K)
    (out : AffineSummary K) (compiled : region.compile? = some out)
    (input output : K) :
    region.relation input output ↔ out.act input = output := by
  unfold compile? at compiled
  split at compiled
  · contradiction
  · rename_i admitted
    cases compiled
    exact region.relation_iff admitted input output

theorem unique_solution (region : Feedback K) (admitted : region.loopGain ≠ 1)
    (input : K) : ∃! output, region.relation input output := by
  refine ⟨region.summary.act input, (region.relation_iff admitted _ _).mpr rfl, ?_⟩
  intro output solves
  exact ((region.relation_iff admitted _ _).mp solves).symm

/-- A solved feedback component can be composed using the existing forward
summary operation, with the order explicitly retained. -/
theorem then_affine (region : Feedback K) (admitted : region.loopGain ≠ 1)
    (after : AffineSummary K) (input response : K) :
    (∃ output, region.relation input output ∧ after.act output = response) ↔
      (region.summary.compose after).act input = response := by
  simp only [region.relation_iff admitted, AffineSummary.act_compose]
  simp

end Feedback

/-! ## A coupled two-variable equilibrium, compiled to the old matrix summary -/

/-- The two unknown outputs depend on each other, rather than being updates
in an already selected evaluation order. -/
def coupledRelation (input output : Fin 2 → ℚ) : Prop :=
  output 0 = input 0 + output 1 / 2 ∧
  output 1 = input 1 + output 0 / 3

def coupledSummary : MatrixAffineSummary (Fin 2) ℚ :=
  ⟨!![(6 : ℚ) / 5, 3 / 5; 2 / 5, 6 / 5], 0⟩

theorem coupled_equilibrium_exact (input output : Fin 2 → ℚ) :
    coupledRelation input output ↔ coupledSummary.act input = output := by
  constructor
  · rintro ⟨first, second⟩
    ext position
    fin_cases position <;>
      simp [coupledSummary, MatrixAffineSummary.act,
        dotProduct, Fin.sum_univ_two] <;> linarith
  · intro solved
    rw [← solved]
    simp only [coupledRelation, coupledSummary, MatrixAffineSummary.act,
      Pi.add_apply, Pi.zero_apply, add_zero, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    norm_num
    constructor <;> ring

theorem coupled_solution_example :
    coupledRelation ![1, 0] ![(6 : ℚ) / 5, 2 / 5] := by
  norm_num [coupledRelation]

/-- Same first input, different second input: retaining just the first port
cannot determine the first response. -/
theorem coupling_requires_other_port :
    (![0, 0] : Fin 2 → ℚ) 0 = (![0, 1] : Fin 2 → ℚ) 0 ∧
    (coupledSummary.act ![0, 0]) 0 ≠ (coupledSummary.act ![0, 1]) 0 := by
  norm_num [coupledSummary, MatrixAffineSummary.act, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

namespace Controls

theorem singular_inconsistent :
    ¬ ∃ output : ℚ, (Feedback.mk 1 0 1).relation 0 output := by
  simp [Feedback.relation]

theorem singular_nonunique :
    (Feedback.mk 1 0 0 : Feedback ℚ).relation 0 0 ∧
      (Feedback.mk 1 0 0 : Feedback ℚ).relation 0 1 := by
  norm_num [Feedback.relation]

theorem finite_iteration_is_not_equilibrium :
    AffineSummary.run (List.replicate 2 (⟨1 / 2, 1⟩ : AffineSummary ℚ)) 0 = 3 / 2 ∧
    (Feedback.mk (1 / 2) 0 1 : Feedback ℚ).summary.act 0 = 2 := by
  norm_num [AffineSummary.run, List.replicate_succ, AffineSummary.act,
    Feedback.summary]

/-- A unique static solution exists, although every finite iteration from
zero is nonnegative and therefore fails to reach it. -/
theorem unstable_feedback_negative_equilibrium :
    (Feedback.mk 2 0 1 : Feedback ℚ).relation 0 (-1) := by
  norm_num [Feedback.relation]

theorem unstable_iterations_nonnegative (count : Nat) (initial : ℚ)
    (nonnegative : 0 ≤ initial) :
    0 ≤ AffineSummary.run (List.replicate count (⟨2, 1⟩ : AffineSummary ℚ)) initial := by
  induction count generalizing initial with
  | zero => simpa [AffineSummary.run] using nonnegative
  | succ count ih =>
    simp only [List.replicate_succ, AffineSummary.run, List.foldl_cons]
    apply ih
    simp only [AffineSummary.act]
    linarith

theorem unstable_iteration_ne_equilibrium (count : Nat) :
    AffineSummary.run (List.replicate count (⟨2, 1⟩ : AffineSummary ℚ)) 0 ≠ -1 := by
  have bound := unstable_iterations_nonnegative count 0 (by norm_num)
  linarith

end Controls
end Mettapedia.GSLT.Dynamics.AffineBoundaryFeedback
