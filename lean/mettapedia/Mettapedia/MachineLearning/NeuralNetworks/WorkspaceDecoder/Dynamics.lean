import Mathlib.Tactic

/-!
# Gated workspace dynamics

This file formalizes the structural update shared by typed workspace decoders.
The results are algebraic: they cover state-dependent reads, transforms, gates,
and writes, but make no neural-network training or nonlinear settling claim.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function Set

universe uSlot uOperator uContent uRead uLatent

/-- A workspace assigns evolving content to every fixed slot address.  This is
structural data and carries no linear or nonlinear training interpretation. -/
abbrev Workspace (Slot : Type uSlot) (Content : Type uContent) := Slot → Content

/-- Reusable read-transform-gate-write operators.  Both the gate and written
content may depend on the current workspace.  The structural theorems below do
not assume that these components are linear or learned. -/
structure GatedOperatorFamily
    (Slot : Type uSlot) (Operator : Type uOperator) (Content : Type uContent)
    (Read : Type uRead) (Latent : Type uLatent) where
  read : Operator → Workspace Slot Content → Read
  transform : Operator → Read → Latent
  gate : Operator → Workspace Slot Content → Latent → Slot → ℝ
  write : Operator → Workspace Slot Content → Latent → Slot → Content

namespace GatedOperatorFamily

variable {Slot : Type uSlot} {Operator : Type uOperator}
  {Content : Type uContent} {Read : Type uRead} {Latent : Type uLatent}

/-- The transformed read used by one operator at the current workspace.  This
definition is structural and does not assert linearity. -/
def latent (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) (operator : Operator) : Latent :=
  family.transform operator (family.read operator workspace)

/-- The scalar gate used by one operator at one slot.  This definition is
structural and does not assert a learned calibration. -/
def gateAt (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) (operator : Operator) (slot : Slot) : ℝ :=
  family.gate operator workspace (family.latent workspace operator) slot

/-- The content proposed by one operator for one slot.  This definition is
structural and does not assert that the proposal is linear. -/
def contentAt (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) (operator : Operator) (slot : Slot) : Content :=
  family.write operator workspace (family.latent workspace operator) slot

section Dynamics

variable [operatorFintype : Fintype Operator]
  [operatorNonempty : Nonempty Operator]
  [contentNormedAddCommGroup : NormedAddCommGroup Content]
  [contentNormedSpace : NormedSpace ℝ Content]

/-- The exact `1 / K` scale, where `K` is the nonempty finite operator family.
This is the damping in the structural update, not a training-rate claim. -/
noncomputable def operatorAverageScale : ℝ :=
  ((Fintype.card Operator : ℝ)⁻¹)

/-- The average gate mass assigned to a slot at the current workspace.  It is
state-dependent in general and has no linear-model interpretation by itself. -/
noncomputable def aggregateGate
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) (slot : Slot) : ℝ :=
  operatorAverageScale (Operator := Operator) *
    ∑ operator, family.gateAt workspace operator slot

/-- The unnormalized average of gated proposed contents.  Separating it from
`aggregateGate` keeps the zero-gate case exact and avoids division by zero. -/
noncomputable def aggregateContent
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) (slot : Slot) : Content :=
  operatorAverageScale (Operator := Operator) •
    ∑ operator, family.gateAt workspace operator slot •
      family.contentAt workspace operator slot

/-- One simultaneous gated-interpolation step.  This is the full structural
update; settling and contraction claims are made only for later linear models. -/
noncomputable def step
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) : Workspace Slot Content :=
  fun slot => workspace slot +
    operatorAverageScale (Operator := Operator) •
      ∑ operator, family.gateAt workspace operator slot •
        (family.contentAt workspace operator slot - workspace slot)

omit operatorNonempty in
/-- Exact affine decomposition of one slot update.  Its coefficients sum to
one; convexity additionally requires unit-interval gates, proved below. -/
theorem step_eq_affineCombination
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) (slot : Slot) :
    family.step workspace slot =
      (1 - family.aggregateGate workspace slot) • workspace slot +
        family.aggregateContent workspace slot := by
  simp only [step, aggregateGate, aggregateContent]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [smul_sub, smul_smul]
  module

/-- Unit-interval gates are the exact condition used for the convexity and
non-expansiveness results; no distributional or training assumption is hidden. -/
def GatesUnitInterval
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) : Prop :=
  ∀ operator slot, family.gateAt workspace operator slot ∈ Icc (0 : ℝ) 1

omit contentNormedAddCommGroup contentNormedSpace in
/-- With unit-interval gates, the averaged gate mass is nonnegative.  This is
a structural convexity fact, not a nonlinear settling theorem. -/
theorem aggregateGate_nonneg
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content)
    (hgates : family.GatesUnitInterval workspace) (slot : Slot) :
    0 ≤ family.aggregateGate workspace slot := by
  apply mul_nonneg
  · exact inv_nonneg.mpr (by positivity)
  · exact Finset.sum_nonneg fun operator _ => (hgates operator slot).1

omit contentNormedAddCommGroup contentNormedSpace in
/-- With unit-interval gates, `K`-averaging keeps total gate mass at most one.
This is the missing condition that turns the affine update into a convex one. -/
theorem aggregateGate_le_one
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content)
    (hgates : family.GatesUnitInterval workspace) (slot : Slot) :
    family.aggregateGate workspace slot ≤ 1 := by
  have hsum : (∑ operator, family.gateAt workspace operator slot) ≤
      (Fintype.card Operator : ℝ) := by
    calc
      (∑ operator, family.gateAt workspace operator slot) ≤ ∑ _operator : Operator, (1 : ℝ) :=
        Finset.sum_le_sum fun operator _ => (hgates operator slot).2
      _ = (Fintype.card Operator : ℝ) := by simp
  have hcard : 0 < (Fintype.card Operator : ℝ) := by positivity
  rw [aggregateGate, operatorAverageScale]
  calc
    (Fintype.card Operator : ℝ)⁻¹ *
        ∑ operator, family.gateAt workspace operator slot ≤
        (Fintype.card Operator : ℝ)⁻¹ * (Fintype.card Operator : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcard.le)
    _ = 1 := inv_mul_cancel₀ hcard.ne'

omit operatorNonempty in
/-- Exact anchored form of the affine update.  It is the basis for the honest
non-expansiveness bound and remains valid without linearity. -/
theorem step_sub_anchor
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) (slot : Slot) (anchor : Content) :
    family.step workspace slot - anchor =
      (1 - family.aggregateGate workspace slot) • (workspace slot - anchor) +
        operatorAverageScale (Operator := Operator) •
          ∑ operator, family.gateAt workspace operator slot •
            (family.contentAt workspace operator slot - anchor) := by
  rw [step_eq_affineCombination]
  simp only [aggregateContent]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [smul_sub, smul_smul]
  rw [aggregateGate]
  module

/-- Convex-radius non-expansiveness: if the old content and every proposal lie
within radius `R` of an anchor, then the updated content also lies within `R`.
This is a one-step structural bound, not a claim that arbitrary state-dependent
workspace dynamics are contractive. -/
theorem step_norm_sub_anchor_le
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content)
    (hgates : family.GatesUnitInterval workspace)
    (slot : Slot) (anchor : Content) (radius : ℝ)
    (hold : ‖workspace slot - anchor‖ ≤ radius)
    (hproposals : ∀ operator,
      ‖family.contentAt workspace operator slot - anchor‖ ≤ radius) :
    ‖family.step workspace slot - anchor‖ ≤ radius := by
  have hgate_nonneg := family.aggregateGate_nonneg workspace hgates slot
  have hgate_le := family.aggregateGate_le_one workspace hgates slot
  have hscale_nonneg : 0 ≤ operatorAverageScale (Operator := Operator) :=
    inv_nonneg.mpr (by positivity)
  rw [family.step_sub_anchor workspace slot anchor]
  calc
    _ ≤ ‖(1 - family.aggregateGate workspace slot) • (workspace slot - anchor)‖ +
        ‖operatorAverageScale (Operator := Operator) •
          ∑ operator, family.gateAt workspace operator slot •
            (family.contentAt workspace operator slot - anchor)‖ := norm_add_le _ _
    _ ≤ (1 - family.aggregateGate workspace slot) * radius +
        operatorAverageScale (Operator := Operator) *
          ∑ operator, family.gateAt workspace operator slot * radius := by
      gcongr
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hgate_le)]
        exact mul_le_mul_of_nonneg_left hold (sub_nonneg.mpr hgate_le)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale_nonneg]
        apply mul_le_mul_of_nonneg_left _ hscale_nonneg
        calc
          ‖∑ operator, family.gateAt workspace operator slot •
              (family.contentAt workspace operator slot - anchor)‖ ≤
              ∑ operator, ‖family.gateAt workspace operator slot •
                (family.contentAt workspace operator slot - anchor)‖ := norm_sum_le _ _
          _ ≤ ∑ operator, family.gateAt workspace operator slot * radius := by
            apply Finset.sum_le_sum
            intro operator _
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (hgates operator slot).1]
            exact mul_le_mul_of_nonneg_left (hproposals operator)
              (hgates operator slot).1
    _ = radius := by
      rw [← Finset.sum_mul]
      rw [aggregateGate]
      ring

/-- A workspace is an equilibrium exactly when every slot's aggregate gated
proposal residual vanishes.  This structural characterization assumes neither
linearity nor convergence. -/
theorem step_eq_self_iff
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) :
    family.step workspace = workspace ↔
      ∀ slot, ∑ operator, family.gateAt workspace operator slot •
        (family.contentAt workspace operator slot - workspace slot) = 0 := by
  constructor
  · intro hstep slot
    have hslot := congrFun hstep slot
    simp only [step] at hslot
    have hscale : operatorAverageScale (Operator := Operator) ≠ 0 := by
      simp [operatorAverageScale, Fintype.card_ne_zero]
    exact (smul_eq_zero.mp (add_left_cancel (hslot.trans (add_zero _).symm))).resolve_left hscale
  · intro hzero
    funext slot
    simp [step, hzero slot]

omit operatorNonempty in
/-- If every operator gate is zero at a slot, one simultaneous update freezes
that fixed address.  This is the exact one-step gate-zero persistence lemma. -/
theorem step_eq_of_gates_zero
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) (slot : Slot)
    (hzero : ∀ operator, family.gateAt workspace operator slot = 0) :
    family.step workspace slot = workspace slot := by
  simp [step, hzero]

omit operatorNonempty in
/-- If a fixed slot's gates remain zero along the trajectory, its content is
constant at every recurrence depth.  The premise is explicit because arbitrary
state-dependent gates need not stay zero after other slots change. -/
theorem iterate_step_eq_of_gates_zero
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) (slot : Slot)
    (hzero : ∀ depth operator,
      family.gateAt (family.step^[depth] workspace) operator slot = 0) :
    ∀ depth, (family.step^[depth] workspace) slot = workspace slot := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [Function.iterate_succ_apply']
      rw [family.step_eq_of_gates_zero _ slot (hzero depth)]
      exact ih

end Dynamics

end GatedOperatorFamily

/-! ## Positive and negative structural fixtures -/

namespace DynamicsFixtures

/-- One slot and one reusable operator give the smallest nondegenerate fixture.
The fixture is structural and is not presented as a trained network. -/
abbrev One := Fin 1

/-- A scalar read-transform-write family whose gate is supplied by the caller.
It is a structural positive/negative example, not a nonlinear model claim. -/
noncomputable def scalarFamily (gate : ℝ) :
    GatedOperatorFamily One One ℝ ℝ ℝ where
  read := fun _ workspace => workspace 0
  transform := fun _ value => value
  gate := fun _ _ _ _ => gate
  write := fun _ _ _ _ => 3

/-- Positive example: a zero gate freezes the scalar slot exactly.  This is a
structural fixture and makes no training claim. -/
theorem zeroGate_freezes_positiveExample (workspace : Workspace One ℝ) :
    (scalarFamily 0).step workspace 0 = workspace 0 := by
  apply GatedOperatorFamily.step_eq_of_gates_zero
  intro operator
  fin_cases operator
  rfl

/-- Negative boundary: gate-zero is substantive; with gate one, a zero slot is
moved to the proposal.  This is not a claim about learned gates. -/
theorem unitGate_moves_negativeExample :
    (scalarFamily 1).step (fun _ => 0) 0 ≠ (0 : ℝ) := by
  norm_num [GatedOperatorFamily.step, GatedOperatorFamily.operatorAverageScale,
    scalarFamily, GatedOperatorFamily.gateAt, GatedOperatorFamily.contentAt,
    GatedOperatorFamily.latent]

end DynamicsFixtures

#print axioms GatedOperatorFamily.step_eq_affineCombination
#print axioms GatedOperatorFamily.step_norm_sub_anchor_le
#print axioms GatedOperatorFamily.step_eq_self_iff
#print axioms GatedOperatorFamily.iterate_step_eq_of_gates_zero
#print axioms DynamicsFixtures.zeroGate_freezes_positiveExample
#print axioms DynamicsFixtures.unitGate_moves_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
