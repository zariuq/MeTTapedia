import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Carom

/-!
# Softmax-routed CAROM: mixture and opacity

This file adds an explicit simplex-valued routing layer to the sealed CAROM
and `GatedOperatorFamily` spine.  Its scope is structural and linear-algebraic:
the router supplies finite simplex weights, while the expert gates and targets
are otherwise arbitrary.  No claim is made about how a nonlinear softmax,
normalization layer, or SwiGLU block learns those weights.

Routing does not add a new update family.  A simplex mixture of gated expert
increments collapses to one gated interpolation with the mixed gain and its
gain-weighted target.  Commands are observational only through the simplex
schedule they induce.  A separate triple-slot state makes immutable input
evidence and fixed per-slot parameters explicit while allowing the workspace
component to evolve under every route and recurrence depth.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function Set

universe uExpert uCommand uState uSlot uEvidence uFixed uContent

namespace RoutedCarom

/-! ## T1: simplex mixture reduction -/

/-- A finite routing distribution.  This is the exact algebraic interface of
a softmax output; no particular logits or temperature are assumed. -/
structure SimplexWeights (Expert : Type uExpert) [Fintype Expert] where
  weight : Expert → ℝ
  nonneg : ∀ expert, 0 ≤ weight expert
  sum_eq_one : ∑ expert, weight expert = 1

variable {Expert : Type uExpert} [Fintype Expert]

/-- The gain obtained after routing mixes the expert-specific gates. -/
noncomputable def mixedGain
    (routing : SimplexWeights Expert) (gain : Expert → ℝ) : ℝ :=
  ∑ expert, routing.weight expert * gain expert

/-- The unnormalized gain-weighted routed proposal. -/
noncomputable def mixedGainProposal
    {Content : Type uContent} [AddCommGroup Content] [Module ℝ Content]
    (routing : SimplexWeights Expert) (gain : Expert → ℝ)
    (proposal : Expert → Content) : Content :=
  ∑ expert, (routing.weight expert * gain expert) • proposal expert

/-- The routed gain-weighted target, used only when `mixedGain` is nonzero. -/
noncomputable def mixedGainWeightedTarget
    {Content : Type uContent} [AddCommGroup Content] [Module ℝ Content]
    (routing : SimplexWeights Expert) (gain : Expert → ℝ)
    (proposal : Expert → Content) : Content :=
  (mixedGain routing gain)⁻¹ • mixedGainProposal routing gain proposal

/-- One routed mixture of gated expert increments. -/
noncomputable def mixedExpertStep
    {Content : Type uContent} [AddCommGroup Content] [Module ℝ Content]
    (routing : SimplexWeights Expert) (gain : Expert → ℝ)
    (proposal : Expert → Content) (current : Content) : Content :=
  current + ∑ expert,
    (routing.weight expert * gain expert) • (proposal expert - current)

/-- Mixture-reduction crown: every nonzero simplex-routed expert mixture is
one member of the sealed gated-interpolation family.  Routing selects a point
in the simplex; it does not create a second update semantics. -/
theorem mixedExpertStep_eq_singleInterpolation
    {Content : Type uContent} [AddCommGroup Content] [Module ℝ Content]
    (routing : SimplexWeights Expert) (gain : Expert → ℝ)
    (proposal : Expert → Content) (current : Content)
    (hgain : mixedGain routing gain ≠ 0) :
    mixedExpertStep routing gain proposal current =
      current + mixedGain routing gain •
        (mixedGainWeightedTarget routing gain proposal - current) := by
  unfold mixedExpertStep mixedGainWeightedTarget mixedGainProposal
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  simp only [smul_smul]
  have hcancel :
      mixedGain routing gain * (mixedGain routing gain)⁻¹ = 1 :=
    mul_inv_cancel₀ hgain
  rw [hcancel, one_smul]
  unfold mixedGain
  module

/-- Simplex routing preserves the unit interval of the mixed gain whenever
every expert gain lies in that interval. -/
theorem mixedGain_mem_unitInterval
    (routing : SimplexWeights Expert) (gain : Expert → ℝ)
    (hgain : ∀ expert, gain expert ∈ Icc (0 : ℝ) 1) :
    mixedGain routing gain ∈ Icc (0 : ℝ) 1 := by
  constructor
  · unfold mixedGain
    exact Finset.sum_nonneg fun expert _ =>
      mul_nonneg (routing.nonneg expert) (hgain expert).1
  · unfold mixedGain
    calc
      (∑ expert, routing.weight expert * gain expert) ≤
          ∑ expert, routing.weight expert * 1 := by
        exact Finset.sum_le_sum fun expert _ =>
          mul_le_mul_of_nonneg_left (hgain expert).2 (routing.nonneg expert)
      _ = 1 := by simpa using routing.sum_eq_one

/-- Zero routed gain is a genuine boundary: if every expert gate is zero, the
mixture fixes the current content for every simplex point. -/
theorem mixedExpertStep_zeroGains
    {Content : Type uContent} [AddCommGroup Content] [Module ℝ Content]
    (routing : SimplexWeights Expert) (proposal : Expert → Content)
    (current : Content) :
    mixedExpertStep routing (fun _ => 0) proposal current = current := by
  simp [mixedExpertStep]

/-! ## T2(a): commands quotient through their routing image -/

/-- A finite mixture schedule is the discrete representation of a
piecewise-constant path through the routing simplex. -/
def commandMixtureSchedule
    {Command : Type uCommand} (route : Command → SimplexWeights Expert)
    (commands : List Command) : List (SimplexWeights Expert) :=
  commands.map route

/-- Full state trajectory generated by a finite mixture schedule. -/
def mixtureTrajectory
    {State : Type uState}
    (step : SimplexWeights Expert → State → State)
    (schedule : List (SimplexWeights Expert)) (initial : State) : List State :=
  List.scanl (fun state routing => step routing state) initial schedule

/-- Command trajectory obtained by first projecting commands to their routing
image. -/
def commandTrajectory
    {Command : Type uCommand} {State : Type uState}
    (route : Command → SimplexWeights Expert)
    (step : SimplexWeights Expert → State → State)
    (commands : List Command) (initial : State) : List State :=
  mixtureTrajectory step (commandMixtureSchedule route commands) initial

/-- Opacity crown: two command sequences with the same simplex schedule have
identical trajectories.  Command syntax is quotiented by its routing image. -/
theorem commandTrajectory_eq_of_mixtureSchedule_eq
    {Command : Type uCommand} {State : Type uState}
    (route : Command → SimplexWeights Expert)
    (step : SimplexWeights Expert → State → State)
    (first second : List Command) (initial : State)
    (hschedule : commandMixtureSchedule route first =
      commandMixtureSchedule route second) :
    commandTrajectory route step first initial =
      commandTrajectory route step second initial := by
  unfold commandTrajectory
  rw [hschedule]

/-! ## T2(b): immutable evidence and fixed parameters -/

/-- Per-slot state with immutable input evidence, fixed slot parameters, and
an evolving workspace register. -/
structure TripleSlotState
    (Slot : Type uSlot) (Evidence : Type uEvidence)
    (Fixed : Type uFixed) (Content : Type uContent) where
  evidence : Slot → Evidence
  fixed : Slot → Fixed
  workspace : Workspace Slot Content

/-- Update only the evolving workspace component. -/
def TripleSlotState.updateWorkspace
    {Slot : Type uSlot} {Evidence : Type uEvidence}
    {Fixed : Type uFixed} {Content : Type uContent}
    (next : Workspace Slot Content → Workspace Slot Content)
    (state : TripleSlotState Slot Evidence Fixed Content) :
    TripleSlotState Slot Evidence Fixed Content where
  evidence := state.evidence
  fixed := state.fixed
  workspace := next state.workspace

@[simp] theorem TripleSlotState.updateWorkspace_evidence
    {Slot : Type uSlot} {Evidence : Type uEvidence}
    {Fixed : Type uFixed} {Content : Type uContent}
    (next : Workspace Slot Content → Workspace Slot Content)
    (state : TripleSlotState Slot Evidence Fixed Content) :
    (state.updateWorkspace next).evidence = state.evidence := by
  rfl

@[simp] theorem TripleSlotState.updateWorkspace_fixed
    {Slot : Type uSlot} {Evidence : Type uEvidence}
    {Fixed : Type uFixed} {Content : Type uContent}
    (next : Workspace Slot Content → Workspace Slot Content)
    (state : TripleSlotState Slot Evidence Fixed Content) :
    (state.updateWorkspace next).fixed = state.fixed := by
  rfl

/-- Run an arbitrary routed schedule while changing only workspace contents. -/
def runTripleSlotSchedule
    {Slot : Type uSlot} {Evidence : Type uEvidence}
    {Fixed : Type uFixed} {Content : Type uContent}
    (step : SimplexWeights Expert →
      Workspace Slot Content → Workspace Slot Content)
    (schedule : List (SimplexWeights Expert))
    (initial : TripleSlotState Slot Evidence Fixed Content) :
    TripleSlotState Slot Evidence Fixed Content :=
  schedule.foldl
    (fun state routing => state.updateWorkspace (step routing)) initial

/-- Evidence-retention crown for arbitrary expert behavior, routes, schedules,
and schedule lengths. -/
theorem runTripleSlotSchedule_evidence
    {Slot : Type uSlot} {Evidence : Type uEvidence}
    {Fixed : Type uFixed} {Content : Type uContent}
    (step : SimplexWeights Expert →
      Workspace Slot Content → Workspace Slot Content)
    (schedule : List (SimplexWeights Expert))
    (initial : TripleSlotState Slot Evidence Fixed Content) :
    (runTripleSlotSchedule step schedule initial).evidence = initial.evidence := by
  induction schedule generalizing initial with
  | nil => rfl
  | cons routing schedule ih =>
      simpa [runTripleSlotSchedule] using
        ih (initial := initial.updateWorkspace (step routing))

/-- Fixed-parameter retention under the same unrestricted routed schedule. -/
theorem runTripleSlotSchedule_fixed
    {Slot : Type uSlot} {Evidence : Type uEvidence}
    {Fixed : Type uFixed} {Content : Type uContent}
    (step : SimplexWeights Expert →
      Workspace Slot Content → Workspace Slot Content)
    (schedule : List (SimplexWeights Expert))
    (initial : TripleSlotState Slot Evidence Fixed Content) :
    (runTripleSlotSchedule step schedule initial).fixed = initial.fixed := by
  induction schedule generalizing initial with
  | nil => rfl
  | cons routing schedule ih =>
      simpa [runTripleSlotSchedule] using
        ih (initial := initial.updateWorkspace (step routing))

/-- Depth-indexed form of unconditional evidence retention for a fixed routed
step.  The step itself remains arbitrary. -/
theorem iterate_updateWorkspace_evidence
    {Slot : Type uSlot} {Evidence : Type uEvidence}
    {Fixed : Type uFixed} {Content : Type uContent}
    (next : Workspace Slot Content → Workspace Slot Content)
    (initial : TripleSlotState Slot Evidence Fixed Content) (depth : ℕ) :
    ((TripleSlotState.updateWorkspace next)^[depth] initial).evidence =
      initial.evidence := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [Function.iterate_succ_apply']
      simpa using ih

/-! ## Positive and negative fixtures -/

/-- Equal routing over two experts. -/
noncomputable def halfRouting : SimplexWeights (Fin 2) where
  weight := fun _ => 1 / 2
  nonneg := by intro; norm_num
  sum_eq_one := by norm_num [Fin.sum_univ_two]

/-- Positive fixture: equal routing, half gates, and targets one and three move
zero to one. -/
theorem halfRouting_mixedStep_positiveExample :
    mixedExpertStep halfRouting (fun _ : Fin 2 => 1 / 2)
      (fun expert => if expert = 0 then (1 : ℝ) else 3) 0 = 1 := by
  norm_num [mixedExpertStep, halfRouting, Fin.sum_univ_two]

/-- Negative fixture: distinct command constructors are opaque when the router
maps both to the same simplex point. -/
theorem commandOpacity_negativeExample :
    commandTrajectory (fun _ : Bool => halfRouting)
        (fun (_routing : SimplexWeights (Fin 2)) (state : ℕ) => state + 1)
        [false] 0 =
      commandTrajectory (fun _ : Bool => halfRouting)
        (fun (_routing : SimplexWeights (Fin 2)) (state : ℕ) => state + 1)
        [true] 0 := by
  apply commandTrajectory_eq_of_mixtureSchedule_eq
  rfl

#print axioms mixedExpertStep_eq_singleInterpolation
#print axioms mixedGain_mem_unitInterval
#print axioms commandTrajectory_eq_of_mixtureSchedule_eq
#print axioms runTripleSlotSchedule_evidence
#print axioms iterate_updateWorkspace_evidence

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
