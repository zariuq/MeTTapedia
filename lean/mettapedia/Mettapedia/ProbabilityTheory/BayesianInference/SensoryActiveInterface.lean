import Mettapedia.ProbabilityTheory.BayesianInference.BlanketFactorization
import Mettapedia.ProbabilityTheory.BayesianInference.SufficientFiltering

/-!
# Sensory readings and active interventions

A world is an external bit, a blanket bit, and an internal bit. The sensory
reading is the first two coordinates. A fork law on those three coordinates is
conditionally independent, and that static fact is not a hypothesis of the
controlled kernels below.

`copyInternal` keeps the current sensory reading and writes the internal bit
into the next external bit, so the sensory reading is not strongly lumpable.
`intervene` and `applyAction` are separate kernels. Each next sensory reading
depends only on the action and the current sensory reading, and prediction and
filtering commute with that reading.
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference.SensoryActive

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.FiniteLumpability
open Mettapedia.ProbabilityTheory.BayesianInference.FiniteMarkovBlanket

/-- External, blanket, and internal coordinates, in that order. -/
abbrev World := Bool × Bool × Bool

/-- The sensory reading drops the internal coordinate. -/
def sensory (world : World) : Bool × Bool :=
  (world.1, world.2.1)

/-- One world in each sensory fibre, with the internal bit cleared. -/
def sensoryRep (reading : Bool × Bool) : World :=
  (reading.1, reading.2, false)

theorem sensory_section : Function.RightInverse sensoryRep sensory :=
  fun _ => rfl

/-- The active reset writes the chosen external bit and clears the rest. -/
def clearWorld (action : Bool) : World :=
  (action, false, false)

def intervene (action : Bool) : World → Prob World :=
  fun _ => dirac (clearWorld action)

/-- The active write sets the external bit and keeps the blanket and internal bits. -/
def writeExternal (action : Bool) (world : World) : World :=
  (action, world.2.1, world.2.2)

def applyAction (action : Bool) (world : World) : Prob World :=
  dirac (writeExternal action world)

/-- The internal bit becomes the next external bit. The blanket is unchanged. -/
def copyInternal (_ : Unit) (world : World) : Prob World :=
  dirac (world.2.2, world.2.1, world.2.2)

/-- Emission that reads the blanket bit of a sensory reading. -/
def blanketEmission (reading : Bool × Bool) : ℝ :=
  if reading.2 then 1 else 0

theorem blanketEmission_nonneg (reading : Bool × Bool) : 0 ≤ blanketEmission reading := by
  unfold blanketEmission
  split_ifs <;> norm_num

theorem bind_dirac {S C : Type*} [Fintype S] [Fintype C] [DecidableEq S]
    (state : S) (kernel : S → Prob C) :
    bind (dirac state) kernel = kernel state := by
  apply Subtype.ext
  funext outcome
  rw [bind_apply]
  exact expectation_dirac state fun source => (kernel source).1 outcome

theorem evidence_dirac {S : Type*} [Fintype S] [DecidableEq S]
    (state : S) (likelihood : S → ℝ) :
    evidence (dirac state) likelihood = likelihood state :=
  expectation_dirac state likelihood

theorem bind_const_dirac {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]
    (prior : Prob S) (point : C) :
    bind prior (fun _ => dirac point) = dirac point := by
  apply Subtype.ext
  funext outcome
  simp only [bind_apply, dirac_apply, mul_ite, mul_one, mul_zero]
  by_cases same : outcome = point
  · simp [same, prior.2.2]
  · simp [same]

theorem copy_same_sensory :
    sensory (false, true, false) = sensory (false, true, true) :=
  rfl

theorem copy_splits_future :
    coarsen (copyInternal () (false, true, false)) sensory ≠
      coarsen (copyInternal () (false, true, true)) sensory := by
  unfold copyInternal
  rw [coarsen_dirac, coarsen_dirac]
  unfold sensory
  intro same
  have mass := congrArg (fun law : Prob (Bool × Bool) => law.1 (false, true)) same
  simp [dirac_apply] at mass

theorem copy_not_lumpable : ¬ StrongLumpability sensory copyInternal := by
  intro lumpable
  exact copy_splits_future
    (lumpable () (false, true, false) (false, true, true) copy_same_sensory)

/-- A fork law is conditionally independent for every choice of its factors.
The copy kernel on the same carrier is still not strongly lumpable. -/
theorem conditional_independence_does_not_give_lumpability
    (blanket : Prob Bool) (external internal : Bool → Prob Bool) :
    CondIndep (forkLaw blanket external internal).1 Prod.fst
        (fun world : World => world.2.1) (fun world : World => world.2.2) ∧
      ¬ StrongLumpability sensory copyInternal :=
  ⟨fork_conditionalIndependent blanket external internal, copy_not_lumpable⟩

theorem intervene_lumpable : StrongLumpability sensory intervene := by
  intro action _world _other _
  unfold intervene
  rfl

theorem apply_lumpable : StrongLumpability sensory applyAction := by
  intro action source target same
  unfold applyAction writeExternal
  rw [coarsen_dirac, coarsen_dirac]
  unfold sensory
  have blanket : source.2.1 = target.2.1 := (Prod.ext_iff.mp same).2
  rw [blanket]

theorem intervene_lumped (action : Bool) :
    lumpedKernel sensory intervene sensoryRep action =
      fun _reading => dirac (action, false) := by
  funext _reading
  unfold lumpedKernel intervene
  rw [coarsen_dirac]
  unfold clearWorld sensory
  rfl

theorem apply_lumped (action : Bool) :
    lumpedKernel sensory applyAction sensoryRep action =
      fun reading => dirac (action, reading.2) := by
  funext reading
  unfold lumpedKernel applyAction
  rw [coarsen_dirac]
  unfold sensoryRep writeExternal sensory
  rfl

theorem intervention_prediction (prior : Prob World) (action : Bool) :
    coarsen (bind prior (intervene action)) sensory = dirac (action, false) := by
  rw [coarsen_predict sensory intervene sensoryRep sensory_section intervene_lumpable,
    intervene_lumped, bind_const_dirac]

theorem apply_prediction (prior : Prob World) (action : Bool) :
    coarsen (bind prior (applyAction action)) sensory =
      bind (coarsen prior sensory) (fun reading => dirac (action, reading.2)) := by
  rw [coarsen_predict sensory applyAction sensoryRep sensory_section apply_lumpable,
    apply_lumped]

theorem intervention_filter (prior : Prob World) (action : Bool)
    (likelihood : Bool × Bool → ℝ) (nonneg : ∀ reading, 0 ≤ likelihood reading)
    (possible : 0 < evidence (bind prior (intervene action)) (likelihood ∘ sensory)) :
    coarsen (posterior (bind prior (intervene action)) (likelihood ∘ sensory)
        (fun world => nonneg (sensory world)) possible) sensory =
      posterior (bind (coarsen prior sensory)
          (lumpedKernel sensory intervene sensoryRep action))
        likelihood nonneg
        (by
          rw [← coarsen_predict sensory intervene sensoryRep sensory_section
              intervene_lumpable,
            evidence_coarsen]
          exact possible) :=
  coarsen_filter_step sensory intervene sensoryRep sensory_section intervene_lumpable
    prior action likelihood nonneg possible

theorem apply_filter (prior : Prob World) (action : Bool)
    (likelihood : Bool × Bool → ℝ) (nonneg : ∀ reading, 0 ≤ likelihood reading)
    (possible : 0 < evidence (bind prior (applyAction action)) (likelihood ∘ sensory)) :
    coarsen (posterior (bind prior (applyAction action)) (likelihood ∘ sensory)
        (fun world => nonneg (sensory world)) possible) sensory =
      posterior (bind (coarsen prior sensory)
          (lumpedKernel sensory applyAction sensoryRep action))
        likelihood nonneg
        (by
          rw [← coarsen_predict sensory applyAction sensoryRep sensory_section
              apply_lumpable,
            evidence_coarsen]
          exact possible) :=
  coarsen_filter_step sensory applyAction sensoryRep sensory_section apply_lumpable
    prior action likelihood nonneg possible

theorem zero_emission_evidence (law : Prob World) :
    evidence law (fun _ => (0 : ℝ)) = 0 := by
  simp [evidence]

theorem zero_emission_blocks_filter (law : Prob World)
    (possible : 0 < evidence law (fun _ => (0 : ℝ))) : False := by
  rw [zero_emission_evidence] at possible
  exact lt_irrefl 0 possible

theorem cleared_blanket_has_no_emission (action : Bool) :
    evidence (bind (dirac (false, true, true)) (intervene action))
        (blanketEmission ∘ sensory) =
      0 := by
  rw [bind_dirac, intervene, evidence_dirac]
  simp [blanketEmission, sensory, clearWorld]

theorem cleared_blanket_blocks_filter (action : Bool)
    (possible : 0 < evidence (bind (dirac (false, true, true)) (intervene action))
      (blanketEmission ∘ sensory)) : False := by
  rw [cleared_blanket_has_no_emission] at possible
  exact lt_irrefl 0 possible

theorem retained_blanket_has_emission :
    evidence (bind (dirac (false, true, true)) (applyAction true))
        (blanketEmission ∘ sensory) =
      1 := by
  rw [bind_dirac, applyAction, evidence_dirac]
  simp [blanketEmission, sensory, writeExternal]

theorem same_sensory_distinct_internal :
    sensory (false, true, false) = sensory (false, true, true) ∧
      (false, true, false).2.2 ≠ (false, true, true).2.2 :=
  ⟨rfl, by decide⟩

theorem internal_not_determined_by_sensory :
    ¬ ∀ source target : World, sensory source = sensory target →
        source.2.2 = target.2.2 := by
  intro determined
  exact Bool.false_ne_true
    (determined (false, true, false) (false, true, true) rfl)

end Mettapedia.ProbabilityTheory.BayesianInference.SensoryActive
