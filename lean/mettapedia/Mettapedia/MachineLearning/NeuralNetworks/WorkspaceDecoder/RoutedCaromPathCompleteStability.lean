import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromNonlinearStability

/-!
# Routed CAROM: path-complete regional stability

A common-center Lyapunov function certifies convergence toward one state, so
it cannot by itself express an itinerary through distinct phase centers.  A
path-complete certificate instead assigns a region, center, and energy to each
phase.  Every licensed labeled edge maps its source region into its target
region and contracts the target energy relative to the source energy.

The results below are finite and schedule-explicit.  They do not discover the
phase graph from data, certify an unlisted edge, or infer a continuous-time
metastable channel.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Function Set

namespace RoutedCarom

universe uPhase uCommand uState uObservation

variable {Phase : Type uPhase} {Command : Type uCommand}
  {State : Type uState} [NormedAddCommGroup State]

/-- A phase-indexed regional Lyapunov certificate for a labeled transition
graph.  The common rate is required only on licensed graph edges. -/
structure PathCompleteRegionalLyapunov
    (transition : Command → State → State)
    (center : Phase → State) (region : Phase → Set State)
    (allowed : Phase → Command → Phase → Prop) where
  energy : Phase → State → ℝ
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  rate_lt_one : rate < 1
  coercivity : Phase → ℝ
  coercivity_pos : ∀ phase, 0 < coercivity phase
  center_mem : ∀ phase, center phase ∈ region phase
  energy_nonneg : ∀ phase state, state ∈ region phase →
    0 ≤ energy phase state
  energy_controls_distance : ∀ phase state, state ∈ region phase →
    coercivity phase * ‖state - center phase‖ ^ 2 ≤ energy phase state
  maps_region : ∀ {source target} command state,
    allowed source command target → state ∈ region source →
      transition command state ∈ region target
  contracts : ∀ {source target} command state,
    allowed source command target → state ∈ region source →
      energy target (transition command state) ≤ rate * energy source state

/-- One labeled edge request in a finite phase path.  Its source is supplied
by the preceding phase, preventing a disconnected list of triples. -/
structure PhasePathStep (Phase : Type uPhase) (Command : Type uCommand) where
  command : Command
  next : Phase

/-- The labeled path follows only graph edges licensed by the certificate. -/
def PathCompleteRegionalLyapunov.PathAdmissible
    {transition : Command → State → State}
    {center : Phase → State} {region : Phase → Set State}
    {allowed : Phase → Command → Phase → Prop}
    (certificate : PathCompleteRegionalLyapunov transition center region allowed) :
    Phase → List (PhasePathStep Phase Command) → Prop
  | _, [] => True
  | phase, step :: steps =>
      allowed phase step.command step.next ∧
        certificate.PathAdmissible step.next steps

/-- Final phase reached by a path. -/
def finalPathPhase : Phase → List (PhasePathStep Phase Command) → Phase
  | phase, [] => phase
  | _, step :: steps => finalPathPhase step.next steps

/-- Runtime state after all labeled transitions in a path. -/
def runPhasePath (transition : Command → State → State) :
    State → List (PhasePathStep Phase Command) → State
  | state, [] => state
  | state, step :: steps =>
      runPhasePath transition (transition step.command state) steps

/-- Runtime endpoint after every labeled edge. -/
def runPhasePathStates (transition : Command → State → State) :
    State → List (PhasePathStep Phase Command) → List State
  | _, [] => []
  | state, step :: steps =>
      let nextState := transition step.command state
      nextState :: runPhasePathStates transition nextState steps

/-- Declared target center after every labeled edge. -/
def phaseCenterTrajectory (center : Phase → State) :
    List (PhasePathStep Phase Command) → List State
  | [] => []
  | step :: steps => center step.next :: phaseCenterTrajectory center steps

/-- Every admissible path endpoint remains in its final phase region. -/
theorem PathCompleteRegionalLyapunov.runPhasePath_mem
    {transition : Command → State → State}
    {center : Phase → State} {region : Phase → Set State}
    {allowed : Phase → Command → Phase → Prop}
    (certificate : PathCompleteRegionalLyapunov transition center region allowed)
    (phase : Phase) (initial : State)
    (steps : List (PhasePathStep Phase Command))
    (hinitial : initial ∈ region phase)
    (hadmissible : certificate.PathAdmissible phase steps) :
    runPhasePath transition initial steps ∈ region (finalPathPhase phase steps) := by
  induction steps generalizing phase initial with
  | nil => simpa [runPhasePath, finalPathPhase] using hinitial
  | cons step steps ih =>
      rcases hadmissible with ⟨hedge, htail⟩
      exact ih step.next (transition step.command initial)
        (certificate.maps_region step.command initial hedge hinitial) htail

/-- A path-complete certificate gives one geometric energy envelope along
every admissible finite labeled path, even though the energy changes by phase. -/
theorem PathCompleteRegionalLyapunov.runPhasePath_energy_le
    {transition : Command → State → State}
    {center : Phase → State} {region : Phase → Set State}
    {allowed : Phase → Command → Phase → Prop}
    (certificate : PathCompleteRegionalLyapunov transition center region allowed)
    (phase : Phase) (initial : State)
    (steps : List (PhasePathStep Phase Command))
    (hinitial : initial ∈ region phase)
    (hadmissible : certificate.PathAdmissible phase steps) :
    certificate.energy (finalPathPhase phase steps)
        (runPhasePath transition initial steps) ≤
      certificate.rate ^ steps.length * certificate.energy phase initial := by
  induction steps generalizing phase initial with
  | nil => simp [runPhasePath, finalPathPhase]
  | cons step steps ih =>
      rcases hadmissible with ⟨hedge, htail⟩
      have hnext : transition step.command initial ∈ region step.next :=
        certificate.maps_region step.command initial hedge hinitial
      calc
        certificate.energy (finalPathPhase phase (step :: steps))
            (runPhasePath transition initial (step :: steps)) =
            certificate.energy (finalPathPhase step.next steps)
              (runPhasePath transition (transition step.command initial) steps) := rfl
        _ ≤ certificate.rate ^ steps.length *
              certificate.energy step.next (transition step.command initial) :=
          ih step.next (transition step.command initial) hnext htail
        _ ≤ certificate.rate ^ steps.length *
              (certificate.rate * certificate.energy phase initial) :=
          mul_le_mul_of_nonneg_left
            (certificate.contracts step.command initial hedge hinitial)
            (pow_nonneg certificate.rate_nonneg _)
        _ = certificate.rate ^ (step :: steps).length *
              certificate.energy phase initial := by
          simp [pow_succ, mul_assoc]

/-- Phase-specific coercivity converts the final energy envelope into a
distance bound around the final phase center. -/
theorem PathCompleteRegionalLyapunov.runPhasePath_distance_sq_le
    {transition : Command → State → State}
    {center : Phase → State} {region : Phase → Set State}
    {allowed : Phase → Command → Phase → Prop}
    (certificate : PathCompleteRegionalLyapunov transition center region allowed)
    (phase : Phase) (initial : State)
    (steps : List (PhasePathStep Phase Command))
    (hinitial : initial ∈ region phase)
    (hadmissible : certificate.PathAdmissible phase steps) :
    certificate.coercivity (finalPathPhase phase steps) *
        ‖runPhasePath transition initial steps -
          center (finalPathPhase phase steps)‖ ^ 2 ≤
      certificate.rate ^ steps.length * certificate.energy phase initial := by
  exact le_trans
    (certificate.energy_controls_distance _ _
      (certificate.runPhasePath_mem phase initial steps hinitial hadmissible))
    (certificate.runPhasePath_energy_le phase initial steps hinitial hadmissible)

/-- Recursive per-handoff observation budgets for an admissible phase path. -/
def PathCompleteRegionalLyapunov.PathBudgetAdmissible
    {transition : Command → State → State}
    {center : Phase → State} {region : Phase → Set State}
    {allowed : Phase → Command → Phase → Prop}
    (certificate : PathCompleteRegionalLyapunov transition center region allowed)
    (margin : Phase → ℝ) :
    Phase → ℝ → List (PhasePathStep Phase Command) → Prop
  | _, _, [] => True
  | phase, budget, step :: steps =>
      allowed phase step.command step.next ∧
      certificate.rate * budget <
        certificate.coercivity step.next * margin step.next ^ 2 ∧
      certificate.PathBudgetAdmissible margin step.next
        (certificate.rate * budget) steps

/-- Every handoff observation equals the observation of its declared phase
center when the path, energy budget, and phase margins are certified. -/
theorem PathCompleteRegionalLyapunov.pathObservationItinerary_eq_centers
    {Observation : Type uObservation}
    {transition : Command → State → State}
    {center : Phase → State} {region : Phase → Set State}
    {allowed : Phase → Command → Phase → Prop}
    (certificate : PathCompleteRegionalLyapunov transition center region allowed)
    (observe : State → Observation) (margin : Phase → ℝ)
    (hmargin : ∀ phase, 0 ≤ margin phase)
    (hstable : ∀ phase,
      ObservationStableOnOpenBall observe (center phase) (margin phase))
    (phase : Phase) (initial : State) (budget : ℝ)
    (steps : List (PhasePathStep Phase Command))
    (hinitial : initial ∈ region phase)
    (henergy : certificate.energy phase initial ≤ budget)
    (hadmissible : certificate.PathBudgetAdmissible margin phase budget steps) :
    List.map observe (runPhasePathStates transition initial steps) =
      List.map observe (phaseCenterTrajectory center steps) := by
  induction steps generalizing phase initial budget with
  | nil => simp [runPhasePathStates, phaseCenterTrajectory]
  | cons step steps ih =>
      rcases hadmissible with ⟨hedge, hbudget, htail⟩
      have hnextMem : transition step.command initial ∈ region step.next :=
        certificate.maps_region step.command initial hedge hinitial
      have hnextEnergy :
          certificate.energy step.next (transition step.command initial) ≤
            certificate.rate * budget := by
        exact le_trans
          (certificate.contracts step.command initial hedge hinitial)
          (mul_le_mul_of_nonneg_left henergy certificate.rate_nonneg)
      have hdistance :
          certificate.coercivity step.next *
              ‖transition step.command initial - center step.next‖ ^ 2 ≤
            certificate.rate * budget :=
        le_trans
          (certificate.energy_controls_distance step.next _ hnextMem)
          hnextEnergy
      have hstrict :
          certificate.coercivity step.next *
              ‖transition step.command initial - center step.next‖ ^ 2 <
            certificate.coercivity step.next * margin step.next ^ 2 :=
        lt_of_le_of_lt hdistance hbudget
      have hsquares :
          ‖transition step.command initial - center step.next‖ ^ 2 <
            margin step.next ^ 2 := by
        nlinarith [certificate.coercivity_pos step.next]
      have hdistanceLt :
          ‖transition step.command initial - center step.next‖ <
            margin step.next := by
        nlinarith [norm_nonneg
          (transition step.command initial - center step.next),
          hmargin step.next]
      have hobservation :
          observe (transition step.command initial) =
            observe (center step.next) :=
        hstable step.next _ hdistanceLt
      have htailItinerary :=
        ih step.next (transition step.command initial)
          (certificate.rate * budget) hnextMem hnextEnergy htail
      simp only [runPhasePathStates, phaseCenterTrajectory, List.map_cons]
      rw [hobservation, htailItinerary]

/-- A common-center certificate is the one-phase complete graph special case
of the phase-indexed construction. -/
def CommonRegionalLyapunov.toPathComplete
    {transition : Command → State → State} {center : State}
    {region : Set State}
    (certificate : CommonRegionalLyapunov transition center region) :
    PathCompleteRegionalLyapunov transition
      (fun _ : Unit => center) (fun _ : Unit => region)
      (fun _ _ _ => True) where
  energy := fun _ => certificate.energy
  rate := certificate.rate
  rate_nonneg := certificate.rate_nonneg
  rate_lt_one := certificate.rate_lt_one
  coercivity := fun _ => certificate.coercivity
  coercivity_pos := fun _ => certificate.coercivity_pos
  center_mem := fun _ => certificate.center_mem
  energy_nonneg := fun _ state hstate =>
    certificate.energy_nonneg state hstate
  energy_controls_distance := fun _ state hstate =>
    certificate.energy_controls_distance state hstate
  maps_region := by
    intro source target command state _ hstate
    exact certificate.maps_region command state hstate
  contracts := by
    intro source target command state _ hstate
    exact certificate.contracts command state hstate

/-! ## A nonconstant moving-center fixture -/

/-- The two Boolean phases have distinct real-valued centers. -/
noncomputable def boolPhaseCenter : Bool → ℝ
  | false => 0
  | true => 1

/-- A command names its source and target phase and transports displacement
from the source center to half that displacement around the target center. -/
noncomputable def movingCenterTransition : (Bool × Bool) → ℝ → ℝ
  | (source, target), state =>
      boolPhaseCenter target + (state - boolPhaseCenter source) / 2

def movingCenterAllowed
    (source : Bool) (command : Bool × Bool) (target : Bool) : Prop :=
  command.1 = source ∧ command.2 = target

noncomputable def movingCenterEnergy (phase : Bool) (state : ℝ) : ℝ :=
  (state - boolPhaseCenter phase) ^ 2

/-- Distinct centers and edge-relative transport have a path-complete energy
rate of one quarter on the whole real line. -/
noncomputable def movingCenterPathCompleteLyapunov :
    PathCompleteRegionalLyapunov movingCenterTransition boolPhaseCenter
      (fun _ => Set.univ) movingCenterAllowed where
  energy := movingCenterEnergy
  rate := 1 / 4
  rate_nonneg := by norm_num
  rate_lt_one := by norm_num
  coercivity := fun _ => 1
  coercivity_pos := by intro; norm_num
  center_mem := by intro; exact Set.mem_univ _
  energy_nonneg := by
    intro phase state _
    exact sq_nonneg _
  energy_controls_distance := by
    intro phase state _
    rw [Real.norm_eq_abs, sq_abs]
    norm_num [movingCenterEnergy]
  maps_region := by
    intro source target command state _ _
    exact Set.mem_univ _
  contracts := by
    intro source target command state hedge _
    rcases command with ⟨commandSource, commandTarget⟩
    rcases hedge with ⟨hsource, htarget⟩
    simp only at hsource htarget
    subst commandSource
    subst commandTarget
    simp only [movingCenterTransition, movingCenterEnergy]
    ring_nf
    exact le_rfl

def movingCenterTwoEdgePath : List (PhasePathStep Bool (Bool × Bool)) :=
  [⟨(false, true), true⟩, ⟨(true, false), false⟩]

theorem movingCenterTwoEdgePath_admissible :
    movingCenterPathCompleteLyapunov.PathAdmissible false
      movingCenterTwoEdgePath := by
  norm_num [PathCompleteRegionalLyapunov.PathAdmissible,
    movingCenterTwoEdgePath, movingCenterPathCompleteLyapunov,
    movingCenterAllowed]

private noncomputable def movingCenterObservation (state : ℝ) : Bool :=
  decide ((1 / 2 : ℝ) ≤ state)

theorem movingCenterObservation_stable (phase : Bool) :
    ObservationStableOnOpenBall movingCenterObservation
      (boolPhaseCenter phase) (1 / 2) := by
  intro state hstate
  rw [Real.norm_eq_abs] at hstate
  cases phase with
  | false =>
      have hlt : state < 1 / 2 := by
        have := (abs_lt.mp (by simpa [boolPhaseCenter] using hstate)).2
        linarith
      have hnot : ¬ (1 / 2 : ℝ) ≤ state := by linarith
      unfold movingCenterObservation
      rw [decide_eq_decide]
      constructor
      · intro hleft
        exact (hnot hleft).elim
      · intro hright
        norm_num [boolPhaseCenter] at hright
  | true =>
      have hlower : -(1 / 2 : ℝ) < state - 1 :=
        (abs_lt.mp (by simpa [boolPhaseCenter] using hstate)).1
      have hge : (1 / 2 : ℝ) ≤ state := by linarith
      unfold movingCenterObservation
      rw [decide_eq_decide]
      constructor
      · intro _
        norm_num [boolPhaseCenter]
      · intro _
        exact hge

theorem movingCenterTwoEdgePath_budget_admissible :
    movingCenterPathCompleteLyapunov.PathBudgetAdmissible
      (fun _ => 1 / 2) false 0 movingCenterTwoEdgePath := by
  norm_num [PathCompleteRegionalLyapunov.PathBudgetAdmissible,
    movingCenterTwoEdgePath, movingCenterPathCompleteLyapunov,
    movingCenterAllowed]

/-- The generic path-complete observation theorem certifies the nonconstant
two-handoff itinerary rather than merely computing it. -/
theorem movingCenterTwoEdgePath_observation_itinerary :
    List.map movingCenterObservation
        (runPhasePathStates movingCenterTransition 0 movingCenterTwoEdgePath) =
      List.map movingCenterObservation
        (phaseCenterTrajectory boolPhaseCenter movingCenterTwoEdgePath) := by
  exact
    movingCenterPathCompleteLyapunov.pathObservationItinerary_eq_centers
      movingCenterObservation (fun _ => 1 / 2)
      (by intro; norm_num) movingCenterObservation_stable
      false 0 0 movingCenterTwoEdgePath (Set.mem_univ _) (by
        norm_num [movingCenterPathCompleteLyapunov, movingCenterEnergy,
          boolPhaseCenter])
      movingCenterTwoEdgePath_budget_admissible

theorem movingCenterTwoEdgePath_observation_value :
    List.map movingCenterObservation
        (runPhasePathStates movingCenterTransition 0 movingCenterTwoEdgePath) =
      [true, false] := by
  norm_num [runPhasePathStates, movingCenterTransition,
    movingCenterTwoEdgePath, movingCenterObservation, boolPhaseCenter]

/-! ## Negative boundary: an unlicensed edge can increase energy -/

def movingCenterForbiddenPath : List (PhasePathStep Bool (Bool × Bool)) :=
  [⟨(true, false), false⟩]

theorem movingCenterForbiddenPath_not_admissible :
    ¬ movingCenterPathCompleteLyapunov.PathAdmissible false
      movingCenterForbiddenPath := by
  norm_num [PathCompleteRegionalLyapunov.PathAdmissible,
    movingCenterForbiddenPath, movingCenterPathCompleteLyapunov,
    movingCenterAllowed]

/-- Applying a command whose declared source does not match the current phase
violates the geometric energy conclusion, so edge admissibility is load-bearing. -/
theorem movingCenterForbiddenPath_violates_energy_bound :
    ¬ movingCenterPathCompleteLyapunov.energy
        (finalPathPhase false movingCenterForbiddenPath)
        (runPhasePath movingCenterTransition 0 movingCenterForbiddenPath) ≤
      movingCenterPathCompleteLyapunov.rate ^ movingCenterForbiddenPath.length *
        movingCenterPathCompleteLyapunov.energy false 0 := by
  norm_num [movingCenterForbiddenPath, finalPathPhase, runPhasePath,
    movingCenterPathCompleteLyapunov, movingCenterTransition,
    movingCenterEnergy, boolPhaseCenter]

#print axioms PathCompleteRegionalLyapunov.runPhasePath_mem
#print axioms PathCompleteRegionalLyapunov.runPhasePath_energy_le
#print axioms PathCompleteRegionalLyapunov.runPhasePath_distance_sq_le
#print axioms PathCompleteRegionalLyapunov.pathObservationItinerary_eq_centers
#print axioms CommonRegionalLyapunov.toPathComplete
#print axioms movingCenterTwoEdgePath_observation_itinerary
#print axioms movingCenterTwoEdgePath_observation_value
#print axioms movingCenterForbiddenPath_not_admissible
#print axioms movingCenterForbiddenPath_violates_energy_bound

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
