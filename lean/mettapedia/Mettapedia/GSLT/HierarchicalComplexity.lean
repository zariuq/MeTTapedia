import Mettapedia.Cybernetics.HierarchicalComplexity.Composition
import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.GSLT.Core.IndexedOperational

/-!
# Observer-indexed hierarchical complexity for GSLT execution

The Model of Hierarchical Complexity classifies an organization by the
outcomes of permuting its component actions.  For an operational theory this
requires three pieces of data that must not be conflated:

* actual one-step witnesses for both orders of execution;
* an observation of their outcomes;
* a homogeneous rank for the component actions when a numerical order is
  assigned.

Independent interleaving gives a chain because its local steps commute.
Authored interaction can give a coordination when the two schedules reach
distinct endpoints.  Interaction alone is insufficient: the existing MHC
criterion remains equality or inequality of the observed schedule outcomes.

An indexed GSLT naturality square supplies the decisive observer-relative
control.  Its two routes have the same endpoint but retain different first
steps.  Endpoint observation therefore sees a chain, while proof-relevant
route observation sees a coordination.  Consequently no MHC order is attached
merely by possessing a GSLT, a transport, or a filled square.

The permutation criterion is due to Commons and Pekker, "Presenting the Formal
Theory of Hierarchical Complexity" (2008).  The GSLT applications and the
observer-indexed separation theorems below are new.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HierarchicalComplexity

open Mettapedia.Cybernetics.HierarchicalComplexity
open Mettapedia.Cybernetics.HierarchicalComplexity.Composition
open Mettapedia.GSLT
open Mettapedia.GSLT.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational

universe uOutcome uObject uStep uCell uTerm uIndex vIndex

/-! ## Binary observations -/

/-- A binary schedule readout determined by the outcome of its first
occurrence.  This is the observation-level core shared by endpoint and route
semantics. -/
def binaryObservation {Outcome : Type uOutcome} (leftThenRight rightThenLeft : Outcome) :
    ScheduleSemantics (Fin 2) Outcome :=
  fun schedule => if schedule 0 = 0 then leftThenRight else rightThenLeft

@[simp] theorem binaryObservation_refl {Outcome : Type uOutcome}
    (leftThenRight rightThenLeft : Outcome) :
    binaryObservation leftThenRight rightThenLeft (Equiv.refl (Fin 2)) =
      leftThenRight := by
  simp [binaryObservation]

@[simp] theorem binaryObservation_swap {Outcome : Type uOutcome}
    (leftThenRight rightThenLeft : Outcome) :
    binaryObservation leftThenRight rightThenLeft
      (Equiv.swap (0 : Fin 2) 1) = rightThenLeft := by
  simp [binaryObservation]

/-- A binary observation is a chain exactly when its two schedule outcomes
agree. -/
theorem binaryObservation_isChain_iff {Outcome : Type uOutcome}
    (leftThenRight rightThenLeft : Outcome) :
    IsChain (binaryObservation leftThenRight rightThenLeft) ↔
      leftThenRight = rightThenLeft := by
  constructor
  · intro invariant
    simpa using invariant (Equiv.refl (Fin 2)) (Equiv.swap 0 1)
  · intro equal first second
    by_cases firstLeft : first 0 = 0 <;>
      by_cases secondLeft : second 0 = 0 <;>
      simp [binaryObservation, firstLeft, secondLeft, equal]

/-- A binary observation is a coordination exactly when its two schedule
outcomes differ. -/
theorem binaryObservation_isCoordination_iff {Outcome : Type uOutcome}
    (leftThenRight rightThenLeft : Outcome) :
    IsCoordination (binaryObservation leftThenRight rightThenLeft) ↔
      leftThenRight ≠ rightThenLeft := by
  constructor
  · intro coordination equal
    exact ((binaryObservation_isChain_iff _ _).mpr equal).not_coordination
      coordination
  · intro different
    exact ⟨Equiv.refl (Fin 2), Equiv.swap 0 1, by simpa using different⟩

/-! ## Operational schedules -/

/-- Two executable orders inside one GSLT.  Unlike a bare pair of state
transformations, this structure retains all four one-step witnesses that make
the comparison operational. -/
structure BinaryOperationalSchedule (theory : GSLT) extends
    BinaryProcess theory.Term where
  leftAtInitial : theory.Step toBinaryProcess.initial
    (toBinaryProcess.left toBinaryProcess.initial)
  rightAfterLeft : theory.Step
    (toBinaryProcess.left toBinaryProcess.initial)
    (toBinaryProcess.right (toBinaryProcess.left toBinaryProcess.initial))
  rightAtInitial : theory.Step toBinaryProcess.initial
    (toBinaryProcess.right toBinaryProcess.initial)
  leftAfterRight : theory.Step
    (toBinaryProcess.right toBinaryProcess.initial)
    (toBinaryProcess.left (toBinaryProcess.right toBinaryProcess.initial))

namespace BinaryOperationalSchedule

variable {theory : GSLT}

/-- Endpoint observation forgets step identity but retains the result of each
execution order. -/
def endpointSemantics (schedule : BinaryOperationalSchedule theory) :
    ScheduleSemantics (Fin 2) theory.Term :=
  schedule.toBinaryProcess.scheduleSemantics

theorem endpoint_isChain_iff (schedule : BinaryOperationalSchedule theory) :
    IsChain schedule.endpointSemantics ↔
      schedule.toBinaryProcess.leftThenRight =
        schedule.toBinaryProcess.rightThenLeft :=
  BinaryProcess.isChain_iff schedule.toBinaryProcess

theorem endpoint_isCoordination_iff
    (schedule : BinaryOperationalSchedule theory) :
    IsCoordination schedule.endpointSemantics ↔
      schedule.toBinaryProcess.leftThenRight ≠
        schedule.toBinaryProcess.rightThenLeft :=
  BinaryProcess.isCoordination_iff schedule.toBinaryProcess

/-- The operational schedule really contains two length-two executions from
the same initial term. -/
theorem has_both_execution_orders (schedule : BinaryOperationalSchedule theory) :
    theory.Step schedule.toBinaryProcess.initial
        (schedule.toBinaryProcess.left schedule.toBinaryProcess.initial) ∧
      theory.Step
        (schedule.toBinaryProcess.left schedule.toBinaryProcess.initial)
        schedule.toBinaryProcess.leftThenRight ∧
      theory.Step schedule.toBinaryProcess.initial
        (schedule.toBinaryProcess.right schedule.toBinaryProcess.initial) ∧
      theory.Step
        (schedule.toBinaryProcess.right schedule.toBinaryProcess.initial)
        schedule.toBinaryProcess.rightThenLeft :=
  ⟨schedule.leftAtInitial, schedule.rightAfterLeft,
    schedule.rightAtInitial, schedule.leftAfterRight⟩

end BinaryOperationalSchedule

/-! ## Independent product: a real GSLT chain -/

namespace IndependentCanary

private inductive PulseState where
  | ready
  | done
  deriving DecidableEq

private inductive PulseStep : PulseState → PulseState → Prop where
  | fire : PulseStep .ready .done

private def pulseTheory : GSLT where
  Term := PulseState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := PulseStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

private def productTheory : GSLT := interleavingProduct pulseTheory pulseTheory

private def leftUpdate : productTheory.Term → productTheory.Term :=
  fun state => (.done, state.2)

private def rightUpdate : productTheory.Term → productTheory.Term :=
  fun state => (state.1, .done)

/-- The two independent component steps are retained as actual steps of the
interleaving product. -/
def schedule : BinaryOperationalSchedule productTheory where
  initial := (.ready, .ready)
  left := leftUpdate
  right := rightUpdate
  leftAtInitial := interleavingProduct_step_left
    (left := pulseTheory) (right := pulseTheory) PulseStep.fire PulseState.ready
  rightAfterLeft := interleavingProduct_step_right
    (left := pulseTheory) (right := pulseTheory) PulseStep.fire PulseState.done
  rightAtInitial := interleavingProduct_step_right
    (left := pulseTheory) (right := pulseTheory) PulseStep.fire PulseState.ready
  leftAfterRight := interleavingProduct_step_left
    (left := pulseTheory) (right := pulseTheory) PulseStep.fire PulseState.done

theorem endpoint_commutes :
    schedule.toBinaryProcess.leftThenRight =
      schedule.toBinaryProcess.rightThenLeft := rfl

/-- Certified component separation is an MHC chain at endpoint observation. -/
theorem schedule_isChain : IsChain schedule.endpointSemantics :=
  (schedule.endpoint_isChain_iff).mpr endpoint_commutes

private def child : Fin 2 → Action.{0, 0} productTheory.Term := fun _ => .simple

def action : Action.{0, 0} productTheory.Term :=
  BinaryProcess.chainAction schedule.toBinaryProcess schedule_isChain child

/-- Independent interleaving does not raise the common rank of two simple
children. -/
theorem rank_action : Action.rank action = 0 := by
  exact BinaryProcess.rank_chainAction_of_equalRank
    schedule.toBinaryProcess schedule_isChain child (fun _ => rfl)

end IndependentCanary

/-! ## Authored interaction: a real GSLT coordination -/

namespace InteractionCanary

private inductive LeftState where
  | start
  | afterAlpha
  deriving DecidableEq

private inductive LeftStep : LeftState → LeftState → Prop where
  | alpha : LeftStep .start .afterAlpha

private inductive RightState where
  | afterBeta
  | alphaAfterBeta
  | betaAfterAlpha
  deriving DecidableEq

private inductive RightStep : RightState → RightState → Prop where
  | alpha : RightStep .afterBeta .alphaAfterBeta

private def leftTheory : GSLT where
  Term := LeftState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := LeftStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

private def rightTheory : GSLT where
  Term := RightState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := RightStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

private inductive BetaCrossing : LeftState → RightState → Prop where
  | beforeAlpha : BetaCrossing .start .afterBeta
  | afterAlpha : BetaCrossing .afterAlpha .betaAfterAlpha

private def interaction : Interaction leftTheory rightTheory where
  leftToRight := BetaCrossing
  rightToLeft := fun _ _ => False
  leftToRight_resp_left := by
    intro source source' target equal crossing
    subst source'
    exact ⟨target, crossing, rfl⟩
  leftToRight_resp_right := by
    intro source target target' crossing equal
    subst target'
    exact crossing
  rightToLeft_resp_left := by
    intro source source' target _ impossible
    exact False.elim impossible
  rightToLeft_resp_right := by
    intro source target target' impossible _
    exact False.elim impossible

private def combinedTheory : GSLT :=
  interactingSum leftTheory rightTheory interaction

private def alphaUpdate : combinedTheory.Term → combinedTheory.Term
  | .inl .start => .inl .afterAlpha
  | .inr .afterBeta => .inr .alphaAfterBeta
  | state => state

private def betaUpdate : combinedTheory.Term → combinedTheory.Term
  | .inl .start => .inr .afterBeta
  | .inl .afterAlpha => .inr .betaAfterAlpha
  | state => state

/-- The two orders are genuine executions of an interacting sum.  Alpha then
beta and beta then alpha reach intentionally distinct authored states. -/
def schedule : BinaryOperationalSchedule combinedTheory where
  initial := .inl .start
  left := alphaUpdate
  right := betaUpdate
  leftAtInitial := .left LeftStep.alpha
  rightAfterLeft := .leftToRight BetaCrossing.afterAlpha
  rightAtInitial := .leftToRight BetaCrossing.beforeAlpha
  leftAfterRight := .right RightStep.alpha

@[simp] theorem alpha_then_beta :
    schedule.toBinaryProcess.leftThenRight = .inr .betaAfterAlpha := rfl

@[simp] theorem beta_then_alpha :
    schedule.toBinaryProcess.rightThenLeft = .inr .alphaAfterBeta := rfl

/-- Authored interaction raises order only because the observed schedules
actually differ. -/
theorem schedule_isCoordination : IsCoordination schedule.endpointSemantics := by
  rw [schedule.endpoint_isCoordination_iff]
  rw [alpha_then_beta, beta_then_alpha]
  intro equal
  have inner : RightState.betaAfterAlpha = RightState.alphaAfterBeta :=
    Sum.inr.inj equal
  cases inner

private def child : Fin 2 → Action.{0, 0} combinedTheory.Term := fun _ => .simple

def action : Action.{0, 0} combinedTheory.Term :=
  BinaryProcess.coordinationAction schedule.toBinaryProcess
    schedule_isCoordination child

/-- The noncommuting interaction raises two simple children to rank one. -/
theorem rank_action : Action.rank action = 1 := by
  have raised := BinaryProcess.rank_coordinationAction_of_equalRank
    schedule.toBinaryProcess schedule_isCoordination child (fun _ => rfl)
  simpa only [action, child, Action.rank_simple, Order.succ_eq_add_one, zero_add]
    using raised

end InteractionCanary

/-! ## Filled diamonds under endpoint and route observations -/

namespace DiamondObservation

variable {Object : Type uObject}
    {Step : Object → Object → Type uStep}
    {Cell : {source target : Object} →
      Route Step source target → Route Step source target → Type uCell}
    {source left right : Object}

/-- Observe only the common endpoint of a filled diamond. -/
def endpointSemantics (diamond : FilledDiamond Step Cell source left right) :
    ScheduleSemantics (Fin 2) Object :=
  binaryObservation diamond.join diamond.join

/-- Observe the complete proof-relevant route selected by each schedule. -/
def routeSemantics (diamond : FilledDiamond Step Cell source left right) :
    ScheduleSemantics (Fin 2) (Route Step source diamond.join) :=
  binaryObservation (diamond.leftBranch.append diamond.closeLeft)
    (diamond.rightBranch.append diamond.closeRight)

/-- Every filled diamond is a chain at endpoint observation. -/
theorem endpoint_isChain (diamond : FilledDiamond Step Cell source left right) :
    IsChain (endpointSemantics diamond) :=
  (binaryObservation_isChain_iff _ _).mpr rfl

/-- Route observation is a chain exactly when the two complete routes are
equal as proof-relevant data. -/
theorem route_isChain_iff (diamond : FilledDiamond Step Cell source left right) :
    IsChain (routeSemantics diamond) ↔
      diamond.leftBranch.append diamond.closeLeft =
        diamond.rightBranch.append diamond.closeRight :=
  binaryObservation_isChain_iff _ _

/-- Route observation is a coordination exactly when the complete routes are
different. -/
theorem route_isCoordination_iff
    (diamond : FilledDiamond Step Cell source left right) :
    IsCoordination (routeSemantics diamond) ↔
      diamond.leftBranch.append diamond.closeLeft ≠
        diamond.rightBranch.append diamond.closeRight :=
  binaryObservation_isCoordination_iff _ _

end DiamondObservation

/-! ## The indexed naturality square changes MHC class with the observer -/

namespace IndexedNaturality

open CategoryTheory
open scoped CategoryTheory

variable {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram.{uTerm, uIndex, vIndex} Index)

/-- A finite observation of the first proof-relevant command step. -/
inductive FirstStepKind where
  | fibre
  | underVia
  | applyVia
  deriving DecidableEq

def firstStepKind {source target : Command diagram}
    (step : Command.Step diagram source target) : FirstStepKind :=
  match step with
  | .fibre _ => .fibre
  | .underVia _ _ => .underVia
  | .applyVia _ _ => .applyVia

def routeFirstStepKind {source target : Command diagram} :
    Route (Command.Step diagram) source target → Option FirstStepKind
  | .refl _ => none
  | .cons step _ => some (firstStepKind diagram step)

/-- Reduce-before-transport and transport-before-reduce are distinct authored
routes.  The finite first-step observation already separates them. -/
theorem reduceBeforeRoute_ne_transportBeforeRoute
    {source target : Index} (route : source ⟶ target)
    {left right : SemanticTerm (diagram.obj source).theory}
    (step : SemanticStep (diagram.obj source).theory left right) :
    Command.reduceBeforeRoute diagram route step ≠
      Command.transportBeforeRoute diagram route step := by
  intro equal
  have observed := congrArg (routeFirstStepKind diagram) equal
  simp [Command.reduceBeforeRoute, Command.transportBeforeRoute,
    routeFirstStepKind, firstStepKind] at observed

/-- The naturality square is a chain when only its common endpoint is
observed. -/
theorem naturality_endpoint_isChain
    {source target : Index} (route : source ⟶ target)
    {left right : SemanticTerm (diagram.obj source).theory}
    (step : SemanticStep (diagram.obj source).theory left right) :
    IsChain (DiamondObservation.endpointSemantics
      (Command.naturalityDiamond diagram route step)) :=
  DiamondObservation.endpoint_isChain _

/-- The same naturality square is a coordination when its complete authored
routes are observed. -/
theorem naturality_route_isCoordination
    {source target : Index} (route : source ⟶ target)
    {left right : SemanticTerm (diagram.obj source).theory}
    (step : SemanticStep (diagram.obj source).theory left right) :
    IsCoordination (DiamondObservation.routeSemantics
      (Command.naturalityDiamond diagram route step)) := by
  rw [DiamondObservation.route_isCoordination_iff]
  exact reduceBeforeRoute_ne_transportBeforeRoute diagram route step

/-- Endpoint and proof-relevant route observation assign opposite MHC classes
to one and the same filled naturality square.  Thus transport structure alone
does not determine a context-free hierarchical order. -/
theorem naturality_classification_is_observer_relative
    {source target : Index} (route : source ⟶ target)
    {left right : SemanticTerm (diagram.obj source).theory}
    (step : SemanticStep (diagram.obj source).theory left right) :
    IsChain (DiamondObservation.endpointSemantics
        (Command.naturalityDiamond diagram route step)) ∧
      IsCoordination (DiamondObservation.routeSemantics
        (Command.naturalityDiamond diagram route step)) :=
  ⟨naturality_endpoint_isChain diagram route step,
    naturality_route_isCoordination diagram route step⟩

end IndexedNaturality

end Mettapedia.GSLT.HierarchicalComplexity

#print axioms Mettapedia.GSLT.HierarchicalComplexity.IndependentCanary.rank_action
#print axioms Mettapedia.GSLT.HierarchicalComplexity.InteractionCanary.rank_action
#print axioms Mettapedia.GSLT.HierarchicalComplexity.IndexedNaturality.naturality_classification_is_observer_relative
