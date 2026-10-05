import Mettapedia.GSLT.Logic.GradedTwoSidedObservation

/-!
# Two-sided observation controls

Two inert states have identical graded futures at every depth, but just one
has a predecessor. Their constructed two-sided readout distinguishes them.
The predecessor-universal box and incoming endpoint lifting consequently
fail for the forward-only observation.

An infinite family of authored two-cycles has nonconstant Boolean-valued
readings, finite branching in both directions, and a proved stabilization
certificate. Its source and target endpoint lifts hold, while both exact
occurrence lifts fail because the observation hides the cycle index.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.GradedTwoSidedObservationControls

open HennessyMilner Distinction.Constructive GradedValueObserver GradedTwoSidedObservation
open Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassFamilyDescent

def unitScale : Scale ℤ := Scale.integers 1 (by decide)

theorem positive : unitScale.Positive := Scale.integers_positive 1 _

namespace DifferentPasts

inductive State where
  | ancestor
  | inherited
  | isolated
  deriving DecidableEq

def next : State → List State
  | .ancestor => [.inherited]
  | _ => []

def previous : State → List State
  | .inherited => [.ancestor]
  | _ => []

def theory : GSLT := equalityGSLT State (fun source target => target ∈ next source)

def dynamics : System.{0, 0} theory where
  Atom := Unit
  observes _ _ := True
  observes_resp _ _ _ _ := Iff.rfl
  Label := Unit
  act _ source target := target ∈ next source
  act_resp_left := by
    intro _ left right target same action
    cases same
    exact ⟨target, action, rfl⟩
  act_resp_right := by
    intro _ source target target' action same
    cases same
    exact action

def presented : PresentedSystem.{0, 0, 0, 0, 0} theory unitScale where
  dynamics := dynamics
  Obs := Unit
  value _ _ := 0
  value_nonneg _ _ := by decide
  value_le_one _ _ := by decide
  value_resp _ _ _ _ := rfl
  successors _ source := next source
  successors_act member := member
  successors_cover action := ⟨_, action, rfl⟩

def vocabulary : presented.Vocabulary where
  observations := [()]
  observations_complete _ := List.mem_singleton_self _
  labels := [()]
  labels_complete _ := List.mem_singleton_self _

def predecessors : Predecessors presented where
  list _ target := previous target
  sound := by
    intro label target source member
    change source ∈ previous target at member
    change target ∈ next source
    cases target with
    | ancestor => exact (List.not_mem_nil member).elim
    | inherited =>
      have same := List.mem_singleton.mp member
      rw [same]
      exact List.mem_singleton_self _
    | isolated => exact (List.not_mem_nil member).elim
  cover := by
    intro label target source action
    change target ∈ next source at action
    cases source with
    | ancestor =>
      have same := List.mem_singleton.mp action
      refine ⟨.ancestor, ?_, rfl⟩
      rw [same]
      exact List.mem_singleton_self _
    | inherited => exact (List.not_mem_nil action).elim
    | isolated => exact (List.not_mem_nil action).elim

def both := twoSided presented predecessors

def bothVocabulary : both.Vocabulary := twoSidedVocabulary presented predecessors vocabulary

theorem forward_stabilizes : presented.Stabilizes vocabulary 1 := by
  intro left right
  cases left <;> cases right <;> decide

theorem both_stabilizes : both.Stabilizes bothVocabulary 1 := by
  intro left right
  cases left <;> cases right <;> decide

theorem forward_identical_futures : presented.GradedBisimilar .inherited .isolated := by
  refine ⟨fun first second => first = .inherited ∧ second = .isolated, ⟨?_, ?_, ?_⟩, rfl, rfl⟩
  · rintro _ _ ⟨rfl, rfl⟩ label target action
    exact (List.not_mem_nil action).elim
  · rintro _ _ ⟨rfl, rfl⟩ label target action
    exact (List.not_mem_nil action).elim
  · intro _ _ related observation
    rfl

theorem forward_readout_equal (depth : Nat) :
    ObservedGradedFamilyDescent.readout presented depth .inherited =
      ObservedGradedFamilyDescent.readout presented depth .isolated :=
  (ObservedGradedFamilyDescent.readout_eq_iff presented vocabulary depth _ _).mpr
    (presented.depthBound_eq_zero_of_gradedBisimilar vocabulary forward_identical_futures depth)

theorem backward_reading_distinguishes :
    both.val (.dia (.backward, ()) .top) .inherited = 1 ∧
      both.val (.dia (.backward, ()) .top) .isolated = 0 := by
  exact ⟨by decide, by decide⟩

theorem both_readout_distinguishes :
    ObservedGradedFamilyDescent.readout both 1 .inherited ≠
      ObservedGradedFamilyDescent.readout both 1 .isolated := by
  intro same
  have equal := congrFun same ⟨.dia (.backward, ()) .top, by decide⟩
  exact (show (1 : ℤ) ≠ 0 by decide)
    (backward_reading_distinguishes.1.symm.trans (equal.trans backward_reading_distinguishes.2))

theorem forward_coarsening_not_injective :
    ¬ Function.Injective (forgetForwardClass presented predecessors 1) := by
  intro injective
  have oldEqual : stateOf presented 1 .inherited = stateOf presented 1 .isolated :=
    (classOf_eq_iff (ObservedGradedFamilyDescent.readout presented 1) _ _).mpr (forward_readout_equal 1)
  have mappedEqual : forgetForwardClass presented predecessors 1 (stateOf both 1 .inherited) =
      forgetForwardClass presented predecessors 1 (stateOf both 1 .isolated) := by
    exact (forgetForwardClass_beta presented predecessors 1 .inherited).trans
      (oldEqual.trans (forgetForwardClass_beta presented predecessors 1 .isolated).symm)
  exact both_readout_distinguishes
    ((classOf_eq_iff (ObservedGradedFamilyDescent.readout both 1) _ _).mp (injective mappedEqual))

theorem both_not_stable_at_zero : ¬ both.Stabilizes bothVocabulary 0 := by
  intro stable
  have same := stable .inherited .isolated
  revert same
  decide

def ancestorEvent : ForwardEvent presented := ⟨(), .ancestor, .inherited, List.mem_singleton_self _⟩

theorem isolated_not_next (source : State) : State.isolated ∉ next source := by
  cases source <;> decide

def forwardStageSpan (depth : Nat) : ReductionSpan (StageState presented depth) where
  Edge := ForwardEvent presented
  source event := stateOf presented depth event.source
  target event := stateOf presented depth event.target

def forwardStageMap (depth : Nat) :
    ObservationSpans.SpanMap (forwardEvents presented).span (forwardStageSpan depth) where
  states := stateOf presented depth
  events := id
  source_comm _ := rfl
  target_comm _ := rfl

theorem forward_incoming_lift_fails (depth : Nat) : ¬ (forwardStageMap depth).TargetLifts := by
  intro lifts
  have same : stateOf presented depth .inherited = stateOf presented depth .isolated :=
    (classOf_eq_iff (ObservedGradedFamilyDescent.readout presented depth) _ _).mpr (forward_readout_equal depth)
  obtain ⟨matched, targetEq, _⟩ := lifts .isolated ancestorEvent same
  have action : State.isolated ∈ next matched.source := targetEq ▸ matched.action
  exact isolated_not_next matched.source action

theorem predecessor_false_box_differs :
    derivedBox (forwardEvents presented).span (fun _ => False) .isolated ∧
      ¬ derivedBox (forwardEvents presented).span (fun _ => False) .inherited := by
  constructor
  · intro event targetEq
    have action : State.isolated ∈ next event.source := targetEq ▸ event.action
    exact isolated_not_next event.source action
  · intro holds
    exact holds ancestorEvent rfl

theorem predecessor_box_no_forward_descent (depth : Nat) :
    ¬ ObservationSpans.PredicateDescends (ObservedGradedFamilyDescent.readout presented depth)
      (derivedBox (forwardEvents presented).span (fun _ => False)) := by
  rintro ⟨observed, exactness⟩
  have holds := (exactness .isolated).mpr predecessor_false_box_differs.1
  apply predecessor_false_box_differs.2
  apply (exactness .inherited).mp
  exact (forward_readout_equal depth).symm ▸ holds

theorem both_endpoint_lifts :
    (stageMap presented predecessors (forwardEvents presented) 1).SourceLifts ∧
      (stageMap presented predecessors (forwardEvents presented) 1).TargetLifts :=
  ⟨source_lifts presented predecessors _ vocabulary 1 positive both_stabilizes,
    target_lifts presented predecessors _ vocabulary 1 positive both_stabilizes⟩

theorem both_predecessor_box_comparison (predicate : StageState both 1 → Prop) (target : State) :
    derivedBox (stageSpan presented predecessors (forwardEvents presented) 1) predicate (stateOf both 1 target) ↔
      derivedBox (forwardEvents presented).span (predicate ∘ stateOf both 1) target :=
  predecessor_box_pullback presented predecessors _ vocabulary 1 positive both_stabilizes predicate target

end DifferentPasts

namespace InfiniteCycles

abbrev State := Bool × Nat

def flip (state : State) : State := (!state.1, state.2)

theorem flip_flip (state : State) : flip (flip state) = state := by
  rcases state with ⟨bit, index⟩
  cases bit <;> rfl

def theory : GSLT := equalityGSLT State (fun source target => target = flip source)

def dynamics : System.{0, 0} theory where
  Atom := Bool
  observes atom source := source.1 = atom
  observes_resp _ _ _ same := by cases same; rfl
  Label := Unit
  act _ source target := target = flip source
  act_resp_left := by
    intro _ left right target same action
    cases same
    exact ⟨target, action, rfl⟩
  act_resp_right := by
    intro _ source target target' action same
    cases same
    exact action

def presented : PresentedSystem.{0, 0, 0, 0, 0} theory unitScale where
  dynamics := dynamics
  Obs := Unit
  value _ state := if state.1 then 1 else 0
  value_nonneg _ state := by split <;> decide
  value_le_one _ state := by change (if state.1 then (1 : ℤ) else 0) ≤ 1; split <;> decide
  value_resp _ _ _ same := by cases same; rfl
  successors _ source := [flip source]
  successors_act member := List.mem_singleton.mp member
  successors_cover action := ⟨flip _, List.mem_singleton_self _, action⟩

def vocabulary : presented.Vocabulary where
  observations := [()]
  observations_complete _ := List.mem_singleton_self _
  labels := [()]
  labels_complete _ := List.mem_singleton_self _

def predecessors : Predecessors presented where
  list _ target := [flip target]
  sound := by
    intro label target source member
    have same := List.mem_singleton.mp member
    change target = flip source
    rw [same]
    exact (flip_flip (show State from target)).symm
  cover := by
    intro label target source action
    refine ⟨flip target, List.mem_singleton_self _, ?_⟩
    change source = flip target
    change target = flip source at action
    rw [action]
    exact (flip_flip (show State from source)).symm

def both := twoSided presented predecessors

def bothVocabulary : both.Vocabulary := twoSidedVocabulary presented predecessors vocabulary

theorem both_stabilizes : both.Stabilizes bothVocabulary 0 := by
  rintro ⟨first, i⟩ ⟨second, j⟩
  cases first <;> cases second <;> rfl

theorem distinct_cycles (first second : Nat) : (false, first) = (false, second) ↔ first = second := by
  exact ⟨congrArg Prod.snd, fun same => same ▸ rfl⟩

theorem two_cycle (state : State) :
    presented.dynamics.act () state (flip state) ∧
      presented.dynamics.act () (flip state) state ∧ flip state ≠ state := by
  refine ⟨rfl, (flip_flip state).symm, ?_⟩
  rcases state with ⟨bit, index⟩
  cases bit <;> intro same <;> cases congrArg Prod.fst same

theorem reading_nonconstant (index : Nat) :
    both.value () (false, index) = 0 ∧ both.value () (true, index) = 1 := ⟨rfl, rfl⟩

theorem observation_retains_phase (first second : Nat) :
    stateOf both 0 (false, first) ≠ stateOf both 0 (true, second) := by
  intro same
  have equal := value_eq_of_stateOf_eq both bothVocabulary 0 positive both_stabilizes same ()
  exact (show (0 : ℤ) ≠ 1 by decide) equal

theorem observation_hides_index (bit : Bool) (first second : Nat) :
    stateOf both 0 (bit, first) = stateOf both 0 (bit, second) := by
  apply (stateOf_eq_iff_graded both bothVocabulary 0 positive both_stabilizes _ _).mpr
  apply ((both.gradedBisimilar_iff_of_stabilizes bothVocabulary positive both_stabilizes _ _).2).mpr
  cases bit <;> rfl

def eventZero : ForwardEvent presented := ⟨(), (false, 0), (true, 0), rfl⟩

theorem both_endpoint_lifts :
    (stageMap presented predecessors (forwardEvents presented) 0).SourceLifts ∧
      (stageMap presented predecessors (forwardEvents presented) 0).TargetLifts :=
  ⟨source_lifts presented predecessors _ vocabulary 0 positive both_stabilizes,
    target_lifts presented predecessors _ vocabulary 0 positive both_stabilizes⟩

theorem source_occurrence_lift_fails :
    ¬ (stageMap presented predecessors (forwardEvents presented) 0).SourceOccurrenceLifts := by
  intro lifts
  obtain ⟨matched, sourceEq, eventEq⟩ :=
    lifts (false, 1) eventZero (observation_hides_index false 0 1)
  change matched = eventZero at eventEq
  have impossible : (0 : Nat) = 1 := congrArg Prod.snd ((congrArg ForwardEvent.source eventEq).symm.trans sourceEq)
  exact (by decide : (0 : Nat) ≠ 1) impossible

theorem target_occurrence_lift_fails :
    ¬ (stageMap presented predecessors (forwardEvents presented) 0).TargetOccurrenceLifts := by
  intro lifts
  obtain ⟨matched, targetEq, eventEq⟩ :=
    lifts (true, 1) eventZero (observation_hides_index true 0 1)
  change matched = eventZero at eventEq
  have impossible : (0 : Nat) = 1 := congrArg Prod.snd ((congrArg ForwardEvent.target eventEq).symm.trans targetEq)
  exact (by decide : (0 : Nat) ≠ 1) impossible

theorem endpoint_lifting_is_not_occurrence_lifting :
    (stageMap presented predecessors (forwardEvents presented) 0).SourceLifts ∧
      (stageMap presented predecessors (forwardEvents presented) 0).TargetLifts ∧
      ¬ (stageMap presented predecessors (forwardEvents presented) 0).SourceOccurrenceLifts ∧
      ¬ (stageMap presented predecessors (forwardEvents presented) 0).TargetOccurrenceLifts :=
  ⟨both_endpoint_lifts.1, both_endpoint_lifts.2, source_occurrence_lift_fails, target_occurrence_lift_fails⟩

def phaseOne : Formula (valueSystem both).Atom both.dynamics.Label := .atom ((), (1 : ℤ))

theorem future_one_actual (index : Nat) :
    (futurePredicate presented (forwardEvents presented) (formulaPredicate (valueSystem both) phaseOne)).1
      (false, index) :=
  ⟨⟨(), (false, index), (true, index), rfl⟩, rfl, rfl⟩

theorem predecessor_one_actual (index : Nat) :
    (predecessorBoxPredicate presented (forwardEvents presented) (formulaPredicate (valueSystem both) phaseOne)).1
      (false, index) := by
  apply (predecessor_box_iff presented (forwardEvents presented) _ _).mpr
  intro label source action
  change (false, index) = flip source at action
  rcases source with ⟨bit, sourceIndex⟩
  cases bit with
  | false =>
    have impossible := congrArg Prod.fst action
    change (false : Bool) = true at impossible
    cases impossible
  | true => rfl

theorem stage_future_and_past_one (index : Nat) :
    derivedDiamond (stageSpan presented predecessors (forwardEvents presented) 0)
        (nativeImage both 0 (formulaPredicate (valueSystem both) phaseOne)) (stateOf both 0 (false, index)) ∧
      derivedBox (stageSpan presented predecessors (forwardEvents presented) 0)
        (nativeImage both 0 (formulaPredicate (valueSystem both) phaseOne)) (stateOf both 0 (false, index)) :=
  ⟨(formula_future_native_iff presented predecessors _ vocabulary 0 positive both_stabilizes phaseOne _).mpr
      (future_one_actual index),
    (formula_predecessor_box_native_iff presented predecessors _ vocabulary 0 positive both_stabilizes phaseOne _).mpr
      (predecessor_one_actual index)⟩

theorem full_modal_native_comparison
    (formula : Formula (valueSystem both).Atom both.dynamics.Label) (source : State) :
    (formulaPredicate (stageSystem both 0) formula).1 (stateOf both 0 source) ↔
      (formulaPredicate (valueSystem both) formula).1 source :=
  native_predicate_stage_iff both bothVocabulary 0 positive both_stabilizes formula source

theorem predecessor_box_native_comparison
    (formula : Formula (valueSystem both).Atom both.dynamics.Label) (target : State) :
    derivedBox (stageSpan presented predecessors (forwardEvents presented) 0)
        (nativeImage both 0 (formulaPredicate (valueSystem both) formula)) (stateOf both 0 target) ↔
      (predecessorBoxPredicate presented (forwardEvents presented)
        (formulaPredicate (valueSystem both) formula)).1 target :=
  formula_predecessor_box_native_iff presented predecessors _ vocabulary 0 positive both_stabilizes formula target

end InfiniteCycles

end Mettapedia.GSLT.GradedTwoSidedObservationControls
