import Mettapedia.GSLT.Logic.HennessyMilnerDirections
import Mettapedia.GSLT.Distinction.Constructive.Transport
import Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent

/-!
# Constructive graded observations of labelled futures and pasts

Authored finite predecessor lists extend an existing presented system by
adding backward labels. Values and forward actions are unchanged. The
backward action respects the equations by the original action laws.

Positive discount and stabilization of the constructed two-sided system
derive both endpoint lifts for the original forward event span. The event
carrier is retained, including any supplied multiplicity or provenance.
Neither endpoint lift asserts equality of the matching event occurrence.
Future diamond and predecessor-universal box therefore commute with the
observation, including for actual equation-invariant native predicates whose
values are constant on the two-sided observational kernel.

This construction concerns the supplied labelled actions. It does not assume
that they cover every step of the underlying GSLT.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.GradedTwoSidedObservation

open HennessyMilner Distinction.Constructive GradedValueObserver
open Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassFamilyDescent

universe uS uAtom uLabel uObs uV uEvent

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
variable {S : GSLT.{uS}} {K : Scale V}
variable (Q : PresentedSystem.{uS, uAtom, uLabel, uObs} S K)

/-- Predecessor branching is authored data, with the same coverage convention
as the existing successor lists. -/
structure Predecessors where
  list : Q.dynamics.Label → S.Term → List S.Term
  sound : ∀ {label target source}, source ∈ list label target → Q.dynamics.act label source target
  cover : ∀ {label target source}, Q.dynamics.act label source target →
    ∃ representative ∈ list label target, S.Equiv source representative

/-- Source equation closure is exact after closing the matched target back
along its authored equation. -/
theorem action_source_closed {label : Q.dynamics.Label} {left right target : S.Term}
    (same : S.Equiv left right) (action : Q.dynamics.act label left target) :
    Q.dynamics.act label right target := by
  obtain ⟨matched, action', targetEq⟩ := Q.dynamics.act_resp_left same action
  exact Q.dynamics.act_resp_right action' (S.equations.iseqv.symm targetEq)

def twoSidedDynamics : System.{uAtom, uLabel} S where
  Atom := Q.dynamics.Atom
  observes := Q.dynamics.observes
  observes_resp := Q.dynamics.observes_resp
  Label := Direction × Q.dynamics.Label
  act label source target := match label.1 with
    | .forward => Q.dynamics.act label.2 source target
    | .backward => Q.dynamics.act label.2 target source
  act_resp_left := by
    rintro ⟨direction, label⟩ left right target same action
    cases direction with
    | forward => exact Q.dynamics.act_resp_left same action
    | backward => exact ⟨target, Q.dynamics.act_resp_right action same, S.equations.iseqv.refl target⟩
  act_resp_right := by
    rintro ⟨direction, label⟩ source target target' action same
    cases direction with
    | forward => exact Q.dynamics.act_resp_right action same
    | backward => exact action_source_closed Q same action

def twoSided (past : Predecessors Q) : PresentedSystem.{uS, uAtom, uLabel, uObs} S K where
  dynamics := twoSidedDynamics Q
  Obs := Q.Obs
  value := Q.value
  value_nonneg := Q.value_nonneg
  value_le_one := Q.value_le_one
  value_resp := Q.value_resp
  successors label source := match label.1 with
    | .forward => Q.successors label.2 source
    | .backward => past.list label.2 source
  successors_act := by
    rintro ⟨direction, label⟩ source target member
    cases direction with
    | forward => exact Q.successors_act member
    | backward => exact past.sound member
  successors_cover := by
    rintro ⟨direction, label⟩ source target action
    cases direction with
    | forward => exact Q.successors_cover action
    | backward => exact past.cover action

variable (past : Predecessors Q)

def twoSidedVocabulary (vocabulary : Q.Vocabulary) : (twoSided Q past).Vocabulary where
  observations := vocabulary.observations
  observations_complete := vocabulary.observations_complete
  labels := vocabulary.labels.map (fun label => (Direction.forward, label)) ++
    vocabulary.labels.map (fun label => (Direction.backward, label))
  labels_complete := by
    rintro ⟨direction, label⟩
    cases direction with
    | forward => exact List.mem_append.mpr (Or.inl
        (List.mem_map.mpr ⟨label, vocabulary.labels_complete label, rfl⟩))
    | backward => exact List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨label, vocabulary.labels_complete label, rfl⟩))

@[simp] theorem twoSided_act_forward (label : Q.dynamics.Label) (source target : S.Term) :
    (twoSided Q past).dynamics.act (.forward, label) source target ↔
      Q.dynamics.act label source target := Iff.rfl

@[simp] theorem twoSided_act_backward (label : Q.dynamics.Label) (source target : S.Term) :
    (twoSided Q past).dynamics.act (.backward, label) source target ↔
      Q.dynamics.act label target source := Iff.rfl

@[simp] theorem twoSided_value (observation : Q.Obs) (source : S.Term) :
    (twoSided Q past).value observation source = Q.value observation source := rfl

/-- The forward labelled system embeds exactly in the constructed two-sided
system. The term map is unchanged, while the label carrier gains a past. -/
def forwardEmbedding : ObservationMap Q (twoSided Q past) 0 where
  error_nonneg := le_rfl
  mapTerm := id
  mapEquiv same := same
  atom := id
  label label := (.forward, label)
  value_close observation term := by change |Q.value observation term - Q.value observation term| ≤ 0; rw [sub_self, abs_zero]
  mapAct _ {_ _} action := action
  liftAct _ {_ target} action := ⟨target, action, S.equations.iseqv.refl target⟩

theorem forward_formula_values (formula : Q.Formula) (source : S.Term) :
    (twoSided Q past).val ((forwardEmbedding Q past).translate formula) source = Q.val formula source :=
  (forwardEmbedding Q past).val_translate formula source

theorem forward_bound_le (vocabulary : Q.Vocabulary) (depth : Nat) (left right : S.Term) :
    Q.depthBound vocabulary depth left right ≤
      (twoSided Q past).depthBound (twoSidedVocabulary Q past vocabulary) depth left right := by
  have bound := (forwardEmbedding Q past).depthBound_le_map vocabulary
    (twoSidedVocabulary Q past vocabulary) depth left right
  simpa only [forwardEmbedding, id_eq, add_zero, zero_add] using bound

def readoutForget (depth : Nat)
    (reading : ObservedGradedFamilyDescent.BoundedFormula (twoSided Q past) depth → V) :
    ObservedGradedFamilyDescent.BoundedFormula Q depth → V :=
  fun formula => reading ⟨(forwardEmbedding Q past).translate formula.1,
    by rw [(forwardEmbedding Q past).depth_translate]; exact formula.2⟩

theorem readoutForget_readout (depth : Nat) (source : S.Term) :
    readoutForget Q past depth (ObservedGradedFamilyDescent.readout (twoSided Q past) depth source) =
      ObservedGradedFamilyDescent.readout Q depth source :=
  funext fun formula => forward_formula_values Q past formula.1 source

/-- Complete observation classes coarsen constructively to the original
forward classes, without choosing a source representative. -/
def forgetForwardClass (depth : Nat) : StageState (twoSided Q past) depth → StageState Q depth :=
  classMap (ObservedGradedFamilyDescent.readout Q depth)
    (ObservedGradedFamilyDescent.readout (twoSided Q past) depth) id (readoutForget Q past depth)
    (fun source => (readoutForget_readout Q past depth source).symm)

theorem forgetForwardClass_beta (depth : Nat) (source : S.Term) :
    forgetForwardClass Q past depth (stateOf (twoSided Q past) depth source) = stateOf Q depth source :=
  classMap_beta _ _ id (readoutForget Q past depth) _ source

theorem forgetForwardClass_surjective (depth : Nat) : Function.Surjective (forgetForwardClass Q past depth) := by
  intro observed
  obtain ⟨source, rfl⟩ := stateOf_surjective Q depth observed
  exact ⟨stateOf (twoSided Q past) depth source, forgetForwardClass_beta Q past depth source⟩

/-- Labelled occurrences may carry arbitrary extra data. Soundness and
coverage connect them to the supplied forward action relation. -/
structure AuthoredEvents where
  span : ReductionSpan.{uS, uEvent} S.Term
  label : span.Edge → Q.dynamics.Label
  sound : ∀ event, Q.dynamics.act (label event) (span.source event) (span.target event)
  cover : ∀ actionLabel source target, Q.dynamics.act actionLabel source target →
    ∃ event, label event = actionLabel ∧
      span.source event = source ∧ span.target event = target

/-- The relation itself has an explicit labelled occurrence presentation. -/
structure ForwardEvent where
  label : Q.dynamics.Label
  source : S.Term
  target : S.Term
  action : Q.dynamics.act label source target

def forwardEvents : AuthoredEvents Q where
  span := { Edge := ForwardEvent Q, source := ForwardEvent.source, target := ForwardEvent.target }
  label := ForwardEvent.label
  sound := ForwardEvent.action
  cover label source target action := ⟨⟨label, source, target, action⟩, rfl, rfl, rfl⟩

variable (events : AuthoredEvents Q)

def stageSpan (stage : Nat) : ReductionSpan.{uS, uEvent} (StageState (twoSided Q past) stage) where
  Edge := events.span.Edge
  source event := stateOf (twoSided Q past) stage (events.span.source event)
  target event := stateOf (twoSided Q past) stage (events.span.target event)

def stageMap (stage : Nat) : ObservationSpans.SpanMap events.span (stageSpan Q past events stage) where
  states := stateOf (twoSided Q past) stage
  events := id
  source_comm _ := rfl
  target_comm _ := rfl

variable (vocabulary : Q.Vocabulary) (stage : Nat) (positive : K.Positive)
variable (stable : (twoSided Q past).Stabilizes (twoSidedVocabulary Q past vocabulary) stage)

include vocabulary positive stable in
theorem match_future (source : S.Term) (event : events.span.Edge)
    (same : stateOf (twoSided Q past) stage (events.span.source event) =
      stateOf (twoSided Q past) stage source) :
    ∃ matched, events.label matched = events.label event ∧ events.span.source matched = source ∧
      stateOf (twoSided Q past) stage (events.span.target matched) =
        stateOf (twoSided Q past) stage (events.span.target event) := by
  have action : (stageSystem (twoSided Q past) stage).act (.forward, events.label event)
      (stateOf (twoSided Q past) stage source)
      (stateOf (twoSided Q past) stage (events.span.target event)) :=
    ⟨events.span.source event, events.span.target event, same, rfl, events.sound event⟩
  obtain ⟨actual, lifted, endpoint⟩ := action_from_stage (twoSided Q past)
    (twoSidedVocabulary Q past vocabulary) stage positive stable _ source action
  obtain ⟨matched, labelEq, sourceEq, targetEq⟩ := events.cover (events.label event) source actual lifted
  exact ⟨matched, labelEq, sourceEq, (congrArg (stateOf (twoSided Q past) stage) targetEq).trans endpoint⟩

include vocabulary positive stable in
theorem match_past (target : S.Term) (event : events.span.Edge)
    (same : stateOf (twoSided Q past) stage (events.span.target event) =
      stateOf (twoSided Q past) stage target) :
    ∃ matched, events.label matched = events.label event ∧ events.span.target matched = target ∧
      stateOf (twoSided Q past) stage (events.span.source matched) =
        stateOf (twoSided Q past) stage (events.span.source event) := by
  have action : (stageSystem (twoSided Q past) stage).act (.backward, events.label event)
      (stateOf (twoSided Q past) stage target)
      (stateOf (twoSided Q past) stage (events.span.source event)) :=
    ⟨events.span.target event, events.span.source event, same, rfl, events.sound event⟩
  obtain ⟨actual, lifted, endpoint⟩ := action_from_stage (twoSided Q past)
    (twoSidedVocabulary Q past vocabulary) stage positive stable _ target action
  obtain ⟨matched, labelEq, sourceEq, targetEq⟩ := events.cover (events.label event) actual target lifted
  exact ⟨matched, labelEq, targetEq, (congrArg (stateOf (twoSided Q past) stage) sourceEq).trans endpoint⟩

include vocabulary positive stable in
theorem source_lifts : (stageMap Q past events stage).SourceLifts := by
  intro source event same
  obtain ⟨matched, _, sourceEq, targetEq⟩ :=
    match_future Q past events vocabulary stage positive stable source event same
  exact ⟨matched, sourceEq, targetEq⟩

include vocabulary positive stable in
theorem target_lifts : (stageMap Q past events stage).TargetLifts := by
  intro target event same
  obtain ⟨matched, _, targetEq, sourceEq⟩ :=
    match_past Q past events vocabulary stage positive stable target event same
  exact ⟨matched, targetEq, sourceEq⟩

include vocabulary positive stable in
theorem future_pullback (predicate : StageState (twoSided Q past) stage → Prop) (source : S.Term) :
    derivedDiamond (stageSpan Q past events stage) predicate (stateOf (twoSided Q past) stage source) ↔
      derivedDiamond events.span (predicate ∘ stateOf (twoSided Q past) stage) source :=
  (stageMap Q past events stage).diamond_pullback
    (source_lifts Q past events vocabulary stage positive stable) predicate source

include vocabulary positive stable in
theorem predecessor_box_pullback (predicate : StageState (twoSided Q past) stage → Prop) (target : S.Term) :
    derivedBox (stageSpan Q past events stage) predicate (stateOf (twoSided Q past) stage target) ↔
      derivedBox events.span (predicate ∘ stateOf (twoSided Q past) stage) target :=
  (stageMap Q past events stage).box_pullback
    (target_lifts Q past events vocabulary stage positive stable) predicate target

theorem future_iff (predicate : S.Term → Prop) (source : S.Term) :
    derivedDiamond events.span predicate source ↔
      ∃ label target, Q.dynamics.act label source target ∧ predicate target := by
  constructor
  · rintro ⟨event, sourceEq, holds⟩
    exact ⟨events.label event, events.span.target event, sourceEq ▸ events.sound event, holds⟩
  · rintro ⟨label, target, action, holds⟩
    obtain ⟨event, _, sourceEq, targetEq⟩ := events.cover label source target action
    exact ⟨event, sourceEq, show predicate (events.span.target event) from targetEq.symm ▸ holds⟩

theorem predecessor_box_iff (predicate : S.Term → Prop) (target : S.Term) :
    derivedBox events.span predicate target ↔
      ∀ label source, Q.dynamics.act label source target → predicate source := by
  constructor
  · intro all label source action
    obtain ⟨event, _, sourceEq, targetEq⟩ := events.cover label source target action
    exact sourceEq ▸ all event targetEq
  · intro all event targetEq
    exact all (events.label event) (events.span.source event) (targetEq ▸ events.sound event)

def futurePredicate (predicate : EquationPredicate S) : EquationPredicate S :=
  invariantPredicate S (derivedDiamond events.span predicate.1) (by
    intro left right same
    rw [future_iff Q events, future_iff Q events]
    exact exists_congr fun label => exists_congr fun target =>
      and_congr ⟨action_source_closed Q same,
        action_source_closed Q (S.equations.iseqv.symm same)⟩ Iff.rfl)

def predecessorBoxPredicate (predicate : EquationPredicate S) : EquationPredicate S :=
  invariantPredicate S (derivedBox events.span predicate.1) (by
    intro left right same
    rw [predecessor_box_iff Q events, predecessor_box_iff Q events]
    constructor
    · intro all label source action
      exact all label source (Q.dynamics.act_resp_right action (S.equations.iseqv.symm same))
    · intro all label source action
      exact all label source (Q.dynamics.act_resp_right action same))

include vocabulary positive stable in
theorem native_future_iff (predicate : EquationPredicate S)
    (invariant : ∀ ⦃left right⦄, (twoSided Q past).GradedBisimilar left right →
      (predicate.1 left ↔ predicate.1 right)) (source : S.Term) :
    derivedDiamond (stageSpan Q past events stage)
        (nativeImage (twoSided Q past) stage predicate) (stateOf (twoSided Q past) stage source) ↔
      (futurePredicate Q events predicate).1 source := by
  rw [future_pullback Q past events vocabulary stage positive stable]
  have exactImage := (nativeImage_exact_iff_graded (twoSided Q past)
    (twoSidedVocabulary Q past vocabulary) stage positive stable predicate).mpr invariant
  have equal : nativeImage (twoSided Q past) stage predicate ∘ stateOf (twoSided Q past) stage =
      predicate.1 := funext fun term => propext (exactImage term)
  rw [equal]
  rfl

include vocabulary positive stable in
theorem native_predecessor_box_iff (predicate : EquationPredicate S)
    (invariant : ∀ ⦃left right⦄, (twoSided Q past).GradedBisimilar left right →
      (predicate.1 left ↔ predicate.1 right)) (target : S.Term) :
    derivedBox (stageSpan Q past events stage)
        (nativeImage (twoSided Q past) stage predicate) (stateOf (twoSided Q past) stage target) ↔
      (predecessorBoxPredicate Q events predicate).1 target := by
  rw [predecessor_box_pullback Q past events vocabulary stage positive stable]
  have exactImage := (nativeImage_exact_iff_graded (twoSided Q past)
    (twoSidedVocabulary Q past vocabulary) stage positive stable predicate).mpr invariant
  have equal : nativeImage (twoSided Q past) stage predicate ∘ stateOf (twoSided Q past) stage =
      predicate.1 := funext fun term => propext (exactImage term)
  rw [equal]
  rfl

include vocabulary positive stable in
theorem formula_future_native_iff
    (formula : Formula (valueSystem (twoSided Q past)).Atom (twoSided Q past).dynamics.Label)
    (source : S.Term) :
    derivedDiamond (stageSpan Q past events stage)
        (nativeImage (twoSided Q past) stage (formulaPredicate (valueSystem (twoSided Q past)) formula))
        (stateOf (twoSided Q past) stage source) ↔
      (futurePredicate Q events (formulaPredicate (valueSystem (twoSided Q past)) formula)).1 source :=
  native_future_iff Q past events vocabulary stage positive stable _
    (fun {_ _} related => logicallyEquivalent_of_graded (twoSided Q past) related formula) source

include vocabulary positive stable in
theorem formula_predecessor_box_native_iff
    (formula : Formula (valueSystem (twoSided Q past)).Atom (twoSided Q past).dynamics.Label)
    (target : S.Term) :
    derivedBox (stageSpan Q past events stage)
        (nativeImage (twoSided Q past) stage (formulaPredicate (valueSystem (twoSided Q past)) formula))
        (stateOf (twoSided Q past) stage target) ↔
      (predecessorBoxPredicate Q events (formulaPredicate (valueSystem (twoSided Q past)) formula)).1 target :=
  native_predecessor_box_iff Q past events vocabulary stage positive stable _
    (fun {_ _} related => logicallyEquivalent_of_graded (twoSided Q past) related formula) target

end Mettapedia.GSLT.GradedTwoSidedObservation
