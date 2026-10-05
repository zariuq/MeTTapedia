import Mettapedia.GSLT.Distinction.HistoryTwoSidedObserver
import Mettapedia.GSLT.Distinction.LevelAccounts

/-!
# The history instance: whole-span, context and substitution coverage

`HistoryObserver` and `HistoryTwoSidedObserver` present the event grammar of
the distinction calculus to the graded observers, with authored successor and
predecessor lists.  This module proves that those lists cover the whole
reduction span with its events, that contexts and renamings of nodes commute
with them and with the readings, and which costs a program can read.

* **Whole-span coverage** (`eventShadow`, `forwardEquiv`, `backwardEquiv`,
  `forward_whole_span`, `backward_whole_span`, `mem_outSteps`, `mem_inSteps`).
  Every edge of the history GSLT's reduction span is the shadow of a labelled
  step at the same endpoints (`eventShadow_sourceOccurrenceLifts`,
  `eventShadow_targetOccurrenceLifts`).  Labelled steps, the entries of the
  authored successor lists and the entries of the authored predecessor lists
  are in bijection, keeping the event and both endpoints; as span relations
  they satisfy the four occurrence laws, keep the event and match the outgoing
  and incoming fibres one to one.  Over a listed node set each fibre is one
  finite list, without repetition when the nodes are listed without
  repetition (`outSteps_nodup`, `inSteps_nodup`).  The authored events of the
  bridge are determined by their action (`labelledEvents_unique`).
* **Contexts** (`fires_add`, `fires_add_iff`, `contextMap`,
  `act_congruent_add`, `lists_congruent_add`).  A parallel context `C` carries every step `s → t` to
  `s + C → t + C` with the same event, forward and backward, and for an event
  that consumes and reads only inside `s` these are all its steps in context.
  The result and fault readings in context are the maximum with the context's
  reading, and the potential is additive (`result_congruent_add`,
  `fault_congruent_add`, `potential_congruent_add`).
* **Substitutions** (`Renaming`, `step_rename`, `unstep_rename`,
  `successors_rename`, `predecessors_rename`, `renameMap`,
  `successors_congruent_rename`, `predecessors_congruent_rename`).  An injective
  renaming of nodes that commutes with evolution and merge commutes exactly
  with the authored lists in both directions, and with the readings after
  renaming them (`reading_rename`).  Every step leaving a renamed configuration
  is the renaming of a step (`renameMap_sourceOccurrenceLifts`).
* **Readings** (`result_fault_fibres`, `history_fault_not_fault_reading`).  The
  result and fault readings are separate: neither is a function of the other,
  and a fault of a history (an event that is not enabled) is not a faulty live
  node.
* **Costs: readable or in the account** (`readable_tfae`,
  `readable_reflected`, `reflected_readable`).  For an event cost in a
  commutative group the following are equivalent: the potential laws hold for
  some node potential; the cost of every run is the change of some reading of
  configurations; every closed run costs nothing; replaying any run for any
  other with the same endpoints is qualified for its account.  Then the
  observer's cost reading reflects it on runs within budget.  Every cost, read
  or not, is an account of runs (`costAccount`); one unit of work per event is
  not readable, and its replay of a loop by the empty run is not qualified
  (`unitWork_not_readable`, `levels_replay`).

**Where choice enters.**  As in `HistoryObserver`: the firing relation and
everything over it use Mathlib's `Multiset.erase`, multiset subtraction and the
decidable order of multisets, which carry `Classical.choice` through
`List.perm_cons_erase`, `List.Perm.erase` and `List.Perm.diff`.  The generic
lemmas on the largest reading (`best_add`, `best_map`) do not.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryCoverage

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.GSLT.Distinction.HistoryObserver
open Mettapedia.GSLT.Distinction.HistoryObserverControls (relabel fires_map)
open Mettapedia.GSLT.Distinction.HistoryTwoSidedObserver
open Mettapedia.GSLT.Distinction.Constructive
open Mettapedia.GSLT.Distinction.SpanTransport
open Mettapedia.GSLT.GradedTwoSidedObservation
open Mettapedia.Cybernetics.DistinctionCalculus.History
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-! ## The largest reading in context and after renaming -/

section Best

universe uA uB uV

variable {α : Type uA} {β : Type uB} {W : Type uV} [Zero W] [LinearOrder W]

/-- The largest reading of a parallel composition is the larger of the two. -/
theorem best_add (f : α → W) (live context : Multiset α) :
    best f (live + context) = max (best f live) (best f context) := by
  induction live using Multiset.induction_on with
  | empty => rw [Multiset.zero_add, best_zero, max_eq_right (best_nonneg f context)]
  | cons x rest inductionHypothesis =>
      rw [Multiset.cons_add, best_cons, best_cons, inductionHypothesis, max_assoc]

/-- The largest reading of a renamed configuration is the largest renamed
reading. -/
theorem best_map (f : β → W) (rename : α → β) (live : Multiset α) :
    best f (live.map rename) = best (f ∘ rename) live := by
  induction live using Multiset.induction_on with
  | empty => rw [Multiset.map_zero, best_zero, best_zero]
  | cons x rest inductionHypothesis =>
      rw [Multiset.map_cons, best_cons, best_cons, inductionHypothesis]
      rfl

end Best

variable {V : Type} [DecidableEq V] (G : Grammar V)

/-! ## Whole-span coverage -/

/-- **The event shadow**: a labelled step forgets its event and is an edge of
the history GSLT's reduction span. -/
def eventShadow : SpanMap (labelledSpan G) (gsltSpan (historyGSLT G)) where
  states := id
  events step := ⟨step.1.2.1, step.1.2.2, ⟨step.1.1, step.2⟩⟩
  source_comm _ := rfl
  target_comm _ := rfl

/-- **Every edge of the GSLT's reduction span leaving a configuration is the
shadow of a labelled step leaving it.** -/
theorem eventShadow_sourceOccurrenceLifts : (eventShadow G).SourceOccurrenceLifts := by
  rintro state ⟨source, target, event, fires⟩ sourceEq
  exact ⟨⟨(event, source, target), fires⟩, sourceEq, rfl⟩

/-- **Every edge of the GSLT's reduction span reaching a configuration is the
shadow of a labelled step reaching it.** -/
theorem eventShadow_targetOccurrenceLifts : (eventShadow G).TargetOccurrenceLifts := by
  rintro state ⟨source, target, event, fires⟩ targetEq
  exact ⟨⟨(event, source, target), fires⟩, targetEq, rfl⟩

/-- An entry of the authored successor lists: an event, a configuration and one
of its listed successors. -/
structure ForwardEntry (G : Grammar V) where
  event : Event V
  source : Multiset V
  target : Multiset V
  listed : target ∈ successors G event source

/-- An entry of the authored predecessor lists: an event, a configuration and
one of its listed predecessors. -/
structure BackwardEntry (G : Grammar V) where
  event : Event V
  source : Multiset V
  target : Multiset V
  listed : source ∈ predecessors G event target

/-- The span of authored successor entries. -/
def forwardSpan : ReductionSpan (Multiset V) where
  Edge := ForwardEntry G
  source := ForwardEntry.source
  target := ForwardEntry.target

/-- The span of authored predecessor entries. -/
def backwardSpan : ReductionSpan (Multiset V) where
  Edge := BackwardEntry G
  source := BackwardEntry.source
  target := BackwardEntry.target

/-- **Labelled steps are the successor entries**, with their events and both
endpoints. -/
def forwardEquiv : LabelledStep G ≃ ForwardEntry G where
  toFun step := ⟨step.1.1, step.1.2.1, step.1.2.2, (mem_successors G).mpr step.2⟩
  invFun entry := ⟨(entry.event, entry.source, entry.target), (mem_successors G).mp entry.listed⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Labelled steps are the predecessor entries**, with their events and both
endpoints. -/
def backwardEquiv : LabelledStep G ≃ BackwardEntry G where
  toFun step := ⟨step.1.1, step.1.2.1, step.1.2.2, (mem_predecessors G).mpr step.2⟩
  invFun entry := ⟨(entry.event, entry.source, entry.target), (mem_predecessors G).mp entry.listed⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The labelled span read through the successor entries. -/
def toForward : SpanMap (labelledSpan G) (forwardSpan G) where
  states := id
  events := forwardEquiv G
  source_comm _ := rfl
  target_comm _ := rfl

/-- The labelled span read through the predecessor entries. -/
def toBackward : SpanMap (labelledSpan G) (backwardSpan G) where
  states := id
  events := backwardEquiv G
  source_comm _ := rfl
  target_comm _ := rfl

theorem toForward_sourceOccurrenceLifts : (toForward G).SourceOccurrenceLifts :=
  fun _ entry sourceEq => ⟨(forwardEquiv G).symm entry, sourceEq, (forwardEquiv G).apply_symm_apply entry⟩

theorem toForward_targetOccurrenceLifts : (toForward G).TargetOccurrenceLifts :=
  fun _ entry targetEq => ⟨(forwardEquiv G).symm entry, targetEq, (forwardEquiv G).apply_symm_apply entry⟩

theorem toBackward_sourceOccurrenceLifts : (toBackward G).SourceOccurrenceLifts :=
  fun _ entry sourceEq => ⟨(backwardEquiv G).symm entry, sourceEq, (backwardEquiv G).apply_symm_apply entry⟩

theorem toBackward_targetOccurrenceLifts : (toBackward G).TargetOccurrenceLifts :=
  fun _ entry targetEq => ⟨(backwardEquiv G).symm entry, targetEq, (backwardEquiv G).apply_symm_apply entry⟩

/-- The fibres of a span equivalence that is the identity on states. -/
def fibreEquiv {A B : ReductionSpan (Multiset V)} (events : A.Edge ≃ B.Edge)
    (source : ∀ edge, B.source (events edge) = A.source edge) (state : Multiset V) :
    {edge : A.Edge // A.source edge = state} ≃ {edge : B.Edge // B.source edge = state} :=
  Equiv.subtypeEquiv events fun edge => by rw [source edge]

/-- The incoming fibres of a span equivalence that is the identity on states. -/
def inFibreEquiv {A B : ReductionSpan (Multiset V)} (events : A.Edge ≃ B.Edge)
    (target : ∀ edge, B.target (events edge) = A.target edge) (state : Multiset V) :
    {edge : A.Edge // A.target edge = state} ≃ {edge : B.Edge // B.target edge = state} :=
  Equiv.subtypeEquiv events fun edge => by rw [target edge]

/-- **Whole-span coverage, forward.** As a relation of spans, reading labelled
steps as authored successor entries satisfies all four occurrence laws, keeps
the event, and matches outgoing and incoming fibres one to one. -/
theorem forward_whole_span :
    (SpanRelation.ofSpanMap (toForward G)).SourceForthOcc ∧
      (SpanRelation.ofSpanMap (toForward G)).SourceBackOcc ∧
      (SpanRelation.ofSpanMap (toForward G)).TargetForthOcc ∧
      (SpanRelation.ofSpanMap (toForward G)).TargetBackOcc ∧
      (SpanRelation.ofSpanMap (toForward G)).Keeps (LabelledStep.event G) ForwardEntry.event ∧
      (SpanRelation.ofSpanMap (toForward G)).OutFibresMatch ∧
      (SpanRelation.ofSpanMap (toForward G)).InFibresMatch := by
  refine ⟨SpanRelation.ofSpanMap_sourceForthOcc _,
    (SpanRelation.ofSpanMap_sourceBackOcc_iff _).mpr (toForward_sourceOccurrenceLifts G),
    SpanRelation.ofSpanMap_targetForthOcc _,
    (SpanRelation.ofSpanMap_targetBackOcc_iff _).mpr (toForward_targetOccurrenceLifts G),
    ?_, ?_, ?_⟩
  · rintro step _ rfl
    rfl
  · rintro state _ rfl
    exact ⟨fibreEquiv (A := labelledSpan G) (B := forwardSpan G) (forwardEquiv G) (fun _ => rfl) state,
      fun _ => rfl⟩
  · rintro state _ rfl
    exact ⟨inFibreEquiv (A := labelledSpan G) (B := forwardSpan G) (forwardEquiv G) (fun _ => rfl) state,
      fun _ => rfl⟩

/-- **Whole-span coverage, backward.** The same for the authored predecessor
entries. -/
theorem backward_whole_span :
    (SpanRelation.ofSpanMap (toBackward G)).SourceForthOcc ∧
      (SpanRelation.ofSpanMap (toBackward G)).SourceBackOcc ∧
      (SpanRelation.ofSpanMap (toBackward G)).TargetForthOcc ∧
      (SpanRelation.ofSpanMap (toBackward G)).TargetBackOcc ∧
      (SpanRelation.ofSpanMap (toBackward G)).Keeps (LabelledStep.event G) BackwardEntry.event ∧
      (SpanRelation.ofSpanMap (toBackward G)).OutFibresMatch ∧
      (SpanRelation.ofSpanMap (toBackward G)).InFibresMatch := by
  refine ⟨SpanRelation.ofSpanMap_sourceForthOcc _,
    (SpanRelation.ofSpanMap_sourceBackOcc_iff _).mpr (toBackward_sourceOccurrenceLifts G),
    SpanRelation.ofSpanMap_targetForthOcc _,
    (SpanRelation.ofSpanMap_targetBackOcc_iff _).mpr (toBackward_targetOccurrenceLifts G),
    ?_, ?_, ?_⟩
  · rintro step _ rfl
    rfl
  · rintro state _ rfl
    exact ⟨fibreEquiv (A := labelledSpan G) (B := backwardSpan G) (backwardEquiv G) (fun _ => rfl) state,
      fun _ => rfl⟩
  · rintro state _ rfl
    exact ⟨inFibreEquiv (A := labelledSpan G) (B := backwardSpan G) (backwardEquiv G) (fun _ => rfl) state,
      fun _ => rfl⟩

section Observer

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)

/-- A successor entry is an entry of the two-sided observer's forward list. -/
theorem forwardEntry_observer (R : NodeReadings K V) (entry : ForwardEntry G) :
    entry.target ∈ (observer G K R).successors (.forward, entry.event) entry.source :=
  entry.listed

/-- A predecessor entry is an entry of the two-sided observer's backward list. -/
theorem backwardEntry_observer (R : NodeReadings K V) (entry : BackwardEntry G) :
    entry.source ∈ (observer G K R).successors (.backward, entry.event) entry.target :=
  entry.listed

/-- **The bridge's authored labelled events are determined by their action**:
two with the same event and endpoints are equal. -/
theorem labelledEvents_unique (R : NodeReadings K V) (first second : (labelledEvents G K R).span.Edge)
    (label : (labelledEvents G K R).label first = (labelledEvents G K R).label second)
    (source : (labelledEvents G K R).span.source first = (labelledEvents G K R).span.source second)
    (target : (labelledEvents G K R).span.target first = (labelledEvents G K R).span.target second) :
    first = second :=
  Subtype.ext (Prod.ext label (Prod.ext source target))

end Observer

/-! ### Finite fibres over a listed node set -/

/-- The labelled steps leaving a configuration, read from the authored successor
list of every listed event. -/
def outSteps (L : Listing V) (source : Multiset V) : List (LabelledStep G) :=
  L.events.flatMap fun event =>
    (successors G event source).attach.map fun target =>
      ⟨(event, source, target.1), (mem_successors G).mp target.2⟩

/-- The labelled steps reaching a configuration, read from the authored
predecessor list of every listed event. -/
def inSteps (L : Listing V) (target : Multiset V) : List (LabelledStep G) :=
  L.events.flatMap fun event =>
    (predecessors G event target).attach.map fun source =>
      ⟨(event, source.1, target), (mem_predecessors G).mp source.2⟩

/-- **The outgoing fibre is the listed one**: a labelled step is in the list of
a configuration exactly when it leaves that configuration. -/
theorem mem_outSteps (L : Listing V) (source : Multiset V) (step : LabelledStep G) :
    step ∈ outSteps G L source ↔ step.1.2.1 = source := by
  constructor
  · intro member
    obtain ⟨_, _, member⟩ := List.mem_flatMap.mp member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    rfl
  · obtain ⟨⟨event, source', target⟩, fires⟩ := step
    rintro rfl
    exact List.mem_flatMap.mpr ⟨event, L.mem_events event,
      List.mem_map.mpr ⟨⟨target, (mem_successors G).mpr fires⟩, List.mem_attach _ _, rfl⟩⟩

/-- **The incoming fibre is the listed one.** -/
theorem mem_inSteps (L : Listing V) (target : Multiset V) (step : LabelledStep G) :
    step ∈ inSteps G L target ↔ step.1.2.2 = target := by
  constructor
  · intro member
    obtain ⟨_, _, member⟩ := List.mem_flatMap.mp member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    rfl
  · obtain ⟨⟨event, source, target'⟩, fires⟩ := step
    rintro rfl
    exact List.mem_flatMap.mpr ⟨event, L.mem_events event,
      List.mem_map.mpr ⟨⟨source, (mem_predecessors G).mpr fires⟩, List.mem_attach _ _, rfl⟩⟩

omit [DecidableEq V] in
/-- Listing distinct nodes lists distinct events. -/
theorem events_nodup (L : Listing V) (distinct : L.nodes.Nodup) : L.events.Nodup := by
  have evolveInjective : Function.Injective (Event.evolve : V → Event V) :=
    fun _ _ same => by cases same; rfl
  have forkInjective : Function.Injective (Event.fork : V → Event V) :=
    fun _ _ same => by cases same; rfl
  have eraseInjective : Function.Injective (Event.erase : V → Event V) :=
    fun _ _ same => by cases same; rfl
  have mergeNodup : (L.nodes.flatMap fun x => L.nodes.map (Event.merge x)).Nodup := by
    refine List.nodup_flatMap.mpr ⟨fun x _ => distinct.map fun _ _ same => by cases same; rfl, ?_⟩
    refine distinct.imp fun {x x'} different => ?_
    intro event first second
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp first
    obtain ⟨y', _, same⟩ := List.mem_map.mp second
    cases same
    exact different rfl
  unfold Listing.events
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr
    ⟨distinct.map evolveInjective, distinct.map forkInjective, ?_⟩, mergeNodup, ?_⟩,
    distinct.map eraseInjective, ?_⟩
  · intro first firstMember second secondMember same
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp secondMember
    cases same
  · intro first firstMember second secondMember same
    obtain ⟨_, _, member⟩ := List.mem_flatMap.mp secondMember
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp firstMember with member | member <;>
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member <;> cases same
  · intro first firstMember second secondMember same
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp secondMember
    rcases List.mem_append.mp firstMember with member | member
    · rcases List.mem_append.mp member with member | member <;>
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp member <;> cases same
    · obtain ⟨_, _, member⟩ := List.mem_flatMap.mp member
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      cases same

/-- **Over distinct listed nodes the outgoing list has no repetition**: every
labelled step leaving a configuration is listed exactly once. -/
theorem outSteps_nodup (L : Listing V) (distinct : L.nodes.Nodup) (source : Multiset V) :
    (outSteps G L source).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun event _ => ?_, ?_⟩
  · refine (List.nodup_attach.mpr ?_).map fun first second same => ?_
    · unfold successors
      cases step G event source <;> simp
    · exact Subtype.ext (congrArg (fun step : LabelledStep G => step.1.2.2) same)
  · refine (events_nodup L distinct).imp fun {event event'} different => ?_
    intro step first second
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp first
    obtain ⟨_, _, same⟩ := List.mem_map.mp second
    exact different (congrArg (fun step : LabelledStep G => step.1.1) same).symm

/-- **Over distinct listed nodes the incoming list has no repetition.** -/
theorem inSteps_nodup (L : Listing V) (distinct : L.nodes.Nodup) (target : Multiset V) :
    (inSteps G L target).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun event _ => ?_, ?_⟩
  · refine (List.nodup_attach.mpr ?_).map fun first second same => ?_
    · unfold predecessors
      cases unstep G event target <;> simp
    · exact Subtype.ext (congrArg (fun step : LabelledStep G => step.1.2.1) same)
  · refine (events_nodup L distinct).imp fun {event event'} different => ?_
    intro step first second
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp first
    obtain ⟨_, _, same⟩ := List.mem_map.mp second
    exact different (congrArg (fun step : LabelledStep G => step.1.1) same).symm

/-! ## Contexts -/

/-- **A parallel context carries every step**, with the same event. -/
theorem fires_add (context : Multiset V) {event : Event V} {source target : Multiset V}
    (fires : Fires G event source target) : Fires G event (source + context) (target + context) := by
  cases fires with
  | @evolve x _ member =>
      have fired := Fires.evolve (G := G) (Multiset.mem_add.mpr (Or.inl member) : x ∈ source + context)
      rwa [Multiset.erase_add_left_pos context member, ← Multiset.cons_add] at fired
  | @fork x _ member =>
      have fired := Fires.fork (G := G) (Multiset.mem_add.mpr (Or.inl member) : x ∈ source + context)
      rwa [← Multiset.cons_add] at fired
  | @merge x y _ enabled =>
      have fired := Fires.merge (G := G) (enabled.trans (Multiset.le_add_right source context))
      rwa [← tsub_add_eq_add_tsub enabled, ← Multiset.cons_add] at fired
  | @erase x _ member =>
      have fired := Fires.erase (G := G) (Multiset.mem_add.mpr (Or.inl member) : x ∈ source + context)
      rwa [Multiset.erase_add_left_pos context member] at fired

/-- **For an event local to a configuration, its steps in context are exactly
its steps in place, with the context added.** -/
theorem fires_add_iff (context : Multiset V) {event : Event V} {source : Multiset V}
    (inPlace : HistoryIndependence.consumed event + HistoryIndependence.read event ≤ source)
    (result : Multiset V) :
    Fires G event (source + context) result ↔
      ∃ target, result = target + context ∧ Fires G event source target := by
  constructor
  · intro fires
    obtain ⟨_, resultEq⟩ := (HistoryIndependence.fires_iff G event _ result).mp fires
    have consumedLe : HistoryIndependence.consumed event ≤ source :=
      (Multiset.le_add_right _ _).trans inPlace
    refine ⟨source - HistoryIndependence.consumed event + HistoryIndependence.produced G event, ?_,
      (HistoryIndependence.fires_iff G event source _).mpr ⟨inPlace, rfl⟩⟩
    rw [resultEq, ← tsub_add_eq_add_tsub consumedLe, add_right_comm]
  · rintro ⟨target, rfl, fires⟩
    exact fires_add G context fires

theorem step_add (context : Multiset V) {event : Event V} {source target : Multiset V}
    (fired : step G event source = some target) :
    step G event (source + context) = some (target + context) :=
  (step_eq_some_iff G event _ _).mpr (fires_add G context ((step_eq_some_iff G event _ _).mp fired))

theorem unstep_add (context : Multiset V) {event : Event V} {source target : Multiset V}
    (undone : unstep G event target = some source) :
    unstep G event (target + context) = some (source + context) :=
  (unstep_eq_some_iff G event _ _).mpr (fires_add G context ((unstep_eq_some_iff G event _ _).mp undone))

/-- **The authored successor list in context**: a listed successor becomes the
only successor in context. -/
theorem successors_add (context : Multiset V) {event : Event V} {source target : Multiset V}
    (member : target ∈ successors G event source) :
    successors G event (source + context) = [target + context] := by
  unfold successors
  rw [step_add G context (mem_toList_iff.mp member)]
  rfl

/-- **The authored predecessor list in context.** -/
theorem predecessors_add (context : Multiset V) {event : Event V} {source target : Multiset V}
    (member : source ∈ predecessors G event target) :
    predecessors G event (target + context) = [source + context] := by
  unfold predecessors
  rw [unstep_add G context (mem_toList_iff.mp member)]
  rfl

/-- **Contexts act on the whole labelled span**, keeping every event. -/
def contextMap (context : Multiset V) : SpanMap (labelledSpan G) (labelledSpan G) where
  states live := live + context
  events step := ⟨(step.1.1, step.1.2.1 + context, step.1.2.2 + context), fires_add G context step.2⟩
  source_comm _ := rfl
  target_comm _ := rfl

theorem contextMap_event (context : Multiset V) (step : LabelledStep G) :
    ((contextMap G context).events step).1.1 = step.1.1 := rfl

section ContextReadings

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)

/-- **Every two-sided action is a congruence for every context.** -/
theorem act_congruent_add (R : NodeReadings K V) (context : Multiset V)
    (label : Direction × Event V) :
    Congruent ((observer G K R).dynamics.act label) (· + context) (· + context) := by
  rcases label with ⟨direction, event⟩
  cases direction with
  | forward => exact fun _ _ fires => fires_add G context fires
  | backward => exact fun _ _ fires => fires_add G context fires

/-- **The observer's authored lists are a congruence for every context**,
forward and backward: a listed entry in place gives a listed entry in context. -/
theorem lists_congruent_add (R : NodeReadings K V) (context : Multiset V)
    (label : Direction × Event V) :
    Congruent (fun live entry => entry ∈ (observer G K R).successors label live)
      (· + context) (· + context) := by
  rcases label with ⟨direction, event⟩
  cases direction with
  | forward =>
      intro source target member
      change target + context ∈ successors G event (source + context)
      rw [successors_add G context member]
      exact List.mem_singleton_self _
  | backward =>
      intro target source member
      change source + context ∈ predecessors G event (target + context)
      rw [predecessors_add G context member]
      exact List.mem_singleton_self _

/-- The GSLT's steps are a congruence for every context. -/
theorem step_congruent_add (context : Multiset V) :
    Congruent (historyGSLT G).Step (· + context) (· + context) :=
  fun _ _ step => let ⟨event, fires⟩ := step; ⟨event, fires_add G context fires⟩

omit [DecidableEq V] in
theorem result_add (R : NodeReadings K V) (live context : Multiset V) :
    reading K R .result (live + context) =
      max (reading K R .result live) (reading K R .result context) :=
  best_add _ _ _

omit [DecidableEq V] in
theorem fault_add (R : NodeReadings K V) (live context : Multiset V) :
    reading K R .fault (live + context) =
      max (reading K R .fault live) (reading K R .fault context) :=
  best_add _ _ _

omit [DecidableEq V] [LinearOrder W] [IsOrderedAddMonoid W] in
theorem potentialSum_add (potential : V → W) (live context : Multiset V) :
    potentialSum potential (live + context) = potentialSum potential live + potentialSum potential context := by
  simp [potentialSum]

omit [DecidableEq V] in
/-- **The result reading is congruent for contexts**: in context it is the
larger of the configuration's and the context's. -/
theorem result_congruent_add (R : NodeReadings K V) (context : Multiset V) :
    Congruent (fun live value => reading K R .result live = value) (· + context)
      (fun value => max value (reading K R .result context)) := by
  rintro live _ rfl
  exact result_add K R live context

omit [DecidableEq V] in
/-- **The fault reading is congruent for contexts.** -/
theorem fault_congruent_add (R : NodeReadings K V) (context : Multiset V) :
    Congruent (fun live value => reading K R .fault live = value) (· + context)
      (fun value => max value (reading K R .fault context)) := by
  rintro live _ rfl
  exact fault_add K R live context

omit [DecidableEq V] [LinearOrder W] [IsOrderedAddMonoid W] in
/-- **The potential is congruent for contexts**: it is additive. -/
theorem potential_congruent_add (potential : V → W) (context : Multiset V) :
    Congruent (fun live value => potentialSum potential live = value) (· + context)
      (· + potentialSum potential context) := by
  rintro live _ rfl
  exact potentialSum_add potential live context

/-- **Two-sided graded bisimilarity is a congruence for every context**: the
observer is faithful. -/
theorem gradedBisimilar_congruent_add (R : NodeReadings K V) (context : Multiset V) :
    Congruent (observer G K R).GradedBisimilar (· + context) (· + context) := by
  intro left right bisimilar
  rw [(observer_gradedBisimilar_iff_eq G K R left right).mp bisimilar]
  exact (observer_gradedBisimilar_iff_eq G K R _ _).mpr rfl

end ContextReadings

/-! ## Substitutions: renamings of node identities -/

/-- **A renaming of node identities** that commutes with the grammar: an
injective substitution of nodes. -/
structure Renaming (G : Grammar V) where
  map : V → V
  injective : Function.Injective map
  evolve_comm : ∀ x, map (G.evolve x) = G.evolve (map x)
  merge_comm : ∀ x y, map (G.merge x y) = G.merge (map x) (map y)

namespace Renaming

variable {G}

omit [DecidableEq V] in
theorem ext {first second : Renaming G} (same : first.map = second.map) : first = second := by
  cases first
  cases second
  cases same
  rfl

/-- The identity renaming. -/
protected def id (G : Grammar V) : Renaming G where
  map x := x
  injective _ _ same := same
  evolve_comm _ := rfl
  merge_comm _ _ := rfl

/-- One renaming after another. -/
def comp (first second : Renaming G) : Renaming G where
  map x := second.map (first.map x)
  injective := second.injective.comp first.injective
  evolve_comm x := by rw [first.evolve_comm, second.evolve_comm]
  merge_comm x y := by rw [first.merge_comm, second.merge_comm]

end Renaming

omit [DecidableEq V] in
theorem pair_map {β : Type} (f : V → β) (x y : V) : (pair x y).map f = pair (f x) (f y) := by
  simp [pair]

theorem map_sub_of_le {β : Type} [DecidableEq β] (f : V → β) {part live : Multiset V}
    (le : part ≤ live) : (live - part).map f = live.map f - part.map f := by
  conv_rhs => rw [← tsub_add_cancel_of_le le]
  rw [Multiset.map_add, add_tsub_cancel_right]

/-- **Renaming commutes exactly with firing**: the renamed event fires on the
renamed configuration exactly when the event fires, to the renamed result. -/
theorem step_rename (rename : Renaming G) (event : Event V) (source : Multiset V) :
    step G (relabel rename.map event) (source.map rename.map) =
      (step G event source).map (Multiset.map rename.map) := by
  cases event with
  | evolve x =>
      simp only [relabel, step, Multiset.mem_map_of_injective rename.injective]
      split_ifs
      · rw [Option.map_some, Multiset.map_cons, rename.evolve_comm,
          Multiset.map_erase rename.map rename.injective]
      · rfl
  | fork x =>
      simp only [relabel, step, Multiset.mem_map_of_injective rename.injective]
      split_ifs
      · rw [Option.map_some, Multiset.map_cons]
      · rfl
  | merge x y =>
      simp only [relabel, step, ← pair_map, Multiset.map_le_map_iff rename.injective]
      split_ifs with enabled
      · rw [Option.map_some, Multiset.map_cons, rename.merge_comm, map_sub_of_le rename.map enabled]
      · rfl
  | erase x =>
      simp only [relabel, step, Multiset.mem_map_of_injective rename.injective]
      split_ifs
      · rw [Option.map_some, Multiset.map_erase rename.map rename.injective]
      · rfl

/-- **Renaming commutes exactly with undoing.** -/
theorem unstep_rename (rename : Renaming G) (event : Event V) (target : Multiset V) :
    unstep G (relabel rename.map event) (target.map rename.map) =
      (unstep G event target).map (Multiset.map rename.map) := by
  cases event with
  | evolve x =>
      simp only [relabel, unstep, ← rename.evolve_comm, Multiset.mem_map_of_injective rename.injective]
      split_ifs
      · rw [Option.map_some, Multiset.map_cons, Multiset.map_erase rename.map rename.injective]
      · rfl
  | fork x =>
      simp only [relabel, unstep, ← Multiset.map_erase rename.map rename.injective,
        Multiset.mem_map_of_injective rename.injective]
      split_ifs
      · rw [Option.map_some]
      · rfl
  | merge x y =>
      simp only [relabel, unstep, ← rename.merge_comm, Multiset.mem_map_of_injective rename.injective]
      split_ifs
      · rw [Option.map_some, Multiset.map_add, pair_map, Multiset.map_erase rename.map rename.injective]
      · rfl
  | erase x =>
      simp only [relabel, unstep, Option.map_some, Multiset.map_cons]

/-- **The authored successor lists commute with renaming.** -/
theorem successors_rename (rename : Renaming G) (event : Event V) (source : Multiset V) :
    successors G (relabel rename.map event) (source.map rename.map) =
      (successors G event source).map (Multiset.map rename.map) := by
  unfold successors
  rw [step_rename, Option.toList_map]

/-- **The authored predecessor lists commute with renaming.** -/
theorem predecessors_rename (rename : Renaming G) (event : Event V) (target : Multiset V) :
    predecessors G (relabel rename.map event) (target.map rename.map) =
      (predecessors G event target).map (Multiset.map rename.map) := by
  unfold predecessors
  rw [unstep_rename, Option.toList_map]

/-- **The steps of a renamed event from a renamed configuration are exactly the
renamed steps.** -/
theorem fires_rename_iff (rename : Renaming G) (event : Event V) (source result : Multiset V) :
    Fires G (relabel rename.map event) (source.map rename.map) result ↔
      ∃ target, result = target.map rename.map ∧ Fires G event source target := by
  rw [← step_eq_some_iff, step_rename, Option.map_eq_some_iff]
  constructor
  · rintro ⟨target, fired, rfl⟩
    exact ⟨target, rfl, (step_eq_some_iff G event source target).mp fired⟩
  · rintro ⟨target, rfl, fires⟩
    exact ⟨target, (step_eq_some_iff G event source target).mpr fires, rfl⟩

/-- **The steps of a renamed configuration are renamed steps**: every enabled
event names live, hence renamed, nodes. -/
theorem relabel_of_fires (rename : Renaming G) {event : Event V} {source : Multiset V}
    {result : Multiset V} (fires : Fires G event (source.map rename.map) result) :
    ∃ original, event = relabel rename.map original := by
  have mapped : ∀ {z : V}, z ∈ source.map rename.map → ∃ x, rename.map x = z := by
    intro z member
    obtain ⟨x, _, same⟩ := Multiset.mem_map.mp member
    exact ⟨x, same⟩
  cases fires with
  | evolve member =>
      obtain ⟨x, rfl⟩ := mapped member
      exact ⟨.evolve x, rfl⟩
  | fork member =>
      obtain ⟨x, rfl⟩ := mapped member
      exact ⟨.fork x, rfl⟩
  | @merge z w _ enabled =>
      obtain ⟨x, rfl⟩ := mapped (z := z) (Multiset.mem_of_le enabled (by simp [pair]))
      obtain ⟨y, rfl⟩ := mapped (z := w) (Multiset.mem_of_le enabled (by simp [pair]))
      exact ⟨.merge x y, rfl⟩
  | erase member =>
      obtain ⟨x, rfl⟩ := mapped member
      exact ⟨.erase x, rfl⟩

/-- **Renamings act on the whole labelled span**, renaming every event. -/
def renameMap (rename : Renaming G) : SpanMap (labelledSpan G) (labelledSpan G) where
  states := Multiset.map rename.map
  events step := ⟨(relabel rename.map step.1.1, step.1.2.1.map rename.map, step.1.2.2.map rename.map),
    fires_map G rename.map rename.injective rename.evolve_comm rename.merge_comm step.2⟩
  source_comm _ := rfl
  target_comm _ := rfl

theorem renameMap_event (rename : Renaming G) (step : LabelledStep G) :
    ((renameMap G rename).events step).1.1 = relabel rename.map step.1.1 := rfl

/-- **Every labelled step leaving a renamed configuration is the renaming of a
labelled step.** -/
theorem renameMap_sourceOccurrenceLifts (rename : Renaming G) :
    (renameMap G rename).SourceOccurrenceLifts := by
  rintro source ⟨⟨event, start, result⟩, fires⟩ sourceEq
  change start = source.map rename.map at sourceEq
  subst sourceEq
  obtain ⟨original, rfl⟩ := relabel_of_fires G rename fires
  obtain ⟨target, rfl, fires'⟩ := (fires_rename_iff G rename original source result).mp fires
  exact ⟨⟨(original, source, target), fires'⟩, rfl, rfl⟩

/-- **Renaming is a congruence of the labelled firing relation.** -/
theorem fires_congruent_rename (rename : Renaming G) :
    Congruent (fun (labelled : Event V × Multiset V) target => Fires G labelled.1 labelled.2 target)
      (Prod.map (relabel rename.map) (Multiset.map rename.map)) (Multiset.map rename.map) :=
  fun _ _ fires => fires_map G rename.map rename.injective rename.evolve_comm rename.merge_comm fires

/-- **The authored successor lists are a congruence for every renaming**, with
the renamed event. -/
theorem successors_congruent_rename (rename : Renaming G) :
    Congruent (fun (labelled : Event V × Multiset V) target => target ∈ successors G labelled.1 labelled.2)
      (Prod.map (relabel rename.map) (Multiset.map rename.map)) (Multiset.map rename.map) := by
  rintro ⟨event, source⟩ target member
  change target.map rename.map ∈ successors G (relabel rename.map event) (source.map rename.map)
  rw [successors_rename]
  exact List.mem_map_of_mem member

/-- **The authored predecessor lists are a congruence for every renaming.** -/
theorem predecessors_congruent_rename (rename : Renaming G) :
    Congruent (fun (labelled : Event V × Multiset V) source => source ∈ predecessors G labelled.1 labelled.2)
      (Prod.map (relabel rename.map) (Multiset.map rename.map)) (Multiset.map rename.map) := by
  rintro ⟨event, target⟩ source member
  change source.map rename.map ∈ predecessors G (relabel rename.map event) (target.map rename.map)
  rw [predecessors_rename]
  exact List.mem_map_of_mem member

/-- The GSLT's steps are a congruence for every renaming. -/
theorem step_congruent_rename (rename : Renaming G) :
    Congruent (historyGSLT G).Step (Multiset.map rename.map) (Multiset.map rename.map) :=
  fun _ _ step => let ⟨event, fires⟩ := step
    ⟨relabel rename.map event, fires_map G rename.map rename.injective rename.evolve_comm
      rename.merge_comm fires⟩

section RenameReadings

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)

/-- **Every two-sided action of the observer is carried by a renaming to the
renamed action.** -/
theorem act_rename (R : NodeReadings K V) (rename : Renaming G) (direction : Direction)
    (event : Event V) {source target : Multiset V}
    (action : (observer G K R).dynamics.act (direction, event) source target) :
    (observer G K R).dynamics.act (direction, relabel rename.map event)
      (source.map rename.map) (target.map rename.map) := by
  cases direction with
  | forward => exact fires_map G rename.map rename.injective rename.evolve_comm rename.merge_comm action
  | backward => exact fires_map G rename.map rename.injective rename.evolve_comm rename.merge_comm action

/-- The readings of renamed nodes. -/
def renamedReadings (R : NodeReadings K V) (rename : V → V) : NodeReadings K V where
  result x := R.result (rename x)
  result_nonneg _ := R.result_nonneg _
  result_le_one _ := R.result_le_one _
  faulty x := R.faulty (rename x)
  potential x := R.potential (rename x)

omit [DecidableEq V] in
/-- **The readings of a renamed configuration are the renamed readings.** -/
theorem reading_rename (R : NodeReadings K V) (rename : V → V) (observation : Reading)
    (live : Multiset V) :
    reading K R observation (live.map rename) = reading K (renamedReadings K R rename) observation live := by
  cases observation with
  | result => exact best_map _ _ _
  | fault => exact best_map _ _ _
  | cost =>
      change K.clamp (potentialSum R.potential (live.map rename)) =
        K.clamp (potentialSum (fun x => R.potential (rename x)) live)
      simp only [potentialSum, Multiset.map_map]
      rfl

omit [DecidableEq V] in
/-- **Readings invariant under a renaming are congruent for it.** -/
theorem reading_congruent_rename (R : NodeReadings K V) (rename : V → V)
    (resultInvariant : ∀ x, R.result (rename x) = R.result x)
    (faultInvariant : ∀ x, R.faulty (rename x) = R.faulty x)
    (potentialInvariant : ∀ x, R.potential (rename x) = R.potential x) (observation : Reading) :
    Congruent (fun live value => reading K R observation live = value) (Multiset.map rename) id := by
  rintro live _ rfl
  rw [reading_rename]
  have same : renamedReadings K R rename = R := by
    obtain ⟨result, _, _, faulty, potential⟩ := R
    simp only [renamedReadings] at resultInvariant faultInvariant potentialInvariant ⊢
    congr 1
    · exact funext resultInvariant
    · exact funext faultInvariant
    · exact funext potentialInvariant
  rw [same]
  rfl

end RenameReadings

/-! ## Readings: result and fault are separate -/

section Readings

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)

omit [DecidableEq V] in
theorem result_singleton (R : NodeReadings K V) (x : V) :
    reading K R .result (x ::ₘ 0) = R.result x := by
  change max (R.result x) (best R.result 0) = R.result x
  rw [best_zero, max_eq_left (R.result_nonneg x)]

omit [DecidableEq V] in
theorem fault_singleton (R : NodeReadings K V) (x : V) :
    reading K R .fault (x ::ₘ 0) = faultIndicator K R x := by
  change max (faultIndicator K R x) (best (faultIndicator K R) 0) = faultIndicator K R x
  rw [best_zero, max_eq_left (faultIndicator_nonneg R x)]

omit [DecidableEq V] in
theorem faultIndicator_true (R : NodeReadings K V) {x : V} (faulty : R.faulty x = true) :
    faultIndicator K R x = K.one := by
  simp [faultIndicator, faulty]

omit [DecidableEq V] in
theorem faultIndicator_false (R : NodeReadings K V) {x : V} (healthy : R.faulty x = false) :
    faultIndicator K R x = 0 := by
  simp [faultIndicator, healthy]

omit [DecidableEq V] in
/-- **The result reading does not determine the fault reading**: adding a
faulty node of result `0` to a healthy node keeps the result and changes the
fault. -/
def result_fault_fibre (R : NodeReadings K V) {healthy faulty : V}
    (healthyFlag : R.faulty healthy = false) (faultyResult : R.result faulty = 0)
    (faultyFlag : R.faulty faulty = true) :
    Core.NonFactorization.NonTrivialFiber (reading K R .result) (reading K R .fault) where
  left := healthy ::ₘ 0
  right := healthy ::ₘ faulty ::ₘ 0
  sameShadow := by
    change max (R.result healthy) (best R.result 0) =
      max (R.result healthy) (max (R.result faulty) (best R.result 0))
    rw [best_zero, faultyResult, max_self]
  differentValue := by
    change max (faultIndicator K R healthy) (best (faultIndicator K R) 0) ≠
      max (faultIndicator K R healthy) (max (faultIndicator K R faulty) (best (faultIndicator K R) 0))
    rw [best_zero, faultIndicator_false K R healthyFlag, faultIndicator_true K R faultyFlag, max_self,
      max_eq_left K.zero_le_one, max_eq_right K.zero_le_one]
    exact ne_of_lt K.one_pos

omit [DecidableEq V] in
/-- **The fault reading does not determine the result reading.** -/
def fault_result_fibre (R : NodeReadings K V) {healthy faulty : V}
    (healthyResult : R.result healthy = K.one) (healthyFlag : R.faulty healthy = false)
    (faultyResult : R.result faulty = 0) (faultyFlag : R.faulty faulty = true) :
    Core.NonFactorization.NonTrivialFiber (reading K R .fault) (reading K R .result) where
  left := faulty ::ₘ 0
  right := healthy ::ₘ faulty ::ₘ 0
  sameShadow := by
    change max (faultIndicator K R faulty) (best (faultIndicator K R) 0) =
      max (faultIndicator K R healthy) (max (faultIndicator K R faulty) (best (faultIndicator K R) 0))
    rw [best_zero, faultIndicator_false K R healthyFlag, faultIndicator_true K R faultyFlag,
      max_eq_left K.zero_le_one, max_eq_right K.zero_le_one]
  differentValue := by
    change max (R.result faulty) (best R.result 0) ≠
      max (R.result healthy) (max (R.result faulty) (best R.result 0))
    rw [best_zero, faultyResult, healthyResult, max_self, max_eq_left K.zero_le_one]
    exact ne_of_lt K.one_pos

/-- **A fault of a history is not a faulty live node.**  Copying a faulty node
is a history that runs, read positively, into a configuration whose fault
reading is `one`; erasing a healthy node twice is a history that faults, read
`0`, from a configuration whose fault reading is `0`. -/
theorem history_fault_not_fault_reading (R : NodeReadings K V) (positive : K.Positive)
    {healthy faulty : V} (healthyFlag : R.faulty healthy = false) (faultyFlag : R.faulty faulty = true) :
    run G [.fork faulty] (faulty ::ₘ 0) = some (faulty ::ₘ faulty ::ₘ 0) ∧
      0 < (presented G K R).val (chain G K R [.fork faulty] .top) (faulty ::ₘ 0) ∧
      reading K R .fault (faulty ::ₘ faulty ::ₘ 0) = K.one ∧
      run G [.erase healthy, .erase healthy] (healthy ::ₘ 0) = none ∧
      (presented G K R).val (chain G K R [.erase healthy, .erase healthy] .top) (healthy ::ₘ 0) = 0 ∧
      reading K R .fault (healthy ::ₘ 0) = 0 := by
  have forked : run G [.fork faulty] (faulty ::ₘ 0) = some (faulty ::ₘ faulty ::ₘ 0) := by
    simp [run, step]
  have faulted : run G [.erase healthy, .erase healthy] (healthy ::ₘ 0) = none := by
    simp [run, step]
  refine ⟨forked, ?_, ?_, faulted, ?_, ?_⟩
  · rw [val_chain, forked]
    exact iterate_discount_pos K positive 1
  · exact (fault_reading_eq_one_iff R _).mpr ⟨faulty, Multiset.mem_cons_self _ _, faultyFlag⟩
  · rw [val_chain, faulted]
    rfl
  · rw [fault_singleton, faultIndicator_false K R healthyFlag]

end Readings

/-! ## Costs: read by the program, or kept in the account -/

section Costs

open Mettapedia.Effects
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.TraceCostValuation (pathAccount)
open Mettapedia.GSLT.Distinction.LevelAccounts (QualifiedReplay LevelReadings)
open HistoryIndependence (presentation costValuation)

/-- One occurrence of a firing. -/
def occurrence {event : Event V} {source target : Multiset V} (fires : Fires G event source target) :
    Occurrence (presentation G) source target :=
  ⟨event, ⟨fires⟩⟩

/-- **A run is a labelled path of its events.** -/
theorem labelledPath_of_run : ∀ {source target : Multiset V}
    (run : OccurrencePath (presentation G) source target), LabelledPath G source run.sites target
  | _, _, .refl _ => .nil _
  | _, _, .cons occurrence rest => .cons occurrence.evidence.down (labelledPath_of_run rest)

/-- The cost of a run is the sum over its events. -/
theorem onPath_cost {A : Type} [AddMonoid A] (cost : Event V → A) :
    ∀ {source target : Multiset V} (run : OccurrencePath (presentation G) source target),
      (costValuation G cost).onPath run = (run.sites.map cost).sum
  | _, _, .refl _ => rfl
  | _, _, .cons occurrence rest => by
      change cost occurrence.site + (costValuation G cost).onPath rest = _
      rw [onPath_cost cost rest]
      rfl

theorem fork_singleton (x : V) : Fires G (.fork x) (x ::ₘ 0) (x ::ₘ x ::ₘ 0) :=
  .fork (Multiset.mem_cons_self x 0)

theorem erase_head (x : V) (rest : Multiset V) : Fires G (.erase x) (x ::ₘ rest) rest := by
  have fires := Fires.erase (G := G) (Multiset.mem_cons_self x rest)
  rwa [Multiset.erase_cons_head] at fires

/-- The loop that copies a node and erases the copy. -/
def forkEraseLoop (x : V) : OccurrencePath (presentation G) (x ::ₘ 0) (x ::ₘ 0) :=
  .cons (occurrence G (fork_singleton G x)) (.cons (occurrence G (erase_head G x _)) (.refl _))

theorem evolve_head (x : V) (rest : Multiset V) :
    Fires G (.evolve x) (x ::ₘ rest) (G.evolve x ::ₘ rest) := by
  have fires := Fires.evolve (G := G) (Multiset.mem_cons_self x rest)
  rwa [Multiset.erase_cons_head] at fires

/-- The loop that copies a node, evolves the copy and erases the result. -/
def evolveLoop (x : V) : OccurrencePath (presentation G) (x ::ₘ 0) (x ::ₘ 0) :=
  .cons (occurrence G (fork_singleton G x))
    (.cons (occurrence G (evolve_head G x _)) (.cons (occurrence G (erase_head G _ _)) (.refl _)))

theorem doubled_sub_pair (x y : V) : y ::ₘ x ::ₘ pair x y - pair x y = pair x y := by
  rw [Multiset.cons_sub_of_le y (Multiset.le_cons_self _ _), Multiset.cons_sub_of_le x le_rfl,
    pair_sub_pair]
  exact Multiset.cons_swap y x 0

theorem fork_second (x y : V) : Fires G (.fork y) (x ::ₘ pair x y) (y ::ₘ x ::ₘ pair x y) :=
  .fork (by simp [pair])

theorem fork_first (x y : V) : Fires G (.fork x) (pair x y) (x ::ₘ pair x y) :=
  .fork (by simp [pair])

theorem merge_doubled (x y : V) :
    Fires G (.merge x y) (y ::ₘ x ::ₘ pair x y) (G.merge x y ::ₘ pair x y) := by
  have fires := Fires.merge (G := G) (x := x) (y := y) (live := y ::ₘ x ::ₘ pair x y)
    ((Multiset.le_cons_self _ _).trans (Multiset.le_cons_self _ _))
  rwa [doubled_sub_pair] at fires

/-- The loop that copies both nodes of a pair, merges the copies and erases the
merge. -/
def mergeLoop (x y : V) : OccurrencePath (presentation G) (pair x y) (pair x y) :=
  .cons (occurrence G (fork_first G x y)) (.cons (occurrence G (fork_second G x y))
    (.cons (occurrence G (merge_doubled G x y)) (.cons (occurrence G (erase_head G _ _)) (.refl _))))

section Group

variable {W : Type} [AddCommGroup W]

theorem forkEraseLoop_cost (cost : Event V → W) (x : V) :
    (costValuation G cost).onPath (forkEraseLoop G x) = cost (.fork x) + cost (.erase x) := by
  change cost (.fork x) + (cost (.erase x) + 0) = _
  rw [add_zero]

theorem evolveLoop_cost (cost : Event V → W) (x : V) :
    (costValuation G cost).onPath (evolveLoop G x) =
      cost (.fork x) + cost (.evolve x) + cost (.erase (G.evolve x)) := by
  change cost (.fork x) + (cost (.evolve x) + (cost (.erase (G.evolve x)) + 0)) = _
  rw [add_zero, add_assoc]

theorem mergeLoop_cost (cost : Event V → W) (x y : V) :
    (costValuation G cost).onPath (mergeLoop G x y) =
      cost (.fork x) + cost (.fork y) + cost (.merge x y) + cost (.erase (G.merge x y)) := by
  change cost (.fork x) + (cost (.fork y) + (cost (.merge x y) + (cost (.erase (G.merge x y)) + 0))) = _
  rw [add_zero, add_assoc, add_assoc]

/-- **A cost the program can read**: the cost of every run is the change of
some reading of configurations. -/
def ProgramReadable (cost : Event V → W) : Prop :=
  ∃ readingOf : Multiset V → W, ∀ (source target : Multiset V)
    (run : OccurrencePath (presentation G) source target),
      (costValuation G cost).onPath run = readingOf target - readingOf source

/-- A cost with the potential laws is read by the extensive potential. -/
theorem readable_of_laws {cost : Event V → W} {potential : V → W}
    (laws : PotentialLaws G cost potential) : ProgramReadable G cost :=
  ⟨potentialSum potential, fun _ _ run => by
    rw [onPath_cost]
    exact labelledPath_potentialSum G laws (labelledPath_of_run G run)⟩

/-- A readable cost qualifies every replay with the same endpoints. -/
theorem replay_of_readable {cost : Event V → W} (readable : ProgramReadable G cost)
    (source target : Multiset V) (first second : OccurrencePath (presentation G) source target) :
    QualifiedReplay (pathAccount (costValuation G cost)) first second := by
  obtain ⟨readingOf, reads⟩ := readable
  change Multiplicative.ofAdd ((costValuation G cost).onPath first) =
    Multiplicative.ofAdd ((costValuation G cost).onPath second)
  rw [reads, reads]

/-- A cost whose every replay is qualified vanishes on closed runs. -/
theorem closed_of_replay {cost : Event V → W}
    (qualified : ∀ (source target : Multiset V) (first second : OccurrencePath (presentation G) source target),
      QualifiedReplay (pathAccount (costValuation G cost)) first second)
    (live : Multiset V) (run : OccurrencePath (presentation G) live live) :
    (costValuation G cost).onPath run = 0 := by
  have same : Multiplicative.ofAdd ((costValuation G cost).onPath run) = Multiplicative.ofAdd 0 :=
    qualified live live run (OccurrencePath.refl (P := presentation G) live)
  exact Multiplicative.ofAdd.injective same

/-- **Local Livšic in a commutative group**: a cost that vanishes on the three
elementary loops has the potential laws of its fork component. -/
theorem laws_of_closed {cost : Event V → W}
    (closed : ∀ (live : Multiset V) (run : OccurrencePath (presentation G) live live),
      (costValuation G cost).onPath run = 0) :
    PotentialLaws G cost fun x => cost (.fork x) := by
  have forkErase : ∀ x, cost (.fork x) + cost (.erase x) = 0 := fun x =>
    (forkEraseLoop_cost G cost x).symm.trans (closed _ (forkEraseLoop G x))
  have evolveZero : ∀ x, cost (.fork x) + cost (.evolve x) + cost (.erase (G.evolve x)) = 0 :=
    fun x => (evolveLoop_cost G cost x).symm.trans (closed _ (evolveLoop G x))
  have mergeZero : ∀ x y,
      cost (.fork x) + cost (.fork y) + cost (.merge x y) + cost (.erase (G.merge x y)) = 0 :=
    fun x y => (mergeLoop_cost G cost x y).symm.trans (closed _ (mergeLoop G x y))
  refine fun x y => ⟨?_, rfl, ?_, ?_⟩
  · have key : cost (.evolve x) - (cost (.fork (G.evolve x)) - cost (.fork x)) =
        (cost (.fork x) + cost (.evolve x) + cost (.erase (G.evolve x))) -
          (cost (.fork (G.evolve x)) + cost (.erase (G.evolve x))) := by abel
    rw [evolveZero, forkErase, sub_zero] at key
    exact sub_eq_zero.mp key
  · rw [eq_neg_iff_add_eq_zero, add_comm]
    exact forkErase x
  · have key : cost (.merge x y) -
          (cost (.fork (G.merge x y)) - cost (.fork x) - cost (.fork y)) =
        (cost (.fork x) + cost (.fork y) + cost (.merge x y) + cost (.erase (G.merge x y))) -
          (cost (.fork (G.merge x y)) + cost (.erase (G.merge x y))) := by abel
    rw [mergeZero, forkErase, sub_zero] at key
    exact sub_eq_zero.mp key

/-- **Which costs a program can read.**  For an event cost in a commutative
group, the following are equivalent:
1. it has the potential laws for some node potential;
2. the program can read it: every run costs the change of some reading;
3. every closed run costs nothing;
4. replaying any run for any other with the same endpoints is qualified for
   its account. -/
theorem readable_tfae (cost : Event V → W) :
    [∃ potential, PotentialLaws G cost potential,
      ProgramReadable G cost,
      ∀ (live : Multiset V) (run : OccurrencePath (presentation G) live live),
        (costValuation G cost).onPath run = 0,
      ∀ (source target : Multiset V) (first second : OccurrencePath (presentation G) source target),
        QualifiedReplay (pathAccount (costValuation G cost)) first second].TFAE := by
  tfae_have 1 → 2 := fun ⟨_, laws⟩ => readable_of_laws G laws
  tfae_have 2 → 4 := replay_of_readable G
  tfae_have 4 → 3 := closed_of_replay G
  tfae_have 3 → 1 := fun closed => ⟨_, laws_of_closed G closed⟩
  tfae_finish

/-- **A readable cost is read by the extensive potential.** -/
theorem readable_by_potential {cost : Event V → W} {potential : V → W}
    (laws : PotentialLaws G cost potential) {source target : Multiset V}
    (run : OccurrencePath (presentation G) source target) :
    (costValuation G cost).onPath run = potentialSum potential target - potentialSum potential source := by
  rw [onPath_cost]
  exact labelledPath_potentialSum G laws (labelledPath_of_run G run)

end Group

section Reflected

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)

/-- **A readable cost is reflected by the observer's cost reading** on every run
whose endpoints lie within budget. -/
theorem readable_reflected (R : NodeReadings K V) {cost : Event V → W}
    (laws : PotentialLaws G cost R.potential) {source target : Multiset V}
    (run : OccurrencePath (presentation G) source target)
    (sourceBudget : 0 ≤ potentialSum R.potential source ∧ potentialSum R.potential source ≤ K.one)
    (targetBudget : 0 ≤ potentialSum R.potential target ∧ potentialSum R.potential target ≤ K.one) :
    (costValuation G cost).onPath run = reading K R .cost target - reading K R .cost source := by
  rw [cost_reading_of_mem R targetBudget.1 targetBudget.2,
    cost_reading_of_mem R sourceBudget.1 sourceBudget.2]
  exact readable_by_potential G laws run

/-- **Only a readable cost is reflected**: if the observer's cost reading
reflects a cost on every run, the cost has the potential laws. -/
theorem reflected_readable (R : NodeReadings K V) {cost : Event V → W}
    (reflects : ∀ (source target : Multiset V) (run : OccurrencePath (presentation G) source target),
      (costValuation G cost).onPath run = reading K R .cost target - reading K R .cost source) :
    ∃ potential, PotentialLaws G cost potential :=
  ⟨_, laws_of_closed G (closed_of_replay G (replay_of_readable G ⟨reading K R .cost, reflects⟩))⟩

end Reflected

/-- **Every event cost is an account of runs**, read by the program or not. -/
abbrev costAccount {A : Type} [AddMonoid A] (cost : Event V → A) :
    RunAccount (OccurrenceCat (presentation G)) (Multiplicative A) :=
  pathAccount (costValuation G cost)

/-- One unit of work per event. -/
def unitWork : Event V → ℤ := fun _ => 1

/-- **Unit work is not readable**: copying and erasing a node is a closed run
that costs `2`. -/
theorem unitWork_not_readable (x : V) : ¬ ProgramReadable G (unitWork (V := V)) := by
  intro readable
  have closed := closed_of_replay G (replay_of_readable G readable) _ (forkEraseLoop G x)
  rw [forkEraseLoop_cost] at closed
  simp [unitWork] at closed

/-- **Unit work stays in the account**: replaying the copy-and-erase loop by
the empty run is not qualified for it. -/
theorem unitWork_replay_not_qualified (x : V) :
    ¬ QualifiedReplay (costAccount G (unitWork (V := V))) (forkEraseLoop G x)
      (OccurrencePath.refl (P := presentation G) (x ::ₘ 0)) := by
  intro qualified
  have costs := Multiplicative.ofAdd.injective qualified
  change (costValuation G unitWork).onPath (forkEraseLoop G x) = 0 at costs
  rw [forkEraseLoop_cost] at costs
  simp [unitWork] at costs

/-- **The levels of a history**: the reference account of an event cost, the
host's unit work, and no recorded overhead. -/
def levels {W : Type} [AddCommGroup W] (reference : Event V → W) :
    LevelReadings (OccurrenceCat (presentation G)) (Multiplicative W) (Multiplicative ℤ)
      (Multiplicative ℤ) where
  reference := costAccount G reference
  work := costAccount G unitWork
  overhead := RunAccount.trivial _ _

/-- **The control between the two cases.**  For a readable reference cost,
replaying the copy-and-erase loop by the empty run is qualified for the
reference account, not for the work, and so not for the three levels together. -/
theorem levels_replay {W : Type} [AddCommGroup W] {reference : Event V → W} {potential : V → W}
    (laws : PotentialLaws G reference potential) (x : V) :
    QualifiedReplay (levels G reference).reference (forkEraseLoop G x)
        (OccurrencePath.refl (P := presentation G) (x ::ₘ 0)) ∧
      ¬ QualifiedReplay (levels G reference).work (forkEraseLoop G x)
        (OccurrencePath.refl (P := presentation G) (x ::ₘ 0)) ∧
      ¬ QualifiedReplay (levels G reference).total (forkEraseLoop G x)
        (OccurrencePath.refl (P := presentation G) (x ::ₘ 0)) := by
  have referenceQualified : QualifiedReplay (levels G reference).reference (forkEraseLoop G x)
      (OccurrencePath.refl (P := presentation G) (x ::ₘ 0)) :=
    replay_of_readable G (readable_of_laws G laws) _ _ _ _
  refine ⟨referenceQualified, unitWork_replay_not_qualified G x, fun total => ?_⟩
  exact unitWork_replay_not_qualified G x
    (((LevelReadings.total_iff (levels G reference) _ _).mp total).2.1)

end Costs

end Mettapedia.GSLT.Distinction.HistoryCoverage
