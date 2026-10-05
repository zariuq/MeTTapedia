import Mettapedia.GSLT.Distinction.HistoryObserverControls
import Mettapedia.GSLT.Logic.GradedTwoSidedObservation

/-!
# The history grammar through the two-sided graded observer

`GradedTwoSidedObservation` extends a presented system by authored
predecessor lists, with labels `Direction × Label`, and compares an original
event span with its stage classes.  This module instantiates it with the
history grammar of `HistoryObserver`.

* **Authored pasts** (`pastLists`, `observer`, `observerVocabulary`).  The
  predecessor lists are the backward steps of `HistoryObserver.unstep`; over a
  listed node set the two-sided vocabulary is finite.  Forward and backward
  lists hold exactly the firing relation (`observer_forward_iff`,
  `observer_backward_iff`), and every step of the history GSLT is a forward
  action and, reversed, a backward one (`observer_step_iff`).
* **Exact readings of pasts** (`pastChain`, `val_pastChain`,
  `history_past_result`).  The formula that undoes a history's events reads
  `0` exactly when no configuration runs that history into the given one, and
  otherwise the discounted readings of the unique configuration that does.
* **The two-sided observer separates configurations**
  (`observer_gradedBisimilar_iff_eq`), and dominates the forward depth bound
  (`observer_bound_ge`).
* **Authored events** (`labelledEvents`, `causalEvents`).  Labelled steps, and
  causal occurrences that also carry the copy they use.  The predecessor box
  over causal occurrences is the box over actions
  (`causal_predecessor_box_iff`): the modal comparison does not see copies
  (`HistoryObserverControls.no_matcher_recovers_occurrences`).
* **No stabilization stage** (`observer_not_stabilizes`).  The stage lifts of
  `GradedTwoSidedObservation` (`source_lifts`, `target_lifts` and the native
  comparisons) take a vocabulary, a positive discount and a stabilization
  certificate of the two-sided system.  The first two are supplied here; the
  third fails at every depth for the one-node grammar, for every positive
  scale and every result and fault reading with zero potential.  The stage
  lifts therefore do not apply to the whole history grammar; the
  finite-depth classes still retain every reading
  (`HistoryObserver.value_eq_of_stateOf_eq`).

As in `HistoryObserver`, every declaration over the history grammar inherits
`Classical.choice` from Mathlib's multiset erase and subtraction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryTwoSidedObserver

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.GSLT.Distinction.HistoryObserver
open Mettapedia.GSLT.Distinction.HistoryObserverControls
open Mettapedia.GSLT.Distinction.Constructive
open Mettapedia.GSLT.GradedTwoSidedObservation
open Mettapedia.Cybernetics.DistinctionCalculus.History
open Mettapedia.OSLF.Framework.DerivedModalities

variable {V : Type} [DecidableEq V] (G : Grammar V)
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)

/-! ## Authored pasts -/

/-- The authored predecessor lists of the history observer. -/
def pastLists (R : NodeReadings K V) : Predecessors (presented G K R) where
  list := predecessors G
  sound member := (mem_predecessors G).mp member
  cover action := ⟨_, (mem_predecessors G).mpr action, rfl⟩

/-- **The history grammar as a two-sided graded observer.** -/
abbrev observer (R : NodeReadings K V) : PresentedSystem (historyGSLT G) K :=
  twoSided (presented G K R) (pastLists G K R)

/-- Over a listed node set the two-sided vocabulary is finite. -/
def observerVocabulary (R : NodeReadings K V) (L : Listing V) : (observer G K R).Vocabulary :=
  twoSidedVocabulary (presented G K R) (pastLists G K R) (vocabulary G K R L)

theorem observer_forward_iff (R : NodeReadings K V) {event : Event V} {source target : Multiset V} :
    target ∈ (observer G K R).successors (.forward, event) source ↔ Fires G event source target :=
  mem_successors G

theorem observer_backward_iff (R : NodeReadings K V) {event : Event V} {source target : Multiset V} :
    source ∈ (observer G K R).successors (.backward, event) target ↔ Fires G event source target :=
  mem_predecessors G

/-- **Two-sided action coverage**: every step of the history GSLT is a forward
action and, reversed, a backward action of the observer. -/
theorem observer_step_iff (R : NodeReadings K V) (source target : Multiset V) :
    (historyGSLT G).Step source target ↔
      ((∃ event, (observer G K R).dynamics.act (.forward, event) source target) ∧
        ∃ event, (observer G K R).dynamics.act (.backward, event) target source) := by
  change (∃ event, Fires G event source target) ↔
    ((∃ event, Fires G event source target) ∧ ∃ event, Fires G event source target)
  exact ⟨fun step => ⟨step, step⟩, fun both => both.1⟩

/-! ## Exact readings of pasts -/

/-- The formula that undoes a history's events, last first, and then tests
`inner`. -/
def pastChain (R : NodeReadings K V) :
    List (Event V) → (observer G K R).Formula → (observer G K R).Formula
  | [], inner => inner
  | event :: rest, inner => .dia (.backward, event) (pastChain R rest inner)

/-- **The value of a past formula**: `0` when nothing runs the history into the
configuration, and the discounted value of `inner` at the unique
configuration that does otherwise. -/
theorem val_pastChain (R : NodeReadings K V) :
    ∀ (history : List (Event V)) (inner : (observer G K R).Formula) (target : Multiset V),
      (observer G K R).val (pastChain G K R history inner) target =
        (unrun G history target).elim 0
          (fun source => K.discount^[history.length] ((observer G K R).val inner source))
  | [], inner, target => rfl
  | event :: rest, inner, target => by
      change K.discount (listSup ((observer G K R).val (pastChain G K R rest inner))
        (predecessors G event target)) = _
      cases undone : unstep G event target with
      | none =>
          simp only [predecessors, undone, Option.toList_none, listSup_nil, K.discount_zero, unrun,
            Option.bind_none, Option.elim_none]
      | some middle =>
          simp only [predecessors, undone, Option.toList_some, listSup_cons, listSup_nil, unrun,
            Option.bind_some]
          rw [max_eq_left ((observer G K R).val_nonneg _ middle), val_pastChain R rest inner middle]
          cases ran : unrun G rest middle with
          | none => simp only [Option.elim_none, K.discount_zero]
          | some source =>
              simp only [Option.elim_some, List.length_cons, Function.iterate_succ_apply']

/-- **The observer reads the unique past of a history**: each reading of the
configuration that runs the history into the given one. -/
theorem history_past_result (R : NodeReadings K V) {history : List (Event V)}
    {source target : Multiset V} (path : LabelledPath G source history.reverse target)
    (observation : Reading) :
    (observer G K R).val (pastChain G K R history (.atom observation)) target =
      K.discount^[history.length] (reading K R observation source) := by
  rw [val_pastChain, (unrun_eq_some_iff G history source target).mpr path]
  rfl

/-- **The observer reads which pasts exist**: with a positive discount the past
formula of a history is `0` exactly when nothing runs it into the
configuration. -/
theorem history_past_absent_iff (R : NodeReadings K V) (positive : K.Positive)
    (history : List (Event V)) (target : Multiset V) :
    (observer G K R).val (pastChain G K R history .top) target = 0 ↔
      ¬ ∃ source, LabelledPath G source history.reverse target := by
  rw [val_pastChain]
  cases undone : unrun G history target with
  | none =>
      simp only [Option.elim_none, true_iff]
      rintro ⟨source, path⟩
      rw [(unrun_eq_some_iff G history source target).mpr path] at undone
      cases undone
  | some source =>
      simp only [Option.elim_some, PresentedSystem.val_top]
      exact ⟨fun zero => absurd zero (ne_of_gt (iterate_discount_pos K positive _)),
        fun absent => absurd ⟨source, (unrun_eq_some_iff G history source target).mp undone⟩ absent⟩

/-! ## The observer separates configurations -/

/-- **Two-sided graded bisimilarity of the history observer is equality.** -/
theorem observer_gradedBisimilar_iff_eq (R : NodeReadings K V) (left right : Multiset V) :
    (observer G K R).GradedBisimilar left right ↔ left = right := by
  constructor
  · rintro ⟨relation, ⟨forth, back, _⟩, related⟩
    exact eq_of_matchesErasures (G := G) (relation := relation)
      (fun _ _ related x member =>
        forth related (.forward, .erase x) (Fires.erase (G := G) member))
      (fun _ _ related x member =>
        back related (.forward, .erase x) (Fires.erase (G := G) member)) related
  · rintro rfl
    exact ⟨_, (observer G K R).isGradedBisimulation_equiv, rfl⟩

/-- The two-sided depth bound dominates the forward one. -/
theorem observer_bound_ge (R : NodeReadings K V) (L : Listing V) (depth : Nat)
    (left right : Multiset V) :
    (presented G K R).depthBound (vocabulary G K R L) depth left right ≤
      (observer G K R).depthBound (observerVocabulary G K R L) depth left right :=
  forward_bound_le (presented G K R) (pastLists G K R) (vocabulary G K R L) depth left right

/-! ## Authored events -/

/-- The labelled steps of the history grammar as authored events. -/
def labelledEvents (R : NodeReadings K V) : AuthoredEvents (presented G K R) where
  span := labelledSpan G
  label step := step.1.1
  sound step := step.2
  cover label source target action := ⟨⟨(label, source, target), action⟩, rfl, rfl, rfl⟩

/-- The causal occurrences as authored events: each retains the copy it uses. -/
def causalEvents (R : NodeReadings K V) : AuthoredEvents (presented G K R) where
  span := causalSpan G
  label := CausalOccurrence.event
  sound := CausalOccurrence.fires
  cover label source target action := ⟨firstCopy G ⟨(label, source, target), action⟩, rfl, rfl, rfl⟩

/-- **The predecessor box over causal occurrences is the box over actions.** -/
theorem causal_predecessor_box_iff (R : NodeReadings K V) (predicate : Multiset V → Prop)
    (target : Multiset V) :
    derivedBox (causalSpan G) predicate target ↔
      ∀ event source, Fires G event source target → predicate source :=
  predecessor_box_iff (presented G K R) (causalEvents G K R) predicate target

/-- The future diamond over causal occurrences is the diamond over actions. -/
theorem causal_future_iff (R : NodeReadings K V) (predicate : Multiset V → Prop)
    (source : Multiset V) :
    derivedDiamond (causalSpan G) predicate source ↔
      ∃ event target, Fires G event source target ∧ predicate target :=
  future_iff (presented G K R) (causalEvents G K R) predicate source

/-! ## No stabilization stage -/

/-- What a backward event needs, as a size. -/
def backNeed : Event Unit → Nat
  | .evolve _ => 1
  | .fork _ => 2
  | .merge _ _ => 1
  | .erase _ => 0

/-- The size a backward event reaches. -/
def backShift : Event Unit → Nat → Nat
  | .evolve _, size => size
  | .fork _, size => size - 1
  | .merge _ _, size => size + 1
  | .erase _, size => size + 1

/-- On one node a backward event is determined by sizes. -/
theorem unit_backward_iff (event : Event Unit) (source target : Multiset Unit) :
    Fires unitGrammar event target source ↔
      backNeed event ≤ Multiset.card source ∧
        Multiset.card target = backShift event (Multiset.card source) := by
  rw [unit_fires_iff]
  cases event <;> simp only [need, shift, backNeed, backShift] <;> omega

/-- Needs of two-sided labels. -/
def twoSidedNeed : Direction × Event Unit → Nat
  | (.forward, event) => need event
  | (.backward, event) => backNeed event

/-- Shifts of two-sided labels. -/
def twoSidedShift : Direction × Event Unit → Nat → Nat
  | (.forward, event) => shift event
  | (.backward, event) => backShift event

variable {K}

/-- The two-sided history observer on one node is size-determined. -/
def observerSized (R : NodeReadings K Unit) (zero : ∀ node, R.potential node = 0) :
    SizeDetermined (observer unitGrammar K R) where
  need := twoSidedNeed
  shift := twoSidedShift
  need_le := by
    rintro ⟨direction, event⟩
    cases direction <;> cases event <;> simp [twoSidedNeed, need, backNeed]
  shift_ge := by
    rintro ⟨direction, event⟩ size
    cases direction <;> cases event <;> simp only [twoSidedShift, shift, backShift] <;> omega
  act_iff := by
    rintro ⟨direction, event⟩ source target
    cases direction
    · exact unit_fires_iff event source target
    · exact unit_backward_iff event source target
  value_agree := reading_agree R zero

/-- **No stabilization stage for the two-sided history observer**: for every
positive scale and every result and fault reading with zero potential, the
one-node observer has no stabilization certificate at any depth, so the stage
lifts of `GradedTwoSidedObservation` never apply to it. -/
theorem observer_not_stabilizes (positive : K.Positive) (R : NodeReadings K Unit)
    (zero : ∀ node, R.potential node = 0) (depth : Nat) :
    ¬ (observer unitGrammar K R).Stabilizes (observerVocabulary unitGrammar K R unitListing) depth :=
  not_stabilizes_of_faithful _ _ positive
    (fun left right => (observer_gradedBisimilar_iff_eq unitGrammar K R left right).mp)
    (observerSized R zero).separated depth

end Mettapedia.GSLT.Distinction.HistoryTwoSidedObserver
