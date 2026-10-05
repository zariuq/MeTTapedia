import Mettapedia.Machines.BranchLocalNeed.InferenceControl
import Mettapedia.Machines.BranchLocalNeed.FrontierLaws
import Mettapedia.Machines.BranchLocalNeed.InteractionValuation
import Mettapedia.GSLT.Dynamics.WeightedBranchingResumption
import Mettapedia.GSLT.Causality.OccurrenceMachineHistory

/-!
# Weighted handlers of the branch-local Need machine

The operation catalogue is constructed from actual Need successors. Its
responses are successor positions, so duplicate rules remain distinct. Each
open or returned leaf retains the complete work occurrence: heap, shared
choices, control stack, receipts and existing cost counters.

The free handler agrees with an independently defined weighted frontier run.
Every retained occurrence carries a reference-machine derivation and its exact
transition cost. A returned leaf is proved halted; exhausting an unfolding
budget does not certify closure. Production-only semantic factors agree with
the existing chronological history account without discarding delivery or
administrative transitions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption

open NeedReference
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Dynamics
open WeightedResumption

section WeightedExecution

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}
  {V : Type*}

abbrev WorkState (Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*) :=
  WorkOccurrence (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)

variable (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)

def successors (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (before : WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    List (WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect × V) :=
  (step spec before.state).zipIdx.map fun (after, index) =>
    (⟨after, before.trace ++ [index]⟩, coefficient before.state after)

/-- Returning retains the halted world rather than replacing it by its value. -/
def source (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V) :
    WeightedBranchingResumption.Coalgebra
      (WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect)
      (WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect) V :=
  fun occurrence =>
    match occurrence.state.control with
    | .halted _ => .inl occurrence
    | _ => .inr (successors spec coefficient occurrence)

/-- Completed and pending leaves both own their original branch-local world. -/
def retained {State : Type*} : State ⊕ State → State := Sum.elim id id

theorem successors_erasure (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (before : WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (successors spec coefficient before).map Prod.fst =
      (NeedInferenceControl.Reference.occurrenceSystem spec).successors before := by
  simp [successors, NeedInferenceControl.Reference.occurrenceSystem,
    WorkOccurrence.lift, NeedInferenceControl.Reference.branchingSystem, List.map_map]

theorem successors_length (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (before : WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (successors spec coefficient before).length = (step spec before.state).length := by
  simp [successors]

/-- Both directions use the actual indexed successor lookup, not an image relation. -/
theorem successor_iff (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (before after : WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (value : V) :
    (after, value) ∈ successors spec coefficient before ↔
      ∃ index, (step spec before.state)[index]? = some after.state ∧
        after.trace = before.trace ++ [index] ∧
        value = coefficient before.state after.state := by
  constructor
  · intro member
    obtain ⟨⟨next, index⟩, located, same⟩ := List.mem_map.mp member
    cases same
    exact ⟨index, List.mk_mem_zipIdx_iff_getElem?.mp located, rfl, rfl⟩
  · rintro ⟨index, located, trace, rfl⟩
    apply List.mem_map.mpr
    refine ⟨(after.state, index), List.mk_mem_zipIdx_iff_getElem?.mpr located, ?_⟩
    change ((⟨after.state, before.trace ++ [index]⟩ :
      WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect),
      coefficient before.state after.state) = _
    apply Prod.ext
    · cases after
      simp_all
    · rfl

theorem source_return_iff (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (before after : WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    source spec coefficient before = .inl after ↔
      before = after ∧ isHalted before.state = true := by
  cases control : before.state.control <;> simp [source, control, isHalted]

theorem source_branches (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (before : WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (running : isHalted before.state = false) :
    source spec coefficient before = .inr (successors spec coefficient before) := by
  cases control : before.state.control <;> simp_all [source, isHalted]

/-- The weighted source exposes exactly coefficients attached to actual Need
successors. A property proved for those transitions therefore covers every
factor, including repeated physical successors. -/
theorem source_coefficients_satisfy (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (holds : V → Prop)
    (steps : ∀ before after, after ∈ step spec before → holds (coefficient before after)) :
    WeightedBranchingResumption.CoefficientsSatisfy (source spec coefficient) holds := by
  intro before alternatives inspected next member
  have same : alternatives = successors spec coefficient before := by
    cases control : before.state.control <;> simp_all [source]
  rw [same] at member
  obtain ⟨index, located, _, coefficientEq⟩ :=
    (successor_iff spec coefficient before next.1 next.2).mp member
  rw [coefficientEq]
  exact steps before.state next.1.state (List.mem_of_getElem? located)

/-- Native interpretation is the instance of the common free handler. -/
theorem handler_agrees [Monoid V] (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (fuel : Nat)
    (before : WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    interpret WeightedBranchingResumption.catalogue
      (WeightedBranchingResumption.cut (source spec coefficient) fuel before) =
      WeightedBranchingResumption.contributions (source spec coefficient) fuel before :=
  WeightedBranchingResumption.interpret_cut _ _ _

theorem resume_exact [Monoid V] (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (first second : Nat)
    (before : WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    WeightedBranchingResumption.contributions (source spec coefficient) (first + second) before =
      WeightedResumption.sequence
        (WeightedBranchingResumption.contributions (source spec coefficient) first before)
        (fun leaf => match leaf with
          | .inl done => [(.inl done, (1 : V))]
          | .inr pending =>
              WeightedBranchingResumption.contributions (source spec coefficient) second pending) :=
  by
    rw [WeightedBranchingResumption.contributions_add]
    apply congrArg (WeightedResumption.sequence
      (WeightedBranchingResumption.contributions (source spec coefficient) first before))
    funext leaf
    cases leaf <;> rfl

/-- Erasing coefficients and the returned/pending tag preserves the actual
reference frontier, including zero-coefficient occurrences and halted worlds. -/
theorem frontier_erasure [Monoid V] (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (fuel : Nat)
    (before : WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (WeightedBranchingResumption.contributions (source spec coefficient) fuel before).map
      (fun leaf => (retained leaf.1).state) =
      NeedFrontierLaws.frontier spec fuel before.state := by
  induction fuel generalizing before with
  | zero => rfl
  | succ fuel ih =>
      cases control : before.state.control with
      | halted outcome =>
          have halted : isHalted before.state = true := by simp [isHalted, control]
          simp [WeightedBranchingResumption.contributions, source, control, retained,
            NeedFrontierLaws.frontier_halted spec (fuel + 1) before.state halted]
      | force cell stack | run localState stack | returned outcome stack =>
          have running : isHalted before.state = false := by simp [isHalted, control]
          simp only [WeightedBranchingResumption.contributions, source, control,
            WeightedResumption.sequence, List.map_flatMap, List.map_map,
            successors, List.flatMap_map,
            NeedFrontierLaws.frontier, NeedFrontierLaws.advance_running spec before.state running]
          change (step spec before.state).zipIdx.flatMap (fun (next, index) =>
            (WeightedBranchingResumption.contributions (source spec coefficient) fuel
              ⟨next, before.trace ++ [index]⟩).map
              (fun leaf => (retained leaf.1).state)) = _
          simp only [ih]
          rw [← List.flatMap_map Prod.fst (NeedFrontierLaws.frontier spec fuel),
            List.zipIdx_map_fst]

/-- The comparison is with the independently implemented batch machine. -/
theorem batch_frontier_erasure [Monoid V] (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (fuel : Nat)
    (before : WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (WeightedBranchingResumption.contributions (source spec coefficient) fuel before).map
      (fun leaf => (retained leaf.1).state) = runFrontier spec fuel [before.state] := by
  rw [frontier_erasure, NeedFrontierLaws.runFrontier_eq_flatMap]
  simp

/-- A handler cannot invent states, even when coefficients vanish or cancel. -/
theorem generated_retained [Monoid V] (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (fuel : Nat)
    {roots : List (WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    {before : WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (generated : Generated (NeedInferenceControl.Reference.occurrenceSystem spec) roots before)
    {leaf : (WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect ⊕
      WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect) × V}
    (member : leaf ∈
      WeightedBranchingResumption.contributions (source spec coefficient) fuel before) :
    Generated (NeedInferenceControl.Reference.occurrenceSystem spec) roots (retained leaf.1) := by
  have invariant := WeightedBranchingResumption.contributions_invariant
    (source spec coefficient)
    (Generated (NeedInferenceControl.Reference.occurrenceSystem spec) roots)
    (Generated (NeedInferenceControl.Reference.occurrenceSystem spec) roots)
    (fun state answer valid returned => by
      obtain ⟨rfl, _⟩ := (source_return_iff spec coefficient state answer).mp returned
      exact valid)
    (fun state alternatives valid branches next nextMember => by
      cases control : state.state.control with
      | halted outcome => simp [source, control] at branches
      | force cell stack | run localState stack | returned outcome stack =>
          have same : successors spec coefficient state = alternatives := by
            exact Sum.inr.inj (by simpa only [source, control] using branches)
          rw [← same] at nextMember
          have successor : next.1 ∈ (successors spec coefficient state).map Prod.fst :=
            List.mem_map.mpr ⟨next, nextMember, rfl⟩
          rw [successors_erasure] at successor
          exact .successor valid successor)
    fuel before generated leaf member
  cases located : leaf.1 <;>
    simpa only [located, retained, Sum.elim_inl, Sum.elim_inr, id_eq] using invariant

/-- A leaf marked returned is actually halted; an open leaf makes no such claim. -/
theorem returned_is_halted [Monoid V] (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (fuel : Nat)
    (before after : WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (value : V)
    (member : (.inl after, value) ∈
      WeightedBranchingResumption.contributions (source spec coefficient) fuel before) :
    isHalted after.state = true := by
  induction fuel generalizing before value with
  | zero => simp [WeightedBranchingResumption.contributions] at member
  | succ fuel ih =>
      cases control : before.state.control with
      | halted outcome =>
          simp only [WeightedBranchingResumption.contributions, source, control,
            List.mem_singleton, Prod.mk.injEq, Sum.inl.injEq] at member
          rw [member.1]
          simp [isHalted, control]
      | force cell stack | run localState stack | returned outcome stack =>
          simp only [WeightedBranchingResumption.contributions, source, control,
            WeightedResumption.sequence, List.mem_flatMap] at member
          obtain ⟨edge, _, leafMember⟩ := member
          obtain ⟨⟨leaf, weight⟩, childMember, same⟩ := List.mem_map.mp leafMember
          have leafSame : leaf = .inl after := (Prod.mk.inj same).1
          subst leafSame
          exact ih edge.1 weight childMember

/-- Existing transition accounting certifies every retained handler occurrence. -/
theorem retained_transition_cost [Monoid V] (coefficient :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → V)
    (initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    {leaf : (WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect ⊕
      WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect) × V}
    (member : leaf ∈ WeightedBranchingResumption.contributions (source spec coefficient)
      fuel (WorkOccurrence.root initial)) :
    (retained leaf.1).state.work.transitions =
      initial.work.transitions + (retained leaf.1).trace.length :=
  NeedInferenceControl.Reference.generated_transition_clock spec
    (generated_retained spec coefficient fuel (.root (by simp)) member)

end WeightedExecution

/-! ## Histories of the weighted Need execution -/

section Histories


open _root_.CategoryTheory
open Mettapedia.GSLT.Causality.OccurrenceMachineHistory
open Mettapedia.OSLF.Binding
open NeedInferenceControl.Reference (pathMachine)

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect V : Type}
variable (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
local notation "World" => Machine Origin Local Resume Rule Value StableFault RetryableFault Effect
local notation "Occurrence" => WorkState Origin Local Resume Rule Value StableFault RetryableFault Effect

/-- The chronological coefficient account of real Need events. -/
def coefficientAccount [Monoid V] (coefficient : World → World → V) (initial : World) :=
  eventAccount (pathMachine spec initial) (fun before after _ => coefficient before after)

/-- Every actual finite history occurs in the weighted frontier at its exact
transition depth, retaining the incoming trace and chronological coefficient.
At that boundary it is still pending, even if its final machine has halted;
observing the halted return consumes the next unfolding step. -/
theorem history_pending_contribution [Monoid V]
    (coefficient : World → World → V) (initial : World)
    {before after : RewriteEventHistory.State (system (pathMachine spec initial))}
    (history : Quiver.Path before after) (priorTrace : List Nat) :
    (.inr ⟨after.term, priorTrace ++ indices (pathMachine spec initial) history⟩,
      (coefficientAccount spec coefficient initial).of history) ∈
      WeightedBranchingResumption.contributions (source spec coefficient)
        (indices (pathMachine spec initial) history).length ⟨before.term, priorTrace⟩ := by
  induction history with
  | nil =>
      simp only [indices, List.append_nil, List.length_nil, WeightedBranchingResumption.contributions,
        List.mem_singleton, Prod.mk.injEq, true_and]
      exact (coefficientAccount spec coefficient initial).of_id _
  | @cons middle after past event ih =>
      let pending : Occurrence := ⟨middle.term, priorTrace ++ indices (pathMachine spec initial) past⟩
      let next : Occurrence :=
        ⟨after.term, priorTrace ++ indices (pathMachine spec initial) (past.cons event)⟩
      have running : isHalted middle.term = false := by
        cases control : middle.term.control <;> simp [isHalted, control]
        have found := event.property
        simp [pathMachine, step, control] at found
      have located : (next, coefficient middle.term after.term) ∈
          successors spec coefficient pending := by
        apply (successor_iff spec coefficient pending next _).mpr
        refine ⟨event.val, event.property, ?_, rfl⟩
        simp [next, pending, indices, List.append_assoc]
      have last : (.inr next, coefficient middle.term after.term) ∈
          WeightedBranchingResumption.contributions (source spec coefficient) 1 pending := by
        rw [WeightedBranchingResumption.contributions,
          source_branches spec coefficient pending running]
        apply List.mem_flatMap.mpr
        refine ⟨(next, coefficient middle.term after.term), located, ?_⟩
        simp [WeightedBranchingResumption.contributions]
      have combined := WeightedBranchingResumption.contributions_continue
        (source spec coefficient) ih last
      simpa only [next, indices, List.length_append, List.length_singleton,
        coefficientAccount, eventAccount_cons] using combined

/-- A history ending in a halted machine is returned by the next observation,
with the same producing trace and coefficient. -/
theorem history_returned_contribution [Monoid V]
    (coefficient : World → World → V) (initial : World)
    {before after : RewriteEventHistory.State (system (pathMachine spec initial))}
    (history : Quiver.Path before after) (priorTrace : List Nat)
    (halted : isHalted after.term = true) :
    (.inl ⟨after.term, priorTrace ++ indices (pathMachine spec initial) history⟩,
      (coefficientAccount spec coefficient initial).of history) ∈
      WeightedBranchingResumption.contributions (source spec coefficient)
        ((indices (pathMachine spec initial) history).length + 1) ⟨before.term, priorTrace⟩ := by
  let final : Occurrence := ⟨after.term, priorTrace ++ indices (pathMachine spec initial) history⟩
  have returned : source spec coefficient final = .inl final :=
    (source_return_iff spec coefficient final final).mpr ⟨rfl, halted⟩
  have last : (.inl final, (1 : V)) ∈
      WeightedBranchingResumption.contributions (source spec coefficient) 1 final := by
    simp [WeightedBranchingResumption.contributions, returned]
  simpa only [mul_one] using WeightedBranchingResumption.contributions_continue
    (source spec coefficient)
    (history_pending_contribution spec coefficient initial history priorTrace) last

/-- Every returned or pending weighted contribution has an event history
with its exact trace extension and ordered coefficient. -/
theorem retained_history [Monoid V]
    (coefficient : World → World → V)
    (initial : World) (fuel : Nat) (before : Occurrence)
    {leaf : (Occurrence ⊕ Occurrence) × V}
    (member : leaf ∈ WeightedBranchingResumption.contributions
      (source spec coefficient) fuel before) :
    ∃ history : History (pathMachine spec initial) before.state
        (NeedWeightedResumption.retained leaf.1).state,
      before.trace ++ indices (pathMachine spec initial) history =
        (NeedWeightedResumption.retained leaf.1).trace ∧
      (coefficientAccount spec coefficient initial).of history = leaf.2 := by
  induction fuel generalizing before leaf with
  | zero =>
      simp only [WeightedBranchingResumption.contributions, List.mem_singleton] at member
      subst leaf
      refine ⟨.nil, ?_, ?_⟩
      · simp [indices, NeedWeightedResumption.retained]
      · exact (coefficientAccount spec coefficient initial).of_id _
  | succ fuel ih =>
      cases control : before.state.control with
      | halted outcome =>
          simp only [WeightedBranchingResumption.contributions, source, control,
            List.mem_singleton] at member
          subst leaf
          refine ⟨.nil, ?_, ?_⟩
          · simp [indices, NeedWeightedResumption.retained]
          · exact (coefficientAccount spec coefficient initial).of_id _
      | force cell stack | run localState stack | returned outcome stack =>
          simp only [WeightedBranchingResumption.contributions, source, control,
            WeightedResumption.sequence,
            List.mem_flatMap] at member
          obtain ⟨edge, edgeMember, tailMember⟩ := member
          obtain ⟨⟨tail, weight⟩, childMember, same⟩ := List.mem_map.mp tailMember
          cases same
          obtain ⟨index, found, trace, coefficientEq⟩ :=
            (NeedWeightedResumption.successor_iff spec
              coefficient before edge.1 edge.2).mp edgeMember
          obtain ⟨history, historyTrace, historyWeight⟩ := ih edge.1 childMember
          let event : (⟨before.state⟩ : RewriteEventHistory.State
              (system (pathMachine spec initial))) ⟶ ⟨edge.1.state⟩ :=
            ⟨index, found⟩
          refine ⟨event.toPath.comp history, ?_, ?_⟩
          · rw [indices_comp]
            change before.trace ++ ([index] ++ indices _ history) = _
            rw [← List.append_assoc, ← trace]
            exact historyTrace
          · change (coefficientAccount spec coefficient initial).of (event.toPath ≫ history) = _
            erw [(coefficientAccount spec coefficient initial).of_comp, historyWeight]
            change (eventAccount (pathMachine spec initial)
              (fun before after _ => coefficient before after)).of event.toPath * weight = _
            rw [eventAccount_generator]
            exact congrArg (fun factor => factor * weight) coefficientEq.symm



/-! ## Production-ledger accounts of returned and suspended histories

The structural history conversion uses the common graph-path interpreter.
The Need-specific event map retains every original successor position, and
the original run account agrees with the independently constructed incremental
production ledger. Both directions connect authentic histories and handler
contributions, including suspended leaves.

Coefficients are assigned by a total function here. This does not qualify
pending native callbacks, serialized C identities, physical capture lifetimes,
external producer provenance, or runtime replay of parent/controller state.
-/

open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open NeedCacheLaws NeedInteractionAuthority NeedInteractionValuation
open Mettapedia.Algebra.SharedCoefficientLedger

/-- Repackage each actual history edge as an occurrence-authenticated interaction
path, preserving the original machine endpoints and successor positions. -/
def historyEventPath (initial : World)
    {before after : RewriteEventHistory.State (system (pathMachine spec initial))}
    (history : Quiver.Path before after) :
    EventPath (machinePresentation spec) before.term after.term :=
  EventPath.ofQuiverPath (machinePresentation spec)
    (fun state : RewriteEventHistory.State (system (pathMachine spec initial)) => state.term)
    (fun {before after : RewriteEventHistory.State (system (pathMachine spec initial))}
      (event : before ⟶ after) => ⟨event.val, ⟨event.property⟩⟩) history

/-- The original empty history maps to the empty interaction path. -/
theorem historyEventPath_nil (initial : World)
    (before : RewriteEventHistory.State (system (pathMachine spec initial))) :
    historyEventPath spec initial (.nil : Quiver.Path before before) =
      EventPath.nil (presentation := machinePresentation spec) before.term :=
  EventPath.ofQuiverPath_nil _ _ _ before

/-- A real selected machine edge extends the same chronological path. -/
theorem historyEventPath_cons (initial : World)
    {before middle after : RewriteEventHistory.State (system (pathMachine spec initial))}
    (past : Quiver.Path before middle) (event : middle ⟶ after) :
    historyEventPath spec initial (past.cons event) =
      EventPath.append (machinePresentation spec) (historyEventPath spec initial past)
        (EventPath.cons (presentation := machinePresentation spec)
          (source := middle.term) (middle := after.term) (target := after.term)
          (site := event.val)
          (⟨event.property⟩ : OccurrenceEvidence spec event.val middle.term after.term)
          (.nil (presentation := machinePresentation spec) after.term)) :=
  EventPath.ofQuiverPath_cons _ _ _ past event

/-- Conversion commutes with the original history composition. -/
theorem historyEventPath_comp (initial : World)
    {before middle after : RewriteEventHistory.State (system (pathMachine spec initial))}
    (first : Quiver.Path before middle) (second : Quiver.Path middle after) :
    historyEventPath spec initial (first.comp second) =
      EventPath.append (machinePresentation spec) (historyEventPath spec initial first)
        (historyEventPath spec initial second) :=
  EventPath.ofQuiverPath_comp _ _ _ first second

/-- Administrative and delivery instructions stay in the original work path. -/
theorem historyEventPath_length (initial : World)
    {before after : RewriteEventHistory.State (system (pathMachine spec initial))}
    (history : Quiver.Path before after) :
    EventPath.pathLength (machinePresentation spec) (historyEventPath spec initial history) =
      history.length :=
  EventPath.ofQuiverPath_length _ _ _ history

/-- The conversion retains the existing chronological replay index list. -/
theorem historyEventPath_indices (initial : World)
    {before after : RewriteEventHistory.State (system (pathMachine spec initial))}
    (history : Quiver.Path before after) :
    ((EventPath.events (machinePresentation spec) (historyEventPath spec initial history)).map
      fun event => event.2.site) = indices (pathMachine spec initial) history := by
  induction history with
  | nil =>
    simp only [historyEventPath_nil, EventPath.events, List.map_nil, indices]
    rfl
  | @cons middle after past event ih =>
    simp only [historyEventPath_cons, indices]
    have joined := congrArg
      (fun events : List (Mettapedia.GSLT.Dynamics.InteractionEventValuation.Occurrence
          (machinePresentation spec)) => events.map fun occurrence => occurrence.2.site)
      (EventPath.events_append (machinePresentation spec)
        (historyEventPath spec initial past)
        (EventPath.cons (presentation := machinePresentation spec)
          (source := middle.term) (middle := after.term) (target := after.term)
          (site := event.val)
          (⟨event.property⟩ : OccurrenceEvidence spec event.val middle.term after.term)
          (.nil (presentation := machinePresentation spec) after.term)))
    exact joined.trans (by
      simp only [List.map_append, EventPath.events, List.map_cons, List.map_nil, ih]
      rfl)

/-- Production-only semantic factors, derived from the actual source state. -/
def productionCoefficient [Monoid V]
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    (before _after : World) : V :=
  (productionReceipt? before).elim 1 coefficient

/-- The existing history RunAccount and independent incremental production
ledger observe the same chronological factors. -/
theorem production_history_account [Monoid V]
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    (initial : World)
    {before after : RewriteEventHistory.State (system (pathMachine spec initial))}
    (history : Quiver.Path before after) :
    (NeedWeightedResumption.coefficientAccount spec (productionCoefficient coefficient) initial).of
        history =
      denote (productionLedger spec coefficient (historyEventPath spec initial history)) := by
  induction history with
  | nil =>
    simp only [historyEventPath_nil, productionLedger, productionReceipts,
      EventPath.events, List.filterMap_nil, List.map_nil, denote, List.prod_nil]
    exact (NeedWeightedResumption.coefficientAccount spec
      (productionCoefficient coefficient) initial).of_id _
  | @cons middle after past event ih =>
    rw [NeedWeightedResumption.coefficientAccount, eventAccount_cons]
    rw [historyEventPath_cons, productionLedger_denote_append]
    change (NeedWeightedResumption.coefficientAccount spec
      (productionCoefficient coefficient) initial).of past * _ = _
    rw [ih]
    congr 1
    simp only [productionLedger, productionReceipts, EventPath.events,
      productionCoefficient, denote, List.filterMap_cons, List.filterMap_nil]
    cases classified : productionReceipt? middle.term <;> simp

/-- Every returned or suspended contribution of the existing weighted handler
has a real reference path and the exact production-ledger coefficient. -/
theorem retained_production_ledger [Monoid V]
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    (initial : World) (fuel : Nat)
    (before : NeedWeightedResumption.WorkState Origin Local Resume Rule Value StableFault
      RetryableFault Effect)
    {leaf : (NeedWeightedResumption.WorkState Origin Local Resume Rule Value StableFault
      RetryableFault Effect ⊕ NeedWeightedResumption.WorkState Origin Local Resume Rule Value
      StableFault RetryableFault Effect) × V}
    (member : leaf ∈ WeightedBranchingResumption.contributions
      (NeedWeightedResumption.source spec (productionCoefficient coefficient)) fuel before) :
    ∃ history : History (pathMachine spec initial) before.state
        (NeedWeightedResumption.retained leaf.1).state,
      before.trace ++ indices (pathMachine spec initial) history =
        (NeedWeightedResumption.retained leaf.1).trace ∧
      Valid (productionLedger spec coefficient (historyEventPath spec initial history)) ∧
      denote (productionLedger spec coefficient (historyEventPath spec initial history)) =
        leaf.2 := by
  obtain ⟨history, trace, account⟩ := NeedWeightedResumption.retained_history
    spec (productionCoefficient coefficient) initial fuel before member
  refine ⟨history, trace, productionLedger_valid spec coefficient _, ?_⟩
  rw [← production_history_account]
  exact account

/-- Every authentic history occurs as a pending weighted contribution,
with its chronological production ledger rather than a supplied coefficient. -/
theorem history_pending_production_contribution [Monoid V]
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    (initial : World)
    {before after : RewriteEventHistory.State (system (pathMachine spec initial))}
    (history : Quiver.Path before after) (priorTrace : List Nat) :
    (.inr ⟨after.term, priorTrace ++ indices (pathMachine spec initial) history⟩,
      denote (productionLedger spec coefficient (historyEventPath spec initial history))) ∈
      WeightedBranchingResumption.contributions
        (NeedWeightedResumption.source spec (productionCoefficient coefficient))
        (indices (pathMachine spec initial) history).length ⟨before.term, priorTrace⟩ := by
  rw [← production_history_account]
  exact NeedWeightedResumption.history_pending_contribution
    spec (productionCoefficient coefficient) initial history priorTrace

/-- A halted authentic history is observed as a completed contribution;
observing the return leaves the same production ledger and exact trace. -/
theorem history_returned_production_contribution [Monoid V]
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    (initial : World)
    {before after : RewriteEventHistory.State (system (pathMachine spec initial))}
    (history : Quiver.Path before after) (priorTrace : List Nat)
    (halted : isHalted after.term = true) :
    (.inl ⟨after.term, priorTrace ++ indices (pathMachine spec initial) history⟩,
      denote (productionLedger spec coefficient (historyEventPath spec initial history))) ∈
      WeightedBranchingResumption.contributions
        (NeedWeightedResumption.source spec (productionCoefficient coefficient))
        ((indices (pathMachine spec initial) history).length + 1)
        ⟨before.term, priorTrace⟩ := by
  rw [← production_history_account]
  exact NeedWeightedResumption.history_returned_contribution
    spec (productionCoefficient coefficient) initial history priorTrace halted

namespace ProductionResumptionControls

private abbrev TestWork :=
  NeedWeightedResumption.WorkState Unit Nat Nat Unit Nat Unit Unit Unit
private abbrev testSpec := CompletedReceiptControls.spec
private def initialOccurrence : TestWork := ⟨CompletedReceiptControls.start, []⟩
private def observe (leaves : List ((TestWork ⊕ TestWork) × Nat)) :=
  leaves.map fun leaf =>
    (match leaf.1 with | .inl _ => true | .inr _ => false,
      (NeedWeightedResumption.retained leaf.1).state.world.receipts.nextSerial,
      (NeedWeightedResumption.retained leaf.1).state.work.transitions,
      leaf.2, (NeedWeightedResumption.retained leaf.1).trace)

/-- Production followed by two cached deliveries retains three receipts,
ten machine transitions, and one coefficient in the completed handler leaf. -/
theorem completed_shared_production :
    observe (WeightedBranchingResumption.contributions
      (NeedWeightedResumption.source testSpec (productionCoefficient (fun _ => (2 : Nat))))
      11 initialOccurrence) = [(true, 3, 10, 2, List.replicate 10 0)] := by decide

/-- Cutting immediately after the production leaves its coefficient,
receipt, work and selected occurrence in a pending contribution. -/
theorem suspension_retains_paid_production :
    observe (WeightedBranchingResumption.contributions
      (NeedWeightedResumption.source testSpec (productionCoefficient (fun _ => (2 : Nat))))
      1 initialOccurrence) = [(false, 1, 1, 2, [0])] := by decide

private def resumed : List ((TestWork ⊕ TestWork) × Nat) :=
  WeightedResumption.sequence
    (WeightedBranchingResumption.contributions
      (NeedWeightedResumption.source testSpec (productionCoefficient (fun _ => (2 : Nat))))
      1 initialOccurrence)
    (fun leaf => match leaf with
      | .inl done => [(.inl done, 1)]
      | .inr pending => WeightedBranchingResumption.contributions
          (NeedWeightedResumption.source testSpec (productionCoefficient (fun _ => (2 : Nat))))
          10 pending)

/-- Resumption retains the earlier factor while charging no new production
for the later cached deliveries. The complete final occurrence stays present. -/
theorem resumed_shared_production :
    observe resumed = [(true, 3, 10, 2, List.replicate 10 0)] := by
  have exactResume := NeedWeightedResumption.resume_exact testSpec
    (productionCoefficient (fun _ => (2 : Nat))) 1 10 initialOccurrence
  calc
    observe resumed = observe (WeightedBranchingResumption.contributions
        (NeedWeightedResumption.source testSpec (productionCoefficient (fun _ => (2 : Nat))))
        (1 + 10) initialOccurrence) := congrArg observe exactResume.symm
    _ = _ := completed_shared_production

private def unpaidSuffix : List ((TestWork ⊕ TestWork) × Nat) :=
  (WeightedBranchingResumption.contributions
    (NeedWeightedResumption.source testSpec (productionCoefficient (fun _ => (2 : Nat))))
    1 initialOccurrence).flatMap fun leaf =>
      match leaf.1 with
      | .inl _ => []
      | .inr pending => WeightedBranchingResumption.contributions
          (NeedWeightedResumption.source testSpec (productionCoefficient (fun _ => (2 : Nat))))
          10 pending

/-- Restarting only the suffix loses the production's incoming coefficient,
even though final values, work, receipts and selected occurrences agree. -/
theorem resetting_incoming_coefficient_refused :
    observe unpaidSuffix = [(true, 3, 10, 1, List.replicate 10 0)] ∧
      observe unpaidSuffix ≠ observe resumed := by
  constructor
  · decide
  · rw [resumed_shared_production]
    decide

/-- A zero production factor does not erase the completed occurrence,
its delivery receipts, or the actual machine transitions. -/
theorem zero_production_retains_completed_occurrence :
    observe (WeightedBranchingResumption.contributions
      (NeedWeightedResumption.source testSpec (productionCoefficient (fun _ => (0 : Nat))))
      11 initialOccurrence) = [(true, 3, 10, 0, List.replicate 10 0)] := by decide

end ProductionResumptionControls


end Histories

end Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption
