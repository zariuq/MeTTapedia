import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.Core.ObservationScopeCompletion

/-!
# Demand-directed execution of an existing controlled search

The executor stops at a satisfied observation or actual frontier closure.  A
budget boundary retains the existing snapshot, including controller memory.
It does not replace pending computations by already enumerated answers.

Satisfaction and closure are independent: the last required answer may also
close the search.  `run_prefix` connects every bounded demanded execution to
the independently defined uncontrolled-length execution of the same
controller.  Conservation and soundness therefore extend to demanded runs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.DemandExecution

open BranchingTemporal
open InferenceControl (Controller)

variable {Node Answer Memory : Type*}

abbrev State (Node Answer Memory : Type*) :=
  InferenceControl.Snapshot Node Answer Memory

def answers (state : State Node Answer Memory) : List Answer :=
  state.search.events.map Emission.value

def satisfied (goal : List Answer → Bool) (state : State Node Answer Memory) : Bool :=
  goal (answers state)

def closed (state : State Node Answer Memory) : Bool :=
  state.search.frontier.isEmpty

def stopped (goal : List Answer → Bool) (state : State Node Answer Memory) : Bool :=
  satisfied goal state || closed state

/-- A fuel allowance bounds expansions, not the number of already computed
answers to discard.  The whole residual snapshot is returned. -/
def run (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (goal : List Answer → Bool) :
    Nat → State Node Answer Memory → State Node Answer Memory
  | 0, state => state
  | fuel + 1, state =>
      if stopped goal state then state
      else run system controller goal fuel
        (InferenceControl.Snapshot.tick system controller state)

theorem run_of_stopped (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (goal : List Answer → Bool)
    (fuel : Nat) (state : State Node Answer Memory)
    (done : stopped goal state = true) :
    run system controller goal fuel state = state := by
  cases fuel <;> simp [run, done]

/-- Splitting the allowance does not restart the original call or forget the
controller's state.  This holds for arbitrary decidable goals. -/
theorem run_add (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (goal : List Answer → Bool)
    (first second : Nat) (state : State Node Answer Memory) :
    run system controller goal (first + second) state =
      run system controller goal second (run system controller goal first state) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih =>
      cases hstop : stopped goal state with
      | false => simp [Nat.succ_add, run, hstop, ih]
      | true => simp [Nat.succ_add, run, hstop,
          run_of_stopped system controller goal second state hstop]

/-- Exact one-step realization extends to every demanded finite prefix.
The goal sees the same ordered answers and closure sees the same number of
pending occurrences; neither can stop one realization before the other. -/
theorem run_mapNodes {NextNode : Type*} (mapping : Node → NextNode)
    (source : BranchingSystem Node Answer) (target : BranchingSystem NextNode Answer)
    (first : Controller Node Answer Memory) (second : Controller NextNode Answer Memory)
    (goal : List Answer → Bool)
    (ticks : ∀ state : State Node Answer Memory,
      (InferenceControl.Snapshot.tick source first state).mapNodes mapping =
        InferenceControl.Snapshot.tick target second (state.mapNodes mapping))
    (fuel : Nat) (state : State Node Answer Memory) :
    (run source first goal fuel state).mapNodes mapping =
      run target second goal fuel (state.mapNodes mapping) := by
  have stopEquality : ∀ state : State Node Answer Memory,
      stopped goal (state.mapNodes mapping) = stopped goal state := by
    intro current
    simp [stopped, satisfied, answers, closed, InferenceControl.Snapshot.mapNodes,
      BranchingTemporal.Snapshot.mapNodes, BranchingTemporal.Emission.mapOrigin,
      List.map_map, Function.comp_def]
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [run, stopEquality]
      cases done : stopped goal state with
      | true => rfl
      | false => simp only [Bool.false_eq_true, ↓reduceIte, ih, ticks]

/-- The demand mechanism only shortens the original controlled run. -/
theorem run_prefix (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (goal : List Answer → Bool)
    (fuel : Nat) (state : State Node Answer Memory) :
    ∃ used ≤ fuel, run system controller goal fuel state =
      InferenceControl.Snapshot.run system controller used state := by
  induction fuel generalizing state with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ fuel ih =>
      cases hstop : stopped goal state with
      | true => exact ⟨0, Nat.zero_le _, by simp [run, hstop,
          InferenceControl.Snapshot.run]⟩
      | false =>
          obtain ⟨used, bound, same⟩ :=
            ih (InferenceControl.Snapshot.tick system controller state)
          refine ⟨1 + used, by omega, ?_⟩
          simpa [run, hstop, InferenceControl.Snapshot.run_add,
            InferenceControl.Snapshot.run] using same

theorem events_prefix (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (goal : List Answer → Bool)
    (fuel : Nat) (state : State Node Answer Memory) :
    state.search.events.IsPrefix (run system controller goal fuel state).search.events := by
  obtain ⟨used, _, same⟩ := run_prefix system controller goal fuel state
  rw [same]
  exact InferenceControl.Snapshot.events_prefix_run system controller used state

theorem run_sound (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (goal : List Answer → Bool)
    (fuel : Nat) {roots : List Node} {state : State Node Answer Memory}
    (sound : state.search.Sound system roots) :
    (run system controller goal fuel state).search.Sound system roots := by
  obtain ⟨used, _, same⟩ := run_prefix system controller goal fuel state
  rw [same]
  exact InferenceControl.Snapshot.sound_run system controller sound used

/-- A newly interpreted controller can continue captured work after an
explicit memory transfer. Reachability is still authorized by the same
branching system; the transfer does not reinitialize its frontier. -/
theorem run_after_memory_transfer_sound {NextMemory : Type*}
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer NextMemory)
    (transfer : Memory → NextMemory) (goal : List Answer → Bool) (fuel : Nat)
    {roots : List Node} {state : State Node Answer Memory}
    (sound : state.search.Sound system roots) :
    (run system controller goal fuel
      (InferenceControl.Snapshot.mapMemory transfer state)).search.Sound system roots := by
  exact run_sound system controller goal fuel
    ((InferenceControl.Snapshot.mapMemory_sound_iff system roots transfer state).mpr sound)

/-- A zero allowance after changing controller memory leaves pending work
pending. It cannot certify closure even if the new controller would select a
different occurrence on its next step. -/
theorem zero_budget_after_memory_transfer_not_closed {NextMemory : Type*}
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer NextMemory)
    (transfer : Memory → NextMemory) (goal : List Answer → Bool)
    (state : State Node Answer Memory) (pending : state.search.frontier ≠ []) :
    closed (run system controller goal 0
      (InferenceControl.Snapshot.mapMemory transfer state)) = false := by
  change state.search.frontier.isEmpty = false
  exact List.isEmpty_eq_false_iff.mpr pending

/-- Once the full controlled run would reach a stopping boundary, the demand
executor reaches some stopping boundary within the same allowance. -/
theorem stopped_of_full_run (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (goal : List Answer → Bool)
    (fuel : Nat) (state : State Node Answer Memory)
    (done : stopped goal
      (InferenceControl.Snapshot.run system controller fuel state) = true) :
    stopped goal (run system controller goal fuel state) = true := by
  induction fuel generalizing state with
  | zero => exact done
  | succ fuel ih =>
      cases hstop : stopped goal state with
      | true => simp [run, hstop]
      | false =>
          have next : stopped goal (InferenceControl.Snapshot.run system controller fuel
              (InferenceControl.Snapshot.tick system controller state)) = true := by
            change stopped goal (InferenceControl.Snapshot.run system controller fuel
              (InferenceControl.Snapshot.run system controller 1 state)) = true
            rw [← InferenceControl.Snapshot.run_add, Nat.add_comm 1 fuel]
            exact done
          simpa [run, hstop] using
            ih (InferenceControl.Snapshot.tick system controller state) next

/-- A valid finite denotation is conserved even when only a demanded prefix
has been observed.  Concrete operational instances supply this denotation. -/
theorem residual_account (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (denotation : AdditiveDenotation system)
    (goal : List Answer → Bool) (fuel : Nat) (state : State Node Answer Memory) :
    account denotation (run system controller goal fuel state).search =
      account denotation state.search := by
  obtain ⟨used, _, same⟩ := run_prefix system controller goal fuel state
  rw [same]
  exact InferenceControl.Snapshot.account_run system controller denotation used state

/-- Controller replacement preserves the complete emitted-plus-pending
account whenever the source system has this finite additive denotation. -/
theorem residual_account_after_memory_transfer {NextMemory : Type*}
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer NextMemory)
    (denotation : AdditiveDenotation system) (transfer : Memory → NextMemory)
    (goal : List Answer → Bool) (fuel : Nat) (state : State Node Answer Memory) :
    account denotation
        (run system controller goal fuel
          (InferenceControl.Snapshot.mapMemory transfer state)).search =
      account denotation state.search := by
  exact residual_account system controller denotation goal fuel
    (InferenceControl.Snapshot.mapMemory transfer state)

/-- Closed demanded executions have no latent answer account. -/
theorem closed_account (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (denotation : AdditiveDenotation system)
    (goal : List Answer → Bool) (fuel : Nat) (state : State Node Answer Memory)
    (complete : closed (run system controller goal fuel state) = true) :
    eventBag (run system controller goal fuel state).search.events =
      account denotation state.search := by
  have empty : (run system controller goal fuel state).search.frontier = [] :=
    List.isEmpty_iff.mp complete
  simpa [account, empty, foldValues] using
    residual_account system controller denotation goal fuel state

/-- Absolute occurrence demand.  Additional demand after resumption adds to
the already emitted count; it does not erase the previous prefix. -/
def atLeast (requested : Nat) (values : List Answer) : Bool :=
  decide (requested ≤ values.length)

@[simp] theorem atLeast_iff (requested : Nat) (values : List Answer) :
    atLeast requested values = true ↔ requested ≤ values.length := by
  simp [atLeast]

/-- The new executable counter has exactly the existing scope contract. -/
theorem atLeast_scope (requested : Nat) (state : State Node Answer Memory) :
    satisfied (atLeast requested) state = true ↔
      ObservationScopeCompletion.CountSatisfied
        (.finitePrefix requested) state.search.events.length := by
  simp [satisfied, atLeast, answers, ObservationScopeCompletion.CountSatisfied]

/-- Each expansion publishes at most one answer occurrence.  The executor
can therefore stop at an exact occurrence count without dropping a suffix. -/
theorem events_length_tick_le (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (state : State Node Answer Memory) :
    (InferenceControl.Snapshot.tick system controller state).search.events.length ≤
      state.search.events.length + 1 := by
  change (BranchingTemporal.tick system (controller.scheduler state.memory)
    state.search).events.length ≤ state.search.events.length + 1
  cases ordered : (controller.scheduler state.memory).reorder state.search.frontier with
  | nil => simp [BranchingTemporal.tick, ordered]
  | cons node pending =>
      cases emitted : system.emit node with
      | none =>
          simp only [BranchingTemporal.tick, ordered, emitted]
          change (state.search.events ++ []).length ≤ state.search.events.length + 1
          simp
      | some answer =>
          simp only [BranchingTemporal.tick, ordered, emitted]
          change (state.search.events ++ [(⟨node, answer⟩ : Emission Node Answer)]).length ≤
            state.search.events.length + 1
          simp

/-- Increasing fuel for a bounded demand does not overshoot the requested
count.  This includes demand zero and resumption from a partial prefix. -/
theorem atLeast_no_overshoot (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (requested fuel : Nat)
    (state : State Node Answer Memory) (initialBound : state.search.events.length ≤ requested) :
    (run system controller (atLeast requested) fuel state).search.events.length ≤ requested := by
  induction fuel generalizing state with
  | zero => exact initialBound
  | succ fuel ih =>
      cases hstop : stopped (atLeast requested) state with
      | true => simpa [run, hstop] using initialBound
      | false =>
          have notEnough : state.search.events.length < requested := by
            have : satisfied (atLeast requested) state = false := by
              simpa [stopped] using (Bool.or_eq_false_iff.mp hstop).1
            simp only [satisfied, atLeast, answers, List.length_map, decide_eq_false_iff_not]
              at this
            omega
          have nextBound := events_length_tick_le system controller state
          simpa [run, hstop] using
            ih (InferenceControl.Snapshot.tick system controller state) (by omega)

theorem atLeast_satisfied_exact (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (requested fuel : Nat)
    (state : State Node Answer Memory) (initialBound : state.search.events.length ≤ requested)
    (enough : satisfied (atLeast requested)
      (run system controller (atLeast requested) fuel state) = true) :
    (run system controller (atLeast requested) fuel state).search.events.length = requested := by
  have upper := atLeast_no_overshoot system controller requested fuel state initialBound
  have lower : requested ≤
      (run system controller (atLeast requested) fuel state).search.events.length := by
    simpa [satisfied, atLeast, answers] using enough
  omega

/-- Before satisfaction, any early stop is real closure.  Since a closed
snapshot is absorbing, the demanded and full-length executions then agree. -/
theorem unsatisfied_eq_full_run (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (goal : List Answer → Bool)
    (fuel : Nat) (state : State Node Answer Memory)
    (notEnough : satisfied goal (run system controller goal fuel state) = false) :
    run system controller goal fuel state =
      InferenceControl.Snapshot.run system controller fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases hstop : stopped goal state with
      | true =>
          have notEnoughNow : satisfied goal state = false := by
            simpa [run, hstop] using notEnough
          have isClosed : closed state = true := by
            simpa [stopped, notEnoughNow] using hstop
          have empty : state.search.frontier = [] := List.isEmpty_iff.mp isClosed
          rw [run_of_stopped system controller goal (fuel + 1) state hstop,
            InferenceControl.Snapshot.run_eq_self_of_frontier_nil
              system controller state empty]
      | false =>
          have nextNotEnough : satisfied goal
              (run system controller goal fuel
                (InferenceControl.Snapshot.tick system controller state)) = false := by
            simpa [run, hstop] using notEnough
          rw [run, hstop, ih _ nextNotEnough]
          change InferenceControl.Snapshot.run system controller fuel
            (InferenceControl.Snapshot.run system controller 1 state) = _
          rw [← InferenceControl.Snapshot.run_add, Nat.add_comm 1 fuel]

/-- A proved finite descent bound completes a demanded execution either by
satisfaction or by exhaustive closure. -/
theorem finite_demand_stops (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (certificate : DescentCertificate system)
    (goal : List Answer → Bool) (state : State Node Answer Memory) :
    stopped goal (run system controller goal
      (foldRanks certificate.rank state.search.frontier) state) = true := by
  apply stopped_of_full_run
  have complete := InferenceControl.Snapshot.run_completes_at_rank
    system controller certificate state
  simp [stopped, closed, complete]

/-- The finite-search shortage certificate uses the entire operational
account, rather than failure to find a witness before a budget expires. -/
theorem finite_shortage (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (certificate : DescentCertificate system)
    (denotation : AdditiveDenotation system) (requested : Nat)
    (state : State Node Answer Memory)
    (notEnough : satisfied (atLeast requested)
      (run system controller (atLeast requested)
        (foldRanks certificate.rank state.search.frontier) state) = false) :
    closed (run system controller (atLeast requested)
      (foldRanks certificate.rank state.search.frontier) state) = true ∧
      (account denotation state.search).card < requested := by
  have complete : closed (run system controller (atLeast requested)
      (foldRanks certificate.rank state.search.frontier) state) = true := by
    have stops := finite_demand_stops system controller certificate (atLeast requested) state
    simpa [stopped, notEnough] using stops
  refine ⟨complete, ?_⟩
  have exhausted := closed_account system controller denotation (atLeast requested)
    (foldRanks certificate.rank state.search.frontier) state complete
  rw [← exhausted]
  simp only [eventBag, Multiset.coe_card, List.length_map]
  simp only [satisfied, atLeast, answers, List.length_map, decide_eq_false_iff_not]
    at notEnough
  omega

/-- A full run's witnessed satisfaction is also reached by demand-directed
execution with the same allowance. -/
theorem satisfied_of_full_run (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (goal : List Answer → Bool)
    (fuel : Nat) (state : State Node Answer Memory)
    (enough : satisfied goal
      (InferenceControl.Snapshot.run system controller fuel state) = true) :
    satisfied goal (run system controller goal fuel state) = true := by
  cases result : satisfied goal (run system controller goal fuel state) with
  | true => rfl
  | false =>
      rw [unsatisfied_eq_full_run system controller goal fuel state result, enough] at result
      contradiction

/-- All members of a finite reachable witness family appear together after
some finite allowance.  Infinite answer spaces require no finite denotation. -/
theorem reachable_events_cooccur (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (roots : List Node)
    (fair : InferenceControl.Snapshot.FairFrom system controller roots)
    (witnesses : List (Emission Node Answer))
    (valid : ∀ event ∈ witnesses, EventValid system roots event) :
    ∃ fuel, witnesses ⊆ (InferenceControl.Snapshot.run system controller fuel
      (InferenceControl.Snapshot.initial controller roots)).search.events := by
  induction witnesses with
  | nil => exact ⟨0, by simp⟩
  | cons event rest ih =>
      obtain ⟨first, headMember⟩ :=
        InferenceControl.Snapshot.fair_emits_reachable system controller roots fair
          (valid event (by simp)).1 (valid event (by simp)).2
      obtain ⟨second, restSubset⟩ := ih (by
        intro member membership
        exact valid member (by simp [membership]))
      refine ⟨first + second, ?_⟩
      intro member membership
      rcases List.mem_cons.mp membership with head | tail
      · subst member
        rw [InferenceControl.Snapshot.run_add]
        exact (InferenceControl.Snapshot.events_prefix_run system controller second _).subset
          headMember
      · have preserved :=
          (InferenceControl.Snapshot.events_prefix_run system controller first
            (InferenceControl.Snapshot.run system controller second
              (InferenceControl.Snapshot.initial controller roots))).subset (restSubset tail)
        rw [← InferenceControl.Snapshot.run_add, Nat.add_comm second first] at preserved
        exact preserved

/-- A fair controller satisfies every finitely witnessed occurrence demand.
Distinct occurrences may have equal values; their origins distinguish them. -/
theorem fair_atLeast_liveness (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (roots : List Node)
    (fair : InferenceControl.Snapshot.FairFrom system controller roots)
    (requested : Nat) (witnesses : List (Emission Node Answer))
    (distinct : witnesses.Nodup) (enough : requested ≤ witnesses.length)
    (valid : ∀ event ∈ witnesses, EventValid system roots event) :
    ∃ fuel, satisfied (atLeast requested)
      (run system controller (atLeast requested) fuel
        (InferenceControl.Snapshot.initial controller roots)) = true := by
  obtain ⟨fuel, subset⟩ := reachable_events_cooccur system controller roots fair witnesses valid
  refine ⟨fuel, satisfied_of_full_run system controller (atLeast requested) fuel _ ?_⟩
  have count := distinct.length_le_of_subset subset
  simp only [satisfied, atLeast, answers, List.length_map, decide_eq_true_eq]
  omega

/-- Fair independent selection returns exactly the requested number, while
the remaining search stays owned by the resulting snapshot. -/
theorem fair_atLeast_exact (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (roots : List Node)
    (fair : InferenceControl.Snapshot.FairFrom system controller roots)
    (requested : Nat) (witnesses : List (Emission Node Answer))
    (distinct : witnesses.Nodup) (enough : requested ≤ witnesses.length)
    (valid : ∀ event ∈ witnesses, EventValid system roots event) :
    ∃ fuel, (run system controller (atLeast requested) fuel
      (InferenceControl.Snapshot.initial controller roots)).search.events.length = requested := by
  obtain ⟨fuel, satisfied⟩ :=
    fair_atLeast_liveness system controller roots fair requested witnesses distinct enough valid
  exact ⟨fuel, atLeast_satisfied_exact system controller requested fuel _ (by simp
    [InferenceControl.Snapshot.initial, BranchingTemporal.initial]) satisfied⟩

theorem closure_does_not_mean_satisfaction :
    ∃ state : State Nat Nat Unit, closed state = true ∧
      satisfied (atLeast 7) state = false := by
  exact ⟨⟨⟨[⟨0, 0⟩], []⟩, ()⟩, rfl, by decide⟩

namespace Controls

def controller : Controller (FiniteSearch Nat) Nat Unit :=
  Controller.fixed Scheduler.breadthFirst

def root : FiniteSearch Nat :=
  .choice (.answer 3) (.delay (.answer 5))

def start : State (FiniteSearch Nat) Nat Unit :=
  InferenceControl.Snapshot.initial controller [root]

example : answers (run FiniteSearch.system controller (atLeast 1) 20 start) = [3] := by
  decide

example : closed (run FiniteSearch.system controller (atLeast 1) 20 start) = false := by
  decide

example : answers (run FiniteSearch.system controller (atLeast 7) 20 start) = [3, 5] := by
  decide

example : closed (run FiniteSearch.system controller (atLeast 7) 20 start) = true := by
  decide

example : closed (run FiniteSearch.system controller (atLeast 7) 1 start) = false := by
  decide

example :
    let result := run FiniteSearch.system controller (atLeast 2) 20 start
    satisfied (atLeast 2) result = true ∧ closed result = true := by
  decide

example :
    answers (run FiniteSearch.system controller (atLeast 2) 20
      (run FiniteSearch.system controller (atLeast 1) 20 start)) = [3, 5] := by
  decide

end Controls

end Mettapedia.GSLT.Core.DemandExecution
