import Mettapedia.Machines.BranchLocalNeed.InferenceControl
import Mettapedia.Machines.BranchLocalNeed.FrontierLaws
import Mettapedia.GSLT.Dynamics.WeightedBranchingResumption

/-!
# Weighted handlers of the branch-local Need machine

The operation catalogue is constructed from actual Need successors. Its
responses are successor positions, so duplicate rules remain distinct. Each
open or returned leaf retains the complete work occurrence: heap, shared
choices, control stack, receipts and existing cost counters.

The free handler agrees with an independently defined weighted frontier run.
Every retained occurrence carries a reference-machine derivation and its exact
transition cost. A returned leaf is proved halted; exhausting an unfolding
budget does not certify closure.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption

open NeedReference
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Dynamics
open WeightedResumption

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

end Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption
