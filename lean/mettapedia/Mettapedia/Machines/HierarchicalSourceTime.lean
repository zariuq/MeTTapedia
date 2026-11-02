import Mettapedia.Machines.FiniteStackWorker
import Mettapedia.Machines.HierarchicalPrefixLaws

/-!
# Original source-machine time in a live prefix hierarchy

The two counted source executions are joined by the existing physical
two-pass composition. The first program has separate input/output ports,
so its output-transfer cost is paid by its original transition time with
a constant computed from the fixed transition table. The retained worker
and hierarchy then use that combined original-time bound directly.

This theorem is for the actual composed machines. It is not an assertion
that an unspecified compiler is fast. Preparing an IC autoencoder packet,
retaining its context and verifying its reconstruction remain additional
wrapper operations; arbitrary source outputs are not checked IC features.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Machines.HierarchicalSourceTime

open Turing StateTransition KolmogorovComplexity
open Mettapedia.Computability

variable {κ : Type}

structure Call (first second : FinTM2) where
  word : BinString
  middle : List (first.Γ first.k₁)
  output : List (second.Γ second.k₁)
  firstTime : Nat
  secondTime : Nat

def sourceTime {first second : FinTM2} (call : Call first second) : Nat :=
  (1 + 2 * StackMachineSpaceGrowth.machinePushBound first) * call.firstTime + call.secondTime + 2

def timed {first second : FinTM2} (call : Call first second) :
    HierarchicalPrefixSearch.TimedEntry (List (second.Γ second.k₁)) :=
  ((call.word, call.output), sourceTime call)

variable (first second : FinTM2)
  [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)]
  (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)

inductive SourcePath (first second : FinTM2) (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (input : κ → BinString → List (first.Γ first.k₀))
    (nextInput : κ → List (second.Γ second.k₁) → κ) : κ → List (Call first second) → Prop
  | nil (context : κ) : SourcePath first second bridge input nextInput context []
  | cons {context : κ} (call : Call first second) {rest : List (Call first second)}
      (left : TM2OutputsInTime first (input context call.word) (some call.middle) call.firstTime)
      (right : TM2OutputsInTime second (call.middle.map bridge) (some call.output) call.secondTime)
      (later : SourcePath first second bridge input nextInput (nextInput context call.output) rest) :
      SourcePath first second bridge input nextInput context (call :: rest)

theorem sourcePath_to_timed (distinct : first.k₀ ≠ first.k₁)
    (input : κ → BinString → List (first.Γ first.k₀)) (nextInput : κ → List (second.Γ second.k₁) → κ)
    {context : κ} {calls : List (Call first second)}
    (path : SourcePath first second bridge input nextInput context calls) :
    HierarchicalPrefixSearch.TimedPath
      (fun context => FiniteStackWorker.worker (StackMachineComposition.machine first second bridge) (input context))
      nextInput context (calls.map (timed (first := first) (second := second))) := by
  induction path with
  | nil context => exact .nil context
  | @cons context call rest left right later ih =>
      have joined := StackMachinePortTime.composition_linear first second bridge distinct left right
      exact .cons (FiniteStackWorker.complete (StackMachineComposition.machine first second bridge)
        (input context) call.word call.output (sourceTime call) joined) ih

/-- Every declared source-call path is reached by the live competing
hierarchy using original execution times and a charged physical handoff.
Constants are fixed by the first finite machine before all contexts/calls. -/
theorem path_by_source_time (distinct : first.k₀ ≠ first.k₁)
    (input : κ → BinString → List (first.Γ first.k₀)) (nextInput : κ → List (second.Γ second.k₁) → κ)
    (accepts : BinString → Bool) (free : PrefixFree {word | accepts word = true})
    {context : κ} {calls : List (Call first second)}
    (path : SourcePath first second bridge input nextInput context calls)
    (admitted : ∀ call ∈ calls, accepts call.word = true) (depth : Nat) (bounded : calls.length ≤ depth) :
    let workers := fun context => FiniteStackWorker.worker (StackMachineComposition.machine first second bridge) (input context)
    HierarchicalPrefixSearch.Follows depth (calls.map fun call => (call.word, call.output))
      (ResumablePrefixClock.run (HierarchicalPrefixSearch.tick workers accepts nextInput depth)
        (HierarchicalPrefixSearch.nestedBound (calls.map (timed (first := first) (second := second))))
        (HierarchicalPrefixSearch.initial workers depth context)) := by
  have asTimed := sourcePath_to_timed first second bridge distinct input nextInput path
  have permitted : ∀ entry ∈ calls.map (timed (first := first) (second := second)), accepts entry.1.1 = true := by
    intro entry member
    obtain ⟨call, present, rfl⟩ := List.mem_map.mp member
    exact admitted call present
  have reached := HierarchicalPrefixSearch.path_by_bound
    (fun context => FiniteStackWorker.worker (StackMachineComposition.machine first second bridge) (input context))
    accepts free nextInput asTimed permitted depth (by simpa using bounded)
  simpa only [List.map_map, timed, Function.comp_def] using reached

omit [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)] in
theorem weighted_source_time_sum (calls : List (Call first second)) :
    HierarchicalPrefixSearch.nestedBound (calls.map timed) =
      (HierarchicalPrefixSearch.weightedTerms 0 (calls.map timed)).sum :=
  HierarchicalPrefixSearch.nestedBound_eq_weighted_sum _

end Mettapedia.Machines.HierarchicalSourceTime
