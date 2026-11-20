import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationRunProfile

/-!
# Infinite profile executions have no erased administrative progress

A stream supplies an instruction at each actual configuration. Every finite
prefix exports an actual run with exactly as many firings as instructions,
and the decoded configurations form an infinite source reduction. This
states correspondence for a given stream, without a fairness or termination
claim about an external scheduler.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open AlgebraicParallel NativeTypesOnTheStep.Computing ConversionCoherence

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  (qualified : Qualified S) (presentation : SchemaPresentation S.R)

structure Stream where
  configuration : Nat → Configuration (S := S)
  instruction : ∀ index, Instruction presentation (configuration index)
  target : Nat → Nat
  fresh : ∀ index, target index ∉ (configuration index).state.present
  advance : ∀ index, configuration (index + 1) = (instruction index).next qualified (target index) (fresh index)

namespace Execution

variable {qualified presentation}

theorem length_cast {before after : Configuration (S := S)} (same : before = after)
    (execution : Execution qualified presentation before) : (same ▸ execution).length = execution.length := by
  cases same
  rfl

theorem last_cast {before after : Configuration (S := S)} (same : before = after)
    (execution : Execution qualified presentation before) : (same ▸ execution).last = execution.last := by
  cases same
  rfl

end Execution

namespace Stream

variable {qualified presentation}

def segment (stream : Stream qualified presentation) : (first count : Nat) →
    Execution qualified presentation (stream.configuration first)
  | first, 0 => .nil (stream.configuration first)
  | first, count + 1 => .cons (stream.instruction first) (stream.target first) (stream.fresh first)
      (stream.advance first ▸ stream.segment (first + 1) count)

theorem segment_length (stream : Stream qualified presentation) (first count : Nat) :
    (stream.segment first count).length = count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
      change (stream.advance first ▸ stream.segment (first + 1) count).length + 1 = count + 1
      rw [Execution.length_cast, ih]

theorem segment_last (stream : Stream qualified presentation) (first count : Nat) :
    (stream.segment first count).last = stream.configuration (first + count) := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
      change (stream.advance first ▸ stream.segment (first + 1) count).last = _
      rw [Execution.last_cast, ih]
      congr 1
      omega

theorem native_prefix_count (stream : Stream qualified presentation) (count : Nat) :
    (stream.segment 0 count).toRun.word.length = count :=
  (stream.segment 0 count).event_count.trans (stream.segment_length 0 count)

theorem native_prefix_state (stream : Stream qualified presentation) (count : Nat) :
    (stream.segment 0 count).toRun.last = (stream.configuration count).state := by
  have state := congrArg Configuration.state (stream.segment_last 0 count)
  simpa only [Nat.zero_add] using (stream.segment 0 count).toRun_last.trans state

def readout (stream : Stream qualified presentation) (index : Nat) : Σ n : Nat, Tm Head n :=
  ⟨(stream.configuration index).state.frame.arity, (stream.configuration index).code⟩

def ScopedStep (before after : Σ n : Nat, Tm Head n) : Prop :=
  ∃ (n : Nat) (left right : Tm Head n), before = ⟨n, left⟩ ∧ after = ⟨n, right⟩ ∧
    StepCore S.R.computation S.R.headEq left right

theorem source_step (stream : Stream qualified presentation) (index : Nat) :
    ScopedStep (S := S) (stream.readout index) (stream.readout (index + 1)) := by
  refine ⟨_, (stream.configuration index).code, (stream.instruction index).event.target,
    rfl, ?_, (stream.instruction index).reduction⟩
  unfold readout
  rw [stream.advance index]
  exact congrArg (fun term => (⟨(stream.configuration index).state.frame.arity, term⟩ : Σ n : Nat, Tm Head n))
    ((stream.instruction index).next_code qualified (stream.target index) (stream.fresh index))

end Stream

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Stream.native_prefix_count
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Stream.source_step
