import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedParameterMap
import Mettapedia.Machines.BranchLocalNeed.LocalRepresentation
import Mettapedia.Machines.BranchLocalNeed.LocalStepPaths
import Mettapedia.GSLT.Causality.OccurrenceMachineHistory

/-!
# Execution commutes with polarized parameter instantiation

Primitive compatibility is checked locally on native arguments/results. All
source constructors and actual Need transitions then commute, including
ordinary force, lexical application, shared cache replay and ordered choices.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.PolarizedNeedParameterMap

open Mettapedia.Machines.BranchLocalNeed NeedReference PolarizedNeed PolarizedNeedMachine

variable {H H' O E E' F N : Type} {m : Nat}

def nativeOutcome (heads : H → H') : Produced (Tm H m) F N → Produced (Tm H' m) F N
  | .value term => .value (term.mapHead heads)
  | .stableFault fault => .stableFault fault
  | .retryableFault reason => .retryableFault reason

theorem lift_outcome (heads : H → H') (effects : E → E')
    (result : Produced (Tm H m) F N) :
    liftOutcome (Operation := O) (Effect := E') (nativeOutcome heads result) =
      outcome heads effects (liftOutcome result) := by
  cases result <;> rfl

theorem alternatives_captured (heads : H → H') (effects : E → E')
    (body : Closure H O E m) :
    alternatives (StableFault := F) (NativeFault := N) (captured heads effects body) =
      (alternatives body).map (fun pair => (pair.1, state heads effects pair.2)) := by
  rcases body with ⟨n, v, k, body, native, values, needs⟩
  cases body <;> rfl

theorem after_allocation (heads : H → H') (effects : E → E')
    (consumer : Resume H O E m) (cell : CellId) :
    afterAllocation (StableFault := F) (NativeFault := N) (resume heads effects consumer) cell =
      state heads effects (afterAllocation consumer cell) := by
  cases consumer <;> rfl

theorem after_demand (heads : H → H') (effects : E → E')
    (consumer : Resume H O E m) (result : Outcome H O E F N m) :
    afterDemand (resume heads effects consumer) (outcome heads effects result) =
      state heads effects (afterDemand consumer result) := by
  cases consumer with
  | finish continuation => exact deliver_outcome heads effects result continuation
  | bindNative body continuation =>
      cases result with
      | value result =>
          cases result with
          | returned inner => cases inner <;>
              simp only [resume, outcome, answer, runtimeValue, afterDemand, state,
                captured_native_open]
          | nativeFunction body => rfl
          | valueFunction body => rfl
      | stableFault fault => rfl
      | retryableFault reason => rfl
  | bindSigma body continuation =>
      cases result with
      | value result =>
          cases result with
          | returned inner => cases inner <;>
              simp only [resume, outcome, answer, runtimeValue, afterDemand, state,
                captured_native_open, kont]
          | nativeFunction body => rfl
          | valueFunction body => rfl
      | stableFault fault => rfl
      | retryableFault reason => rfl
  | bindValue body continuation =>
      cases result with
      | value result => cases result <;>
          simp only [resume, outcome, answer, afterDemand, state, captured_value_open]
      | stableFault fault => rfl
      | retryableFault reason => rfl
  | bindNeed body continuation => rfl

theorem action_state (heads : H → H') (effects : E → E')
    (source : O → Tm H m → Produced (Tm H m) F N)
    (target : O → Tm H' m → Produced (Tm H' m) F N)
    (primitives : ∀ operation argument, target operation (argument.mapHead heads) =
      nativeOutcome heads (source operation argument))
    (current : Local H O E F N m) :
    PolarizedNeedMachine.action target (state heads effects current) =
      (mapping heads effects).mapAction (PolarizedNeedMachine.action source current) := by
  cases current with
  | demand cell consumer => rfl
  | complete result => exact congrArg Action.done (mapping_outcome heads effects result).symm
  | evaluate body continuation =>
      rcases body with ⟨n, v, k, body, native, values, needs⟩
      cases body <;>
        simp only [state, captured, code, PolarizedNeedMachine.action,
          NeedRepresentation.Mapping.mapAction, mapping_outcome, capture_value,
          ← Tm.mapHead_subst, primitives]
      all_goals first
        | rfl
        | (rw [← finish_outcome heads effects]; rfl)
        | (rw [lift_outcome heads effects, finish_outcome])

theorem compatible (heads : H → H') (effects : E → E')
    (source : O → Tm H m → Produced (Tm H m) F N)
    (target : O → Tm H' m → Produced (Tm H' m) F N)
    (primitives : ∀ operation argument, target operation (argument.mapHead heads) =
      nativeOutcome heads (source operation argument)) :
    NeedRepresentation.Compatible (mapping heads effects) (reference source) (reference target) where
  alternatives := alternatives_captured heads effects
  action := action_state heads effects source target primitives
  afterDemand := by
    intro consumer result
    change afterDemand (resume heads effects consumer) ((mapping heads effects).mapOutcome result) = _
    rw [mapping_outcome]
    exact after_demand heads effects consumer result
  afterAllocation := after_allocation heads effects

theorem local_step (heads : H → H') (effects : E → E')
    (current : Local H O E F N m) :
    localStep (state heads effects current) = (localStep current).map (state heads effects) := by
  cases current with
  | demand cell consumer => rfl
  | complete result => rfl
  | evaluate body continuation =>
      rcases body with ⟨n, v, k, body, native, values, needs⟩
      cases body with
      | nativeLambda body =>
          cases continuation with
          | nativeApply argument rest =>
              change some (.evaluate
                (NativeBody.open (captured heads effects ⟨n, v, k, body, native, values, needs⟩)
                  (argument.mapHead heads)) (kont heads effects rest)) =
                some (state heads effects (.evaluate
                  (NativeBody.open ⟨n, v, k, body, native, values, needs⟩ argument) rest))
              rw [captured_native_open]
              rfl
          | done => rfl
          | pair first rest => rfl
          | valueApply argument rest => rfl
      | valueLambda body =>
          cases continuation with
          | valueApply argument rest =>
              change some (.evaluate
                (ValueBody.open (captured heads effects ⟨n, v, k, body, native, values, needs⟩)
                  (runtimeValue heads effects argument)) (kont heads effects rest)) =
                some (state heads effects (.evaluate
                  (ValueBody.open ⟨n, v, k, body, native, values, needs⟩ argument) rest))
              rw [captured_value_open]
              rfl
          | done => rfl
          | pair first rest => rfl
          | nativeApply argument rest => rfl
      | forceThunk inner =>
          simp only [state, captured, code, localStep, capture_value]
          cases captureValue native values needs inner <;> rfl
      | unpackNative inner body =>
          simp only [state, captured, code, localStep, capture_value]
          cases found : captureValue native values needs inner with
          | native term => rfl
          | thunk body native values needs => rfl
          | packNative index inner =>
              change some (.evaluate
                (PairBody.open (captured heads effects ⟨n, v, k, body, native, values, needs⟩)
                  (index.mapHead heads) (runtimeValue heads effects inner)) (kont heads effects continuation)) =
                some (state heads effects (.evaluate
                  (PairBody.open ⟨n, v, k, body, native, values, needs⟩ index inner) continuation))
              rw [captured_pair_open]
              rfl
      | nativeApply function argument =>
          simp only [state, captured, code, localStep, ← Tm.mapHead_subst, Option.map_some, kont]
      | valueApply function argument =>
          simp only [state, captured, code, localStep, capture_value, Option.map_some, kont]
      | returnValue inner => rfl
      | bindNative first body => rfl
      | bindValue first body => rfl
      | sequenceSigma first body => rfl
      | choose left right => rfl
      | call operation argument => rfl
      | emit effect next => rfl
      | letNeed suspended body => rfl
      | forceNeed reference => rfl

/-- Exact successor transport preserves every ordered alternative and the
actual mapped heap, receipts, owner identities and work account. -/
theorem step_map (heads : H → H') (effects : E → E')
    (source : O → Tm H m → Produced (Tm H m) F N)
    (target : O → Tm H' m → Produced (Tm H' m) F N)
    (primitives : ∀ operation argument, target operation (argument.mapHead heads) =
      nativeOutcome heads (source operation argument))
    (machine : NeedMachine H O E F N m) :
    (NeedLocalSteps.step (extension source) machine).map (mapping heads effects).mapMachine =
      NeedLocalSteps.step (extension target) ((mapping heads effects).mapMachine machine) :=
  NeedRepresentation.local_step_map _ _ _ (compatible heads effects source target primitives)
    (local_step heads effects) machine

theorem replay_map (heads : H → H') (effects : E → E')
    (source : O → Tm H m → Produced (Tm H m) F N)
    (target : O → Tm H' m → Produced (Tm H' m) F N)
    (primitives : ∀ operation argument, target operation (argument.mapHead heads) =
      nativeOutcome heads (source operation argument))
    (initial : NeedMachine H O E F N m) (trace : List Nat) :
    (NeedLocalSteps.pathMachine (extension target) ((mapping heads effects).mapMachine initial)).follow
      ((mapping heads effects).mapMachine initial) trace =
    ((NeedLocalSteps.pathMachine (extension source) initial).follow initial trace).map
      (mapping heads effects).mapMachine :=
  Mettapedia.GSLT.Causality.OccurrenceMachineHistory.follow_map _ _ _
    (fun machine => (step_map heads effects source target primitives machine).symm) initial trace

/-- An execution of an instantiated closure and heap has an original
execution at precisely the same successor positions. No endpoint is invented. -/
theorem replay_reflects (heads : H → H') (effects : E → E')
    (source : O → Tm H m → Produced (Tm H m) F N)
    (target : O → Tm H' m → Produced (Tm H' m) F N)
    (primitives : ∀ operation argument, target operation (argument.mapHead heads) =
      nativeOutcome heads (source operation argument))
    (initial : NeedMachine H O E F N m) (trace : List Nat)
    (endpoint : NeedMachine H' O E' F N m)
    (ran : (NeedLocalSteps.pathMachine (extension target) ((mapping heads effects).mapMachine initial)).follow
      ((mapping heads effects).mapMachine initial) trace = some endpoint) :
    ∃ original, (NeedLocalSteps.pathMachine (extension source) initial).follow initial trace = some original ∧
      (mapping heads effects).mapMachine original = endpoint :=
  Mettapedia.GSLT.Causality.OccurrenceMachineHistory.replay_reflects _ _ _
    (fun machine => (step_map heads effects source target primitives machine).symm) ran

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.PolarizedNeedParameterMap
