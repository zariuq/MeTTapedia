import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalContinuation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedMachineRunSegments
import Mettapedia.Machines.OccurrenceObservation

/-!
# Primitive invocation observations and independent source event folds

Existing receipt payloads do not record a primitive's evaluated argument.
This separate observation records a call when its actual input control is
stepped. Source event lists are folded independently over existing natural
derivations; no machine path appears in that definition.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.PolarizedNeedInvocation

open Mettapedia.Machines.BranchLocalNeed NeedReference PolarizedNeedMachine
open PolarizedNeedNaturalSemantics

inductive Event (Head Operation Effect : Type) (m : Nat) where
  | invoke (operation : Operation) (argument : Tm Head m)
  | emitted (effect : Effect)
  deriving Repr, DecidableEq

variable {H O E F N : Type} {m : Nat}

def atControl : NeedControl H O E F N m → List (Event H O E m)
  | .run (.evaluate ⟨_, _, _, .call operation argument, native, _, _⟩ _) _ =>
      [.invoke operation (subst native argument)]
  | .run (.evaluate ⟨_, _, _, .emit effect _, _, _, _⟩ _) _ => [.emitted effect]
  | _ => []

def atState (state : NeedMachine H O E F N m) := atControl state.control

mutual
  def evalEvents {primitive : O → Tm H m → Produced (Tm H m) F N}
      {closure : Closure H O E m} {world final : NeedWorld H O E F N m}
      {outcome : Outcome H O E F N m}
      (derivation : Eval primitive closure world outcome final) : List (Event H O E m) :=
    match derivation with
    | .call operation argument native _ _ _ => [.invoke operation (subst native argument)]
    | .emit effect body => .emitted effect :: evalEvents body
    | .forceNeed _ forced => forceEvents forced
    | .nativeApply _ function body => evalEvents function ++ evalEvents body
    | .nativeApplyMismatch _ function _ => evalEvents function
    | .nativeApplyFault _ function _ => evalEvents function
    | .valueApply _ function body => evalEvents function ++ evalEvents body
    | .valueApplyMismatch _ function _ => evalEvents function
    | .valueApplyFault _ function _ => evalEvents function
    | .forceThunk _ _ body => evalEvents body
    | .unpackNative _ _ body => evalEvents body
    | .bindNativeValue _ forced body => forceEvents forced ++ evalEvents body
    | .bindNativeMismatch _ _ forced _ => forceEvents forced
    | .bindNativeFault _ _ forced _ => forceEvents forced
    | .bindValueValue _ forced body => forceEvents forced ++ evalEvents body
    | .bindValueMismatch _ _ forced _ => forceEvents forced
    | .bindValueFault _ _ forced _ => forceEvents forced
    | .sequenceSigmaValue _ forced body => forceEvents forced ++ evalEvents body
    | .sequenceSigmaMismatch _ _ forced _ => forceEvents forced
    | .sequenceSigmaFault _ _ forced _ => forceEvents forced
    | .choose _ _ _ forced => forceEvents forced
    | .letNeed _ body => evalEvents body
    | _ => []
  termination_by structural derivation

  def forceEvents {primitive : O → Tm H m → Produced (Tm H m) F N}
      {cell : CellId} {world final : NeedWorld H O E F N m} {outcome : Outcome H O E F N m}
      (derivation : Force primitive cell world outcome final) : List (Event H O E m) :=
    match derivation with
    | .suspended _ _ body => evalEvents body
    | _ => []
  termination_by structural derivation
end

def kontEvents {primitive : O → Tm H m → Produced (Tm H m) F N}
    {kont : Kont H O E m} {input outcome : Outcome H O E F N m}
    {world final : NeedWorld H O E F N m}
    (derivation : KontEval primitive kont input world outcome final) : List (Event H O E m) :=
  match derivation with
  | .pairNative _ _ rest => kontEvents rest
  | .nativeApply _ _ body rest => evalEvents body ++ kontEvents rest
  | .valueApply _ _ body rest => evalEvents body ++ kontEvents rest
  | _ => []

theorem returned_events {primitive : O → Tm H m → Produced (Tm H m) F N}
    {kont : Kont H O E m} {value : RuntimeValue H O E m} {outcome : Outcome H O E F N m}
    {world final : NeedWorld H O E F N m}
    (derivation : KontEval primitive kont (.value (.returned value)) world outcome final) :
    kontEvents derivation = [] := by
  induction kont generalizing value with
  | done => cases derivation; rfl
  | pair first rest ih =>
      cases derivation with
      | pairNative first second rest => exact ih rest
      | pairMismatch first rest answer world wrong => rfl
  | nativeApply argument rest ih => cases derivation; rfl
  | valueApply argument rest ih => cases derivation; rfl

theorem stable_events {primitive : O → Tm H m → Produced (Tm H m) F N}
    {kont : Kont H O E m} {fault : F} {outcome : Outcome H O E F N m}
    {world final : NeedWorld H O E F N m}
    (derivation : KontEval primitive kont (.stableFault fault) world outcome final) :
    kontEvents derivation = [] := by cases derivation <;> rfl

theorem retry_events {primitive : O → Tm H m → Produced (Tm H m) F N}
    {kont : Kont H O E m} {reason : RetryReason (Fault N)} {outcome : Outcome H O E F N m}
    {world final : NeedWorld H O E F N m}
    (derivation : KontEval primitive kont (.retryableFault reason) world outcome final) :
    kontEvents derivation = [] := by cases derivation <;> rfl

theorem fault_events {primitive : O → Tm H m → Produced (Tm H m) F N}
    {kont : Kont H O E m} {input outcome : Outcome H O E F N m}
    {world final : NeedWorld H O E F N m}
    (derivation : KontEval primitive kont input world outcome final) (fault : FaultOutcome input) :
    kontEvents derivation = [] := by
  cases fault with
  | stableFault fault => exact stable_events derivation
  | retryableFault reason => exact retry_events derivation

theorem native_result_consumer {primitive : O → Tm H m → Produced (Tm H m) F N}
    (result : Produced (Tm H m) F N) {kont : Kont H O E m} {outcome : Outcome H O E F N m}
    {world final : NeedWorld H O E F N m}
    (derivation : KontEval primitive kont (liftOutcome result) world outcome final) :
    outcome = finish (liftOutcome result) kont ∧ final = world ∧ kontEvents derivation = [] := by
  cases result with
  | value value => exact ⟨derivation.returned_exact.1, derivation.returned_exact.2, returned_events derivation⟩
  | stableFault fault =>
      refine ⟨?_, derivation.stable_exact.2, stable_events derivation⟩
      rw [derivation.stable_exact.1]
      cases kont <;> rfl
  | retryableFault reason =>
      refine ⟨?_, derivation.retry_exact.2, retry_events derivation⟩
      rw [derivation.retry_exact.1]
      cases kont <;> rfl

theorem pair_non_native_events {primitive : O → Tm H m → Produced (Tm H m) F N}
    {first : Tm H m} {rest : Kont H O E m} {input outcome : Outcome H O E F N m}
    {world final : NeedWorld H O E F N m}
    (wrong : ∀ term, input ≠ .value (.returned (.native term)))
    (derivation : KontEval primitive (.pair first rest) input world outcome final) :
    kontEvents derivation = [] := by
  cases derivation with
  | pairNative first second rest => exact False.elim (wrong second rfl)
  | pairMismatch first rest answer world wrong => rfl
  | stableFault kont fault world => rfl
  | retryableFault kont reason world => rfl

theorem pair_input_events {primitive : O → Tm H m → Produced (Tm H m) F N}
    {kont : Kont H O E m} {input outcome : Outcome H O E F N m}
    {world final : NeedWorld H O E F N m} (first : Tm H m)
    (derivation : KontEval primitive kont (pairOutcome first input) world outcome final) :
    kontEvents (KontEval.pair_input first derivation).val = kontEvents derivation := by
  cases input with
  | value answer =>
      cases answer with
      | returned value =>
          cases value with
          | native second => rfl
          | thunk code native values needs =>
              exact (pair_non_native_events (by intro term impossible; cases impossible) _).trans
                (retry_events derivation).symm
          | packNative index payload =>
              exact (pair_non_native_events (by intro term impossible; cases impossible) _).trans
                (retry_events derivation).symm
      | nativeFunction body =>
          exact (pair_non_native_events (by intro term impossible; cases impossible) _).trans
            (retry_events derivation).symm
      | valueFunction body =>
          exact (pair_non_native_events (by intro term impossible; cases impossible) _).trans
            (retry_events derivation).symm
  | stableFault fault => exact (stable_events _).trans (stable_events derivation).symm
  | retryableFault reason => exact (retry_events _).trans (retry_events derivation).symm

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.PolarizedNeedInvocation
