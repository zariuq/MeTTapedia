import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolUnaryInvariant

/-!
# Inversion of the actual private tuple communications

The callback and field phases are real processes of the shared presentation.
Every raw firing from the displayed phase has its specified actual endpoint.
The scope and parallel equations then identify that endpoint with the next
displayed phase. The distinction between raw firing inversion and inversion
through arbitrary structural representatives is retained explicitly.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes

/-- No active firing occurs inside a guarded receiver or an asynchronous
output; their continuation remains suspended. -/
theorem input_no_raw_step {Γ : Ctx sig} (channel : Name Γ)
    (body : Proc (.nm :: Γ)) {target : Proc Γ} :
    ¬ Step (inp1 channel body) target := by intro step; cases step

theorem output_no_raw_step {Γ : Ctx sig} (channel datum : Name Γ)
    {target : Proc Γ} : ¬ Step (out1 channel datum) target := by intro step; cases step

def callbackContractum {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Proc Γ :=
  nu (nu (par
    (par (out1 (.var .zero) (weaken (weaken first)))
      (out1 (.var (.succ .zero)) (weaken (weaken second))))
    (receiveFields body)))

def firstFieldContractum {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Proc Γ :=
  nu (nu (par
    (inp1 (.var (.succ .zero)) (secondBody first body))
    (out1 (.var (.succ .zero)) (weaken (weaken second)))))

/-- Extruding the sender's private scope exposes the real public rendezvous.
This representative is obtained from the actual separately scoped invocation. -/
def rendezvousState {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Proc Γ :=
  nu (par
    (par (out1 (weaken channel) (.var .zero)) (weaken (receivePair channel body)))
    (sendFields first second))

def rendezvousContractum {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Proc Γ :=
  nu (par
    (nu (par (out1 (.var (.succ .zero)) (.var .zero)) (receiveFields body)))
    (sendFields first second))

private theorem parallel_exchange {Γ : Ctx sig} (p q r : Proc Γ) :
    StructuralEq (par (par p q) r) (par (par p r) q) :=
  .trans (.parAssoc _ _ _)
    (.trans (.par (.refl _) (.parComm _ _)) (.symm (.parAssoc _ _ _)))

theorem invocation_rendezvous_representative {Γ : Ctx sig}
    (channel first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
    StructuralEq (invocation channel first second body)
      (rendezvousState channel first second body) :=
  .trans (.nuPar _ _) (.nu (parallel_exchange _ _ _))

/-- The public rendezvous retains the selected session's sender continuation.
The actual endpoint contains no fields taken from an independently chosen call. -/
theorem rendezvousState_raw_endpoint_iff {Γ : Ctx sig}
    (channel first second : Name Γ) (body : Proc (.nm :: .nm :: Γ))
    (endpoint : Proc Γ) :
    Step (rendezvousState channel first second body) endpoint ↔
      endpoint = rendezvousContractum first second body := by
  let receiverBody : Proc (.nm :: Γ) :=
    nu (par (out1 (.var (.succ .zero)) (.var .zero)) (receiveFields body))
  constructor
  · intro step
    cases step with
    | nu outer => cases outer with
      | parL _ firing =>
          have supplied := (unary_communication_iff (weaken channel) (.var .zero)
            (rename (liftRen (fun (s : Srt) (x : Var Γ s) => .succ x) [.nm]) receiverBody) _).1 firing
          rw [inst_liftRen_succ_var] at supplied
          cases supplied
          rfl
      | parR _ impossible => exact False.elim (input_no_raw_step _ _ impossible)
  · rintro rfl
    apply Step.nu
    apply Step.parL
    have firing := Step.comm1 (weaken channel) (.var .zero)
      (rename (liftRen (fun (s : Srt) (x : Var Γ s) => .succ x) [.nm]) receiverBody)
    rw [inst_liftRen_succ_var] at firing
    exact firing

theorem rendezvous_actual_endpoint {Γ : Ctx sig}
    (channel first second : Name Γ) (body : Proc (.nm :: .nm :: Γ))
    {endpoint : Proc Γ} (step : Step (rendezvousState channel first second body) endpoint) :
    StructuralEq endpoint (callbackState first second body) := by
  rw [(rendezvousState_raw_endpoint_iff channel first second body endpoint).1 step]
  exact .nu (.trans (.nuPar _ _) (.nu (parallel_exchange _ _ _)))

/-- Both payloads are released by the callback selected for this session.
There is no competing raw transition into the still-guarded receiver. -/
theorem callbackState_raw_endpoint_iff {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) (endpoint : Proc Γ) :
    Step (callbackState first second body) endpoint ↔
      endpoint = callbackContractum first second body := by
  constructor
  · intro step
    cases step with
    | nu outer => cases outer with
      | nu inner => cases inner with
        | parL _ firing =>
          have supplied := (unary_communication_iff (.var (.succ .zero)) (.var .zero)
            (rename (liftRen (fun (s : Srt) (x : Var (.nm :: Γ) s) => .succ x) [.nm])
              (par (out1 (.var .zero) (weaken (weaken first)))
                (out1 (.var (.succ .zero)) (weaken (weaken second))))) _).1 firing
          rw [sender_callback_endpoint] at supplied
          cases supplied
          rfl
        | parR _ impossible => exact False.elim (input_no_raw_step _ _ impossible)
  · rintro rfl
    apply Step.nu
    apply Step.nu
    apply Step.parL
    have firing := Step.comm1 (.var (.succ .zero)) (.var .zero)
      (rename (liftRen (fun (s : Srt) (x : Var (.nm :: Γ) s) => .succ x) [.nm])
        (par (out1 (.var .zero) (weaken (weaken first)))
          (out1 (.var (.succ .zero)) (weaken (weaken second)))))
    rw [sender_callback_endpoint] at firing
    exact firing

/-- The first payload is the only raw firing at the fields phase. The second
payload cannot bypass its input guard, nor pair with a different callback. -/
theorem fieldsState_raw_endpoint_iff {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) (endpoint : Proc Γ) :
    Step (fieldsState first second body) endpoint ↔
      endpoint = firstFieldContractum first second body := by
  constructor
  · intro step
    cases step with
    | nu outer => cases outer with
      | nu inner => cases inner with
        | parL _ firing =>
          have supplied := (unary_communication_iff (.var .zero) (weaken (weaken first))
            (inp1 (.var (.succ (.succ .zero))) (rename receiveBodyRen body)) _).1 firing
          rw [first_field_endpoint] at supplied
          cases supplied
          rfl
        | parR _ impossible => exact False.elim (output_no_raw_step _ _ impossible)
  · rintro rfl
    exact .nu (.nu (.parL _ (.comm1 _ _ _)))

/-- The endpoint of an actual callback firing differs from the next displayed
phase only by the already authored parallel equation. -/
theorem callback_actual_endpoint {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) {endpoint : Proc Γ}
    (step : Step (callbackState first second body) endpoint) :
    StructuralEq endpoint (fieldsState first second body) := by
  rw [(callbackState_raw_endpoint_iff first second body endpoint).1 step]
  exact .nu (.nu (parallel_exchange _ _ _))

theorem first_field_actual_endpoint {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) {endpoint : Proc Γ}
    (step : Step (fieldsState first second body) endpoint) :
    StructuralEq endpoint (secondState first second body) := by
  rw [(fieldsState_raw_endpoint_iff first second body endpoint).1 step]
  exact .nu (.nu (.parComm _ _))

/-- The original selected fields determine every actual final-phase endpoint;
erasing its two unused private scopes returns the source binary contractum. -/
theorem second_field_actual_endpoint {Γ : Ctx sig} (first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) {endpoint : Proc Γ}
    (step : Step (secondState first second body) endpoint) :
    StructuralEq endpoint (openPair body first second) := by
  rw [(secondState_endpoint_iff first second body endpoint).1 step]
  exact .trans (.nu (.nuUnused _)) (.nuUnused _)

/-- A supplied last-phase firing reads back to the real source binary COMM
and relates its supplied target endpoint, rather than selecting another run. -/
theorem final_phase_binary_reflection {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) {endpoint : Proc Γ}
    (step : Step (secondState first second (lower body)) endpoint) :
    Step (par (out2 channel first second) (inp2 channel body))
      (openPair body first second) ∧
      StructuralEq endpoint (lower (openPair body first second)) := by
  refine ⟨.comm2 _ _ _ _, ?_⟩
  rw [lower_openPair]
  exact second_field_actual_endpoint first second (lower body) step

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol
