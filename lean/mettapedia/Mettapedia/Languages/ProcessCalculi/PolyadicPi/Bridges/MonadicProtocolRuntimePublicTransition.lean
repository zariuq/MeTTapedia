import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeIdleTransition
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimePublicRegistry

/-!
# Reconstructing the witness at the actual public rendezvous

The independently selected source binary communication commits one offered
owner to its actual receiver guard. Pending bodies stay suspended, and the
original source scope, all other owners, and literal residual idle occurrences
remain in the witness. That selected owner gains three private receipts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePublicTransition

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors RuntimeWitness ScopedActiveFrontier NamePassingChannelRoles
open ActiveMarking ActiveHeaderInvariant ScopedCommunicationInversion RuntimePublicUpdate

theorem selected_body_guarded {Γ : Ctx sig} (frame : List (Proc Γ))
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom) (input : Fin frame.length)
    (persistent : Bool) (channel : Name Γ) (body : Proc (.nm :: .nm :: Γ))
    (selected : frame[input.val] = binaryReceiver persistent channel body) : Guarded body := by
  have head := heads _ (List.getElem_mem input.isLt)
  rw [selected] at head
  cases persistent with
  | false => cases head with
    | input2 _ guarded => exact guarded
  | true => cases head with
    | server2 _ guarded => exact guarded

theorem committed_live {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (live : ∀ owner, Live (registry owner)) (owner : Fin n) (call : Call Γ) :
    ∀ other, Live (commit registry owner call other) := by
  intro other
  by_cases same : other = owner
  · subst other
    rw [commit, Function.update_self]
    trivial
  · rw [commit, Function.update_of_ne same]
    exact live other

theorem committed_guards {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (guards : ∀ owner, SlotGuarded (registry owner)) (owner : Fin n) (call : Call Γ)
    (guarded : Guarded call.body) : ∀ other, SlotGuarded (commit registry owner call other) := by
  intro other
  by_cases same : other = owner
  · subst other
    rw [commit, Function.update_self]
    exact .pending .callback call guarded
  · rw [commit, Function.update_of_ne same]
    exact guards other

def sourceAfter {Γ : Ctx sig} {source current : Proc Γ} (before : Witness source current)
    (owner : Fin before.n) (call : Call before.world) (input : Fin before.frame.length)
    (persistent : Bool) : Proc Γ :=
  before.scope.close (registrySource (commit before.registry owner call)
    (parallel (updatedFrame persistent before.frame input)))

/-- The supplied endpoint is obtained independently by the real public
firing inversion. No pending continuation is activated during this update. -/
theorem updated {Γ : Ctx sig} {source current after : Proc Γ} (before : Witness source current)
    (owner : Fin before.n) (channel : Name before.world) (call : Call before.world)
    (offered : before.registry owner = .offered channel call.first call.second)
    (input : Fin before.frame.length) (persistent : Bool)
    (original : before.frame[input.val] = binaryReceiver persistent channel call.body)
    (supplied : StructuralEq after (before.scope.close ((privateScope before.n).close
      (registryTarget (commit before.registry owner call) (parallel (updatedFrame persistent before.frame input)))))) :
    StepModulo source (sourceAfter before owner call input persistent) ∧
      ∃ witness : Witness (sourceAfter before owner call input persistent) after,
        witness.debt = before.debt + 3 := by
  have step := RuntimePublicRegistry.source_commit before.registry owner channel call offered
    before.frame input persistent original
  have typed := before.typed.modulo_step step
  have guarded := selected_body_guarded before.frame before.heads input persistent channel call.body original
  let witness : Witness (sourceAfter before owner call input persistent) after :=
    ⟨before.world, before.scope, before.n, commit before.registry owner call,
      updatedFrame persistent before.frame input, updated_heads persistent before.frame input before.heads,
      committed_live before.registry before.live owner call,
      committed_guards before.registry before.guards owner call guarded,
      before.roles, typed, StructuralEq.refl _, supplied⟩
  exact ⟨modulo_source_equation before.source (RuntimeIdleTransition.scope_step before.scope step), witness,
    RuntimePublicRegistry.public_debt before.registry owner channel call offered⟩

/-- The given marked exposure recovers both the original publication owner
and original idle decoder; its actual closed endpoint determines the witness. -/
theorem receipt_updated {Γ : Ctx sig} {source current after : Proc Γ} (before : Witness source current)
    (owner : Fin before.n) (channel first second : Var before.world .nm)
    (offered : before.registry owner = .offered (.var channel) (.var first) (.var second))
    (input : Fin before.frame.length) (persistent : Bool) (body : Proc (.nm :: .nm :: before.world))
    (original : before.frame[input.val] = binaryReceiver persistent (.var channel) body)
    {openedTarget : Proc (World before.n before.world)}
    (actual : Exposure (assembly before.registry (parallel before.frame)) openedTarget)
    (traced : TracedExposure (assemblyMarks before.registry before.frame) actual)
    (unary : inputHeader actual.selected = .input1)
    (chosenInput : traced.continuation.inputOrigin = .idle input.val)
    (chosenOutput : traced.continuation.outputOrigin = .publication owner)
    (closed : StructuralEq after (before.scope.close ((privateScope before.n).close openedTarget))) :
    StepModulo source (sourceAfter before owner ⟨.var first, .var second, body⟩ input persistent) ∧
      ∃ witness : Witness (sourceAfter before owner ⟨.var first, .var second, body⟩ input persistent) after,
        witness.debt = before.debt + 3 := by
  have endpoint := supplied_public_update before.registry owner channel first second offered before.live
    before.frame before.heads input persistent body original actual traced unary chosenInput chosenOutput
  exact updated before owner (.var channel) ⟨.var first, .var second, body⟩ offered input persistent original
    (closed.trans (before.scope.congr endpoint))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePublicTransition
