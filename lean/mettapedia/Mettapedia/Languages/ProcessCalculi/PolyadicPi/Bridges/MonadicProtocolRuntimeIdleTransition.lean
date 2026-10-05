import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeActivation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeIdleUpdate

/-!
# Reconstructing a mixed runtime after a selected ordinary communication

The source step opens the original unary guard with the original datum.
Only that activated body is normalized; the exact residual idle occurrences,
retained servers and all pending tuple owners pass through the activation
equations. The supplied target stays fixed and no private debt is spent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeIdleTransition

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors RuntimeWitness ScopedActiveFrontier NamePassingChannelRoles
open ActiveMarking ActiveHeaderInvariant ScopedCommunicationInversion ActiveUnarySelectedBoundary

theorem scope_step {Γ Δ : Ctx sig} (scope : Scope Γ Δ) {source target : Proc Δ}
    (step : StepModulo source target) : StepModulo (scope.close source) (scope.close target) := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  exact ⟨scope.close redex, scope.close contractum, scope.congr before,
    scope.step firing, scope.congr after⟩

theorem selected_body_guarded {Γ : Ctx sig} (frame : List (Proc Γ))
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom) (input : Fin frame.length)
    (persistent : Bool) (channel : Var Γ .nm) (body : Proc (.nm :: Γ))
    (selected : frame[input.val] = receiver persistent (.var channel) body) : Guarded body := by
  have head := heads _ (List.getElem_mem input.isLt)
  rw [selected] at head
  cases persistent with
  | false => cases head with
    | input1 _ guarded => exact guarded
  | true => cases head with
    | server1 _ guarded => exact guarded

theorem residual_heads {Γ : Ctx sig} (frame : List (Proc Γ))
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom) (output input : Fin frame.length)
    (persistent : Bool) :
    ∀ atom ∈ RuntimeIdleUpdate.updatedFrame persistent frame output input, IdleFrame.Head atom := by
  cases persistent with
  | false => exact RuntimeIdleUpdate.remaining_heads frame output input heads
  | true =>
      intro atom member
      rcases List.mem_cons.mp member with same | kept
      · subst atom; exact heads _ (List.getElem_mem input.isLt)
      · exact RuntimeIdleUpdate.remaining_heads frame output input heads atom kept

def sourceAfter {Γ : Ctx sig} {source current : Proc Γ} (before : Witness source current)
    (output input : Fin before.frame.length) (persistent : Bool)
    (body : Proc (.nm :: before.world)) (datum : Var before.world .nm) : Proc Γ :=
  before.scope.close (par
    (registrySource before.registry (parallel (RuntimeIdleUpdate.updatedFrame persistent before.frame output input)))
    (inst body (.var datum)))

theorem source_updated_step {Γ : Ctx sig} {source current : Proc Γ} (before : Witness source current)
    (output input : Fin before.frame.length) (different : input ≠ output)
    (persistent : Bool) (channel datum : Var before.world .nm) (body : Proc (.nm :: before.world))
    (originalOutput : before.frame[output.val] = out1 (.var channel) (.var datum))
    (originalInput : before.frame[input.val] = receiver persistent (.var channel) body) :
    StepModulo source (sourceAfter before output input persistent body datum) := by
  have step := RuntimeIdleUpdate.source_registry_step before.registry before.frame output input different
    persistent channel datum body originalOutput originalInput
  have ordered := modulo_target_equation step (StructuralEq.parComm _ _)
  exact modulo_source_equation before.source (scope_step before.scope ordered)

/-- The endpoint comparison is supplied by the independent firing inversion.
This theorem rebuilds the original source-derived witness at that endpoint. -/
theorem updated {Γ : Ctx sig} {source current after : Proc Γ} (before : Witness source current)
    (output input : Fin before.frame.length) (different : input ≠ output)
    (persistent : Bool) (channel datum : Var before.world .nm) (body : Proc (.nm :: before.world))
    (originalOutput : before.frame[output.val] = out1 (.var channel) (.var datum))
    (originalInput : before.frame[input.val] = receiver persistent (.var channel) body)
    (supplied : StructuralEq after (before.scope.close ((privateScope before.n).close
      (par (rename (ambient before.n) (lower (inst body (.var datum))))
        (registryTarget before.registry
          (parallel (RuntimeIdleUpdate.updatedFrame persistent before.frame output input))))))) :
    StepModulo source (sourceAfter before output input persistent body datum) ∧
      ∃ witness : Witness (sourceAfter before output input persistent body datum) after,
        witness.debt = before.debt := by
  let kept := RuntimeIdleUpdate.updatedFrame persistent before.frame output input
  let activated := inst body (.var datum)
  have original := RuntimeIdleUpdate.source_registry_step before.registry before.frame output input different
    persistent channel datum body originalOutput originalInput
  have ordered := modulo_target_equation original (StructuralEq.parComm _ _)
  have typed := before.typed.modulo_step ordered
  have guarded := (selected_body_guarded before.frame before.heads input persistent channel body originalInput).inst (.var datum)
  have outside := (privateScope before.n).par_right (registryTarget before.registry (parallel kept)) (lower activated)
  rw [privateScope_inclusion] at outside
  have targetEqual := supplied.trans (before.scope.congr
    (outside.symm.trans (StructuralEq.parComm _ _)))
  obtain ⟨witness, counted⟩ := RuntimeActivation.activated before.scope before.registry kept
    (residual_heads before.frame before.heads output input persistent) before.live before.guards
    before.roles activated guarded typed (StructuralEq.refl _) targetEqual
  exact ⟨source_updated_step before output input different persistent channel datum body originalOutput originalInput,
    witness, counted⟩

/-- The exact supplied trace and endpoint from an opened idle firing suffice
for the complete source step, witness reconstruction and unchanged-debt law. -/
theorem receipt_updated {Γ : Ctx sig} {source current after : Proc Γ} (before : Witness source current)
    (output input : Fin before.frame.length) (different : input ≠ output)
    (persistent : Bool) (channel datum : Var before.world .nm) (body : Proc (.nm :: before.world))
    (originalOutput : before.frame[output.val] = out1 (.var channel) (.var datum))
    (originalInput : before.frame[input.val] = receiver persistent (.var channel) body)
    {openedTarget : Proc (World before.n before.world)}
    (actual : Exposure (assembly before.registry (parallel before.frame)) openedTarget)
    (traced : TracedExposure (assemblyMarks before.registry before.frame) actual)
    (unary : inputHeader actual.selected = .input1)
    (chosenInput : traced.continuation.inputOrigin = .idle input.val)
    (chosenOutput : traced.continuation.outputOrigin = .idle output.val)
    (closed : StructuralEq after (before.scope.close ((privateScope before.n).close openedTarget))) :
    StepModulo source (sourceAfter before output input persistent body datum) ∧
      ∃ witness : Witness (sourceAfter before output input persistent body datum) after,
        witness.debt = before.debt := by
  have endpoint := RuntimeIdleUpdate.supplied_idle_endpoint before.registry before.live before.frame before.heads
    output input different persistent channel datum body originalOutput originalInput actual traced unary chosenInput chosenOutput
  exact updated before output input different persistent channel datum body originalOutput originalInput
    (closed.trans (before.scope.congr ((privateScope before.n).congr endpoint)))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeIdleTransition
