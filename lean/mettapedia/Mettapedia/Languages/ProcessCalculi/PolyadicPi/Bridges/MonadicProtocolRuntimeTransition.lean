import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeOpening
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimePublicSelection
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimePrivateTransition
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeIdleTransition
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimePublicTransition

/-!
# Readback of every supplied tuple-protocol firing

An actual equation-saturated unary firing is opened with its original marked
occurrences. Its selected output is either a private committed instruction,
an offered publication, or an ordinary source message. The original source
role judgment determines the public receiver's arity. Each case reconstructs
the supplied target, retaining every other occurrence and activating a source
guard only after its actual final receipt.

Private administration spends one debt unit. Ordinary source communication
preserves debt; a binary public commitment advances its original source
communication immediately and leaves exactly three private receipts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeTransition

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors RuntimeWitness ScopedActiveFrontier
open ActiveMarking ActiveGuardedBodies ActiveHeaderInvariant ScopedCommunicationInversion NamePassingChannelRoles

private theorem output_header_cases {Label : Type} {Γ Ω : Ctx sig} {redex reduct : Proc Γ}
    {selected : Communication redex reduct} {marked : ActiveMarking.Tree Label}
    (communication : MarkedCommunication selected marked) (reindex : Ren sig Γ Ω) :
    (outputObservation communication reindex).header.header = Header.output1 ∨
      (outputObservation communication reindex).header.header = Header.output2 := by
  cases communication <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem private_receipt {Γ : Ctx sig} {source current after : Proc Γ}
    (before : Witness source current) {returned : Proc (World before.n before.world)}
    {actual : Exposure (assembly before.registry (parallel before.frame)) returned}
    (traced : TracedExposure (assemblyMarks before.registry before.frame) actual)
    (owner : Fin before.n) (call : Call before.world) (kind : OutputKind)
    (field : outputObservation traced.continuation
      (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion before.n)) =
      Actor.observation (.output owner kind (loweredCall call)))
    (closed : StructuralEq after (before.scope.close ((privateScope before.n).close returned))) :
    ∃ next : Witness source after, next.debt + 1 = before.debt := by
  have owned : (outputObservation traced.continuation
      (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion before.n))).header.channel =
      Var.succ (key before.n owner kind.port) := by
    rw [field]
    rfl
  obtain ⟨selected, selectedPhase, originalCall, committed, endpoint⟩ :=
    RuntimePrivateUpdate.actual_private_update before.registry before.frame before.live traced owner kind.port owned
  exact RuntimePrivateTransition.updated before selected selectedPhase originalCall committed
    (closed.trans (before.scope.congr ((privateScope before.n).congr endpoint)))

theorem public_receipt {Γ : Ctx sig} {source current after : Proc Γ}
    (before : Witness source current) {returned : Proc (World before.n before.world)}
    (actual : Exposure (assembly before.registry (parallel before.frame)) returned)
    (traced : TracedExposure (assemblyMarks before.registry before.frame) actual)
    (owner : Fin before.n) (channel first second : Name before.world)
    (offered : before.registry owner = .offered channel first second)
    (field : outputObservation traced.continuation
      (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion before.n)) =
      Actor.observation (.publication owner channel))
    (closed : StructuralEq after (before.scope.close ((privateScope before.n).close returned))) :
    ∃ sourceAfter : Proc Γ, StepModulo source sourceAfter ∧
      ∃ next : Witness sourceAfter after, next.debt = before.debt + 3 := by
  obtain ⟨slots, framed⟩ := (EntryRoles.registry_source_typing_iff before.roles before.registry
    (parallel before.frame)).mp before.typed
  have frames := (EntryRoles.parallel_typing_iff before.roles before.frame).mp framed
  have outputTyped := slots owner
  rw [offered, Slot.source] at outputTyped
  cases channel with
  | op op _ => cases op
  | var channel =>
    cases first with
    | op op _ => cases op
    | var first =>
      cases second with
      | op op _ => cases op
      | var second =>
        obtain ⟨input, body, _, inputShape, _, chosenInput, chosenOutput⟩ :=
          RuntimePublicSelection.traced_public_receiver before.registry before.frame before.heads
            before.roles frames owner channel first second outputTyped traced field
        obtain ⟨persistent, original⟩ : ∃ persistent : Bool,
            before.frame[input.val] = RuntimePublicUpdate.binaryReceiver persistent (.var channel) body := by
          rcases inputShape with ordinary | server
          · exact ⟨false, ordinary⟩
          · exact ⟨true, server⟩
        have unary := RuntimePublicSelection.traced_unary before.registry before.frame before.heads traced
        obtain ⟨step, next, debt⟩ := RuntimePublicTransition.receipt_updated before owner channel first second
          offered input persistent body original actual traced unary chosenInput chosenOutput closed
        exact ⟨_, step, next, debt⟩

theorem ordinary_receipt {Γ : Ctx sig} {source current after : Proc Γ}
    (before : Witness source current) {returned : Proc (World before.n before.world)}
    (actual : Exposure (assembly before.registry (parallel before.frame)) returned)
    (traced : TracedExposure (assemblyMarks before.registry before.frame) actual)
    (output : Fin before.frame.length) (channel datum : Name before.world)
    (originalOutput : before.frame[output.val] = out1 channel datum)
    (field : outputObservation traced.continuation
      (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion before.n)) =
      output1 (.idle output.val) channel datum (RuntimePublicSelection.environment before.n))
    (closed : StructuralEq after (before.scope.close ((privateScope before.n).close returned))) :
    ∃ sourceAfter : Proc Γ, StepModulo source sourceAfter ∧
      ∃ next : Witness sourceAfter after, next.debt = before.debt := by
  obtain ⟨_, framed⟩ := (EntryRoles.registry_source_typing_iff before.roles before.registry
    (parallel before.frame)).mp before.typed
  have frames := (EntryRoles.parallel_typing_iff before.roles before.frame).mp framed
  have outputTyped := frames _ (List.getElem_mem output.isLt)
  rw [originalOutput] at outputTyped
  cases channel with
  | op op _ => cases op
  | var channel =>
    cases datum with
    | op op _ => cases op
    | var datum =>
      obtain ⟨input, body, _, inputShape, _, chosenInput, chosenOutput⟩ :=
        RuntimePublicSelection.traced_unary_receiver before.registry before.frame before.heads
          before.roles frames output channel datum outputTyped traced field
      obtain ⟨persistent, originalInput⟩ : ∃ persistent : Bool,
          before.frame[input.val] = ActiveUnarySelectedBoundary.receiver persistent (.var channel) body := by
        rcases inputShape with ordinary | server
        · exact ⟨false, ordinary⟩
        · exact ⟨true, server⟩
      have different : input ≠ output := by
        intro same
        rw [same, originalOutput] at originalInput
        cases persistent <;> cases originalInput
      have unary := RuntimePublicSelection.traced_unary before.registry before.frame before.heads traced
      obtain ⟨step, next, debt⟩ := RuntimeIdleTransition.receipt_updated before output input different
        persistent channel datum body originalOutput originalInput actual traced unary chosenInput chosenOutput closed
      exact ⟨_, step, next, debt⟩

/-- Every actual target step retains its supplied endpoint in the next
witness. It either spends one private receipt or performs one real source
communication, with at most three newly owed private receipts. -/
theorem readStep {Γ : Ctx sig} {source current after : Proc Γ}
    (before : Witness source current) (firing : StepModulo current after) :
    (∃ next : Witness source after, next.debt + 1 = before.debt) ∨
      (∃ sourceAfter : Proc Γ, StepModulo source sourceAfter ∧
        ∃ next : Witness sourceAfter after, next.debt + 1 ≤ before.debt + 4) := by
  obtain ⟨returned, actual, traced, closed⟩ := RuntimeOpening.expose before firing
  let observed := outputObservation traced.continuation
    (scopeEnvironment (fun _ : Origin before.n => Var.zero) traced.binders (StructuralOwnership.inclusion before.n))
  have classified := RuntimePublicSelection.output_classification before.registry before.frame before.heads observed
    (traced_output_observed (fun _ => Var.zero) traced (StructuralOwnership.inclusion before.n))
    (output_header_cases traced.continuation _)
  rcases classified with committed | published | ordinary
  · obtain ⟨owner, _, call, kind, _, _, field⟩ := committed
    exact Or.inl (private_receipt before traced owner call kind field closed)
  · obtain ⟨owner, channel, first, second, offered, field⟩ := published
    obtain ⟨sourceAfter, step, next, debt⟩ := public_receipt before actual traced owner channel first second
      offered field closed
    exact Or.inr ⟨sourceAfter, step, next, by omega⟩
  · obtain ⟨output, channel, datum, original, field⟩ := ordinary
    obtain ⟨sourceAfter, step, next, debt⟩ := ordinary_receipt before actual traced output channel datum
      original field closed
    exact Or.inr ⟨sourceAfter, step, next, by omega⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeTransition
