import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolIdleFrame

/-!
# Public channel roles recover the source arity of lowered listeners

The existing idle-frame reading retains the original prefix, its ordered
binders and whether its provider is persistent. Injective transport of the
actual public subject identifies the source channel. Its independent source
typing then distinguishes unary reference lookup from binary invocation even
though both lowered listeners have unary target headers.

These are source-prefix compatibility results. They do not assume or provide
an arbitrary-target operational reflection theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.PublicRoles

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingChannelRoles

/-- The decoder body retains the original binary receiver's body and field
order. Its two private transport names are introduced beneath the public
listener, rather than becoming source arguments. -/
def decoderBody {Γ : Ctx sig} (body : Proc (.nm :: .nm :: Γ)) : Proc (.nm :: Γ) :=
  nu (par (out1 (.var (.succ .zero)) (.var .zero)) (receiveFields (lower body)))

/-- A lowered listener on a reference subject comes from exactly a unary
source receiver, either consumed once or supplied by the retained server. -/
theorem reference_input {Label : Type} {Γ Ω : Ctx sig}
    (origin : Label) (environment : Ren sig Γ Ω)
    (faithful : Function.Injective (environment .nm))
    (roles : Roles Γ) (channel : Var Γ .nm) (reference : roles channel = .reference)
    {atom : Proc Γ} {observation : ActiveGuardedBodies.Observation Label Ω}
    (reading : IdleFrame.Reading origin environment atom observation)
    (typed : Typed roles atom) (input : observation.header.header = .input1)
    (subject : observation.header.channel = environment .nm channel) :
    ∃ body : Proc (.nm :: Γ),
      observation = ActiveGuardedBodies.input1 origin (.var channel) (lower body) environment ∧
      Typed (extendRole .call roles) body ∧
      (atom = inp1 (.var channel) body ∨ atom = rep (inp1 (.var channel) body)) := by
  cases reading with
  | output => cases input
  | input1 receiver body =>
      cases typed with
      | inp1 receiver receiverRole bodyTyped =>
          have same := faithful (show environment .nm receiver = environment .nm channel from subject)
          subst receiver
          exact ⟨body, rfl, bodyTyped, Or.inl rfl⟩
  | input2 receiver body =>
      cases typed with
      | inp2 receiver receiverRole bodyTyped =>
          have same := faithful (show environment .nm receiver = environment .nm channel from subject)
          subst receiver
          rw [reference] at receiverRole
          cases receiverRole
  | server1 receiver body =>
      cases typed with
      | rep bodyTyped =>
          cases bodyTyped with
          | inp1 receiver receiverRole bodyTyped =>
              have same := faithful (show environment .nm receiver = environment .nm channel from subject)
              subst receiver
              exact ⟨body, rfl, bodyTyped, Or.inr rfl⟩
  | server2 receiver body =>
      cases typed with
      | rep bodyTyped =>
          cases bodyTyped with
          | inp2 receiver receiverRole bodyTyped =>
              have same := faithful (show environment .nm receiver = environment .nm channel from subject)
              subst receiver
              rw [reference] at receiverRole
              cases receiverRole

/-- A lowered listener on a call subject retains an actual binary source
body, its reference/call binder order, and its original persistence. -/
theorem call_input {Label : Type} {Γ Ω : Ctx sig}
    (origin : Label) (environment : Ren sig Γ Ω)
    (faithful : Function.Injective (environment .nm))
    (roles : Roles Γ) (channel : Var Γ .nm) (call : roles channel = .call)
    {atom : Proc Γ} {observation : ActiveGuardedBodies.Observation Label Ω}
    (reading : IdleFrame.Reading origin environment atom observation)
    (typed : Typed roles atom) (input : observation.header.header = .input1)
    (subject : observation.header.channel = environment .nm channel) :
    ∃ body : Proc (.nm :: .nm :: Γ),
      observation = ActiveGuardedBodies.input1 origin (.var channel) (decoderBody body) environment ∧
      Typed (pairRoles roles) body ∧
      (atom = inp2 (.var channel) body ∨ atom = rep (inp2 (.var channel) body)) := by
  cases reading with
  | output => cases input
  | input1 receiver body =>
      cases typed with
      | inp1 receiver receiverRole bodyTyped =>
          have same := faithful (show environment .nm receiver = environment .nm channel from subject)
          subst receiver
          rw [call] at receiverRole
          cases receiverRole
  | input2 receiver body =>
      cases typed with
      | inp2 receiver receiverRole bodyTyped =>
          have same := faithful (show environment .nm receiver = environment .nm channel from subject)
          subst receiver
          exact ⟨body, rfl, bodyTyped, Or.inl rfl⟩
  | server1 receiver body =>
      cases typed with
      | rep bodyTyped =>
          cases bodyTyped with
          | inp1 receiver receiverRole bodyTyped =>
              have same := faithful (show environment .nm receiver = environment .nm channel from subject)
              subst receiver
              rw [call] at receiverRole
              cases receiverRole
  | server2 receiver body =>
      cases typed with
      | rep bodyTyped =>
          cases bodyTyped with
          | inp2 receiver receiverRole bodyTyped =>
              have same := faithful (show environment .nm receiver = environment .nm channel from subject)
              subst receiver
              exact ⟨body, rfl, bodyTyped, Or.inr rfl⟩

/-- Matching a real unary source output with an actual lowered idle listener
recovers a unary source receiver on the same source channel. -/
theorem unary_output_receiver {Label : Type} {Γ Ω : Ctx sig}
    (origin : Label) (environment : Ren sig Γ Ω)
    (faithful : Function.Injective (environment .nm)) (roles : Roles Γ)
    (channel datum : Var Γ .nm) (outputTyped : Typed roles (out1 (.var channel) (.var datum)))
    {atom : Proc Γ} {observation : ActiveGuardedBodies.Observation Label Ω}
    (reading : IdleFrame.Reading origin environment atom observation)
    (typed : Typed roles atom) (input : observation.header.header = .input1)
    (subject : observation.header.channel =
      (ActiveGuardedBodies.output1 origin (.var channel) (.var datum) environment).header.channel) :
    ∃ body : Proc (.nm :: Γ),
      observation = ActiveGuardedBodies.input1 origin (.var channel) (lower body) environment ∧
      Typed (extendRole .call roles) body ∧
      (atom = inp1 (.var channel) body ∨ atom = rep (inp1 (.var channel) body)) :=
  reference_input origin environment faithful roles channel
    (unary_output_roles roles channel datum outputTyped).1 reading typed input subject

/-- A real offered binary source output can select only a binary source
receiver. The lowered publication's unary header does not erase source arity. -/
theorem binary_output_receiver {Label : Type} {Γ Ω : Ctx sig}
    (origin : Label) (environment : Ren sig Γ Ω)
    (faithful : Function.Injective (environment .nm)) (roles : Roles Γ)
    (channel first second : Var Γ .nm)
    (outputTyped : Typed roles (out2 (.var channel) (.var first) (.var second)))
    {atom : Proc Γ} {observation : ActiveGuardedBodies.Observation Label Ω}
    (reading : IdleFrame.Reading origin environment atom observation)
    (typed : Typed roles atom) (input : observation.header.header = .input1)
    (subject : observation.header.channel = environment .nm channel) :
    ∃ body : Proc (.nm :: .nm :: Γ),
      observation = ActiveGuardedBodies.input1 origin (.var channel) (decoderBody body) environment ∧
      Typed (pairRoles roles) body ∧
      (atom = inp2 (.var channel) body ∨ atom = rep (inp2 (.var channel) body)) :=
  call_input origin environment faithful roles channel
    (binary_output_roles roles channel first second outputTyped).1 reading typed input subject

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.PublicRoles
