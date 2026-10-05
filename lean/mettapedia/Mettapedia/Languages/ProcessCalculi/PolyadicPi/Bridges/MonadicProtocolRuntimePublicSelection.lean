import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeSelection
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolPublicRoles

/-!
# Public selection in the actual mixed tuple runtime

All lowered actors have unary headers. A public selected actor is nevertheless
read from its original source occurrence, not classified from that header alone.
Computed private names are disjoint from the injectively embedded source names.
Consequently an offered publication selects a binary source receiver, whereas
an ordinary unary message selects a unary source receiver, under the independent
source role judgment. The supplied trace retains the actual selected occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePublicSelection

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors ScopedActiveFrontier
open ActiveMarking ActiveGuardedBodies NamePassingChannelRoles

def environment {Γ : Ctx sig} (n : Nat) : Ren sig Γ (.nm :: World n Γ) :=
  fun _ name => .succ (ambient n _ name)

theorem environment_injective {Γ : Ctx sig} (n : Nat) :
    Function.Injective (environment (Γ := Γ) n .nm) := by
  intro first second same
  have included := Var.succ.inj same
  rw [← privateScope_inclusion n] at included
  exact (privateScope n).inclusion_injective .nm included

theorem frame_reading {Γ : Ctx sig} {n : Nat} (frame : List (Proc Γ))
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom)
    (observation : Observation (Origin n) (.nm :: World n Γ))
    (member : observation ∈ observe (fun _ => Var.zero)
      (IdleFrame.marks (Origin.idle (n := n)) 0 frame)
      (rename (ambient n) (lower (parallel frame))) (StructuralOwnership.inclusion n)) :
    ∃ position : Fin frame.length,
      IdleFrame.Reading (.idle position.val) (environment n) frame[position.val] observation := by
  rw [observe_rename, ← IdleFrame.parallel_lower] at member
  obtain ⟨position, observed⟩ := (IdleFrame.observe_parallel (Origin.idle (n := n))
    (fun _ => Var.zero) (environment n) 0 frame observation).mp member
  simp only [Nat.zero_add] at observed
  exact ⟨position, IdleFrame.observed_head (.idle position.val) (fun _ => Var.zero)
    (environment n) (heads _ (List.getElem_mem position.isLt)) observation observed⟩

theorem actor_origin {Γ : Ctx sig} {n : Nat} (actor : Actor n Γ) :
    actor.observation.header.origin = actor.origin := by
  cases actor <;> rfl

theorem reading_origin {Label : Type} {Γ Ω : Ctx sig} (origin : Label)
    (reindex : Ren sig Γ Ω) {atom : Proc Γ} {observation : Observation Label Ω}
    (reading : IdleFrame.Reading origin reindex atom observation) :
    observation.header.origin = origin := by
  cases reading <;> rfl

theorem public_input {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (heads : ∀ atom ∈ frame, IdleFrame.Head atom)
    (observation : Observation (Origin n) (.nm :: World n Γ))
    (member : observation ∈ observe (fun _ => Var.zero) (assemblyMarks registry frame)
      (assembly registry (parallel frame)) (StructuralOwnership.inclusion n))
    (channel : Var Γ .nm) (subject : observation.header.channel = environment n .nm channel)
    (input : observation.header.header = ActiveHeaderInvariant.Header.input1 ∨
      observation.header.header = ActiveHeaderInvariant.Header.input2) :
    ∃ position : Fin frame.length,
      IdleFrame.Reading (.idle position.val) (environment n) frame[position.val] observation := by
  simp only [assemblyMarks, assembly, par, observe, Set.mem_union] at member
  rcases member with actorMember | framed
  · obtain ⟨actor, present, equal⟩ := (RuntimeActors.observe_parallel _ _).mp actorMember
    cases actor with
    | publication => rw [equal] at input; simp only [Actor.observation, output1, reduceCtorEq, or_self] at input
    | output => rw [equal] at input; simp only [Actor.observation, output1, reduceCtorEq, or_self] at input
    | waiter owner first second =>
        rw [equal] at subject
        change Var.succ (key n owner .session) = Var.succ (ambient n .nm channel) at subject
        exact False.elim (key_ne_ambient n owner .session channel (Var.succ.inj subject))
    | input owner kind call =>
        rw [equal] at subject
        change Var.succ (key n owner kind.port) = Var.succ (ambient n .nm channel) at subject
        exact False.elim (key_ne_ambient n owner kind.port channel (Var.succ.inj subject))
  · exact frame_reading frame heads observation framed

/-- The output is either one committed private instruction, an actual
uncommitted publication, or an ordinary source message at its literal index. -/
theorem output_classification {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (heads : ∀ atom ∈ frame, IdleFrame.Head atom)
    (observation : Observation (Origin n) (.nm :: World n Γ))
    (member : observation ∈ observe (fun _ => Var.zero) (assemblyMarks registry frame)
      (assembly registry (parallel frame)) (StructuralOwnership.inclusion n))
    (output : observation.header.header = ActiveHeaderInvariant.Header.output1 ∨
      observation.header.header = ActiveHeaderInvariant.Header.output2) :
    (∃ (owner : Fin n) (phase : Phase) (call : Call Γ) (kind : OutputKind),
      registry owner = .pending phase call ∧ kind.live phase ∧
      observation = Actor.observation (.output owner kind (loweredCall call))) ∨
    (∃ (owner : Fin n) (channel first second : Name Γ),
      registry owner = .offered channel first second ∧
      observation = Actor.observation (.publication owner channel)) ∨
    (∃ (position : Fin frame.length) (channel datum : Name Γ),
      frame[position.val] = out1 channel datum ∧
      observation = output1 (.idle position.val) channel datum (environment n)) := by
  simp only [assemblyMarks, assembly, par, observe, Set.mem_union] at member
  rcases member with actorMember | framed
  · obtain ⟨actor, present, equal⟩ := (RuntimeActors.observe_parallel _ _).mp actorMember
    obtain ⟨owner, _, present⟩ := List.mem_flatMap.mp present
    cases state : registry owner with
    | released => simp only [slotActors, state, List.not_mem_nil] at present
    | offered channel first second =>
        simp only [slotActors, state, List.mem_cons, List.not_mem_nil, or_false] at present
        rcases present with same | same
        · subst actor; exact Or.inr (Or.inl ⟨owner, channel, first, second, state, equal⟩)
        · subst actor
          rw [equal] at output
          simp only [Actor.observation, input1, reduceCtorEq, or_self] at output
    | pending phase call =>
        simp only [slotActors, state] at present
        obtain ⟨kind, live, same⟩ := List.mem_map.mp present
        subst actor
        cases kind with
        | input kind =>
            rw [equal] at output
            simp only [privateActor, Actor.observation, input1, reduceCtorEq, or_self] at output
        | output kind => exact Or.inl ⟨owner, phase, call, kind, state, output_atom_live phase kind live, equal⟩
  · obtain ⟨position, reading⟩ := frame_reading frame heads observation framed
    generalize original : frame[position.val] = atom at reading
    cases reading with
    | output channel datum => exact Or.inr (Or.inr ⟨position, channel, datum, original, rfl⟩)
    | input1 | input2 | server1 | server2 =>
        simp only [input1, reduceCtorEq, or_self] at output

theorem observations_unary {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (heads : ∀ atom ∈ frame, IdleFrame.Head atom)
    (observation : Observation (Origin n) (.nm :: World n Γ))
    (member : observation ∈ observe (fun _ => Var.zero) (assemblyMarks registry frame)
      (assembly registry (parallel frame)) (StructuralOwnership.inclusion n)) :
    observation.header.header = ActiveHeaderInvariant.Header.input1 ∨
      observation.header.header = ActiveHeaderInvariant.Header.output1 := by
  simp only [assemblyMarks, assembly, par, observe, Set.mem_union] at member
  rcases member with actorMember | framed
  · obtain ⟨actor, _, equal⟩ := (RuntimeActors.observe_parallel _ _).mp actorMember
    rw [equal]
    cases actor <;> first | exact Or.inl rfl | exact Or.inr rfl
  · obtain ⟨position, reading⟩ := frame_reading frame heads observation framed
    generalize frame[position.val] = atom at reading
    cases reading <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem input_observation_header {Label : Type} {Γ Ω : Ctx sig} {redex reduct : Proc Γ}
    {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (communication : MarkedCommunication selected marked)
    (reindex : Ren sig Γ Ω) :
    (inputObservation communication reindex).header.header =
      ActiveHeaderInvariant.inputHeader selected := by
  cases communication <;> rfl

theorem input_observation_origin {Label : Type} {Γ Ω : Ctx sig} {redex reduct : Proc Γ}
    {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (communication : MarkedCommunication selected marked)
    (reindex : Ren sig Γ Ω) :
    (inputObservation communication reindex).header.origin = communication.inputOrigin := by
  cases communication <;> rfl

theorem output_observation_origin {Label : Type} {Γ Ω : Ctx sig} {redex reduct : Proc Γ}
    {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (communication : MarkedCommunication selected marked)
    (reindex : Ren sig Γ Ω) :
    (outputObservation communication reindex).header.origin = communication.outputOrigin := by
  cases communication <;> rfl

theorem input_header_cases {Γ : Ctx sig} {redex reduct : Proc Γ}
    (selected : ScopedCommunicationInversion.Communication redex reduct) :
    ActiveHeaderInvariant.inputHeader selected = .input1 ∨
      ActiveHeaderInvariant.inputHeader selected = .input2 := by
  cases selected <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem traced_unary {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (heads : ∀ atom ∈ frame, IdleFrame.Head atom)
    {target : Proc (World n Γ)}
    {exposure : ScopedCommunicationInversion.Exposure (assembly registry (parallel frame)) target}
    (traced : TracedExposure (assemblyMarks registry frame) exposure) :
    ActiveHeaderInvariant.inputHeader exposure.selected = .input1 := by
  have only := observations_unary registry frame heads _
    (traced_input_observed (fun _ => Var.zero) traced (StructuralOwnership.inclusion n))
  rw [input_observation_header] at only
  rcases only with input | output
  · exact input
  · have possible := input_header_cases exposure.selected
    rcases possible with unary | binary
    · exact unary
    · rw [binary] at output; cases output

/-- A selected publication reads back the supplied receiver's real binary
guard and persistence. The independent source role proof forbids an illicit
cross-arity match introduced merely by unary lowering. -/
theorem traced_public_receiver {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (heads : ∀ atom ∈ frame, IdleFrame.Head atom)
    (roles : Roles Γ) (frameTyped : ∀ atom ∈ frame, Typed roles atom)
    (owner : Fin n) (channel first second : Var Γ .nm)
    (outputTyped : Typed roles (out2 (.var channel) (.var first) (.var second)))
    {target : Proc (World n Γ)}
    {exposure : ScopedCommunicationInversion.Exposure (assembly registry (parallel frame)) target}
    (traced : TracedExposure (assemblyMarks registry frame) exposure)
    (published : outputObservation traced.continuation
      (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion n)) =
      Actor.observation (.publication owner (.var channel))) :
    ∃ (position : Fin frame.length) (body : Proc (.nm :: .nm :: Γ)),
      Typed (pairRoles roles) body ∧
      (frame[position.val] = inp2 (.var channel) body ∨ frame[position.val] = rep (inp2 (.var channel) body)) ∧
      inputObservation traced.continuation
        (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion n)) =
        input1 (.idle position.val) (.var channel) (PublicRoles.decoderBody body) (environment n) ∧
      traced.continuation.inputOrigin = .idle position.val ∧
      traced.continuation.outputOrigin = .publication owner := by
  let selectedEnvironment := scopeEnvironment (fun _ : Origin n => Var.zero)
    traced.binders (StructuralOwnership.inclusion n)
  have subject : (inputObservation traced.continuation selectedEnvironment).header.channel =
      environment n .nm channel := by
    rw [communication_subjects_agree traced.continuation selectedEnvironment, published]
    rfl
  have arity := traced_unary registry frame heads traced
  have input : (inputObservation traced.continuation selectedEnvironment).header.header =
      ActiveHeaderInvariant.Header.input1 := (input_observation_header _ _).trans arity
  obtain ⟨position, reading⟩ := public_input registry frame heads _
    (traced_input_observed (fun _ => Var.zero) traced _) channel subject (Or.inl input)
  obtain ⟨body, guard, typed, source⟩ := PublicRoles.binary_output_receiver (.idle position.val)
    (environment n) (environment_injective n) roles channel first second outputTyped reading
    (frameTyped _ (List.getElem_mem position.isLt)) input subject
  refine ⟨position, body, typed, source, guard, ?_, ?_⟩
  · have origin := congrArg (fun observation : Observation (Origin n) (.nm :: World n Γ) =>
      observation.header.origin) guard
    have actual : (inputObservation traced.continuation selectedEnvironment).header.origin =
        traced.continuation.inputOrigin := input_observation_origin traced.continuation selectedEnvironment
    exact actual.symm.trans origin
  · have origin := congrArg (fun observation : Observation (Origin n) (.nm :: World n Γ) =>
      observation.header.origin) published
    exact (output_observation_origin traced.continuation selectedEnvironment).symm.trans origin

theorem traced_unary_receiver {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (heads : ∀ atom ∈ frame, IdleFrame.Head atom)
    (roles : Roles Γ) (frameTyped : ∀ atom ∈ frame, Typed roles atom)
    (sender : Fin frame.length) (channel datum : Var Γ .nm)
    (outputTyped : Typed roles (out1 (.var channel) (.var datum)))
    {target : Proc (World n Γ)}
    {exposure : ScopedCommunicationInversion.Exposure (assembly registry (parallel frame)) target}
    (traced : TracedExposure (assemblyMarks registry frame) exposure)
    (sent : outputObservation traced.continuation
      (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion n)) =
      output1 (.idle sender.val) (.var channel) (.var datum) (environment n)) :
    ∃ (position : Fin frame.length) (body : Proc (.nm :: Γ)),
      Typed (extendRole .call roles) body ∧
      (frame[position.val] = inp1 (.var channel) body ∨ frame[position.val] = rep (inp1 (.var channel) body)) ∧
      inputObservation traced.continuation
        (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion n)) =
        input1 (.idle position.val) (.var channel) (lower body) (environment n) ∧
      traced.continuation.inputOrigin = .idle position.val ∧
      traced.continuation.outputOrigin = .idle sender.val := by
  let selectedEnvironment := scopeEnvironment (fun _ : Origin n => Var.zero)
    traced.binders (StructuralOwnership.inclusion n)
  have subject : (inputObservation traced.continuation selectedEnvironment).header.channel =
      environment n .nm channel := by
    rw [communication_subjects_agree traced.continuation selectedEnvironment, sent]
    rfl
  have arity := traced_unary registry frame heads traced
  have input : (inputObservation traced.continuation selectedEnvironment).header.header =
      ActiveHeaderInvariant.Header.input1 := (input_observation_header _ _).trans arity
  obtain ⟨position, reading⟩ := public_input registry frame heads _
    (traced_input_observed (fun _ => Var.zero) traced _) channel subject (Or.inl input)
  obtain ⟨body, guard, typed, source⟩ := PublicRoles.unary_output_receiver (.idle position.val)
    (environment n) (environment_injective n) roles channel datum outputTyped reading
    (frameTyped _ (List.getElem_mem position.isLt)) input subject
  exact ⟨position, body, typed, source, guard,
    (input_observation_origin traced.continuation selectedEnvironment).symm.trans
      (congrArg (fun observation : Observation (Origin n) (.nm :: World n Γ) =>
        observation.header.origin) guard),
    (output_observation_origin traced.continuation selectedEnvironment).symm.trans
      (congrArg (fun observation : Observation (Origin n) (.nm :: World n Γ) =>
        observation.header.origin) sent)⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePublicSelection
