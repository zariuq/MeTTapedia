import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeActors

/-!
# Private selection in an offered and committed runtime inventory

An offered sender has a public publication and a private callback waiter,
but no private output. Thus its waiter cannot run before a receiver actually
commits. Every private output in an arbitrary structural exposure instead
belongs to a retained committed occurrence. Distinct occurrence capabilities
then determine its partner and its unique enabled phase, including the actual
guard quotient and ordered datum.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeSelection

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors ScopedActiveFrontier
open ActiveMarking ActiveGuardedBodies

theorem private_origin {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (observation : Observation (Origin n) (.nm :: World n Γ))
    (member : observation ∈ observe (fun _ => Var.zero) (assemblyMarks registry frame)
      (assembly registry (parallel frame)) (StructuralOwnership.inclusion n))
    (owner : Fin n) (port : Port)
    (owned : observation.header.channel = Var.succ (key n owner port)) :
    ∃ actor ∈ entries registry, observation = actor.observation := by
  simp only [assemblyMarks, assembly, par, observe, Set.mem_union] at member
  rcases member with actor | framed
  · exact (RuntimeActors.observe_parallel _ _).mp actor
  · have absent := ActiveSubjectObservations.observed_ne_of_count_zero Var.zero
        (Var.succ (key n owner port)) (rename (ambient n) (lower (parallel frame)))
        (IdleFrame.marks (Origin.idle (n := n)) 0 frame) (StructuralOwnership.inclusion n)
        (PrivateUpdate.frame_count_zero n owner port (lower (parallel frame))) observation framed
    exact False.elim (absent owned)

theorem private_output {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (observation : Observation (Origin n) (.nm :: World n Γ))
    (member : observation ∈ observe (fun _ => Var.zero) (assemblyMarks registry frame)
      (assembly registry (parallel frame)) (StructuralOwnership.inclusion n))
    (owner : Fin n) (port : Port)
    (owned : observation.header.channel = Var.succ (key n owner port))
    (output : observation.header.header = ActiveHeaderInvariant.Header.output1 ∨
      observation.header.header = ActiveHeaderInvariant.Header.output2) :
    ∃ (sender : Fin n) (phase : Phase) (call : Call Γ) (kind : OutputKind),
      registry sender = .pending phase call ∧ kind.live phase ∧
      observation = Actor.observation (.output sender kind (loweredCall call)) := by
  obtain ⟨actor, present, equal⟩ := private_origin registry frame observation member owner port owned
  obtain ⟨sender, _, present⟩ := List.mem_flatMap.mp present
  cases state : registry sender with
  | released => simp only [slotActors, state, List.not_mem_nil] at present
  | offered channel first second =>
      simp only [state, slotActors, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with same | same
      · subst actor
        cases channel with
        | op op args => cases op
        | var name =>
            rw [equal] at owned
            change Var.succ (ambient n .nm name) = Var.succ (key n owner port) at owned
            exact False.elim (key_ne_ambient n owner port name (Var.succ.inj owned).symm)
      · subst actor
        rw [equal] at output
        simp only [Actor.observation, input1, reduceCtorEq, or_self] at output
  | pending phase call =>
      simp only [state, slotActors] at present
      obtain ⟨kind, live, same⟩ := List.mem_map.mp present
      subst actor
      cases kind with
      | input inputKind =>
          rw [equal] at output
          simp only [privateActor, Actor.observation, input1, reduceCtorEq, or_self] at output
      | output outputKind =>
          exact ⟨sender, phase, call, outputKind, state, output_atom_live phase _ live, equal⟩

theorem private_input {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (observation : Observation (Origin n) (.nm :: World n Γ))
    (member : observation ∈ observe (fun _ => Var.zero) (assemblyMarks registry frame)
      (assembly registry (parallel frame)) (StructuralOwnership.inclusion n))
    (owner : Fin n) (phase : Phase) (call : Call Γ)
    (committed : registry owner = .pending phase call) (port : Port)
    (owned : observation.header.channel = Var.succ (key n owner port))
    (input : observation.header.header = ActiveHeaderInvariant.Header.input1 ∨
      observation.header.header = ActiveHeaderInvariant.Header.input2) :
    ∃ kind : InputKind, kind.live phase ∧
      observation = Actor.observation (.input owner kind (loweredCall call)) := by
  obtain ⟨actor, present, equal⟩ := private_origin registry frame observation member owner port owned
  obtain ⟨receiver, _, present⟩ := List.mem_flatMap.mp present
  cases state : registry receiver with
  | released => simp only [slotActors, state, List.not_mem_nil] at present
  | offered channel first second =>
      simp only [state, slotActors, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with same | same
      · subst actor
        rw [equal] at input
        simp only [Actor.observation, output1, reduceCtorEq, or_self] at input
      · subst actor
        rw [equal] at owned
        change Var.succ (key n receiver .session) = Var.succ (key n owner port) at owned
        have owners := (key_injective n receiver owner .session port (Var.succ.inj owned)).1
        subst receiver
        rw [committed] at state
        cases state
  | pending currentPhase currentCall =>
      simp only [state, slotActors] at present
      obtain ⟨kind, live, same⟩ := List.mem_map.mp present
      subst actor
      cases kind with
      | output outputKind =>
          rw [equal] at input
          simp only [privateActor, Actor.observation, output1, reduceCtorEq, or_self] at input
      | input inputKind =>
          have subjects := owned
          rw [equal] at subjects
          change Var.succ (key n receiver inputKind.port) = Var.succ (key n owner port) at subjects
          have owners := (key_injective n receiver owner inputKind.port port (Var.succ.inj subjects)).1
          subst receiver
          rw [committed] at state
          cases state
          exact ⟨inputKind, input_atom_live phase _ live, equal⟩

private theorem output_kind {Label : Type} {Γ Ω : Ctx sig} {redex reduct : Proc Γ}
    {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : MarkedCommunication selected marked)
    (environment : Ren sig Γ Ω) :
    (outputObservation comm environment).header.header = ActiveHeaderInvariant.Header.output1 ∨
      (outputObservation comm environment).header.header = ActiveHeaderInvariant.Header.output2 := by
  cases comm
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem input_kind {Label : Type} {Γ Ω : Ctx sig} {redex reduct : Proc Γ}
    {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : MarkedCommunication selected marked)
    (environment : Ren sig Γ Ω) :
    (inputObservation comm environment).header.header = ActiveHeaderInvariant.Header.input1 ∨
      (inputObservation comm environment).header.header = ActiveHeaderInvariant.Header.input2 := by
  cases comm
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem traced_private_selection {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) {target : Proc (World n Γ)}
    {exposure : ScopedCommunicationInversion.Exposure (assembly registry (parallel frame)) target}
    (traced : TracedExposure (assemblyMarks registry frame) exposure)
    (owner : Fin n) (port : Port)
    (owned : (outputObservation traced.continuation
      (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion n))).header.channel =
      Var.succ (key n owner port)) :
    ∃ (selectedOwner : Fin n) (phase : Phase) (call : Call Γ),
      registry selectedOwner = .pending phase call ∧
      inputObservation traced.continuation
          (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion n)) =
        Actor.observation (.input selectedOwner phase.selectedInput (loweredCall call)) ∧
      outputObservation traced.continuation
          (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion n)) =
        Actor.observation (.output selectedOwner phase.selectedOutput (loweredCall call)) := by
  let environment := scopeEnvironment (fun _ : Origin n => Var.zero) traced.binders (StructuralOwnership.inclusion n)
  obtain ⟨sender, phase, call, output, committed, outputLive, outputEqual⟩ :=
    private_output registry frame _ (traced_output_observed (fun _ => Var.zero) traced _)
      owner port owned (output_kind traced.continuation environment)
  have selectedSubject : (inputObservation traced.continuation environment).header.channel =
      Var.succ (key n sender output.port) := by
    rw [communication_subjects_agree traced.continuation environment, outputEqual]
    rfl
  obtain ⟨input, inputLive, inputEqual⟩ := private_input registry frame _
    (traced_input_observed (fun _ => Var.zero) traced _) sender phase call committed output.port
    selectedSubject (input_kind traced.continuation environment)
  have subjects := communication_subjects_agree traced.continuation environment
  rw [inputEqual, outputEqual] at subjects
  change Var.succ (key n sender input.port) = Var.succ (key n sender output.port) at subjects
  have ports := (key_injective n sender sender input.port output.port (Var.succ.inj subjects)).2
  have chosen : output = phase.selectedOutput ∧ input = phase.selectedInput := by
    cases phase <;> cases output <;> cases input <;>
      simp_all [OutputKind.live, InputKind.live, OutputKind.port, InputKind.port,
        Phase.selectedInput, Phase.selectedOutput]
  rw [chosen.1] at outputEqual
  rw [chosen.2] at inputEqual
  exact ⟨sender, phase, call, committed, inputEqual, outputEqual⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeSelection
