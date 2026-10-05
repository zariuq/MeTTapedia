import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveGuardedBodies
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSyntaxMarking
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolSessionOwnership

/-!
# Structural exposure cannot change a committed session's private partners

The original registry is assembled from the actual active phase atoms. A
source-language frame is reindexed past their computed private capabilities.
Every equation-saturated firing retains an exact scoped exposure. If its
selected subject is a registry-private capability, original observation
recovery identifies the unique occurrence and enabled phase pair, including
the actual receiver body modulo the equations and ordered payload fields.

Fresh binder observations occupy a separate extra name position; they cannot
collide with any registry-private capability. This argument does not identify
names from equal origin tags, including tags copied by server unfolding.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.StructuralOwnership

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open MonadicProtocol.Capabilities MonadicProtocol.Ownership
open ScopedActiveFrontier ActiveMarking
open ActiveGuardedBodies

abbrev Entry (n : Nat) := Fin n × AtomKind

inductive Origin (n : Nat) where
  | actor (entry : Entry n)
  | external

abbrev ObservationWorld (n : Nat) (Γ : Ctx sig) := Srt.nm :: World n Γ

def inclusion {Γ : Ctx sig} (n : Nat) : Ren sig (World n Γ) (ObservationWorld n Γ) :=
  fun _ name => .succ name

def binderName {Γ : Ctx sig} (n : Nat) : Origin n → Var (ObservationWorld n Γ) .nm :=
  fun _ => .zero

abbrev mark {Label : Type} (origin : Label) {Γ : Ctx sig} (process : Proc Γ) : ActiveMarking.Tree Label :=
  ActiveSyntaxMarking.mark origin process

theorem mark_fits {Label : Type} (origin : Label) {Γ : Ctx sig} (process : Proc Γ) :
    Fits (mark origin process) process := ActiveSyntaxMarking.mark_fits origin process

def entries {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ) : List (Entry n) :=
  (List.finRange n).flatMap (fun owner =>
    (atoms (registry owner).phase).map (fun atom => (owner, atom)))

theorem entry_live {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (entry : Entry n) (member : entry ∈ entries registry) :
    entry.2 ∈ atoms (registry entry.1).phase := by
  obtain ⟨owner, _, member⟩ := List.mem_flatMap.mp member
  obtain ⟨kind, present, same⟩ := List.mem_map.mp member
  cases same
  exact present

def render {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ) (entry : Entry n) : Proc (World n Γ) :=
  match entry.2 with
  | .output kind => placedOutput n entry.1 kind (registry entry.1).call
  | .input kind => placedInput n entry.1 kind (registry entry.1).call

def entryMark {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (entry : Entry n) : ActiveMarking.Tree (Origin n) :=
  match entry.2 with
  | .output _ => .out1 (.actor entry)
  | .input kind => .inp1 (.actor entry)
      (mark .external (rename (liftRen (placement n entry.1) [.nm])
        (inputBody kind (registry entry.1).call)))

def entryObservation {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (entry : Entry n) : ActiveGuardedBodies.Observation (Origin n) (ObservationWorld n Γ) :=
  match entry.2 with
  | .output kind => output1 (.actor entry) (keyName n entry.1 kind.port)
      (placedDatum n entry.1 kind (registry entry.1).call) (inclusion n)
  | .input kind => input1 (.actor entry) (keyName n entry.1 kind.port)
      (rename (liftRen (placement n entry.1) [.nm]) (inputBody kind (registry entry.1).call))
      (inclusion n)

theorem entry_fits {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ) (entry : Entry n) :
    Fits (entryMark registry entry) (render registry entry) := by
  rcases entry with ⟨owner, kind⟩
  cases kind with
  | output kind =>
      dsimp only [render, entryMark]
      rw [output_header]
      exact .out1 _ _ _
  | input kind =>
      dsimp only [render, entryMark]
      rw [input_header]
      exact .inp1 _ _ (mark_fits _ _)

theorem observe_entry {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ) (entry : Entry n) :
    observe (binderName n) (entryMark registry entry) (render registry entry) (inclusion n) =
      {entryObservation registry entry} := by
  rcases entry with ⟨owner, kind⟩
  cases kind with
  | output kind =>
      dsimp only [render, entryMark, entryObservation]
      rw [output_header]
      simp only [out1, observe]
  | input kind =>
      dsimp only [render, entryMark, entryObservation]
      rw [input_header]
      simp only [inp1, observe]

def parallelMark {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ) :
    List (Entry n) → ActiveMarking.Tree (Origin n)
  | [] => .nil
  | entry :: rest => .par (entryMark registry entry) (parallelMark registry rest)

theorem parallel_fits {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (selected : List (Entry n)) :
    Fits (parallelMark registry selected) (parallel (selected.map (render registry))) := by
  induction selected with
  | nil => exact .nil
  | cons entry rest ih => exact .par (entry_fits registry entry) ih

theorem observe_parallel {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (selected : List (Entry n)) (observation : ActiveGuardedBodies.Observation (Origin n) (ObservationWorld n Γ)) :
    observation ∈ observe (binderName n) (parallelMark registry selected)
      (parallel (selected.map (render registry))) (inclusion n) ↔
      ∃ entry ∈ selected, observation = entryObservation registry entry := by
  induction selected with
  | nil => simp [parallelMark, parallel, nil, observe]
  | cons entry rest ih =>
      simp only [List.map_cons, parallelMark, parallel, par, observe, Set.mem_union,
        observe_entry, Set.mem_singleton_iff, ih, List.mem_cons]
      constructor
      · rintro (equal | ⟨other, present, equal⟩)
        · exact ⟨entry, Or.inl rfl, equal⟩
        · exact ⟨other, Or.inr present, equal⟩
      · rintro ⟨other, equal | present, observed⟩
        · subst other; exact Or.inl observed
        · exact Or.inr ⟨other, present, observed⟩

private theorem nameKey_ne {Γ Ω : Ctx sig} (environment : Ren sig Γ Ω) (forbidden : Var Ω .nm)
    (excluded : ∀ name, environment .nm name ≠ forbidden) (name : Name Γ) :
    ActiveMarkedNames.nameKey (environment .nm) name ≠ forbidden := by
  cases name with
  | var name => exact excluded name
  | op operator _ => cases operator

private theorem observe_channel_ne {Label : Type} {Ω : Ctx sig}
    (binderNames : Label → Var Ω .nm) (forbidden : Var Ω .nm)
    (binderExcluded : ∀ origin, binderNames origin ≠ forbidden) :
    ∀ {Γ : Ctx sig} (process : Proc Γ) (marked : ActiveMarking.Tree Label)
      (environment : Ren sig Γ Ω) (_excluded : ∀ name, environment .nm name ≠ forbidden)
      (observation : ActiveGuardedBodies.Observation Label Ω),
      observation ∈ observe binderNames marked process environment →
      observation.header.channel ≠ forbidden
  | _, .var _, _, _, _, _, member => by simp only [observe, Set.mem_empty_iff_false] at member
  | _, .op .nil .nil, _, _, _, _, member => by simp only [observe, Set.mem_empty_iff_false] at member
  | _, .op .par (.cons first (.cons second .nil)), marked, environment, excluded, observation, member => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false] at member
      rename_i left right
      rcases member with firstMember | secondMember
      · exact observe_channel_ne binderNames forbidden binderExcluded first left environment excluded observation firstMember
      · exact observe_channel_ne binderNames forbidden binderExcluded second right environment excluded observation secondMember
  | _, .op .inp1 (.cons channel (.cons _ .nil)), marked, environment, excluded, observation, member => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false, Set.mem_singleton_iff] at member
      subst observation
      exact nameKey_ne environment forbidden excluded channel
  | _, .op .inp2 (.cons channel (.cons _ .nil)), marked, environment, excluded, observation, member => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false, Set.mem_singleton_iff] at member
      subst observation
      exact nameKey_ne environment forbidden excluded channel
  | _, .op .out1 (.cons channel (.cons _ .nil)), marked, environment, excluded, observation, member => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false, Set.mem_singleton_iff] at member
      subst observation
      exact nameKey_ne environment forbidden excluded channel
  | _, .op .out2 (.cons channel (.cons _ (.cons _ .nil))), marked, environment, excluded, observation, member => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false, Set.mem_singleton_iff] at member
      subst observation
      exact nameKey_ne environment forbidden excluded channel
  | _, .op .nu (.cons body .nil), marked, environment, excluded, observation, member => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false] at member
      rename_i origin inner
      apply observe_channel_ne binderNames forbidden binderExcluded body inner _ _ observation member
      intro name
      cases name with
      | zero => exact binderExcluded origin
      | succ name => exact excluded name
  | _, .op .rep (.cons body .nil), marked, environment, excluded, observation, member => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false] at member
      rename_i inner
      exact observe_channel_ne binderNames forbidden binderExcluded body inner environment excluded observation member
termination_by _ process _ _ _ _ _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

def assembly {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ) (frame : Proc Γ) : Proc (World n Γ) :=
  par (parallel ((entries registry).map (render registry))) (rename (ambient n) frame)

def assemblyMark {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (frame : Proc Γ) : ActiveMarking.Tree (Origin n) :=
  .par (parallelMark registry (entries registry)) (mark .external frame)

theorem assembly_fits {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ) (frame : Proc Γ) :
    Fits (assemblyMark registry frame) (assembly registry frame) :=
  .par (parallel_fits registry _) ((mark_fits (Origin.external (n := n)) frame).rename (ambient n))

/-- No active offer in the actual source frame can acquire a private
registry subject, including offers below its own private restrictions. -/
theorem frame_no_private {Γ : Ctx sig} {n : Nat} (frame : Proc Γ)
    (owner : Fin n) (port : Port)
    (observation : ActiveGuardedBodies.Observation (Origin n) (ObservationWorld n Γ))
    (member : observation ∈ observe (binderName n) (mark .external frame)
      (rename (ambient n) frame) (inclusion n)) :
    observation.header.channel ≠ Var.succ (key n owner port) := by
  rw [observe_rename] at member
  apply observe_channel_ne (binderName n) _ (fun _ impossible => by
      change Var.zero = Var.succ _ at impossible
      cases impossible)
    frame (mark .external frame) _ _ observation member
  intro name impossible
  exact key_ne_ambient n owner port name (Var.succ.inj impossible).symm

/-- Private-header recovery is derived from the actual registry atom list
and exclusion of the actual source frame, rather than supplied as an image
reflection hypothesis. The recovered observation includes its guard body. -/
theorem private_origin {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ) (frame : Proc Γ)
    (observation : ActiveGuardedBodies.Observation (Origin n) (ObservationWorld n Γ))
    (member : observation ∈ observe (binderName n) (assemblyMark registry frame)
      (assembly registry frame) (inclusion n))
    (owner : Fin n) (port : Port) (owned : observation.header.channel = Var.succ (key n owner port)) :
    ∃ entry ∈ entries registry, observation = entryObservation registry entry := by
  simp only [assemblyMark, assembly, par, observe, Set.mem_union] at member
  rcases member with actor | external
  · exact (observe_parallel registry _ observation).mp actor
  · exact False.elim (frame_no_private frame owner port observation external owned)

private theorem input_origin {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (frame : Proc Γ) (observation : ActiveGuardedBodies.Observation (Origin n) (ObservationWorld n Γ))
    (member : observation ∈ observe (binderName n) (assemblyMark registry frame)
      (assembly registry frame) (inclusion n))
    (owner : Fin n) (port : Port) (owned : observation.header.channel = Var.succ (key n owner port))
    (isInput : observation.header.header = ActiveHeaderInvariant.Header.input1 ∨
      observation.header.header = ActiveHeaderInvariant.Header.input2) :
    ∃ receiver kind, AtomKind.input kind ∈ atoms (registry receiver).phase ∧
      observation = entryObservation registry (receiver, .input kind) := by
  obtain ⟨⟨receiver, kind⟩, present, equal⟩ := private_origin registry frame observation member owner port owned
  cases kind with
  | output kind =>
      rw [equal] at isInput
      simp [entryObservation, output1] at isInput
  | input kind => exact ⟨receiver, kind, entry_live registry _ present, equal⟩

private theorem output_origin {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (frame : Proc Γ) (observation : ActiveGuardedBodies.Observation (Origin n) (ObservationWorld n Γ))
    (member : observation ∈ observe (binderName n) (assemblyMark registry frame)
      (assembly registry frame) (inclusion n))
    (owner : Fin n) (port : Port) (owned : observation.header.channel = Var.succ (key n owner port))
    (isOutput : observation.header.header = ActiveHeaderInvariant.Header.output1 ∨
      observation.header.header = ActiveHeaderInvariant.Header.output2) :
    ∃ sender kind, AtomKind.output kind ∈ atoms (registry sender).phase ∧
      observation = entryObservation registry (sender, .output kind) := by
  obtain ⟨⟨sender, kind⟩, present, equal⟩ := private_origin registry frame observation member owner port owned
  cases kind with
  | input kind =>
      rw [equal] at isOutput
      simp [entryObservation, input1] at isOutput
  | output kind => exact ⟨sender, kind, entry_live registry _ present, equal⟩

private theorem input_header_kind {Label : Type} {Γ Ω : Ctx sig} {redex reduct : Proc Γ}
    {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : MarkedCommunication selected marked) (environment : Ren sig Γ Ω) :
    (inputObservation comm environment).header.header = ActiveHeaderInvariant.Header.input1 ∨
      (inputObservation comm environment).header.header = ActiveHeaderInvariant.Header.input2 := by
  cases comm
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem output_header_kind {Label : Type} {Γ Ω : Ctx sig} {redex reduct : Proc Γ}
    {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : MarkedCommunication selected marked) (environment : Ren sig Γ Ω) :
    (outputObservation comm environment).header.header = ActiveHeaderInvariant.Header.output1 ∨
      (outputObservation comm environment).header.header = ActiveHeaderInvariant.Header.output2 := by
  cases comm
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- An arbitrary structurally exposed private firing belongs to one
committed occurrence and its current phase. The recovered input observation
includes the actual guard quotient; the output retains the actual datum. -/
theorem traced_private_selection {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (frame : Proc Γ) {target : Proc (World n Γ)}
    {exposure : ScopedCommunicationInversion.Exposure (assembly registry frame) target}
    (traced : TracedExposure (assemblyMark registry frame) exposure) (owner : Fin n) (port : Port)
    (owned : (inputObservation traced.continuation
      (scopeEnvironment (binderName n) traced.binders (inclusion n))).header.channel =
        Var.succ (key n owner port)) :
    ∃ selectedOwner : Fin n,
      inputObservation traced.continuation (scopeEnvironment (binderName n) traced.binders (inclusion n)) =
        entryObservation registry (selectedOwner, .input (registry selectedOwner).phase.selectedInput) ∧
      outputObservation traced.continuation (scopeEnvironment (binderName n) traced.binders (inclusion n)) =
        entryObservation registry (selectedOwner, .output (registry selectedOwner).phase.selectedOutput) := by
  let environment := scopeEnvironment (binderName n) traced.binders (inclusion n)
  have subjects := communication_subjects_agree traced.continuation environment
  obtain ⟨receiver, inputKind, inputPresent, inputEqual⟩ := input_origin registry frame _
    (traced_input_observed (binderName n) traced (inclusion n)) owner port owned
    (input_header_kind traced.continuation environment)
  obtain ⟨sender, outputKind, outputPresent, outputEqual⟩ := output_origin registry frame _
    (traced_output_observed (binderName n) traced (inclusion n)) owner port
    (subjects.symm.trans owned) (output_header_kind traced.continuation environment)
  rw [inputEqual, outputEqual] at subjects
  change Var.succ (key n receiver inputKind.port) = Var.succ (key n sender outputKind.port) at subjects
  obtain ⟨sameOwner, samePort⟩ := key_injective n receiver sender inputKind.port outputKind.port (Var.succ.inj subjects)
  subst receiver
  have inputLive := input_atom_live (registry sender).phase inputKind inputPresent
  have outputLive := output_atom_live (registry sender).phase outputKind outputPresent
  have chosen : outputKind = (registry sender).phase.selectedOutput ∧
      inputKind = (registry sender).phase.selectedInput := by
    cases phase : (registry sender).phase <;> cases outputKind <;> cases inputKind <;>
      simp_all [OutputKind.live, InputKind.live, OutputKind.port, InputKind.port,
        Phase.selectedOutput, Phase.selectedInput]
  rw [chosen.1] at outputEqual
  rw [chosen.2] at inputEqual
  exact ⟨sender, inputEqual, outputEqual⟩

private theorem observed_unary_result {Label : Type} {Γ Δ Ω : Ctx sig}
    {redex reduct : Proc Γ} {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : MarkedCommunication selected marked)
    (environment : Ren sig Γ Ω) (original : Ren sig Δ Ω) (inputOrigin outputOrigin : Label)
    (channel datum : Name Δ) (body : Proc (.nm :: Δ))
    (guard : inputObservation comm environment = input1 inputOrigin channel body original)
    (field : outputObservation comm environment = output1 outputOrigin channel datum original) :
    EqClosure equations (rename environment reduct) (rename original (inst body datum)) := by
  cases comm with
  | unary suppliedChannel suppliedDatum suppliedBody suppliedOutput suppliedInput continuation fitted =>
      have datumEq := congrArg (fun observation => observation.header.fields) field
      change [ActiveMarkedNames.nameKey (environment .nm) suppliedDatum] =
        [ActiveMarkedNames.nameKey (original .nm) datum] at datumEq
      exact unary_opening suppliedInput inputOrigin suppliedChannel channel suppliedBody body
        environment original suppliedDatum datum guard (List.cons.inj datumEq).1
  | binary suppliedChannel first second suppliedBody suppliedOutput suppliedInput continuation fitted =>
      have impossible := congrArg ActiveGuardedBodies.Observation.unaryBody guard
      change none = some (bodyQ original [.nm] body) at impossible
      cases impossible

/-- The supplied selected reduct is the same committed phase's exact
continuation modulo the equations after the actual scoped reindexing. This
keeps the surrounding telescope and residual frame in `exposure`; it does
not replace the supplied target with a separately successful schedule. -/
theorem traced_private_reduct {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (frame : Proc Γ) {target : Proc (World n Γ)}
    {exposure : ScopedCommunicationInversion.Exposure (assembly registry frame) target}
    (traced : TracedExposure (assemblyMark registry frame) exposure) (owner : Fin n) (port : Port)
    (owned : (inputObservation traced.continuation
      (scopeEnvironment (binderName n) traced.binders (inclusion n))).header.channel =
        Var.succ (key n owner port)) :
    ∃ selectedOwner : Fin n,
      EqClosure equations
        (rename (scopeEnvironment (binderName n) traced.binders (inclusion n)) exposure.reduct)
        (rename (inclusion n) (rename (placement n selectedOwner)
          (selectedReduct (registry selectedOwner).phase (registry selectedOwner).call))) := by
  obtain ⟨selectedOwner, guard, field⟩ := traced_private_selection registry frame traced owner port owned
  let phase := (registry selectedOwner).phase
  let call := (registry selectedOwner).call
  let body := rename (liftRen (placement n selectedOwner) [.nm]) (inputBody phase.selectedInput call)
  let datum := placedDatum n selectedOwner phase.selectedOutput call
  have channels : phase.selectedOutput.port = phase.selectedInput.port := by cases phase <;> rfl
  have actualField : outputObservation traced.continuation
      (scopeEnvironment (binderName n) traced.binders (inclusion n)) =
      output1 (.actor (selectedOwner, .output phase.selectedOutput))
        (keyName n selectedOwner phase.selectedInput.port) datum (inclusion n) := by
    change outputObservation traced.continuation
      (scopeEnvironment (binderName n) traced.binders (inclusion n)) =
      output1 (.actor (selectedOwner, .output phase.selectedOutput))
        (keyName n selectedOwner phase.selectedOutput.port) datum (inclusion n) at field
    simpa only [channels] using field
  have opened := observed_unary_result traced.continuation
    (scopeEnvironment (binderName n) traced.binders (inclusion n)) (inclusion n)
    (.actor (selectedOwner, .input phase.selectedInput)) (.actor (selectedOwner, .output phase.selectedOutput))
    (keyName n selectedOwner phase.selectedInput.port) datum body guard actualField
  have fired : Step (par (placedOutput n selectedOwner phase.selectedOutput call)
      (placedInput n selectedOwner phase.selectedInput call)) (inst body datum) := by
    rw [output_header, input_header, channels]
    exact .comm1 _ _ _
  have outputPresent : AtomKind.output phase.selectedOutput ∈ atoms phase := by cases phase <;> simp [atoms, Phase.selectedOutput]
  have inputPresent : AtomKind.input phase.selectedInput ∈ atoms phase := by cases phase <;> simp [atoms, Phase.selectedInput]
  have exactReduct := (registry_atom_endpoint registry selectedOwner selectedOwner phase.selectedOutput phase.selectedInput
    outputPresent inputPresent fired).2
  rw [exactReduct] at opened
  exact ⟨selectedOwner, opened⟩

/-- Actual equation-saturated executions supply the precise exposure used
by the private readback laws above. Both its before and after endpoints are
the endpoints supplied to the operational relation. -/
theorem modulo_private_readback {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (frame : Proc Γ) {target : Proc (World n Γ)} (firing : StepModulo (assembly registry frame) target) :
    ∃ (exposure : ScopedCommunicationInversion.Exposure (assembly registry frame) target)
      (traced : TracedExposure (assemblyMark registry frame) exposure),
      ∀ (owner : Fin n) (port : Port),
        (inputObservation traced.continuation
          (scopeEnvironment (binderName n) traced.binders (inclusion n))).header.channel = Var.succ (key n owner port) →
        ∃ selectedOwner : Fin n, EqClosure equations
          (rename (scopeEnvironment (binderName n) traced.binders (inclusion n)) exposure.reduct)
          (rename (inclusion n) (rename (placement n selectedOwner)
            (selectedReduct (registry selectedOwner).phase (registry selectedOwner).call))) := by
  obtain ⟨exposure, ⟨traced⟩⟩ := modulo_step_has_traced_origins Origin.external (assembly_fits registry frame) firing
  exact ⟨exposure, traced, fun owner port owned => traced_private_reduct registry frame traced owner port owned⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.StructuralOwnership
