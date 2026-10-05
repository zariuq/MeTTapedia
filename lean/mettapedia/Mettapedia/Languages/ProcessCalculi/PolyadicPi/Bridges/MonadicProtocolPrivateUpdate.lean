import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectFiring
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolStructuralOwnership
import Mathlib.Data.List.FinRange

/-!
# Actual private protocol updates retain the whole supplied endpoint

Distinct computed occurrence capabilities exclude unrelated source frames
and persistent servers. The selected phase has exactly one input and one
output on its enabled port. The selected-subject update therefore follows
any supplied structurally exposed firing, preserving all other occurrences
and the actual enclosing scopes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.PrivateUpdate

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership StructuralOwnership ScopedActiveFrontier
open ActiveSubjectResidual ActiveSubjectFiring

local instance {Γ : Ctx sig} : DecidableEq (Var Γ Srt.nm) := decEqVar (S := sig)

private theorem private_keys_ne {Γ : Ctx sig} (n : Nat) (owner other : Fin n)
    (port otherPort : Port) (different : owner ≠ other ∨ port ≠ otherPort) :
    key (Γ := Γ) n owner port ≠ key n other otherPort := by
  intro equal
  obtain ⟨owners, ports⟩ := key_injective n owner other port otherPort equal
  rcases different with different | different
  · exact different owners
  · exact different ports

theorem frame_count_zero {Γ : Ctx sig} (n : Nat) (owner : Fin n) (port : Port) (frame : Proc Γ) :
    count Var.zero (Var.succ (key n owner port)) (inclusion n) (rename (ambient n) frame) = 0 := by
  rw [count_rename]
  apply count_zero_of_excluded Var.zero (Var.succ (key n owner port)) (by intro impossible; cases impossible)
  intro name equal
  exact key_ne_ambient n owner port name (Var.succ.inj equal).symm

private theorem frame_repFree {Γ : Ctx sig} (n : Nat) (owner : Fin n) (port : Port) (frame : Proc Γ) :
    repFree Var.zero (Var.succ (key n owner port)) (inclusion n) (rename (ambient n) frame) :=
  repFree_of_count_zero _ _ _ _ (frame_count_zero n owner port frame)

theorem phase_repFree {Γ : Ctx sig} (n : Nat) (owner selected : Fin n)
    (port : Port) (phase : Phase) (call : Call Γ) :
    repFree Var.zero (Var.succ (key n selected port)) (inclusion n) (placed n owner phase call) := by
  unfold placed
  rw [repFree_rename]
  cases phase <;> simp [contents, repFree, sendFields, receiveFields, weaken, rename, renameArgs, liftRen, par, out1, inp1]

theorem own_phase_count {Γ : Ctx sig} (n : Nat) (owner : Fin n) (phase : Phase) (call : Call Γ) :
    count Var.zero (Var.succ (key n owner phase.selectedInput.port)) (inclusion n) (placed n owner phase call) = 2 := by
  unfold placed
  rw [count_rename]
  cases phase <;>
    simp [contents, count, sendFields, receiveFields, weaken, rename, renameArgs, liftRen, par, out1, inp1, onSubject,
      ActiveMarkedNames.nameKey, placement, inclusion, prependRen,
      Phase.selectedInput, InputKind.port,
      private_keys_ne n owner owner .callback .session (Or.inr (by decide)),
      private_keys_ne n owner owner .session .callback (Or.inr (by decide))]

theorem other_phase_count {Γ : Ctx sig} (n : Nat) (owner selected : Fin n)
    (different : owner ≠ selected) (port : Port) (phase : Phase) (call : Call Γ) :
    count Var.zero (Var.succ (key n selected port)) (inclusion n) (placed n owner phase call) = 0 := by
  unfold placed
  rw [count_rename]
  cases phase <;>
    simp [contents, count, sendFields, receiveFields, weaken, rename, renameArgs, liftRen, par, out1, inp1, onSubject,
      ActiveMarkedNames.nameKey, placement, inclusion, prependRen,
      private_keys_ne n owner selected .callback port (Or.inl different),
      private_keys_ne n owner selected .session port (Or.inl different)]

def phaseAssembly {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ) (frame : Proc Γ) : Proc (World n Γ) :=
  par (parallel ((List.finRange n).map (fun owner => placed n owner (registry owner).phase (registry owner).call)))
    (rename (ambient n) frame)

private theorem phases_atoms {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ) (owners : List (Fin n)) :
    StructuralEq (parallel (owners.map (fun owner => placed n owner (registry owner).phase (registry owner).call)))
      (parallel ((owners.flatMap (fun owner => (atoms (registry owner).phase).map (fun atom => (owner, atom)))).map (render registry))) := by
  induction owners with
  | nil => exact .refl _
  | cons owner rest ih =>
      have headEq := (contents_atoms (registry owner).phase (registry owner).call).rename (placement n owner)
      rw [parallel_rename] at headEq
      simp only [List.map_map] at headEq
      have renderEqual : (fun kind => rename (placement n owner) (atomTemplate kind (registry owner).call)) =
          (fun kind => render registry (owner, kind)) := by
        funext kind
        cases kind <;> rfl
      change StructuralEq (rename (placement n owner) (contents (registry owner).phase (registry owner).call))
        (parallel ((atoms (registry owner).phase).map
          (fun kind => rename (placement n owner) (atomTemplate kind (registry owner).call)))) at headEq
      rw [renderEqual] at headEq
      simp only [List.map_cons, List.flatMap_cons, List.map_append, List.map_map, parallel]
      exact .trans (.par headEq ih) (parallel_append _ _)

theorem phaseAssembly_eq {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ) (frame : Proc Γ) :
    StructuralEq (phaseAssembly registry frame) (assembly registry frame) :=
  .par (phases_atoms registry (List.finRange n)) (.refl _)

theorem parallel_zero {Ω : Ctx sig} (fresh subject : Var Ω .nm)
    {Γ : Ctx sig} (environment : Ren sig Γ Ω) (processes : List (Proc Γ))
    (zero : ∀ process ∈ processes, count fresh subject environment process = 0) :
    count fresh subject environment (parallel processes) = 0 := by
  induction processes with
  | nil => simp only [parallel, nil, count]
  | cons process rest ih =>
      simp only [parallel, par, count, zero process (List.mem_cons_self ..),
        ih (fun next present => zero next (List.mem_cons_of_mem _ present)), Nat.zero_add]

theorem parallel_single {Ω : Ctx sig} (fresh subject : Var Ω .nm)
    {Γ : Ctx sig} {α : Type} [DecidableEq α] (environment : Ren sig Γ Ω)
    (actors : α → Proc Γ) (selected : α) (owners : List α) (unique : owners.Nodup) (present : selected ∈ owners)
    (others : ∀ other ∈ owners, other ≠ selected → count fresh subject environment (actors other) = 0) :
    count fresh subject environment (parallel (owners.map actors)) = count fresh subject environment (actors selected) := by
  induction owners with
  | nil => cases present
  | cons owner rest ih =>
      have noDuplicates := List.nodup_cons.mp unique
      by_cases same : owner = selected
      · subst owner
        have restZero : count fresh subject environment (parallel (rest.map actors)) = 0 := by
          apply parallel_zero
          intro process member
          obtain ⟨other, otherPresent, rfl⟩ := List.mem_map.mp member
          exact others other (List.mem_cons_of_mem _ otherPresent) (by
            intro equal
            exact noDuplicates.1 (equal ▸ otherPresent))
        simp only [List.map_cons, parallel, par, count, restZero, Nat.add_zero]
      · have restMember := (List.mem_cons.mp present).resolve_left (Ne.symm same)
        simp only [List.map_cons, parallel, par, count, others owner (List.mem_cons_self ..) same,
          Nat.zero_add]
        exact ih noDuplicates.2 restMember (fun other member different =>
          others other (List.mem_cons_of_mem _ member) different)

theorem parallel_repFree {Ω : Ctx sig} (fresh subject : Var Ω .nm)
    {Γ : Ctx sig} (environment : Ren sig Γ Ω) (processes : List (Proc Γ))
    (safe : ∀ process ∈ processes, repFree fresh subject environment process) :
    repFree fresh subject environment (parallel processes) := by
  induction processes with
  | nil => simp only [parallel, nil, repFree]
  | cons process rest ih =>
      simp only [parallel, par, repFree]
      exact ⟨safe process (List.mem_cons_self ..), ih (fun next present => safe next (List.mem_cons_of_mem _ present))⟩

/-- Every actual registry phase has exactly two occurrences on its enabled
capability. Different occurrence numbers keep duplicate calls separate. -/
theorem phaseAssembly_count {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (frame : Proc Γ) (owner : Fin n) :
    count Var.zero (Var.succ (key n owner (registry owner).phase.selectedInput.port))
      (inclusion n) (phaseAssembly registry frame) = 2 := by
  unfold phaseAssembly
  simp only [par, count]
  rw [frame_count_zero n owner (registry owner).phase.selectedInput.port frame, Nat.add_zero]
  rw [parallel_single _ _ _ _ owner _ (List.nodup_finRange n) (List.mem_finRange owner)]
  · exact own_phase_count n owner (registry owner).phase (registry owner).call
  · intro other _ different
    exact other_phase_count n other owner different _ (registry other).phase (registry other).call

private theorem phaseAssembly_safe {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (frame : Proc Γ) (owner : Fin n) (port : Port) :
    repFree Var.zero (Var.succ (key n owner port)) (inclusion n) (phaseAssembly registry frame) := by
  unfold phaseAssembly
  simp only [par, repFree]
  refine ⟨?_, frame_repFree n owner port frame⟩
  apply parallel_repFree
  intro process present
  obtain ⟨other, _, rfl⟩ := List.mem_map.mp present
  exact phase_repFree n other owner port (registry other).phase (registry other).call

/-- Persistent source code cannot duplicate or contract any active private
phase capability of the registry's actual structural class. -/
theorem assembly_safe {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (frame : Proc Γ) (owner : Fin n) (port : Port) :
    repFree Var.zero (Var.succ (key n owner port)) (inclusion n) (assembly registry frame) :=
  (repFree_structural _ _ (phaseAssembly_eq registry frame) (inclusion n)).mp
    (phaseAssembly_safe registry frame owner port)

theorem assembly_count {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (frame : Proc Γ) (owner : Fin n) :
    count Var.zero (Var.succ (key n owner (registry owner).phase.selectedInput.port))
      (inclusion n) (assembly registry frame) = 2 :=
  (count_structural _ _ (phaseAssembly_eq registry frame) (inclusion n)
    (phaseAssembly_safe registry frame owner _)).symm.trans (phaseAssembly_count registry frame owner)

private theorem scope_environment_eq {Label : Type} {Ω Γ Δ : Ctx sig}
    (fresh : Var Ω .nm) {scope : Scope Γ Δ} (binders : ActiveMarking.ScopeMarks Label scope)
    (environment : Ren sig Γ Ω) :
    ActiveGuardedBodies.scopeEnvironment (fun _ : Label => fresh) binders environment =
      ActiveSubjectFiring.scopeEnvironment fresh scope environment := by
  induction binders with
  | nil => rfl
  | bind origin rest ih => exact ih (prependRen fresh environment)

theorem observed_choice {Label : Type} {Γ Δ : Ctx sig} (scope : Scope Γ Δ)
    (binders : ActiveMarking.ScopeMarks Label scope) {redex reduct : Proc Δ}
    {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : ActiveMarking.MarkedCommunication selected marked)
    (inputOrigin outputOrigin : Label) (subject : Var Γ .nm) (datum : Name Γ) (body : Proc (.nm :: Γ))
    (guard : ActiveGuardedBodies.inputObservation comm
      (ActiveGuardedBodies.scopeEnvironment (fun _ : Label => (Var.zero : Var (.nm :: Γ) .nm)) binders (fun _ name => .succ name)) =
      ActiveGuardedBodies.input1 inputOrigin (.var subject) body (fun _ name => .succ name))
    (field : ActiveGuardedBodies.outputObservation comm
      (ActiveGuardedBodies.scopeEnvironment (fun _ : Label => (Var.zero : Var (.nm :: Γ) .nm)) binders (fun _ name => .succ name)) =
      ActiveGuardedBodies.output1 outputOrigin (.var subject) datum (fun _ name => .succ name)) :
    ActiveSubjectFiring.UnaryChoice (Var.succ subject)
      (ActiveSubjectFiring.scopeEnvironment Var.zero scope (fun _ name => .succ name))
      (rename scope.inclusion datum) selected := by
  rw [scope_environment_eq] at guard field
  cases comm with
  | unary suppliedChannel suppliedDatum suppliedBody suppliedOutput suppliedInput continuation fitted =>
      simp only [ActiveSubjectFiring.UnaryChoice]
      have subjectEq := congrArg (fun observation => observation.header.channel) guard
      have fieldEq := congrArg (fun observation => observation.header.fields) field
      change ActiveMarkedNames.nameKey
        ((ActiveSubjectFiring.scopeEnvironment Var.zero scope (fun _ name => .succ name)) .nm)
        suppliedChannel = Var.succ subject at subjectEq
      refine ⟨by simp only [onSubject, subjectEq, decide_true], ?_⟩
      cases datum with
      | var old =>
          change [ActiveMarkedNames.nameKey
            ((ActiveSubjectFiring.scopeEnvironment Var.zero scope (fun _ name => .succ name)) .nm)
            suppliedDatum] = [Var.succ old] at fieldEq
          apply scope_names_back Var.zero (Var.succ old) (by intro impossible; cases impossible)
            scope (fun _ name => .succ name) old (fun name equal => Var.succ.inj equal)
            suppliedDatum (List.cons.inj fieldEq).1
      | op operator _ => cases operator
  | binary suppliedChannel first second suppliedBody suppliedOutput suppliedInput continuation fitted =>
      have impossible := congrArg ActiveGuardedBodies.Observation.unaryBody guard
      change none = some (ActiveGuardedBodies.bodyQ (fun _ name => .succ name) [.nm] body) at impossible
      cases impossible

/-- The selected real private firing updates the original registry assembly
in its original context. The supplied endpoint, its enclosing scopes and its
entire untouched frame are retained; the actual session fields are recovered. -/
theorem traced_private_endpoint {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (frame : Proc Γ) {target : Proc (World n Γ)}
    {exposure : ScopedCommunicationInversion.Exposure (assembly registry frame) target}
    (traced : ActiveMarking.TracedExposure (assemblyMark registry frame) exposure) (owner : Fin n) (port : Port)
    (owned : (ActiveGuardedBodies.inputObservation traced.continuation
      (ActiveGuardedBodies.scopeEnvironment (binderName n) traced.binders (inclusion n))).header.channel =
        Var.succ (key n owner port)) :
    ∃ selectedOwner : Fin n,
      StructuralEq
        (release Var.zero (Var.succ (key n selectedOwner (registry selectedOwner).phase.selectedInput.port))
          (inclusion n) (placedDatum n selectedOwner (registry selectedOwner).phase.selectedOutput (registry selectedOwner).call)
          (assembly registry frame)) target := by
  obtain ⟨selectedOwner, guard, field⟩ := traced_private_selection registry frame traced owner port owned
  let phase := (registry selectedOwner).phase
  let call := (registry selectedOwner).call
  have channels : phase.selectedOutput.port = phase.selectedInput.port := by cases phase <;> rfl
  have actualField : ActiveGuardedBodies.outputObservation traced.continuation
      (ActiveGuardedBodies.scopeEnvironment (binderName n) traced.binders (inclusion n)) =
      ActiveGuardedBodies.output1 (.actor (selectedOwner, .output phase.selectedOutput))
        (keyName n selectedOwner phase.selectedInput.port)
        (placedDatum n selectedOwner phase.selectedOutput call) (inclusion n) := by
    change ActiveGuardedBodies.outputObservation traced.continuation
      (ActiveGuardedBodies.scopeEnvironment (binderName n) traced.binders (inclusion n)) =
      ActiveGuardedBodies.output1 (.actor (selectedOwner, .output phase.selectedOutput))
        (keyName n selectedOwner phase.selectedOutput.port)
        (placedDatum n selectedOwner phase.selectedOutput call) (inclusion n) at field
    simpa only [channels] using field
  have chosen := observed_choice exposure.scope traced.binders traced.continuation
    (.actor (selectedOwner, .input phase.selectedInput)) (.actor (selectedOwner, .output phase.selectedOutput))
    (key n selectedOwner phase.selectedInput.port) (placedDatum n selectedOwner phase.selectedOutput call)
    (rename (liftRen (placement n selectedOwner) [.nm]) (inputBody phase.selectedInput call)) guard actualField
  refine ⟨selectedOwner, supplied_unary_endpoint _ _ _ _ exposure
    (assembly_safe registry frame selectedOwner _) ?_ chosen⟩
  exact le_of_eq (assembly_count registry frame selectedOwner)

private theorem selected_matching {Γ : Ctx sig} (n : Nat) (owner : Fin n) (port : Port) :
    onSubject (inclusion (Γ := Γ) n) (Var.succ (key n owner port)) (keyName n owner port) = true := by
  simp only [onSubject, inclusion, keyName, ActiveMarkedNames.nameKey, decide_true]

/-- The simultaneous selected-subject update is this occurrence's actual
next phase, with its pending second field or original continuation retained. -/
theorem release_phase {Γ : Ctx sig} (n : Nat) (owner : Fin n) (phase : Phase) (call : Call Γ) :
    StructuralEq
      (release Var.zero (Var.succ (key n owner phase.selectedInput.port)) (inclusion n)
        (placedDatum n owner phase.selectedOutput call) (placed n owner phase call))
      (rename (placement n owner) (nextContents phase call)) := by
  have channels : phase.selectedOutput.port = phase.selectedInput.port := by cases phase <;> rfl
  have shaped := (contents_selected phase call).rename (placement n owner)
  rw [rename_par] at shaped
  have counted := count_structural Var.zero (Var.succ (key n owner phase.selectedInput.port)) shaped
    (inclusion n) (phase_repFree n owner owner phase.selectedInput.port phase call)
  have updated := release_structural Var.zero (Var.succ (key n owner phase.selectedInput.port)) shaped
    (inclusion n) (placedDatum n owner phase.selectedOutput call)
  have headers : rename (placement n owner) (selectedPair phase call) =
      par (out1 (keyName n owner phase.selectedInput.port) (placedDatum n owner phase.selectedOutput call))
        (inp1 (keyName n owner phase.selectedInput.port)
          (rename (liftRen (placement n owner) [.nm]) (inputBody phase.selectedInput call))) := by
    unfold selectedPair
    rw [rename_par]
    change par (placedOutput n owner phase.selectedOutput call) (placedInput n owner phase.selectedInput call) = _
    rw [output_header, input_header, channels]
  rw [headers] at counted updated
  change count Var.zero (Var.succ (key n owner phase.selectedInput.port)) (inclusion n) (placed n owner phase call) = _ at counted
  rw [own_phase_count] at counted
  simp only [par, inp1, out1, count, selected_matching (Γ := Γ) n owner phase.selectedInput.port, ite_true] at counted
  have zero : count Var.zero (Var.succ (key n owner phase.selectedInput.port)) (inclusion n)
      (rename (placement n owner) (untouched phase call)) = 0 := by omega
  simp only [par, inp1, out1, release, selected_matching (Γ := Γ) n owner phase.selectedInput.port, ite_true] at updated
  rw [show release Var.zero (Var.succ (key n owner phase.selectedInput.port)) (inclusion n)
      (placedDatum n owner phase.selectedOutput call) (rename (placement n owner) (untouched phase call)) =
      rename (placement n owner) (untouched phase call) from release_of_count_zero _ _ _ _ _ zero] at updated
  have fired := ((selected_step_iff phase call _).2 rfl).rename (placement n owner)
  rw [headers] at fired
  have opened := (unary_communication_iff _ _ _ _).1 fired
  rw [← opened] at updated
  have reassembled := (selected_remainder phase call).rename (placement n owner)
  rw [rename_par] at reassembled
  exact .trans updated (.trans
    (.par (.trans (.parComm _ _) (.parUnit _)) (.refl _)) reassembled)

/-- One selected occurrence is advanced; all other occurrences and the
source frame retain their exact process bodies and multiplicity. -/
def updateAssembly {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (owner : Fin n) (frame : Proc Γ) : Proc (World n Γ) :=
  par (parallel ((List.finRange n).map (fun other =>
    if other = owner then rename (placement n other) (nextContents (registry other).phase (registry other).call)
    else placed n other (registry other).phase (registry other).call))) (rename (ambient n) frame)

theorem release_parallel {Ω : Ctx sig} (fresh subject : Var Ω .nm)
    {Γ : Ctx sig} (environment : Ren sig Γ Ω) (datum : Name Γ) (processes : List (Proc Γ)) :
    release fresh subject environment datum (parallel processes) =
      parallel (processes.map (release fresh subject environment datum)) := by
  induction processes with
  | nil => simp only [parallel, nil, release, List.map_nil]
  | cons process rest ih => simp only [parallel, par, release, List.map_cons, ih]

theorem parallel_congr {Γ : Ctx sig} {α : Type} (owners : List α) (before after : α → Proc Γ)
    (equal : ∀ owner ∈ owners, StructuralEq (before owner) (after owner)) :
    StructuralEq (parallel (owners.map before)) (parallel (owners.map after)) := by
  induction owners with
  | nil => exact .refl _
  | cons owner rest ih =>
      exact .par (equal owner (List.mem_cons_self ..))
        (ih (fun other present => equal other (List.mem_cons_of_mem _ present)))

theorem release_assembly {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (owner : Fin n) (frame : Proc Γ) :
    StructuralEq
      (release Var.zero (Var.succ (key n owner (registry owner).phase.selectedInput.port)) (inclusion n)
        (placedDatum n owner (registry owner).phase.selectedOutput (registry owner).call) (assembly registry frame))
      (updateAssembly registry owner frame) := by
  have original := release_structural Var.zero (Var.succ (key n owner (registry owner).phase.selectedInput.port))
    (phaseAssembly_eq registry frame).symm (inclusion n)
    (placedDatum n owner (registry owner).phase.selectedOutput (registry owner).call)
  refine .trans original ?_
  unfold phaseAssembly updateAssembly
  simp only [par, release]
  rw [release_of_count_zero _ _ _ _ _ (frame_count_zero n owner _ frame), release_parallel, List.map_map]
  refine .par ?_ (.refl _)
  apply parallel_congr
  intro other _
  by_cases same : other = owner
  · subst other
    simp only [ite_true]
    exact release_phase n owner (registry owner).phase (registry owner).call
  · simp only [same, ite_false, Function.comp_apply]
    rw [release_of_count_zero _ _ _ _ _ (other_phase_count n other owner same _ (registry other).phase (registry other).call)]
    exact .refl _

/-- Every supplied privately selected step reaches exactly the finite
registry with that occurrence advanced, modulo the existing equations. -/
theorem traced_private_update {Γ : Ctx sig} {n : Nat} (registry : Fin n → Session Γ)
    (frame : Proc Γ) {target : Proc (World n Γ)}
    {exposure : ScopedCommunicationInversion.Exposure (assembly registry frame) target}
    (traced : ActiveMarking.TracedExposure (assemblyMark registry frame) exposure) (owner : Fin n) (port : Port)
    (owned : (ActiveGuardedBodies.inputObservation traced.continuation
      (ActiveGuardedBodies.scopeEnvironment (binderName n) traced.binders (inclusion n))).header.channel =
        Var.succ (key n owner port)) :
    ∃ selectedOwner : Fin n, StructuralEq target (updateAssembly registry selectedOwner frame) := by
  obtain ⟨selectedOwner, supplied⟩ := traced_private_endpoint registry frame traced owner port owned
  exact ⟨selectedOwner, .trans (.symm supplied) (release_assembly registry selectedOwner frame)⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.PrivateUpdate
