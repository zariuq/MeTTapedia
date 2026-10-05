import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeSelection
import Mathlib.Logic.Function.Basic

/-!
# Exact private updates in a mixed tuple runtime

Offered senders, unrelated committed calls and the ordinary source frame
cannot use a selected committed occurrence's private capability. Its enabled
capability has exactly two active prefixes and occurs under no active server.
The existing selected-subject release theorem therefore determines the entire
supplied target, including all untouched offered and committed occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePrivateUpdate

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors RuntimeSelection ScopedActiveFrontier
open ActiveMarking ActiveGuardedBodies ActiveSubjectResidual ActiveSubjectFiring

local instance {Γ : Ctx sig} : DecidableEq (Var Γ .nm) := decEqVar (S := sig)

theorem slot_repFree {Γ : Ctx sig} (n : Nat) (owner selected : Fin n) (port : Port) (slot : Slot Γ) :
    repFree Var.zero (Var.succ (key n selected port)) (StructuralOwnership.inclusion n) (slot.placed n owner) := by
  cases slot with
  | pending phase call => exact PrivateUpdate.phase_repFree n owner selected port phase (loweredCall call)
  | released call =>
      rw [released_placed]
      exact repFree_of_count_zero _ _ _ _ (PrivateUpdate.frame_count_zero n selected port (lower (readback call)))
  | offered channel first second =>
      unfold Slot.placed
      rw [repFree_rename]
      simp only [Slot.template, weaken]
      rw [repFree_rename]
      simp only [par, out1, sendFields, inp1, repFree, true_and]

private theorem different_key {Γ : Ctx sig} (n : Nat) (other selected : Fin n)
    (port : Port) (different : other ≠ selected) : key (Γ := Γ) n other .session ≠ key n selected port := by
  intro same
  exact different (key_injective n other selected .session port same).1

private theorem publication_count {Γ : Ctx sig} (n : Nat) (other selected : Fin n)
    (port : Port) (channel : Name Γ) :
    count Var.zero (Var.succ (key n selected port)) (StructuralOwnership.inclusion n)
      (Actor.render (.publication other channel)) = 0 := by
  cases channel with
  | op op args => cases op
  | var name =>
      simp only [Actor.render, rename, out1, count]
      change (if onSubject (StructuralOwnership.inclusion n) (Var.succ (key n selected port))
        (.var (ambient n .nm name)) then 1 else 0) = 0
      have absent : onSubject (StructuralOwnership.inclusion n) (Var.succ (key n selected port))
          (.var (ambient n .nm name)) = false := by
        apply decide_eq_false_iff_not.mpr
        intro same
        exact key_ne_ambient n selected port name (Var.succ.inj same).symm
      rw [absent]
      simp only [Bool.false_eq_true, ite_false]

private theorem waiter_count {Γ : Ctx sig} (n : Nat) (other selected : Fin n)
    (port : Port) (different : other ≠ selected) (first second : Name Γ) :
    count Var.zero (Var.succ (key n selected port)) (StructuralOwnership.inclusion n)
      (Actor.render (.waiter other first second)) = 0 := by
  change count Var.zero (Var.succ (key n selected port)) (StructuralOwnership.inclusion n)
    (placedInput n other .callback (waiterCall first second)) = 0
  rw [input_header]
  simp only [inp1, count]
  change (if onSubject (StructuralOwnership.inclusion n) (Var.succ (key n selected port))
    (keyName n other .session) then 1 else 0) = 0
  have absent : onSubject (StructuralOwnership.inclusion (Γ := Γ) n) (Var.succ (key n selected port))
      (keyName n other .session) = false := by
    apply decide_eq_false_iff_not.mpr
    intro same
    exact different_key n other selected port different (Var.succ.inj same)
  rw [absent]
  simp only [Bool.false_eq_true, ite_false]

theorem other_slot_count {Γ : Ctx sig} (n : Nat) (other selected : Fin n)
    (different : other ≠ selected) (port : Port) (slot : Slot Γ) :
    count Var.zero (Var.succ (key n selected port)) (StructuralOwnership.inclusion n) (slot.placed n other) = 0 := by
  cases slot with
  | pending phase call => exact PrivateUpdate.other_phase_count n other selected different port phase (loweredCall call)
  | released call =>
      rw [released_placed]
      exact PrivateUpdate.frame_count_zero n selected port (lower (readback call))
  | offered channel first second =>
      have counted := count_structural Var.zero (Var.succ (key n selected port))
        (slot_equation other (.offered channel first second) trivial) (StructuralOwnership.inclusion n)
        (slot_repFree n other selected port (.offered channel first second))
      rw [counted]
      change count _ _ _ (par (Actor.render (.publication other channel))
        (par (Actor.render (.waiter other first second)) nil)) = 0
      simp only [par, nil, count]
      rw [publication_count n other selected port channel,
        waiter_count n other selected port different first second]

theorem registry_repFree {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : Proc Γ)
    (owner : Fin n) (port : Port) :
    repFree Var.zero (Var.succ (key n owner port)) (StructuralOwnership.inclusion n)
      (registryTarget registry frame) := by
  unfold registryTarget
  simp only [par, repFree]
  refine ⟨?_, repFree_of_count_zero _ _ _ _ (PrivateUpdate.frame_count_zero n owner port (lower frame))⟩
  apply PrivateUpdate.parallel_repFree
  intro process member
  obtain ⟨other, _, rfl⟩ := List.mem_map.mp member
  exact slot_repFree n other owner port (registry other)

theorem registry_count {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : Proc Γ)
    (owner : Fin n) (phase : Phase) (call : Call Γ) (committed : registry owner = .pending phase call) :
    count Var.zero (Var.succ (key n owner phase.selectedInput.port)) (StructuralOwnership.inclusion n)
      (registryTarget registry frame) = 2 := by
  unfold registryTarget
  simp only [par, count]
  rw [PrivateUpdate.frame_count_zero n owner phase.selectedInput.port (lower frame), Nat.add_zero]
  rw [PrivateUpdate.parallel_single _ _ _ _ owner _ (List.nodup_finRange n) (List.mem_finRange owner)]
  · rw [committed]
    exact PrivateUpdate.own_phase_count n owner phase (loweredCall call)
  · intro other _ different
    exact other_slot_count n other owner different phase.selectedInput.port (registry other)

theorem assembly_repFree {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : Proc Γ)
    (live : ∀ owner, Live (registry owner)) (owner : Fin n) (port : Port) :
    repFree Var.zero (Var.succ (key n owner port)) (StructuralOwnership.inclusion n)
      (assembly registry frame) :=
  (repFree_structural _ _ (registry_equation registry frame live) (StructuralOwnership.inclusion n)).mp
    (registry_repFree registry frame owner port)

theorem assembly_count {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : Proc Γ)
    (live : ∀ owner, Live (registry owner)) (owner : Fin n) (phase : Phase) (call : Call Γ)
    (committed : registry owner = .pending phase call) :
    count Var.zero (Var.succ (key n owner phase.selectedInput.port)) (StructuralOwnership.inclusion n)
      (assembly registry frame) = 2 :=
  (count_structural _ _ (registry_equation registry frame live) (StructuralOwnership.inclusion n)
    (registry_repFree registry frame owner phase.selectedInput.port)).symm.trans
      (registry_count registry frame owner phase call committed)

theorem traced_endpoint {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (live : ∀ owner, Live (registry owner)) {target : Proc (World n Γ)}
    {exposure : ScopedCommunicationInversion.Exposure (assembly registry (parallel frame)) target}
    (traced : TracedExposure (assemblyMarks registry frame) exposure) (owner : Fin n) (port : Port)
    (owned : (outputObservation traced.continuation
      (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion n))).header.channel =
      Var.succ (key n owner port)) :
    ∃ (selected : Fin n) (phase : Phase) (call : Call Γ), registry selected = .pending phase call ∧
      StructuralEq
        (release Var.zero (Var.succ (key n selected phase.selectedInput.port)) (StructuralOwnership.inclusion n)
          (placedDatum n selected phase.selectedOutput (loweredCall call)) (assembly registry (parallel frame))) target := by
  obtain ⟨selected, phase, call, committed, guard, field⟩ :=
    traced_private_selection registry frame traced owner port owned
  have channels : phase.selectedOutput.port = phase.selectedInput.port := by cases phase <;> rfl
  have actualField : outputObservation traced.continuation
      (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion n)) =
      output1 (.privateActor selected (.output phase.selectedOutput))
        (keyName n selected phase.selectedInput.port) (placedDatum n selected phase.selectedOutput (loweredCall call))
        (StructuralOwnership.inclusion n) := by
    change outputObservation traced.continuation
      (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion n)) =
      output1 (.privateActor selected (.output phase.selectedOutput))
        (keyName n selected phase.selectedOutput.port) (placedDatum n selected phase.selectedOutput (loweredCall call))
        (StructuralOwnership.inclusion n) at field
    simpa only [channels] using field
  have chosen := PrivateUpdate.observed_choice exposure.scope traced.binders traced.continuation
    (.privateActor selected (.input phase.selectedInput)) (.privateActor selected (.output phase.selectedOutput))
    (key n selected phase.selectedInput.port) (placedDatum n selected phase.selectedOutput (loweredCall call))
    (rename (liftRen (placement n selected) [.nm]) (inputBody phase.selectedInput (loweredCall call))) guard actualField
  refine ⟨selected, phase, call, committed, supplied_unary_endpoint _ _ _ _ exposure
    (assembly_repFree registry (parallel frame) live selected _) ?_ chosen⟩
  exact le_of_eq (assembly_count registry (parallel frame) live selected phase call committed)

def advance {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (phase : Phase) (call : Call Γ) : Fin n → Slot Γ :=
  Function.update registry owner (next phase call)

theorem release_registry {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : Proc Γ) (live : ∀ owner, Live (registry owner))
    (owner : Fin n) (phase : Phase) (call : Call Γ) (committed : registry owner = .pending phase call) :
    StructuralEq
      (release Var.zero (Var.succ (key n owner phase.selectedInput.port)) (StructuralOwnership.inclusion n)
        (placedDatum n owner phase.selectedOutput (loweredCall call)) (assembly registry frame))
      (registryTarget (advance registry owner phase call) frame) := by
  have original := release_structural Var.zero (Var.succ (key n owner phase.selectedInput.port))
    (registry_equation registry frame live).symm (StructuralOwnership.inclusion n)
    (placedDatum n owner phase.selectedOutput (loweredCall call))
  refine original.trans ?_
  unfold registryTarget
  simp only [par, release]
  rw [release_of_count_zero _ _ _ _ _ (PrivateUpdate.frame_count_zero n owner _ (lower frame)),
    PrivateUpdate.release_parallel, List.map_map]
  refine .par ?_ (.refl _)
  apply PrivateUpdate.parallel_congr
  intro other _
  by_cases same : other = owner
  · subst other
    simp only [advance, Function.update_self, committed, Function.comp_apply]
    change StructuralEq
      (release Var.zero (Var.succ (key n owner phase.selectedInput.port)) (StructuralOwnership.inclusion n)
        (placedDatum n owner phase.selectedOutput (loweredCall call)) (placed n owner phase (loweredCall call)))
      (rename (placement n owner) (next phase call).template)
    rw [next_template]
    exact PrivateUpdate.release_phase n owner phase (loweredCall call)
  · simp only [advance, Function.update_of_ne same, Function.comp_apply]
    rw [release_of_count_zero _ _ _ _ _ (other_slot_count n other owner same _ (registry other))]
    exact .refl _

theorem actual_private_update {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (live : ∀ owner, Live (registry owner)) {target : Proc (World n Γ)}
    {exposure : ScopedCommunicationInversion.Exposure (assembly registry (parallel frame)) target}
    (traced : TracedExposure (assemblyMarks registry frame) exposure) (owner : Fin n) (port : Port)
    (owned : (outputObservation traced.continuation
      (scopeEnvironment (fun _ => Var.zero) traced.binders (StructuralOwnership.inclusion n))).header.channel =
      Var.succ (key n owner port)) :
    ∃ (selected : Fin n) (phase : Phase) (call : Call Γ), registry selected = .pending phase call ∧
      StructuralEq target (registryTarget (advance registry selected phase call) (parallel frame)) := by
  obtain ⟨selected, phase, call, committed, supplied⟩ := traced_endpoint registry frame live traced owner port owned
  exact ⟨selected, phase, call, committed, supplied.symm.trans
    (release_registry registry (parallel frame) live selected phase call committed)⟩

theorem source_unchanged {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : Proc Γ) (owner : Fin n) (phase : Phase) (call : Call Γ)
    (committed : registry owner = .pending phase call) :
    registrySource (advance registry owner phase call) frame = registrySource registry frame := by
  have each : ∀ other, (advance registry owner phase call other).source = (registry other).source := by
    intro other
    by_cases same : other = owner
    · subst other
      rw [advance, Function.update_self, committed]
      exact RuntimeState.source_unchanged phase call
    · rw [advance, Function.update_of_ne same]
  unfold registrySource
  congr 2
  apply List.map_congr_left
  intro other _
  exact each other

theorem remaining_decreases {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (phase : Phase) (call : Call Γ) (committed : registry owner = .pending phase call) :
    registryRemaining (advance registry owner phase call) + 1 = registryRemaining registry := by
  let rest := (List.finRange n).erase owner
  have permutation : (List.finRange n).Perm (owner :: rest) := List.perm_cons_erase (List.mem_finRange owner)
  have before := (permutation.map (fun other => (registry other).remaining)).sum_eq
  have after := (permutation.map (fun other => (advance registry owner phase call other).remaining)).sum_eq
  have unchanged : rest.map (fun other => (advance registry owner phase call other).remaining) =
      rest.map (fun other => (registry other).remaining) := by
    apply List.map_congr_left
    intro other member
    have different := ((List.nodup_finRange n).mem_erase_iff.mp member).1
    rw [advance, Function.update_of_ne different]
  unfold registryRemaining
  rw [before, after]
  simp only [List.map_cons, List.sum_cons]
  rw [unchanged]
  simp only [advance, Function.update_self, committed]
  have balance := administrative_balance phase call
  omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePrivateUpdate
