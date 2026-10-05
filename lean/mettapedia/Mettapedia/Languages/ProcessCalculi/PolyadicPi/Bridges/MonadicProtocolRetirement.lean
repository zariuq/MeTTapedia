import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolInitialization
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Function.Basic

/-!
# Releasing a continuation without reusing an occurrence identity

A completed session retains its private pair as an unused pair of binders.
The actual released continuation moves into the ordinary frame. The selected
owner is updated in place; every other owner, including an equal call, is
retained. Both comparisons are about the supplied source and closed target
terms, and the completed slot contributes no administrative debt.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Retirement

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open MonadicProtocol.Capabilities MonadicProtocol.Ownership MonadicProtocol.RuntimeState
open MonadicProtocol.Initialization ScopedActiveFrontier

def retired {Γ : Ctx sig} (call : Call Γ) : Slot Γ := .released ⟨call.first, call.second, nil⟩

theorem retired_source {Γ : Ctx sig} (call : Call Γ) : (retired call).source = nil := rfl
theorem retired_remaining {Γ : Ctx sig} (call : Call Γ) : (retired call).remaining = 0 := rfl
theorem retired_closed {Γ : Ctx sig} (call : Call Γ) :
    StructuralEq (retired call).closed nil := by
  have reading : readback (Call.mk call.first call.second nil) = nil := rfl
  have equal := released_entry (Call.mk call.first call.second nil)
  rw [reading, lower_nil] at equal
  exact equal

def registry {Γ : Ctx sig} {n : Nat} (before : Fin n → Slot Γ)
    (owner : Fin n) (call : Call Γ) : Fin n → Slot Γ :=
  Function.update before owner (retired call)

theorem selected_retired {Γ : Ctx sig} {n : Nat} (before : Fin n → Slot Γ)
    (owner : Fin n) (call : Call Γ) : registry before owner call owner = retired call :=
  Function.update_self _ _ _

theorem other_retained {Γ : Ctx sig} {n : Nat} (before : Fin n → Slot Γ)
    (owner other : Fin n) (call : Call Γ) (different : other ≠ owner) :
    registry before owner call other = before other :=
  Function.update_of_ne different _ _

private theorem parallel_map_equal {Γ : Ctx sig} {n : Nat}
    (owners : List (Fin n)) (first second : Fin n → Proc Γ)
    (equal : ∀ owner ∈ owners, first owner = second owner) :
    parallel (owners.map first) = parallel (owners.map second) := by
  rw [List.map_congr_left equal]

/-- Extracting one owner uses the permutation of the finite owner list;
the terms attached to different owners are never compared for equality. -/
theorem move_occurrence {Γ : Ctx sig} {n : Nat}
    (before after : Fin n → Proc Γ) (owner : Fin n) (body : Proc Γ)
    (selected : StructuralEq (before owner) (par body (after owner)))
    (others : ∀ other, other ≠ owner → before other = after other) :
    StructuralEq (parallel ((List.finRange n).map before))
      (par body (parallel ((List.finRange n).map after))) := by
  let rest := (List.finRange n).erase owner
  have exposed : (List.finRange n).Perm (owner :: rest) :=
    List.perm_cons_erase (List.mem_finRange owner)
  have unchanged : parallel (rest.map before) = parallel (rest.map after) := by
    apply parallel_map_equal
    intro other member
    exact others other ((List.nodup_finRange n).mem_erase_iff.mp member).1
  have first := parallel_perm (exposed.map before)
  have last := parallel_perm (exposed.map after)
  simp only [List.map_cons, parallel] at first last
  rw [unchanged] at first
  exact first.trans ((StructuralEq.par selected (.refl _)).trans
    ((StructuralEq.parAssoc _ _ _).trans (.par (.refl _) last.symm)))

private theorem sources_agree_elsewhere {Γ : Ctx sig} {n : Nat}
    (before : Fin n → Slot Γ) (owner other : Fin n) (call : Call Γ)
    (different : other ≠ owner) :
    (before other).source = (registry before owner call other).source := by
  rw [other_retained before owner other call different]

private theorem closed_agree_elsewhere {Γ : Ctx sig} {n : Nat}
    (before : Fin n → Slot Γ) (owner other : Fin n) (call : Call Γ)
    (different : other ≠ owner) :
    (before other).closed = (registry before owner call other).closed := by
  rw [other_retained before owner other call different]

theorem release_source {Γ : Ctx sig} {n : Nat} (before : Fin n → Slot Γ)
    (owner : Fin n) (call : Call Γ) (frame : Proc Γ)
    (released : before owner = .released call) :
    StructuralEq (registrySource before frame)
      (par (registrySource (registry before owner call) frame) (readback call)) := by
  have moved := move_occurrence (fun index => (before index).source)
    (fun index => (registry before owner call index).source) owner (readback call)
    (by rw [released, selected_retired, retired_source]; exact (StructuralEq.parUnit _).symm)
    (fun other different => sources_agree_elsewhere before owner other call different)
  have expose := StructuralEq.par moved (StructuralEq.refl frame)
  exact expose.trans ((StructuralEq.parAssoc _ _ _).trans
    (StructuralEq.parComm _ _))

theorem release_target {Γ : Ctx sig} {n : Nat} (before : Fin n → Slot Γ)
    (owner : Fin n) (call : Call Γ) (frame : Proc Γ)
    (released : before owner = .released call) :
    StructuralEq ((privateScope n).close (registryTarget before frame))
      (par ((privateScope n).close (registryTarget (registry before owner call) frame))
        (lower (readback call))) := by
  have selected : StructuralEq (before owner).closed
      (par (lower (readback call)) (registry before owner call owner).closed) := by
    rw [released, selected_retired]
    exact (released_entry call).trans
      ((StructuralEq.parUnit _).symm.trans (.par (.refl _) (retired_closed call).symm))
  have moved := move_occurrence (fun index => (before index).closed)
    (fun index => (registry before owner call index).closed) owner (lower (readback call)) selected
    (fun other different => closed_agree_elsewhere before owner other call different)
  have original := registry_closed n before frame
  have after := registry_closed n (registry before owner call) frame
  have expose := StructuralEq.par moved (StructuralEq.refl (lower frame))
  refine original.trans (expose.trans ?_)
  exact (StructuralEq.parAssoc _ _ _).trans
    ((StructuralEq.parComm _ _).trans
      (.par after.symm (.refl _)))

theorem release_remaining {Γ : Ctx sig} {n : Nat} (before : Fin n → Slot Γ)
    (owner : Fin n) (call : Call Γ) (released : before owner = .released call) :
    registryRemaining (registry before owner call) = registryRemaining before := by
  have each : ∀ other, (registry before owner call other).remaining = (before other).remaining := by
    intro other
    by_cases same : other = owner
    · subst other
      rw [selected_retired, released]
      rfl
    · rw [other_retained before owner other call same]
  simp only [registryRemaining, each]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Retirement
