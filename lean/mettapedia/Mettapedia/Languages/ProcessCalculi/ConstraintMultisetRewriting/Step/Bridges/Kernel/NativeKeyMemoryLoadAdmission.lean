import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CellCorrespondence
import Mettapedia.Machines.TIsa.X86MemoryFieldLoad

/-!
# Checked admission of the captured proposition field load

The selected edge comes from the actual imported source instruction. Its
checked guard derives the source memory firing used by the existing ten-fetch
native certificate. Source control words are tied to actual entry/exit RIP
observations, and the complete memory-cell readback is retained.

Entry geometry, readiness and image observations remain explicit. The paired
controls reuse the owner's actual public entry fixture. This module does not
infer immutable permission modes from raw CPU execution, implement a sealed
host commit, or identify these word cells with the HOL native-state carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeKeyMemoryLoadAdmission

open Mettapedia.Machines.TIsa Cells CellEffects Control
open _root_.X86Registers X86RegisterRefinement X86Execution

local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Key := X86MemoryView.Key
abbrev Snapshot := CellOccurrences.State Key
abbrev NativeState := X86RegisterRefinement.State

def effect (address : Nat) : Recipe Key :=
  P1Memory.loadRecipe .u64 .word64 0 6 1 8 address

def success (address activation : Nat) (point next : Word) : Edge Key :=
  ⟨activation, point, next, effect address⟩

def edges (address activation : Nat) (point next invalid : Word) : List (Edge Key) :=
  [success address activation point next,
   ⟨activation, point, invalid, P1Memory.boundsFailureRecipe false .word64 0 1 8⟩,
   ⟨activation, point, invalid, P1Memory.loadBooleanFailureRecipe .u64 .word64 0 1 8 address⟩]

theorem captured_edges (address activation : Nat) (point next invalid : Word) :
    (X86P1FieldLoadCapture.image.source.body.atPath
      ([1,1,1,1] ++ List.replicate 7 0 ++ [1])).bind
        (fun statement => match statement with
          | .instruction instruction => P1Memory.memoryEdges? instruction address activation point next invalid
          | _ => none) = some (edges address activation point next invalid) := by
  rw [X86P1FieldLoadCapture.source_instruction]
  rfl

theorem success_at (address activation : Nat) (point next invalid : Word) :
    (edges address activation point next invalid)[0]? = some (success address activation point next) := rfl

theorem effect_outputs (address : Nat) : (effect address).outputs = [.register 6] := rfl

theorem effect_inputs (address : Nat) :
    (effect address).inputs = Memory.capabilityKeys 0 ++ .register 1 :: Memory.byteKeys address 8 := rfl

def scope (view : X86MemoryView.View) (activation : Nat) : Finset (Location Key) :=
  insert (.inl activation) (view.keys.image Sum.inr)

def data (snapshot : Snapshot) : Key → Word := fun key => snapshot.values (.inr key)

def firing (address activation : Nat) (point next invalid : Word) (candidate : Key → Word) :
    CellOccurrences.Firing (edges address activation point next invalid) :=
  ⟨⟨0, by simp [edges]⟩, candidate⟩

theorem firing_edge (address activation : Nat) (point next invalid : Word) (candidate : Key → Word) :
    (firing address activation point next invalid candidate).edge = success address activation point next := rfl

theorem checked_eligible (address activation : Nat) (point next invalid : Word)
    (snapshot : Snapshot) (candidate : Key → Word) (afterValues : Location Key → Word)
    (checked : CheckedAdmission.step? (edges address activation point next invalid) 0
      snapshot.keys snapshot.values candidate = some afterValues) :
    CheckedAdmission.eligible (success address activation point next) snapshot.keys snapshot.values candidate ∧
      afterValues = CheckedAdmission.commit (success address activation point next) snapshot.values candidate := by
  obtain ⟨selected, found, allowed, endpoint⟩ :=
    (CheckedAdmission.step_iff _ 0 _ _ _ _).mp checked
  have same : selected = success address activation point next :=
    Option.some.inj (found.symm.trans (success_at address activation point next invalid))
  subst selected
  exact ⟨allowed, endpoint⟩

theorem checked_occurrence (address activation : Nat) (point next invalid : Word)
    (snapshot : Snapshot) (candidate : Key → Word) (afterValues : Location Key → Word)
    (checked : CheckedAdmission.step? (edges address activation point next invalid) 0
      snapshot.keys snapshot.values candidate = some afterValues) :
    ∃ admitted : (CellOccurrences.step (edges address activation point next invalid)).Admits
        (s := snapshot) (firing address activation point next invalid candidate),
      ((CellOccurrences.step (edges address activation point next invalid)).result
        (firing address activation point next invalid candidate) admitted).values = afterValues := by
  obtain ⟨allowed, endpoint⟩ := checked_eligible address activation point next invalid snapshot candidate afterValues checked
  have admitted : (CellOccurrences.step (edges address activation point next invalid)).Admits
      (s := snapshot) (firing address activation point next invalid candidate) := by
    change CheckedAdmission.eligible (success address activation point next) snapshot.keys snapshot.values candidate
    exact allowed
  refine ⟨admitted, ?_⟩
  rw [CellOccurrences.result_values, firing_edge]
  exact endpoint.symm

theorem checked_data_support (view : X86MemoryView.View) (address activation : Nat)
    (point next invalid : Word) (snapshot : Snapshot) (candidate : Key → Word)
    (afterValues : Location Key → Word) (keys : snapshot.keys = scope view activation)
    (checked : CheckedAdmission.step? (edges address activation point next invalid) 0
      snapshot.keys snapshot.values candidate = some afterValues) :
    (effect address).support ⊆ view.keys := by
  have allowed := (checked_eligible address activation point next invalid snapshot candidate afterValues checked).1
  intro key member
  have lifted : (Sum.inr key : Location Key) ∈ (success address activation point next).recipe.support := by
    simpa [success, Edge.recipe, Recipe.support, Recipe.writes] using member
  have present := allowed.1 lifted
  simpa [keys, scope] using present

theorem checked_data_firing (view : X86MemoryView.View) (address activation : Nat)
    (point next invalid : Word) (snapshot : Snapshot) (candidate : Key → Word)
    (afterValues : Location Key → Word) (keys : snapshot.keys = scope view activation)
    (checked : CheckedAdmission.step? (edges address activation point next invalid) 0
      snapshot.keys snapshot.values candidate = some afterValues) :
    (CellEffects.profile [effect address]).theory.rewrites
      (Cells.encode view.keys (data snapshot))
      (Cells.encode view.keys (fun key => afterValues (.inr key))) := by
  obtain ⟨allowed, endpoint⟩ := checked_eligible address activation point next invalid snapshot candidate afterValues checked
  have projected : (fun key => afterValues (.inr key)) =
      overwrite (effect address).writes (data snapshot) candidate := by
    funext key
    rw [endpoint]
    rfl
  obtain ⟨invocation, enabled, fired⟩ := CellEffects.effect_realized (effect address) view.keys
    (data snapshot) candidate
    (checked_data_support view address activation point next invalid snapshot candidate afterValues keys checked)
    allowed.2.2
  rw [projected]
  exact ⟨ULift.up ⟨0, by simp⟩, invocation, enabled, fired.symm⟩

theorem checked_next (address activation : Nat) (point next invalid : Word)
    (snapshot : Snapshot) (candidate : Key → Word) (afterValues : Location Key → Word)
    (checked : CheckedAdmission.step? (edges address activation point next invalid) 0
      snapshot.keys snapshot.values candidate = some afterValues) :
    afterValues (.inl activation) = next := by
  rw [(checked_eligible address activation point next invalid snapshot candidate afterValues checked).2]
  simp [CheckedAdmission.commit, Edge.finish, success]

theorem checked_mode (view : X86MemoryView.View) (address activation : Nat)
    (point next invalid : Word) (snapshot : Snapshot) (native : NativeState)
    (candidate : Key → Word) (afterValues : Location Key → Word)
    (keys : snapshot.keys = scope view activation)
    (known : ∀ key ∈ view.keys, X86MemoryView.readback view.modes native key = some (data snapshot key))
    (checked : CheckedAdmission.step? (edges address activation point next invalid) 0
      snapshot.keys snapshot.values candidate = some afterValues) :
    view.modes 0 = 1 ∨ view.modes 0 = 2 := by
  have supported := checked_data_support view address activation point next invalid snapshot candidate afterValues keys checked
  have present : Memory.Key.capabilityMode 0 ∈ view.keys := supported (by
    simp [effect, P1Memory.loadRecipe, Recipe.support, Memory.capabilityKeys])
  have observed := known (.capabilityMode 0) present
  have same : view.modes 0 = data snapshot (.capabilityMode 0) := by
    simpa [X86MemoryView.readback] using Option.some.inj observed
  have guarded := (checked_eligible address activation point next invalid snapshot candidate afterValues checked).1.2.2
  have modes := (P1Memory.load_guard_iff .u64 .word64 0 6 1 8 address (data snapshot) candidate).mp guarded
  rw [same]
  exact modes.1

theorem checked_load_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (view : X86MemoryView.View) (snapshot : Snapshot)
    (native : NativeState) (base : Int) (origin : X86LegacyFetch.Basis native)
    (profile : X86Readiness.Profile) (flags : BitVec 32)
    (address activation : Nat) (point next invalid : Word)
    (candidate : Key → Word) (afterValues : Location Key → Word)
    (keys : snapshot.keys = scope view activation)
    (known : ∀ key ∈ view.keys, X86MemoryView.readback view.modes native key = some (data snapshot key))
    (pointAt : point = origin.address.signExtend 64)
    (nextAt : next = (X86Execution.address base 316).signExtend 64)
    (frameArea : X86CanonicalSpan.Area (data snapshot (.register 0)) frameLayout.size)
    (frameAligned : (data snapshot (.register 0)).toNat % 8 = 0)
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (placed : origin.address.toInt = base + 260) (upper : base + 647 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage native base)
    (rangeFits : (data snapshot (.capabilityBase 0)).toNat + (data snapshot (.capabilityLength 0)).toNat < 2 ^ 64)
    (pointerLower : (data snapshot (.capabilityBase 0)).toNat ≤ (data snapshot (.register 1)).toNat)
    (pointerUpper : (data snapshot (.register 1)).toNat ≤
      (data snapshot (.capabilityBase 0)).toNat + (data snapshot (.capabilityLength 0)).toNat)
    (aligned : address % 8 = 0)
    (checked : CheckedAdmission.step? (edges address activation point next invalid) 0
      snapshot.keys snapshot.values candidate = some afterValues) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ admitted : (CellOccurrences.step (edges address activation point next invalid)).Admits
        (s := snapshot) (firing address activation point next invalid candidate),
    ∃ after nextFlags,
      ((CellOccurrences.step (edges address activation point next invalid)).result
        (firing address activation point next invalid candidate) admitted).values = afterValues ∧
      (X86FuelPrefix.fetches 10).run native = .ok () after ∧
      RegisterFrame (insert .r10 X86Bounds.writes) native after ∧
      X86MemoryView.represents view
        (Cells.encode view.keys (fun key => afterValues (.inr key))) after ∧
      native.regs.get? .rip = some (snapshot.values (.inl activation)) ∧
      after.regs.get? .rip = some (afterValues (.inl activation)) ∧
      after.regs.get? .rflags = some nextFlags ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base ∧
      X86ControlFlags.Preserved native after ∧ profile.Holds after := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  have supported := checked_data_support view address activation point next invalid snapshot candidate afterValues keys checked
  have basePresent : Memory.Key.capabilityBase 0 ∈ view.keys := supported (by
    simp [effect, P1Memory.loadRecipe, Recipe.support, Memory.capabilityKeys])
  have lengthPresent : Memory.Key.capabilityLength 0 ∈ view.keys := supported (by
    simp [effect, P1Memory.loadRecipe, Recipe.support, Memory.capabilityKeys])
  have source := checked_data_firing view address activation point next invalid snapshot candidate afterValues keys checked
  obtain ⟨after, nextFlags, run, frame, represented, flagsRead, rip, image, control, stable⟩ :=
    X86MemoryFieldLoad.captured_load_profile other extra vector view (data snapshot) native base origin profile flags
      known basePresent lengthPresent frameArea frameAligned holds flagsKnown quiet placed upper loaded rangeFits
      pointerLower pointerUpper address aligned (Cells.encode view.keys (fun key => afterValues (.inr key))) source
  obtain ⟨admitted, same⟩ := checked_occurrence address activation point next invalid snapshot candidate afterValues checked
  have atPoint := (checked_eligible address activation point next invalid snapshot candidate afterValues checked).1.2.1
  change snapshot.values (.inl activation) = point at atPoint
  have entryRip : native.regs.get? .rip = some (snapshot.values (.inl activation)) := by
    rw [atPoint, pointAt]
    exact origin.rip
  have afterRip : after.regs.get? .rip = some (afterValues (.inl activation)) := by
    rw [checked_next address activation point next invalid snapshot candidate afterValues checked, nextAt]
    exact rip
  exact ⟨admitted, after, nextFlags, same, run, frame, represented, entryRip, afterRip,
    flagsRead, image, control, stable⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeKeyMemoryLoadAdmission
