import Mettapedia.Machines.TIsa.X86P1InvalidCapture
import Mettapedia.Machines.TIsa.CheckedAdmission

/-!
# Source bounds failure related to the actual proposition call

The source instruction at path [0,0] supplies its real memory edges. The
failure guard uses the existing capability and pointer cells, and has no data
outputs. Its exact resource transition changes only the selected control cell.

For nonwrapping capabilities and typed in-region pointers, failed access is
equivalent to the emitted bounds condition. Matching source observations and
the original loaded-image/ABI entry facts therefore derive the actual
twenty-seven/twenty-nine-fetch invalid-input allowance call, both outcome words,
the republished receipt, register restoration and image preservation. No native execution or result-correctness
premise is supplied. Resource data cells and host receipt bytes remain separate
observations; this theorem does not identify those two memories globally.

Other load/store failures, source admission, host publication and the complete
consumer/compiler theorems remain open.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1BoundsFailureSource
open Cells CellEffects Control
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

theorem access_zero_iff (base length pointer : Word) (width result : Nat)
    (fits : base.toNat + length.toNat < 2 ^ 64) (lower : base.toNat ≤ pointer.toNat)
    (upper : pointer.toNat ≤ base.toNat + length.toNat) :
    Memory.access? base length pointer 0 width = some result ↔
      (pointer - base).toNat + width ≤ length.toNat ∧ result = pointer.toNat := by
  have observed := P1Memory.access?_iff_inside base length pointer (0#32) width result fits lower upper
  have subtract : (pointer - base).toNat = pointer.toNat - base.toNat :=
    BitVec.toNat_sub_of_le (by exact lower)
  change Memory.access? base length pointer 0 width = some result ↔
    (base.toNat : Int) ≤ (pointer.toNat : Int) + 0 ∧
      (pointer.toNat : Int) + 0 + width ≤ (base.toNat : Int) + length.toNat ∧
      result = ((pointer.toNat : Int) + 0).toNat at observed
  rw [observed,subtract]
  simp only [Int.add_zero,Int.toNat_natCast]
  constructor <;> rintro ⟨first,rest⟩ <;> omega

theorem access_none_iff (base length pointer : Word) (width : Nat)
    (fits : base.toNat + length.toNat < 2 ^ 64) (lower : base.toNat ≤ pointer.toNat)
    (upper : pointer.toNat ≤ base.toNat + length.toNat) :
    Memory.access? base length pointer 0 width = none ↔
      ¬ (pointer - base).toNat + width ≤ length.toNat := by
  constructor
  · intro empty valid
    have accepted := (access_zero_iff base length pointer width pointer.toNat fits lower upper).mpr ⟨valid,rfl⟩
    rw [empty] at accepted
    contradiction
  · intro outside
    cases computed : Memory.access? base length pointer 0 width with
    | none => rfl
    | some result => exact False.elim (outside ((access_zero_iff base length pointer width result fits lower upper).mp computed).1)

def failure (activation : Nat) (point invalid : Word) : Edge P1Memory.Key :=
  ⟨activation,point,invalid,P1Memory.boundsFailureRecipe false .word32 0 1 0⟩

theorem captured_failure (activation address : Nat) (point next invalid : Word) :
    (X86P1LoadCapture.propImage.source.body.atPath [0,0]).bind
      (fun statement => match statement with
        | .instruction instruction => P1Memory.memoryEdges? instruction address activation point next invalid
        | _ => none) =
      some [⟨activation,point,next,P1Memory.loadRecipe .u32z .word32 0 6 1 0 address⟩,
        failure activation point invalid,
        ⟨activation,point,invalid,P1Memory.loadBooleanFailureRecipe .u32z .word32 0 1 0 address⟩] := by
  rw [X86P1LoadCapture.source_instruction]
  rfl

theorem guard_iff (before after : Location P1Memory.Key → Word) (activation : Nat) (point invalid : Word) :
    (failure activation point invalid).effect.guard
      ((failure activation point invalid).effect.inputs.map (fun key => before (.inr key)))
      ((failure activation point invalid).effect.outputs.map (fun key => after (.inr key))) = true ↔
      (before (.inr (.capabilityMode 0)) = 1 ∨ before (.inr (.capabilityMode 0)) = 2) ∧
        Memory.access? (before (.inr (.capabilityBase 0))) (before (.inr (.capabilityLength 0)))
          (before (.inr (.register 1))) 0 4 = none :=
  P1Memory.bounds_failure_guard_iff false .word32 0 1 0
    (fun key => before (.inr key)) (fun key => after (.inr key))

theorem guarded_transition (activation : Nat) (point invalid : Word)
    (keys : Finset (Location P1Memory.Key)) (before : Location P1Memory.Key → Word)
    (included : (failure activation point invalid).recipe.support ⊆ keys)
    (atPoint : before (.inl activation) = point)
    (mode : before (.inr (.capabilityMode 0)) = 1 ∨ before (.inr (.capabilityMode 0)) = 2)
    (rejected : Memory.access? (before (.inr (.capabilityBase 0))) (before (.inr (.capabilityLength 0)))
      (before (.inr (.register 1))) 0 4 = none) :
    (edgeProgram [failure activation point invalid]).theory.rewrites (encode keys before)
      (encode keys (Function.update before (.inl activation) invalid)) := by
  let selected := failure activation point invalid
  have guarded := (Edge.guard_iff selected before (Function.update before (.inl activation) invalid)).mpr
    ⟨atPoint,by simp [selected,failure],(guard_iff before _ activation point invalid).mpr ⟨mode,rejected⟩⟩
  obtain ⟨invocation,enabled,endpoint⟩ := selected.readonly_realized rfl keys before
    (Function.update before (.inl activation) invalid) included guarded
  exact ⟨ULift.up ⟨0,by simp⟩,invocation,enabled,endpoint.symm⟩

theorem source_iff_native_bounds {state : State} {layout : X86Bounds.Layout}
    (facts : X86Bounds.Facts layout state) (before : Location P1Memory.Key → Word)
    (baseKnown : before (.inr (.capabilityBase 0)) = facts.base)
    (lengthKnown : before (.inr (.capabilityLength 0)) = facts.length)
    (pointerKnown : before (.inr (.register 1)) = facts.pointer)
    (fits : facts.base.toNat + facts.length.toNat < 2 ^ 64)
    (lower : facts.base.toNat ≤ facts.pointer.toNat)
    (upper : facts.pointer.toNat ≤ facts.base.toNat + facts.length.toNat) :
    Memory.access? (before (.inr (.capabilityBase 0))) (before (.inr (.capabilityLength 0)))
      (before (.inr (.register 1))) 0 4 = none ↔
        ¬ (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat := by
  rw [baseKnown,lengthKnown,pointerKnown]
  exact access_none_iff facts.base facts.length facts.pointer 4 fits lower upper

theorem failure_transition_iff (activation : Nat) (point invalid : Word)
    (keys : Finset (Location P1Memory.Key)) (before : Location P1Memory.Key → Word)
    (result : Multiset (Cell (Location P1Memory.Key))) :
    (edgeProgram [failure activation point invalid]).theory.rewrites (encode keys before) result ↔
      (failure activation point invalid).recipe.support ⊆ keys ∧ before (.inl activation) = point ∧
      (before (.inr (.capabilityMode 0)) = 1 ∨ before (.inr (.capabilityMode 0)) = 2) ∧
      Memory.access? (before (.inr (.capabilityBase 0))) (before (.inr (.capabilityLength 0)))
        (before (.inr (.register 1))) 0 4 = none ∧
      result = encode keys (Function.update before (.inl activation) invalid) := by
  rw [edgeProgram_rewrite_iff]
  constructor
  · rintro ⟨selected,member,after,included,pointKnown,_,guarded,rfl⟩
    have selectedEq : selected = failure activation point invalid := List.mem_singleton.mp member
    subst selected
    obtain ⟨mode,rejected⟩ := (guard_iff before after activation point invalid).mp guarded
    exact ⟨included,pointKnown,mode,rejected,by rw [Edge.finish_of_no_outputs _ rfl]; rfl⟩
  · rintro ⟨included,pointKnown,mode,rejected,rfl⟩
    refine ⟨failure activation point invalid,by simp,Function.update before (.inl activation) invalid,
      included,pointKnown,by simp [failure],?_,?_⟩
    · exact (guard_iff before _ activation point invalid).mpr ⟨mode,rejected⟩
    · rw [Edge.finish_of_no_outputs _ rfl]
      rfl

theorem admitted_failure_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (call : X86AllowanceCall.Inputs state) (base : Int)
    (entryAt : call.prologue.code.toInt = base) (exitAt : call.exit = address base 619)
    (upper : base + 647 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base)
    {layout : X86Bounds.Layout} (pointerIs : layout.pointer = 6) (regionIs : layout.region = 0)
    (facts : X86Bounds.Facts layout state) (receipt : X86FailureHandler.FrameFacts state)
    (imageSpillApart : ∀ index < X86P1LoadCapture.propImage.size,
      ((address base index).signExtend 52).toNat ∉ X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (imageBodyApart : X86P1RefusedCapture.ImageApart receipt base)
    (imageReceiptApart : ∀ index < X86P1LoadCapture.propImage.size,
      ((address base index).signExtend 52).toNat ∉ X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (baseSpillApart : ∀ byte < 8, ((address facts.baseAddress.toInt byte).signExtend 52).toNat ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (lengthSpillApart : ∀ byte < 8, ((address facts.lengthAddress.toInt byte).signExtend 52).toNat ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (statusReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress receipt.statusAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (resultReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress receipt.resultAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (budgetBodyApart : ∀ byte < 8, X86WriteWords.physicalAddress call.fuel.budgetAddress byte ∉
      X86P1RefusedCapture.writes receipt)
    (bottomApart : ∀ byte < 8, X86WriteWords.physicalAddress call.bottom byte ∉
      X86P1RefusedCapture.writes receipt ∪ X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (savedApart : ∀ slot : Fin 6, ∀ byte < 8,
      X86WriteWords.physicalAddress (address call.prologue.bottom.toInt (8 * slot.val)) byte ∉
        X86P1RefusedCapture.writes receipt ∪ X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (rangeFits : facts.base.toNat + facts.length.toNat < 2 ^ 64)
    (pointerLower : facts.base.toNat ≤ facts.pointer.toNat)
    (pointerUpper : facts.pointer.toNat ≤ facts.base.toNat + facts.length.toNat)
    (activation : Nat) (point invalid : Word) (keys : Finset (Location P1Memory.Key))
    (before : Location P1Memory.Key → Word)
    (baseKnown : before (.inr (.capabilityBase 0)) = facts.base)
    (lengthKnown : before (.inr (.capabilityLength 0)) = facts.length)
    (pointerKnown : before (.inr (.register 1)) = facts.pointer)
    (result : Multiset (Cell (Location P1Memory.Key)))
    (transition : (edgeProgram [failure activation point invalid]).theory.rewrites (encode keys before) result) :
    letI : OtherOpcodeHandlers := X86P1RefusedCapture.callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    result = encode keys (Function.update before (.inl activation) invalid) ∧
      ∃ body after, (X86FuelPrefix.fetches (8 + (X86P1InvalidCapture.guardSteps facts.length + 4) + 10)).run state =
          .ok () after ∧
        X86AllowanceCall.Result call (X86P1RefusedCapture.writes receipt) (call.fuel.budget - call.fuel.receipt) body after ∧
        lookup after 0 = some ExitStatus.invalidInput.word ∧
        (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.statusAddress byte) =
          some (ExitStatus.invalidInput.word.extractLsb' (8 * byte) 8)) ∧
        (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.resultAddress byte) =
          some (ExitStatus.invalidInput.word.extractLsb' (8 * byte) 8)) ∧
        (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress call.fuel.receiptAddress byte) =
          some (call.fuel.receipt.extractLsb' (8 * byte) 8)) ∧
        X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := X86P1RefusedCapture.callHandlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨_,_,_,rejected,same⟩ := (failure_transition_iff activation point invalid keys before result).mp transition
  have outside := (source_iff_native_bounds facts before baseKnown lengthKnown pointerKnown
    rangeFits pointerLower pointerUpper).mp rejected
  exact ⟨same,X86P1InvalidCapture.public_invalid other extra vector state call base entryAt exitAt upper loaded
    pointerIs regionIs facts receipt imageSpillApart imageBodyApart imageReceiptApart baseSpillApart lengthSpillApart
    statusReceiptApart resultReceiptApart budgetBodyApart bottomApart savedApart outside⟩

namespace Controls
def world : Location P1Memory.Key → Word
  | .inl _ => 9
  | .inr (.capabilityBase 0) => 12288
  | .inr (.capabilityLength 0) => 32
  | .inr (.capabilityMode 0) => 1
  | .inr (.register 1) => 12320
  | _ => 99
def keys : Finset (Location P1Memory.Key) :=
  {.inl 0,.inr (.capabilityBase 0),.inr (.capabilityLength 0),.inr (.capabilityMode 0),.inr (.register 1)}

theorem end_pointer_fires :
    (edgeProgram [failure 0 9 607]).theory.rewrites (encode keys world)
      (encode keys (Function.update world (.inl 0) 607)) :=
  guarded_transition 0 9 607 keys world (by decide) rfl (Or.inl rfl) (by decide)

theorem legal_pointer_refused :
    CheckedAdmission.step? [failure 0 9 607] 0 keys (Function.update world (.inr (.register 1)) (12288#64))
      (fun _ => 99) = none := by decide

theorem missing_capability_refused :
    CheckedAdmission.step? [failure 0 9 607] 0 (keys.erase (.inr (.capabilityMode 0))) world
      (fun _ => 99) = none := by decide

theorem wrong_mode_refused :
    CheckedAdmission.step? [failure 0 9 607] 0 keys (Function.update world (.inr (.capabilityMode 0)) (0#64))
      (fun _ => 99) = none := by decide

theorem end_access_rejected : Memory.access? (12288#64) (32#64) (12320#64) 0 4 = none := by decide
theorem last_word_accessible : Memory.access? (12288#64) (32#64) (12316#64) 0 4 = some 12316 := by decide
theorem no_write_effect : (failure 0 24 590).effect.outputs = [] := rfl

theorem accepted_load_excludes_failure (address : Nat) (after : P1Memory.Key → Word) :
    ¬ (P1Memory.loadRecipe .u32z .word32 0 6 1 0 address).guard
      ((P1Memory.loadRecipe .u32z .word32 0 6 1 0 address).inputs.map (fun key => world (.inr key)))
      ((P1Memory.loadRecipe .u32z .word32 0 6 1 0 address).outputs.map after) = true := by
  intro accepted
  obtain ⟨_,access,_⟩ := (P1Memory.load_guard_iff .u32z .word32 0 6 1 0 address _ after).mp accepted
  change Memory.access? (12288#64) (32#64) (12320#64) 0 4 = some address at access
  rw [end_access_rejected] at access
  contradiction
end Controls

#print axioms access_none_iff
#print axioms captured_failure
#print axioms guarded_transition
#print axioms failure_transition_iff
#print axioms admitted_failure_executes
#print axioms Controls.end_pointer_fires
end Mettapedia.Machines.TIsa.X86P1BoundsFailureSource
