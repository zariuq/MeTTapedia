import Mettapedia.Machines.TIsa.X86Prefix

/-!
# Byte-read facts for the pinned Sail fetch path

The range lemma unfolds the imported inclusive loop rather than replacing
the model's byte-read implementation. The rb lemmas retain canonical-address
checks, app-view selection and error propagation. Ordinary sequential memory
gives successful reads and missing-byte faults, with state preservation.

The model's app-view path uses its 52-bit physical-address convention.
Linking those indices to native virtual addresses and composing the complete
instruction-fetch/decode operation remain separate refinement obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2_000_000

namespace Mettapedia.Machines.TIsa.X86FetchMemory

open _root_.X86Registers X86RegisterRefinement X86Move

theorem singleton_range {β : Type} (initial : β) (body : Int → β → SailM (ForInStep β)) :
    IntRange.forIn' { start := 0, stop := 0 } initial (fun index _ => body index) =
      (do
        let step ← body 0 initial
        match step with
        | .done value => pure value
        | .yield value => pure value) := by
  let range : IntRange := { start := 0, stop := 0 }
  have finish (value : β) (aligned : ((1 : Int) - range.start) % range.step = 0) :
      IntRange.forIn'.loop range (fun index _ => body index) value 1 aligned = pure value := by
    rw [IntRange.forIn'.loop.eq_1]
    rfl
  unfold IntRange.forIn'
  rw [IntRange.forIn'.loop.eq_1]
  change (do
    let step ← body 0 initial
    match step with
    | .done value => pure value
    | .yield value => IntRange.forIn'.loop range (fun index _ => body index) value 1 _) = _
  simp only [finish]

theorem log_memory_read_exact (state : State) (pointer : Word) (address : BitVec 52)
    (byte : BitVec 8) (known : state.regs.get? .rip = some pointer) :
    (Functions.log_memory_read address 1 byte).run state = .ok () state := by
  unfold Functions.log_memory_read Functions.read_rip
  rw [run_bind, run_bind, readRegister_exact, known]
  rfl

theorem singleton_yield {β : Type} (initial : β) (body : Int → β → SailM β) :
    IntRange.forIn' { start := 0, stop := 0 } initial (fun index _ value => do
      pure (.yield (← body index value))) = body 0 initial := by
  rw [singleton_range]
  simp only [bind_assoc, pure_bind, bind_pure]

theorem forIn_singleton_yield {β : Type} (initial : β) (body : Int → β → SailM β) :
    ForIn.forIn ({ start := 0, stop := 0 } : IntRange) initial (fun index value => do
      pure (.yield (← body index value))) = body 0 initial := by
  change IntRange.forIn' _ _ _ = _
  exact singleton_yield initial body

theorem forIn_singleton {β : Type} (initial : β) (body : Int → β → SailM (ForInStep β)) :
    forIn ({ start := 0, stop := 0 } : IntRange) initial body = (do
      let step ← body 0 initial
      match step with
      | .done value => pure value
      | .yield value => pure value) := by
  change IntRange.forIn' _ _ _ = _
  exact singleton_range initial body

theorem update_byte (byte : BitVec 8) :
    Sail.BitVec.updateSubrange (0#8) 7 0 byte = byte := by
  revert byte
  decide

theorem rb_one_unfold [MemoryPrimitives] (address : BitVec 64) (access : String) :
    Functions.rb 1 address access = (do
      if !(← Functions.canonical_address_p address.toInt) then
        Functions.x86_model_error "rb: non-canonical address"
      else pure ()
      let linear := Functions.sail_mask_signed 48 address
      let physical ← if (← readReg .app_view) then pure (Functions.sail_mask_signed 52 linear)
        else Functions.ia32e_la_to_pa linear access
      Functions.memi physical) := by
  simp only [Functions.rb, bind_pure]
  change forIn ({ start := 0, stop := 0 } : IntRange) (0#8) _ = _
  rw [forIn_singleton]
  simp only [bind_assoc, pure_bind]
  simp [Sail.BitVec.addInt, update_byte, -bind_pure_comp]
  funext state
  change EStateM.run _ state = EStateM.run _ state
  simp only [run_bind]
  cases canonical : (Functions.canonical_address_p address.toInt).run state with
  | error error after => rfl
  | ok isCanonical after =>
    cases isCanonical
    · rfl
    · simp only [Bool.true_eq_false, ite_false, run_bind, run_pure]
      cases application : (readReg Register.app_view).run after with
      | error error next => rfl
      | ok app next =>
        cases app
        · simp only [Bool.false_eq_true, ite_false, run_bind]
          cases physical : (Functions.ia32e_la_to_pa (Functions.sail_mask_signed 48 address) access).run next with
          | error error afterPhysical => rfl
          | ok physicalAddress afterPhysical =>
            dsimp only
            cases byte : (Functions.memi physicalAddress).run afterPhysical <;>
              rfl
        · simp only [ite_true, run_pure]
          cases byte : (Functions.memi
            (Functions.sail_mask_signed 52 (Functions.sail_mask_signed 48 address))).run next <;>
            rfl

local instance : MemoryPrimitives := X86Memory.ordinary

theorem mask52_toNat (address : BitVec 52) :
    (Functions.sail_mask 64 address).toNat = address.toNat := by
  simp [Functions.sail_mask, Sail.BitVec.length, Sail.BitVec.zeroExtend]
  have bound := BitVec.isLt address
  omega

theorem memi_exact (state : State) (pointer : Word) (address : BitVec 52) (byte : BitVec 8)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? address.toNat = some byte) :
    (Functions.memi address).run state = .ok byte state := by
  have memory : (X86Memory.ordinary.read .Read_plain 64 (Functions.sail_mask 64 address) 1).run state =
      .ok byte state := by
    apply X86Memory.read_one
    simpa only [mask52_toNat] using present
  unfold Functions.memi
  rw [run_bind, memory]
  change (do
    Functions.log_memory_read address 1 byte
    pure byte : SailM (BitVec 8)).run state = _
  rw [run_bind, log_memory_read_exact state pointer address byte rip]
  rfl

theorem read_one_outcome (state : State) (address : BitVec 64) :
    (X86Memory.ordinary.read .Read_plain 64 address 1).run state =
      match state.mem.get? address.toNat with
      | some byte => .ok byte state
      | none => .error (.OutOfMemoryRange address.toNat) state := by
  change (do
    let (value, _) ← Sail.ConcurrencyInterfaceV1.PreSail.readBytes 1 address.toNat
    pure value : SailM (BitVec 8)).run state = _
  have action : (Sail.ConcurrencyInterfaceV1.PreSail.readBytes 1 address.toNat :
      SailM (BitVec 8 × Option Bool)) = (do
    let byte ← Sail.ConcurrencyInterfaceV1.PreSail.readByte address.toNat
    pure (byte, none)) := rfl
  rw [run_bind, action, run_bind, X86Memory.readByte_exact]
  cases state.mem.get? address.toNat <;> rfl

theorem memi_missing (state : State) (address : BitVec 52)
    (missing : state.mem.get? address.toNat = none) :
    (Functions.memi address).run state = .error (.OutOfMemoryRange address.toNat) state := by
  unfold Functions.memi
  rw [run_bind, read_one_outcome, mask52_toNat, missing]

theorem narrow_pointer (address : BitVec 48) :
    Functions.sail_mask_signed 48 (address.signExtend 64) = address := by
  simp [Functions.sail_mask_signed, Sail.BitVec.length, Sail.BitVec.truncate]
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  have wide : index < 64 := by omega
  simp [bound, wide, BitVec.getElem_signExtend]

theorem widen_physical (address : BitVec 48) :
    Functions.sail_mask_signed 52 address = address.signExtend 52 := by
  simp [Functions.sail_mask_signed, Sail.BitVec.length, Sail.BitVec.signExtend]

theorem rb_one_app_view (state : State) (address : BitVec 48) (access : String)
    (application : state.regs.get? .app_view = some true) :
    (Functions.rb 1 (address.signExtend 64) access).run state =
      (Functions.memi (address.signExtend 52)).run state := by
  rw [rb_one_unfold, run_bind]
  have canonical : (Functions.canonical_address_p (address.signExtend 64).toInt).run state =
      .ok true state := by
    simpa only [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64)] using canonical48 state address
  rw [canonical]
  change (do
    let app ← readReg .app_view
    let physical ← if app then pure (Functions.sail_mask_signed 52
      (Functions.sail_mask_signed 48 (address.signExtend 64))) else
      Functions.ia32e_la_to_pa (Functions.sail_mask_signed 48 (address.signExtend 64)) access
    Functions.memi physical : SailM (BitVec 8)).run state = _
  rw [run_bind, readRegister_exact, application]
  simp only [narrow_pointer, widen_physical]
  change (Functions.memi (address.signExtend 52)).run state = _
  rfl

theorem rb_one_exact (state : State) (pointer : Word) (address : BitVec 48)
    (byte : BitVec 8) (access : String)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? (address.signExtend 52).toNat = some byte) :
    (Functions.rb 1 (address.signExtend 64) access).run state = .ok byte state := by
  rw [rb_one_app_view state address access application]
  exact memi_exact state pointer _ byte rip present

theorem rb_one_missing (state : State) (address : BitVec 48) (access : String)
    (application : state.regs.get? .app_view = some true)
    (missing : state.mem.get? (address.signExtend 52).toNat = none) :
    (Functions.rb 1 (address.signExtend 64) access).run state =
      .error (.OutOfMemoryRange (address.signExtend 52).toNat) state := by
  rw [rb_one_app_view state address access application]
  exact memi_missing state _ missing

namespace Controls

private def mapped : State :=
  ⟨((∅ : Std.ExtDHashMap Register RegisterType).insert .app_view true).insert .rip (0x1000#64),
    (), (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (0x89#8), (), 0, #[]⟩

theorem read_opcode : (Functions.rb 1 (0x1000#64) ":X").run mapped =
    .ok (0x89#8) mapped := by
  apply rb_one_exact mapped (0x1000#64) (0x1000#48) (0x89#8) ":X"
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped]
  · simp [mapped]

theorem wrong_opcode_refused : (Functions.rb 1 (0x1000#64) ":X").run mapped ≠
    .ok (0x88#8) mapped := by
  rw [read_opcode]
  intro wrong
  have bytes := (EStateM.Result.ok.inj wrong).1
  exact (by decide : (0x89#8) ≠ (0x88#8)) bytes

private def unmapped : State := { mapped with mem := ∅ }

theorem missing_opcode : (Functions.rb 1 (0x1000#64) ":X").run unmapped =
    .error (.OutOfMemoryRange 4096) unmapped := by
  apply rb_one_missing unmapped (0x1000#48) ":X"
  · simp [unmapped, mapped, Std.ExtDHashMap.get?_insert]
  · simp [unmapped]

end Controls


end Mettapedia.Machines.TIsa.X86FetchMemory
