import Mettapedia.Machines.TIsa.X86FetchModel

/-!
# Arithmetic results from the pinned Sail x86 primitives

The original population-count body receives a checked absolute-value
termination measure. The imported ADD, SUB, OR, AND and XOR implementations
are then related to the portable 64-bit operations, including state
preservation and wraparound. Result projection is inverted to obtain actual
primitive executions. Instruction decoding, flag-specific contracts and
complete native templates remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2_000_000

namespace Mettapedia.Machines.TIsa.X86Alu

open _root_.X86Registers X86RegisterRefinement

theorem complement_rank (value : Int) (negative : value < 0) :
    (Functions.lognot_int value).natAbs < value.natAbs := by
  unfold Functions.lognot_int
  change (-value - 1).natAbs < value.natAbs
  cases value with
  | ofNat number =>
    change (number : Int) < 0 at negative
    omega
  | negSucc number =>
    have complement : -(Int.negSucc number) - 1 = (number : Int) := by omega
    rw [complement]
    simp

theorem positive_half_rank (value : Int) (positive : 0 < value) :
    (Sail.Int.shiftr value 1).natAbs < value.natAbs := by
  have shift : Sail.Int.shiftr value 1 = value / 2 := rfl
  rw [shift]
  have bound := SailInteger.half_abs_decreases value (by omega) (by omega)
  rw [SailInteger.floorFromTrunc_positive value 2 (by decide)] at bound
  exact bound

end Mettapedia.Machines.TIsa.X86Alu

tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/AluFunctions.lean.inc"
  sha256 "222ee9a4cd217ff0d7c75de008c8c7ffc52d5d3d942f5b724ecca43d7b64be5b"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]

namespace Mettapedia.Machines.TIsa.X86Alu

open _root_.X86Registers X86RegisterRefinement

theorem setWidth_ofInt (width original : Nat) (value : Int) (small : width ≤ original) :
    (BitVec.ofInt original value).setWidth width = BitVec.ofInt width value := by
  cases value with
  | ofNat number =>
    simpa only [Int.ofNat_eq_natCast, BitVec.ofInt_natCast] using BitVec.setWidth_ofNat_of_le small number
  | negSucc number =>
    rw [BitVec.ofInt_negSucc_eq_not_ofNat, BitVec.setWidth_not small,
      BitVec.setWidth_ofNat_of_le small, BitVec.ofInt_negSucc_eq_not_ofNat]

theorem bits_of_int_eq (width : Nat) (value : Int) :
    Functions.bits_of_int value width = BitVec.ofInt width value := by
  unfold Functions.bits_of_int Sail.get_slice_int
  rw [Nat.zero_add]
  rw [← BitVec.setWidth_eq_extractLsb' (by omega : width ≤ width + 1)]
  exact setWidth_ofInt width (width + 1) value (by omega)

theorem add_result (left right : Word) :
    Sail.BitVec.truncate
      (Functions.bits_of_int (Sail.BitVec.toNatInt left + Sail.BitVec.toNatInt right) 65) 64 =
        left + right := by
  rw [bits_of_int_eq]
  change (BitVec.ofInt 65 _).setWidth 64 = _
  rw [setWidth_ofInt 64 65 _ (by decide), BitVec.ofInt_add]
  simp [Sail.BitVec.toNatInt]

theorem sub_result (left right : Word) :
    Sail.BitVec.truncate (Functions.bits_of_int (left.toInt - right.toInt) 65) 64 =
      left - right := by
  rw [bits_of_int_eq]
  change (BitVec.ofInt 65 _).setWidth 64 = _
  rw [setWidth_ofInt 64 65 _ (by decide)]
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg]
  simp only [BitVec.ofInt_toInt, BitVec.sub_eq_add_neg]

theorem full_extract (value : Word) : Sail.BitVec.extractLsb value 63 0 = value := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb]

theorem add_value (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => value.1) <$>
      Functions.gpr_add_spec_8 left right flags).run state = .ok (left + right) state := by
  unfold Functions.gpr_add_spec_8 Functions.cf_spec64 Functions.pf_spec64 Functions.of_spec64
  unfold Functions.unsigned_byte_p_int Functions.signed_byte_p_int Functions.logbitp_int
  simp only [map_eq_pure_bind, run_bind, run_pure, run_assert]
  change (EStateM.Result.ok (Sail.BitVec.truncate
    (Functions.bits_of_int (Sail.BitVec.toNatInt left + Sail.BitVec.toNatInt right) 65) 64) state :
      EStateM.Result (Sail.Error exception) State Word) = _
  rw [add_result]

theorem sub_value (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => value.1) <$>
      Functions.gpr_sub_spec_8 left right flags).run state = .ok (left - right) state := by
  unfold Functions.gpr_sub_spec_8 Functions.pf_spec64 Functions.of_spec64
  unfold Functions.signed_byte_p_int Functions.logbitp_int
  simp only [map_eq_pure_bind, run_bind, run_pure, run_assert]
  change (EStateM.Result.ok (Sail.BitVec.truncate
    (Functions.bits_of_int (left.toInt - right.toInt) 65) 64) state :
      EStateM.Result (Sail.Error exception) State Word) = _
  rw [sub_result]

theorem or_value (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => value.1) <$>
      Functions.gpr_or_spec_8 left right flags).run state = .ok (left ||| right) state := by
  unfold Functions.gpr_or_spec_8 Functions.pf_spec64 Functions.logbitp_int
  simp only [map_eq_pure_bind, run_bind, run_pure, run_assert]
  change (EStateM.Result.ok (Sail.BitVec.extractLsb (left ||| right) 63 0) state :
      EStateM.Result (Sail.Error exception) State Word) = _
  rw [full_extract]

theorem and_value (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => value.1) <$>
      Functions.gpr_and_spec_8 left right flags).run state = .ok (left &&& right) state := by
  unfold Functions.gpr_and_spec_8 Functions.pf_spec64 Functions.logbitp_int
  simp only [map_eq_pure_bind, run_bind, run_pure, run_assert]
  change (EStateM.Result.ok (Sail.BitVec.extractLsb (left &&& right) 63 0) state :
      EStateM.Result (Sail.Error exception) State Word) = _
  rw [full_extract]

theorem xor_value (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => value.1) <$>
      Functions.gpr_xor_spec_8 left right flags).run state = .ok (left ^^^ right) state := by
  unfold Functions.gpr_xor_spec_8 Functions.logxor Functions.pf_spec64 Functions.logbitp_int
  simp only [map_eq_pure_bind, run_bind, run_pure, run_assert]
  change (EStateM.Result.ok (Sail.BitVec.extractLsb (left ^^^ right) 63 0) state :
      EStateM.Result (Sail.Error exception) State Word) = _
  rw [full_extract]

theorem project_result_reflects (action : SailM (Word × BitVec 32 × BitVec 32))
    (state after : State) (value : Word)
    (observed : ((fun result : Word × BitVec 32 × BitVec 32 => result.1) <$> action).run state =
      .ok value after) :
    ∃ flags undefined, action.run state = .ok (value, flags, undefined) after := by
  rw [map_eq_pure_bind, run_bind] at observed
  cases executed : action.run state with
  | error error other =>
    simp only [executed] at observed
    cases observed
  | ok result other =>
    simp only [executed, run_pure] at observed
    obtain ⟨result, flags, undefined⟩ := result
    have sameValue := (EStateM.Result.ok.inj observed).1
    have sameState := (EStateM.Result.ok.inj observed).2
    change result = value at sameValue
    refine ⟨flags, undefined, ?_⟩
    rw [sameValue, sameState]

theorem add_executes (state : State) (left right : Word) (flags : BitVec 32) :
    ∃ output undefined, (Functions.gpr_add_spec_8 left right flags).run state =
      .ok (left + right, output, undefined) state :=
  project_result_reflects _ state state _ (add_value state left right flags)

theorem sub_executes (state : State) (left right : Word) (flags : BitVec 32) :
    ∃ output undefined, (Functions.gpr_sub_spec_8 left right flags).run state =
      .ok (left - right, output, undefined) state :=
  project_result_reflects _ state state _ (sub_value state left right flags)

theorem add_mask (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => value.2.2) <$>
      Functions.gpr_add_spec_8 left right flags).run state = .ok (0#32) state := by
  unfold Functions.gpr_add_spec_8 Functions.cf_spec64 Functions.pf_spec64 Functions.of_spec64
  unfold Functions.unsigned_byte_p_int Functions.signed_byte_p_int Functions.logbitp_int
  simp only [map_eq_pure_bind, run_bind, run_pure, run_assert]
  change (EStateM.Result.ok (0#32) state : EStateM.Result (Sail.Error exception) State (BitVec 32)) = _
  rfl

theorem sub_mask (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => value.2.2) <$>
      Functions.gpr_sub_spec_8 left right flags).run state = .ok (0#32) state := by
  unfold Functions.gpr_sub_spec_8 Functions.pf_spec64 Functions.of_spec64
  unfold Functions.signed_byte_p_int Functions.logbitp_int
  simp only [map_eq_pure_bind, run_bind, run_pure, run_assert]
  change (EStateM.Result.ok (0#32) state : EStateM.Result (Sail.Error exception) State (BitVec 32)) = _
  rfl

theorem add_executes_defined (state : State) (left right : Word) (flags : BitVec 32) :
    ∃ output, (Functions.gpr_add_spec_8 left right flags).run state =
      .ok (left + right, output, 0#32) state := by
  obtain ⟨output, undefined, executed⟩ := add_executes state left right flags
  have mask := add_mask state left right flags
  simp only [map_eq_pure_bind, run_bind, executed, run_pure] at mask
  have defined := (EStateM.Result.ok.inj mask).1
  change undefined = (0#32) at defined
  subst undefined
  exact ⟨output, executed⟩

theorem sub_executes_defined (state : State) (left right : Word) (flags : BitVec 32) :
    ∃ output, (Functions.gpr_sub_spec_8 left right flags).run state =
      .ok (left - right, output, 0#32) state := by
  obtain ⟨output, undefined, executed⟩ := sub_executes state left right flags
  have mask := sub_mask state left right flags
  simp only [map_eq_pure_bind, run_bind, executed, run_pure] at mask
  have defined := (EStateM.Result.ok.inj mask).1
  change undefined = (0#32) at defined
  subst undefined
  exact ⟨output, executed⟩

namespace Controls

private def empty : State := ⟨∅, (), ∅, (), 0, #[]⟩

theorem add_wraps : ((fun value : Word × BitVec 32 × BitVec 32 => value.1) <$>
    Functions.gpr_add_spec_8 (0xffffffffffffffff#64) (1#64) (0#32)).run empty = .ok (0#64) empty := by
  exact add_value empty _ _ _

theorem sub_wraps : ((fun value : Word × BitVec 32 × BitVec 32 => value.1) <$>
    Functions.gpr_sub_spec_8 (0#64) (1#64) (0#32)).run empty = .ok (0xffffffffffffffff#64) empty := by
  exact sub_value empty _ _ _

theorem wrong_add_result_refused :
    ((fun value : Word × BitVec 32 × BitVec 32 => value.1) <$>
      Functions.gpr_add_spec_8 (0xffffffffffffffff#64) (1#64) (0#32)).run empty ≠ .ok (1#64) empty := by
  rw [add_wraps]
  intro wrong
  exact (by decide : (0#64) ≠ (1#64)) (EStateM.Result.ok.inj wrong).1

example : Functions.logcount_int (-1) = 0 := by
  rw [Functions.logcount_int.eq_def]
  change Functions.logcount_int 0 = 0
  rw [Functions.logcount_int.eq_def]
  rfl

example : Functions.logcount_int 255 = 8 := by
  simp [Functions.logcount_int, Functions.isEven, Sail.Int.shiftr, Sail.Nat.iterate, Sail.get_slice_int]

end Controls


end Mettapedia.Machines.TIsa.X86Alu
