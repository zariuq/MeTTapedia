import Mettapedia.Machines.TIsa.X86Bounds

/-!
# Frames for every fetched prefix of the actual bounds checker

Existing original-model instruction contracts supply the intermediate states
and footprints. The prefix theorem covers both offset forms and every exit,
including overflow, short buffers and range rejection. Its execution length is
the established outcome-dependent boundsSteps; no execution or frame is assumed.
The same result specializes to every prefix of a successful checked access.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86Bounds
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

theorem move_prefix_frame (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧ RegisterFrame writes state after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,step,frame,_pointer,_rip⟩ := move_step other extra vector layout state origin input
  exact ⟨after,X86FuelPrefix.fetches_one state after step,frame.mono (by decide)⟩

theorem add_prefix_frame (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (nonzero : layout.offset.val ≠ 0)
    (state : State) (origin : X86LegacyFetch.Basis state) (input : Inputs layout state origin) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run state = .ok () after ∧ RegisterFrame writes state after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle,flags,run,frame,offset,flagsKnown,rip⟩ := head_prefix other extra vector layout state origin input
  obtain ⟨after,_flags,step,lastFrame,_offset,_flagsKnown,_carry,_rip,_control⟩ :=
    add_step_control other extra vector layout nonzero state middle origin input frame flags offset flagsKnown rip
  exact ⟨after,X86FuelPrefix.fetches_then 2 1 state middle after run (X86FuelPrefix.fetches_one middle after step),
    (frame.trans lastFrame).mono (by decide)⟩

theorem length_prefix_frame (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (noWrap : (input.pointer - input.base).toNat + layout.offset.val < 2 ^ 64) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (offsetSteps layout + 1)).run state = .ok () after ∧ RegisterFrame writes state after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle,flags,run,frame,_offset,flagsKnown,rip⟩ := offset_prefix other extra vector layout state origin input
  have fallthrough : middle.regs.get? .rip = some ((position origin.address (lengthAt layout)).signExtend 64) := by
    simpa only [if_neg (by omega : ¬ 2 ^ 64 ≤ (input.pointer - input.base).toNat + layout.offset.val)] using rip
  obtain ⟨after,step,lastFrame,_length,_rip⟩ := length_step other extra vector layout state middle origin input frame flags flagsKnown fallthrough
  exact ⟨after,X86FuelPrefix.fetches_then (offsetSteps layout) 1 state middle after run
    (X86FuelPrefix.fetches_one middle after step),(frame.trans lastFrame).mono (by decide)⟩

theorem compare_prefix_frame (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (noWrap : (input.pointer - input.base).toNat + layout.offset.val < 2 ^ 64)
    (enough : layout.count.val ≤ input.length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (offsetSteps layout + 4)).run state = .ok () after ∧ RegisterFrame writes state after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle,flags,run,frame,offset,length,flagsKnown,rip⟩ := borrow_prefix other extra vector layout state origin input noWrap
  have fallthrough : middle.regs.get? .rip = some ((position origin.address (compareAt layout)).signExtend 64) := by
    simpa only [if_neg (by omega : ¬ input.length.toNat < layout.count.val)] using rip
  obtain ⟨after,_flags,step,lastFrame,_flagsKnown,_sense,_rip,_control⟩ :=
    compare_step_control other extra vector layout state middle origin input frame flags offset length flagsKnown fallthrough
  refine ⟨after,?_,(frame.trans lastFrame).mono (by decide)⟩
  simpa only [Nat.add_assoc] using X86FuelPrefix.fetches_then (offsetSteps layout + 3) 1 state middle after run
    (X86FuelPrefix.fetches_one middle after step)

theorem execution_prefix_known (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (count : Nat)
    (within : count ≤ boundsSteps layout input.base input.pointer input.length) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches count).run state = .ok () after ∧ RegisterFrame writes state after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  by_cases early : count ≤ offsetSteps layout
  · by_cases zero : layout.offset.val = 0
    · have small : count ≤ 2 := by simpa only [offsetSteps,if_pos zero] using early
      interval_cases count
      · exact ⟨state,X86FuelPrefix.fetches_zero state,RegisterFrame.refl _ _⟩
      · exact move_prefix_frame other extra vector layout state origin input
      · obtain ⟨after,_flags,run,frame,_rest⟩ := head_prefix other extra vector layout state origin input
        exact ⟨after,run,frame⟩
    · have small : count ≤ 4 := by simpa only [offsetSteps,if_neg zero] using early
      interval_cases count
      · exact ⟨state,X86FuelPrefix.fetches_zero state,RegisterFrame.refl _ _⟩
      · exact move_prefix_frame other extra vector layout state origin input
      · obtain ⟨after,_flags,run,frame,_rest⟩ := head_prefix other extra vector layout state origin input
        exact ⟨after,run,frame⟩
      · exact add_prefix_frame other extra vector layout zero state origin input
      · obtain ⟨after,_flags,run,frame,_rest⟩ := offset_prefix other extra vector layout state origin input
        exact ⟨after,by simpa only [offsetSteps,if_neg zero] using run,frame⟩
  · have noWrap : (input.pointer - input.base).toNat + layout.offset.val < 2 ^ 64 := by
      by_contra bad
      have overflow : 2 ^ 64 ≤ (input.pointer - input.base).toNat + layout.offset.val := by omega
      simp only [boundsSteps,if_pos overflow] at within
      omega
    have endBound : count ≤ offsetSteps layout + 5 := by
      simp only [boundsSteps,if_neg (by omega : ¬ 2 ^ 64 ≤ (input.pointer - input.base).toNat + layout.offset.val)] at within
      split_ifs at within <;> omega
    by_cases one : count = offsetSteps layout + 1
    · subst count
      exact length_prefix_frame other extra vector layout state origin input noWrap
    by_cases two : count = offsetSteps layout + 2
    · subst count
      obtain ⟨after,_flags,run,frame,_rest⟩ := arithmetic_prefix other extra vector layout state origin input noWrap
      exact ⟨after,run,frame⟩
    by_cases three : count = offsetSteps layout + 3
    · subst count
      obtain ⟨after,_flags,run,frame,_rest⟩ := borrow_prefix other extra vector layout state origin input noWrap
      exact ⟨after,run,frame⟩
    have enough : layout.count.val ≤ input.length.toNat := by
      by_contra bad
      have short : input.length.toNat < layout.count.val := by omega
      simp only [boundsSteps,if_neg (by omega : ¬ 2 ^ 64 ≤ (input.pointer - input.base).toNat + layout.offset.val),if_pos short] at within
      omega
    by_cases four : count = offsetSteps layout + 4
    · subst count
      exact compare_prefix_frame other extra vector layout state origin input noWrap enough
    · have last : count = offsetSteps layout + 5 := by omega
      subst count
      obtain ⟨after,_flags,run,frame,_rest⟩ := range_prefix other extra vector layout state origin input noWrap enough
      exact ⟨after,run,frame⟩

theorem execution_prefix_frame (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin) (count : Nat)
    (within : count ≤ boundsSteps layout input.base input.pointer input.length) (observed : State)
    (run : letI : OtherOpcodeHandlers := handlers other extra
           letI : VectorOpcodeHandlers := vector
           (X86FuelPrefix.fetches count).run state = .ok () observed) : RegisterFrame writes state observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,executed,frame⟩ := execution_prefix_known other extra vector layout state origin input count within
  have same := X86FuelPrefix.fetches_deterministic count state after observed executed run
  subst observed
  exact frame

theorem boundsSteps_of_fits (layout : Layout) (base pointer length : Word)
    (fits : (pointer - base).toNat + layout.offset.val + layout.count.val ≤ length.toNat) :
    boundsSteps layout base pointer length = offsetSteps layout + 5 := by
  have noOverflow : ¬ 2 ^ 64 ≤ (pointer - base).toNat + layout.offset.val := by have := length.isLt; omega
  have enough : ¬ length.toNat < layout.count.val := by omega
  simp only [boundsSteps,if_neg noOverflow,if_neg enough]

theorem success_prefix_frame (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (layout : Layout) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs layout state origin)
    (fits : (input.pointer - input.base).toNat + layout.offset.val + layout.count.val ≤ input.length.toNat)
    (count : Nat) (within : count ≤ offsetSteps layout + 5) (observed : State)
    (run : letI : OtherOpcodeHandlers := handlers other extra
           letI : VectorOpcodeHandlers := vector
           (X86FuelPrefix.fetches count).run state = .ok () observed) : RegisterFrame writes state observed :=
  execution_prefix_frame other extra vector layout state origin input count
    (by rw [boundsSteps_of_fits layout input.base input.pointer input.length fits]; exact within) observed run

end Mettapedia.Machines.TIsa.X86Bounds
