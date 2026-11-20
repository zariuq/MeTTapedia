import Mettapedia.Machines.TIsa.X86LoopEntry
import Mettapedia.Machines.TIsa.X86P1LoopCapture

/-!
# The actual ordinary-flat rotated loop entry at its emitted bytes

The captured twenty-seven-byte entry is the cap gate and counter zeroing
followed by the loop's top test. It uses the source loop's cap 32, logical
counter 6 (R10), bound 5 (R9) and R14 scratch. The gate's raw displacement
913 reaches the unsupported-bound handler at 1695. The top test is the header
copy at 785: its raw displacement 495 reaches the loop exit at 1289 and its
fallthrough is the hoisted bounds test at 794. The loaded full image
constructs both generic contracts at any canonical placement.

Admitted bounds run six fetched instructions. The first four realize the
existing guarded entry firing and stop at the header copy with counter zero;
the last two realize the top header firing, which exits exactly when the bound
is zero. Every prefix keeps the entry frame. Excess bounds reach 1695 in three
instructions with the counter kept and admit no source entry firing. The
former entry layout is refused at its former offset and, with its former
displacement, at the current one.

Metering, the hoisted test and bodies, the rejection handler and complete
consumer/ABI refinement remain open.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1LoopEntryCapture
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev flatImage := X86P1LoopCapture.flatImage

theorem entry_span : flatImage.spans.any (fun span =>
    span.offset == 767 && span.length == 27 && span.kind == "LOOP-ENTRY" && span.path == some [1,1,0,0,0,0,1]) = true := by
  kernel_reflexivity

/-- The whole span is the gate-and-zeroing template followed by the header template. -/
theorem entry_layout : X86P1LoopCapture.holds 767
    (X86LoopEntry.code 10 9 (32#32) (913#32) ++ X86LoopHeader.code 10 9 (495#32)) = true := by
  kernel_reflexivity

/-- The former eighteen-byte entry is refused at its former offset and, with its former
displacement, at the current one. -/
theorem former_entry_refused :
    X86P1LoopCapture.holds 744 (X86LoopEntry.code 10 9 (32#32) (788#32)) = false ∧
    X86P1LoopCapture.holds 767 (X86LoopEntry.code 10 9 (32#32) (788#32)) = false := by
  constructor <;> kernel_reflexivity

theorem entry_bytes (index : Fin 18) : flatImage.view.read (767 + index.val) =
    ((X86LoopEntry.code 10 9 (32#32) (913#32))[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem entry_loaded (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (placed : origin.address.toInt = base + 767) (loaded : X86P1LoadCapture.Loaded flatImage native base) :
    codeLoaded native origin.address.toInt (X86LoopEntry.code 10 9 (32#32) (913#32)) := by
  intro index byte present
  have within : index < 18 := by simpa only [X86LoopEntry.code_length] using (List.getElem?_eq_some_iff.mp present).1
  have captured := entry_bytes ⟨index,within⟩
  rw [present,Option.map_some] at captured
  have shifted : address base (767 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using (loaded (767 + index) (by rw [X86P1LoopCapture.byte_extent]; omega)).trans captured

def entryInput (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (index bound : Word) (flags : BitVec 32) (placed : origin.address.toInt = base + 767)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 1762 < (2 ^ 47 : Int))
    (indexKnown : lookup native 10 = some index) (boundKnown : lookup native 9 = some bound)
    (flagsKnown : native.regs.get? .rflags = some flags) (quiet : native.regs.get? .log_register_writes = some false)
    (loaded : X86P1LoadCapture.Loaded flatImage native base) : X86LoopEntry.Inputs native 10 9 := {
  origin with
  indexValue := index
  boundValue := bound
  cap := 32#32
  flags := flags
  indexKnown := indexKnown
  boundKnown := boundKnown
  flagsKnown := flagsKnown
  quiet := quiet
  separateIndex := by decide
  separateBound := by decide
  distinct := by decide
  upper := by rw [placed]; omega
  displacement := 913#32
  target := address base 1695
  jump := by
    rw [address_toInt base lower upper 1695 (by decide),placed]
    rw [show (913#32).toInt = (913 : Int) from rfl]
    omega
  loaded := entry_loaded native base origin placed loaded }

theorem header_reached (base : Int) (origin : BitVec 48) (placed : origin.toInt = base + 767) :
    address origin.toInt 18 = address base 785 := by
  unfold address
  rw [placed]
  congr 1
  omega

theorem header_upper (base : Int) (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 1762 < (2 ^ 47 : Int)) :
    (address base 785).toInt + 3 < (2 ^ 47 : Int) := by
  rw [address_toInt base lower upper 785 (by decide)]
  omega

/-- Gate, zeroing and top test: the hoisted test when the counter starts below the bound,
the loop exit for a zero bound, the unsupported-bound handler above the cap. -/
theorem entry_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (index bound : Word) (flags : BitVec 32) (placed : origin.address.toInt = base + 767)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 1762 < (2 ^ 47 : Int))
    (indexKnown : lookup native 10 = some index) (boundKnown : lookup native 9 = some bound)
    (flagsKnown : native.regs.get? .rflags = some flags) (quiet : native.regs.get? .log_register_writes = some false)
    (loaded : X86P1LoadCapture.Loaded flatImage native base) :
    letI : OtherOpcodeHandlers := X86LoopEntry.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (if bound.toNat ≤ 32 then 6 else 3)).run native = .ok () after ∧
      RegisterFrame (X86LoopEntry.writes 10) native after ∧
      lookup after 10 = some (if bound.toNat ≤ 32 then (0#64) else index) ∧ lookup after 9 = some bound ∧
      after.regs.get? .rip = some ((address base
        (if 32 < bound.toNat then 1695 else if bound.toNat = 0 then 1289 else 794)).signExtend 64) ∧
      X86P1LoadCapture.Loaded flatImage after base ∧
      ∀ count ≤ (if bound.toNat ≤ 32 then 6 else 3), ∀ reached,
        (X86FuelPrefix.fetches count).run native = .ok () reached →
          RegisterFrame (X86LoopEntry.writes 10) native reached := by
  let : OtherOpcodeHandlers := X86LoopEntry.handlers other extra
  let : VectorOpcodeHandlers := vector
  let prepared := entryInput native base origin index bound flags placed lower upper indexKnown boundKnown flagsKnown quiet loaded
  obtain ⟨gated, gateFlags, gateRun, gateFrame, gateIndex, gateBound, gateFlagsKnown, gateRip⟩ :=
    X86LoopEntry.executes other extra vector native 10 9 prepared
  change (X86FuelPrefix.fetches (if bound.toNat ≤ 32 then 4 else 3)).run native = .ok () gated at gateRun
  change lookup gated 10 = some (if bound.toNat ≤ 32 then (0#64) else index) at gateIndex
  change gated.regs.get? .rip = some ((if bound.toNat ≤ 32 then address origin.address.toInt 18
    else address base 1695).signExtend 64) at gateRip
  have gatePrefixes (count : Nat) (within : count ≤ (if bound.toNat ≤ 32 then 4 else 3)) :
      ∃ reached, (X86FuelPrefix.fetches count).run native = .ok () reached ∧
        RegisterFrame (X86LoopEntry.writes 10) native reached :=
    X86LoopEntry.prefix_frame other extra vector native 10 9 prepared count within
  have gateLoaded : X86P1LoadCapture.Loaded flatImage gated base := fun offset within => by
    rw [gateFrame.memory]
    exact loaded offset within
  have settled : ∀ count, ∀ reached, (∃ proved, (X86FuelPrefix.fetches count).run native = .ok () proved ∧
      RegisterFrame (X86LoopEntry.writes 10) native proved) → (X86FuelPrefix.fetches count).run native = .ok () reached →
        RegisterFrame (X86LoopEntry.writes 10) native reached := by
    intro count reached ⟨proved, provedRun, framed⟩ executed
    have same := X86FuelPrefix.fetches_deterministic count native proved reached provedRun executed
    subst reached
    exact framed
  by_cases admitted : bound.toNat ≤ 32
  · rw [if_pos admitted] at gateRun gateIndex gateRip gatePrefixes
    rw [header_reached base origin.address placed] at gateRip
    let headerOrigin := X86StateFrame.basisAt native gated origin (X86StateFrame.registerOnly gateFrame)
      (X86LoopEntry.writes_data 10) (address base 785) (header_upper base lower upper) gateRip
    have headerPlaced : headerOrigin.address.toInt = base + 785 := address_toInt base lower upper 785 (by decide)
    have gateQuiet := (gateFrame.registers .log_register_writes (by decide)).trans quiet
    obtain ⟨after, _, headerRun, headerFrame, indexRead, boundRead, _, rip, afterLoaded⟩ :=
      X86P1LoopCapture.header_executes (X86FrameStore.linkedHandlers other) extra vector gated base headerOrigin
        (0#64) bound gateFlags headerPlaced lower upper gateIndex gateBound gateFlagsKnown gateQuiet gateLoaded
    have notExcess : ¬32 < bound.toNat := by omega
    refine ⟨after, ?_, (gateFrame.trans headerFrame).mono (by decide), ?_, boundRead, ?_, afterLoaded, ?_⟩
    · rw [if_pos admitted]
      exact X86FuelPrefix.fetches_then 4 2 native gated after gateRun headerRun
    · rw [if_pos admitted]
      exact indexRead
    · rw [if_neg notExcess]
      rw [show (0#64 : Word).toNat = 0 from rfl] at rip
      by_cases zero : bound.toNat = 0
      · rw [if_pos (by omega : bound.toNat ≤ 0)] at rip
        rw [if_pos zero]
        exact rip
      · rw [if_neg (by omega : ¬bound.toNat ≤ 0)] at rip
        rw [if_neg zero]
        exact rip
    · intro count within reached executed
      rw [if_pos admitted] at within
      apply settled count reached _ executed
      by_cases early : count ≤ 4
      · exact gatePrefixes count early
      · let input := X86P1LoopCapture.headerInput gated base headerOrigin (0#64) bound gateFlags headerPlaced lower upper
          gateIndex gateBound gateFlagsKnown gateQuiet gateLoaded
        obtain ⟨proved, provedRun, provedFrame⟩ := X86LoopHeader.prefix_frame (X86FrameStore.linkedHandlers other) extra
          vector gated 10 9 input (count - 4) (by omega)
        have total := X86FuelPrefix.fetches_then 4 (count - 4) native gated proved gateRun provedRun
        rw [show 4 + (count - 4) = count by omega] at total
        exact ⟨proved, total, (gateFrame.trans provedFrame).mono (by decide)⟩
  · rw [if_neg admitted] at gateRun gateIndex gateRip gatePrefixes
    refine ⟨gated, ?_, gateFrame, ?_, gateBound, ?_, gateLoaded, ?_⟩
    · rw [if_neg admitted]
      exact gateRun
    · rw [if_neg admitted]
      exact gateIndex
    · rw [if_pos (by omega : 32 < bound.toNat)]
      exact gateRip
    · intro count within reached executed
      rw [if_neg admitted] at within
      exact settled count reached (gatePrefixes count within) executed

/-- The existing guarded entry firing composed with the top header firing. -/
theorem entry_realizes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (keys : Finset (Control.Location P1Source.Reg)) (before : Control.Location P1Source.Reg → Word)
    (flags : BitVec 32) (placed : origin.address.toInt = base + 767)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 1762 < (2 ^ 47 : Int))
    (indexKnown : lookup native 10 = some (before (.inr 6))) (boundKnown : lookup native 9 = some (before (.inr 5)))
    (flagsKnown : native.regs.get? .rflags = some flags) (quiet : native.regs.get? .log_register_writes = some false)
    (loaded : X86P1LoadCapture.Loaded flatImage native base)
    (entryScope : (X86P1LoopCapture.topProfile base).entry.support ⊆ keys)
    (headerScope : (X86P1LoopCapture.topProfile base).header.support ⊆ keys)
    (current : before (.inl 0) = (X86P1LoopCapture.topProfile base).entryPoint)
    (bounded : (before (.inr 5)).toNat ≤ 32) :
    letI : OtherOpcodeHandlers := X86LoopEntry.handlers other extra
    letI : VectorOpcodeHandlers := vector
    X86P1LoopCapture.SourceMatches (X86P1LoopCapture.topProfile base) ∧ ∃ middle after,
      ∃ entry : CellEffects.Invocation (X86P1LoopCapture.topProfile base).entry,
      ∃ header : CellEffects.Invocation (X86P1LoopCapture.topProfile base).header,
      CellEffects.system.Enables (Cells.encode keys before) entry ∧
      CellEffects.system.fire (Cells.encode keys before) entry =
        Cells.encode keys ((X86P1LoopCapture.topProfile base).entryValues before) ∧
      CellEffects.system.Enables (Cells.encode keys ((X86P1LoopCapture.topProfile base).entryValues before)) header ∧
      CellEffects.system.fire (Cells.encode keys ((X86P1LoopCapture.topProfile base).entryValues before)) header =
        Cells.encode keys ((X86P1LoopCapture.topProfile base).headerValues
          ((X86P1LoopCapture.topProfile base).entryValues before)) ∧
      (X86FuelPrefix.fetches 4).run native = .ok () middle ∧ RegisterFrame (X86LoopEntry.writes 10) native middle ∧
      lookup middle 10 = some ((X86P1LoopCapture.topProfile base).entryValues before (.inr 6)) ∧
      lookup middle 9 = some ((X86P1LoopCapture.topProfile base).entryValues before (.inr 5)) ∧
      middle.regs.get? .rip = some ((X86P1LoopCapture.topProfile base).entryValues before (.inl 0)) ∧
      (X86FuelPrefix.fetches 6).run native = .ok () after ∧ RegisterFrame (X86LoopEntry.writes 10) native after ∧
      lookup after 10 = some ((X86P1LoopCapture.topProfile base).headerValues
        ((X86P1LoopCapture.topProfile base).entryValues before) (.inr 6)) ∧
      lookup after 9 = some ((X86P1LoopCapture.topProfile base).headerValues
        ((X86P1LoopCapture.topProfile base).entryValues before) (.inr 5)) ∧
      after.regs.get? .rip = some ((X86P1LoopCapture.topProfile base).headerValues
        ((X86P1LoopCapture.topProfile base).entryValues before) (.inl 0)) ∧
      X86P1LoadCapture.Loaded flatImage after base := by
  let : OtherOpcodeHandlers := X86LoopEntry.handlers other extra
  let : VectorOpcodeHandlers := vector
  let prepared := entryInput native base origin (before (.inr 6)) (before (.inr 5)) flags placed lower upper
    indexKnown boundKnown flagsKnown quiet loaded
  have headerAt : (X86P1LoopCapture.topProfile base).headerPoint = (X86LoopEntry.position prepared 18).signExtend 64 := by
    change (address base 785).signExtend 64 = (address origin.address.toInt 18).signExtend 64
    rw [header_reached base origin.address placed]
  obtain ⟨middle, entry, entryEnabled, entryFired, run, frame, middleIndex, middleBound, middleRip⟩ :=
    X86LoopEntry.realizes_entry_cells other extra vector native 10 9 prepared (X86P1LoopCapture.topProfile base)
      keys before entryScope (by rfl) current rfl rfl bounded headerAt
  obtain ⟨gated, gateFlags, gateRun, _, _, _, gateFlagsKnown, _⟩ := X86LoopEntry.executes other extra vector native 10 9 prepared
  change (X86FuelPrefix.fetches (if (before (.inr 5)).toNat ≤ 32 then 4 else 3)).run native = .ok () gated at gateRun
  rw [if_pos bounded] at gateRun
  have same := X86FuelPrefix.fetches_deterministic 4 native gated middle gateRun run
  subst same
  have entryIndex : (X86P1LoopCapture.topProfile base).entryValues before (.inr 6) = 0 := by
    simp [Control.Loop.entryValues, X86P1LoopCapture.profile]
  have entryBound : (X86P1LoopCapture.topProfile base).entryValues before (.inr 5) = before (.inr 5) := by
    simp [Control.Loop.entryValues, X86P1LoopCapture.profile]
  have entryPoint : (X86P1LoopCapture.topProfile base).entryValues before (.inl 0) =
      (X86P1LoopCapture.topProfile base).headerPoint := by
    simp [Control.Loop.entryValues, X86P1LoopCapture.profile]
  have atHeader : gated.regs.get? .rip = some ((address base 785).signExtend 64) := middleRip.trans (congrArg some entryPoint)
  let headerOrigin := X86StateFrame.basisAt native gated origin (X86StateFrame.registerOnly frame)
    (X86LoopEntry.writes_data 10) (address base 785) (header_upper base lower upper) atHeader
  have headerPlaced : headerOrigin.address.toInt = base + 785 := address_toInt base lower upper 785 (by decide)
  have gateQuiet := (frame.registers .log_register_writes (by decide)).trans quiet
  have gateLoaded : X86P1LoadCapture.Loaded flatImage gated base := fun offset within => by
    rw [frame.memory]
    exact loaded offset within
  obtain ⟨matched, after, header, headerEnabled, headerFired, last, lastFrame, finalRip⟩ :=
    X86P1LoopCapture.header_realizes (X86FrameStore.linkedHandlers other) extra vector gated base headerOrigin keys
      ((X86P1LoopCapture.topProfile base).entryValues before) gateFlags headerPlaced lower upper middleIndex middleBound
      gateFlagsKnown gateQuiet gateLoaded headerScope entryPoint (by rw [entryIndex]; exact Nat.zero_le _)
      (by rw [entryBound]; exact bounded)
  have keepIndex : (X86P1LoopCapture.topProfile base).headerValues
      ((X86P1LoopCapture.topProfile base).entryValues before) (.inr 6) =
        (X86P1LoopCapture.topProfile base).entryValues before (.inr 6) := by
    simp [Control.Loop.headerValues, X86P1LoopCapture.profile]
  have keepBound : (X86P1LoopCapture.topProfile base).headerValues
      ((X86P1LoopCapture.topProfile base).entryValues before) (.inr 5) =
        (X86P1LoopCapture.topProfile base).entryValues before (.inr 5) := by
    simp [Control.Loop.headerValues, X86P1LoopCapture.profile]
  refine ⟨matched, gated, after, entry, header, entryEnabled, entryFired, headerEnabled, headerFired, run, frame,
    middleIndex, middleBound, middleRip, X86FuelPrefix.fetches_then 4 2 native gated after run last,
    (frame.trans lastFrame).mono (by decide), ?_, ?_, finalRip,
    fun offset within => by rw [lastFrame.memory]; exact gateLoaded offset within⟩
  · rw [keepIndex]
    exact (lastFrame.lookup 10 (by decide)).trans middleIndex
  · rw [keepBound]
    exact (lastFrame.lookup 9 (by decide)).trans middleBound

/-- Excess bounds reach the unsupported-bound handler and admit no source entry firing. -/
theorem entry_rejects (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (before : Control.Location P1Source.Reg → Word)
    (flags : BitVec 32) (placed : origin.address.toInt = base + 767)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 1762 < (2 ^ 47 : Int))
    (indexKnown : lookup native 10 = some (before (.inr 6))) (boundKnown : lookup native 9 = some (before (.inr 5)))
    (flagsKnown : native.regs.get? .rflags = some flags) (quiet : native.regs.get? .log_register_writes = some false)
    (loaded : X86P1LoadCapture.Loaded flatImage native base)
    (excess : 32 < (before (.inr 5)).toNat) :
    letI : OtherOpcodeHandlers := X86LoopEntry.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run native = .ok () after ∧ RegisterFrame (X86LoopEntry.writes 10) native after ∧
      lookup after 10 = some (before (.inr 6)) ∧ lookup after 9 = some (before (.inr 5)) ∧
      after.regs.get? .rip = some ((address base 1695).signExtend 64) ∧
      X86P1LoadCapture.Loaded flatImage after base ∧
      ∀ sourceAfter, (X86P1LoopCapture.topProfile base).entry.guard
        ((X86P1LoopCapture.topProfile base).entry.inputs.map before)
        ((X86P1LoopCapture.topProfile base).entry.outputs.map sourceAfter) ≠ true := by
  let prepared := entryInput native base origin (before (.inr 6)) (before (.inr 5)) flags placed lower upper
    indexKnown boundKnown flagsKnown quiet loaded
  obtain ⟨after, run, frame, indexRead, boundRead, rip, refused⟩ :=
    X86LoopEntry.rejects_entry_guard other extra vector native 10 9 prepared (X86P1LoopCapture.topProfile base) before
      rfl rfl excess
  exact ⟨after, run, frame, indexRead, boundRead, rip,
    fun offset within => by rw [frame.memory]; exact loaded offset within, refused⟩

end Mettapedia.Machines.TIsa.X86P1LoopEntryCapture
