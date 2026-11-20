import Mettapedia.Machines.TIsa.X86LoopBottomLatch
import Mettapedia.Machines.TIsa.X86LoopHeader
import Mettapedia.Machines.TIsa.X86P1LoadCapture

/-!
# Actual ordinary-flat loop control joined to native and resource semantics

The current p1 ordinary_flat_fire image is selected by its actual name. Its
source counted-loop signature and physical register map are checked directly.
The loop is emitted rotated: no separate header span exists. Its top test is
a nine-byte CMP/JAE header copy at 785, the tail of the loop entry, exiting to
1289 and otherwise falling through to the hoisted bounds test at 794. Its
bottom test lives in the thirteen-byte latch at 1276: ADD/CMP/JB returns to
the slow body at 1065 while the incremented counter is below the bound and
otherwise falls through to the exit. The fast-path latch at 1047 carries the
same template. Raw image bytes and canonical placement construct the generic
native contracts at arbitrary admitted bases.

Rotation copies the header test and the fast/slow split gives each copy its
own body landing, so the source profile is indexed by the header copy and its
body point; entry, latch and exit points are shared. The top copy realizes the
source header firing in two fetched instructions. In the latch, the first
fetched instruction realizes the source latch firing and stops at the latch's
header copy at 1280; three instructions realize the latch then header firing,
preserve every-prefix frames and decrease the source rank.

This is the loop-control boundary: the hoisted test, both bodies, whole-loop
iteration, early exits, fuel and public ABI remain separate work. Former
header and latch templates are refused at their former and current offsets.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1LoopCapture
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable def flatImage : P1Capture.Program :=
  ImportedP1.programs[13]'(by rw [ImportedP1.exact_count.2]; decide)

theorem selected_by_name : ImportedP1.programs.find? (fun program => program.name == "ordinary_flat_fire") = some flatImage := by
  kernel_reflexivity

theorem byte_extent : flatImage.size = 1762 := by kernel_reflexivity

theorem source_loop :
    (flatImage.source.body.atPath [1,1,0,0,0,0,1]).bind (fun statement => match statement with
      | .counted index bound cap _ => some (index,bound,cap)
      | _ => none) = some (6,5,(32#32)) := by kernel_reflexivity

/-- The image holds exactly `bytes` at `offset`. -/
noncomputable def holds (offset : Nat) (bytes : List Nat) : Bool :=
  NativeImage.readRange? flatImage.view offset bytes.length == some (bytes.map (BitVec.ofNat 8))

theorem latch_span : flatImage.spans.any (fun span =>
    span.offset == 1276 && span.length == 13 && span.kind == "LOOP-LATCH" && span.path == some [1,1,0,0,0,0,1]) = true := by
  kernel_reflexivity

/-- The rotated loop has no header span, and no span starts at the former header or latch offsets. -/
theorem no_header_span : flatImage.spans.any (fun span => span.kind == "LOOP-HEAD") = false ∧
    flatImage.spans.any (fun span => span.offset == 762 || span.offset == 1224) = false := by
  constructor <;> kernel_reflexivity

/-- The top test falls through to the hoisted test; both bodies begin the loop body's first
source instruction; the exit is the loop's source successor. -/
theorem landing_spans :
    flatImage.spans.any (fun span =>
      span.offset == 794 && span.kind == "HOIST-TEST" && span.path == some [1,1,0,0,0,0,1]) = true ∧
    flatImage.spans.any (fun span =>
      span.offset == 928 && span.path == some [1,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0]) = true ∧
    flatImage.spans.any (fun span =>
      span.offset == 1065 && span.path == some [1,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0]) = true ∧
    flatImage.spans.any (fun span =>
      span.offset == 1289 && span.kind == "LOAD-FRAME" && span.path == some [1,1,0,0,0,1]) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> kernel_reflexivity

theorem register_map :
    placed (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) (Registers.logicalSlot 6) = 10 ∧
    placed (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) (Registers.logicalSlot 5) = 9 := by decide

theorem header_bytes (index : Fin 9) : flatImage.view.read (785 + index.val) =
    ((X86LoopHeader.code 10 9 (495#32))[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem latch_bytes (index : Fin 13) : flatImage.view.read (1276 + index.val) =
    ((X86LoopBottomLatch.code 10 9 (-224#32))[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

/-- The fast-path latch is the same template with its backedge to the fast body at 928. -/
theorem fast_latch_holds : holds 1047 (X86LoopBottomLatch.code 10 9 (-132#32)) = true := by kernel_reflexivity

/-- The former JAE header is absent at its former offset and, with its former displacement,
at the current top test; the latch's own test is JB, not JAE. The former ADD/JMP latch is absent
at its former offset and at the current latch, where a changed backedge displacement is refused. -/
theorem former_templates_refused :
    holds 762 (X86LoopHeader.code 10 9 (462#32)) = false ∧
    holds 785 (X86LoopHeader.code 10 9 (462#32)) = false ∧
    holds 1280 (X86LoopHeader.code 10 9 (-224#32)) = false ∧
    holds 1224 (X86LoopLatch.code 10 (-471#32)) = false ∧
    holds 1276 (X86LoopLatch.code 10 (-224#32)) = false ∧
    holds 1276 (X86LoopBottomLatch.code 10 9 (-223#32)) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_reflexivity

theorem header_loaded (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (placed : origin.address.toInt = base + 785) (loaded : X86P1LoadCapture.Loaded flatImage native base) :
    codeLoaded native origin.address.toInt (X86LoopHeader.code 10 9 (495#32)) := by
  intro index byte present
  have within : index < 9 := by
    have := (List.getElem?_eq_some_iff.mp present).1
    rw [X86LoopHeader.code_length] at this
    exact this
  have captured := header_bytes ⟨index,within⟩
  rw [present, Option.map_some] at captured
  have shifted : address base (785 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using (loaded (785 + index) (by rw [byte_extent]; omega)).trans captured

theorem latch_loaded (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (placed : origin.address.toInt = base + 1276) (loaded : X86P1LoadCapture.Loaded flatImage native base) :
    codeLoaded native origin.address.toInt (X86LoopBottomLatch.code 10 9 (-224#32)) := by
  intro index byte present
  have within : index < 13 := by
    have := (List.getElem?_eq_some_iff.mp present).1
    rw [X86LoopBottomLatch.code_length] at this
    exact this
  have captured := latch_bytes ⟨index,within⟩
  rw [present, Option.map_some] at captured
  have shifted : address base (1276 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using (loaded (1276 + index) (by rw [byte_extent]; omega)).trans captured

def headerInput (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (index bound : Word) (flags : BitVec 32)
    (placed : origin.address.toInt = base + 785)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 1762 < (2 ^ 47 : Int))
    (indexKnown : lookup native 10 = some index) (boundKnown : lookup native 9 = some bound)
    (flagsKnown : native.regs.get? .rflags = some flags) (quiet : native.regs.get? .log_register_writes = some false)
    (loaded : X86P1LoadCapture.Loaded flatImage native base) : X86LoopHeader.Inputs native 10 9 := {
  origin with
  indexValue := index
  boundValue := bound
  flags := flags
  indexKnown := indexKnown
  boundKnown := boundKnown
  flagsKnown := flagsKnown
  quiet := quiet
  upper := by rw [placed]; omega
  displacement := 495#32
  target := address base 1289
  jump := by
    rw [address_toInt base lower upper 1289 (by decide), placed]
    change base + 1289 = base + 785 + 9 + 495
    omega
  loaded := header_loaded native base origin placed loaded }

def latchInput (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (index bound : Word) (flags : BitVec 32) (placed : origin.address.toInt = base + 1276)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 1762 < (2 ^ 47 : Int))
    (indexKnown : lookup native 10 = some index) (boundKnown : lookup native 9 = some bound)
    (flagsKnown : native.regs.get? .rflags = some flags) (quiet : native.regs.get? .log_register_writes = some false)
    (loaded : X86P1LoadCapture.Loaded flatImage native base) : X86LoopBottomLatch.Inputs native 10 9 := {
  origin with
  indexValue := index
  boundValue := bound
  flags := flags
  indexKnown := indexKnown
  boundKnown := boundKnown
  flagsKnown := flagsKnown
  quiet := quiet
  distinct := by decide
  upper := by rw [placed]; omega
  displacement := -224#32
  target := address base 1065
  jump := by
    rw [address_toInt base lower upper 1065 (by decide), placed]
    change base + 1065 = base + 1276 + 13 + (-224)
    omega
  loaded := latch_loaded native base origin placed loaded }

theorem header_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (index bound : Word) (flags : BitVec 32) (placed : origin.address.toInt = base + 785)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 1762 < (2 ^ 47 : Int))
    (indexKnown : lookup native 10 = some index) (boundKnown : lookup native 9 = some bound)
    (flagsKnown : native.regs.get? .rflags = some flags) (quiet : native.regs.get? .log_register_writes = some false)
    (loaded : X86P1LoadCapture.Loaded flatImage native base) :
    letI : OtherOpcodeHandlers := X86LoopHeader.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after resultFlags, (X86FuelPrefix.fetches 2).run native = .ok () after ∧
      RegisterFrame X86LoopHeader.writes native after ∧ lookup after 10 = some index ∧ lookup after 9 = some bound ∧
      after.regs.get? .rflags = some resultFlags ∧
      after.regs.get? .rip = some ((if bound.toNat ≤ index.toNat then address base 1289 else address base 794).signExtend 64) ∧
      X86P1LoadCapture.Loaded flatImage after base := by
  let : OtherOpcodeHandlers := X86LoopHeader.handlers other extra
  let : VectorOpcodeHandlers := vector
  let input := headerInput native base origin index bound flags placed lower upper indexKnown boundKnown flagsKnown quiet loaded
  obtain ⟨after, resultFlags, run, framed, indexRead, boundRead, finalFlags, rip⟩ :=
    X86LoopHeader.executes other extra vector native 10 9 input
  refine ⟨after, resultFlags, run, framed, indexRead, boundRead, finalFlags, ?_, ?_⟩
  · have fallthrough : X86LoopHeader.position input 9 = address base 794 := by
      change address origin.address.toInt 9 = address base 794
      unfold address
      rw [placed]
      congr 1
      omega
    change after.regs.get? .rip = some ((if bound.toNat ≤ index.toNat then address base 1289 else X86LoopHeader.position input 9).signExtend 64) at rip
    rw [fallthrough] at rip
    exact rip
  · intro offset within
    rw [framed.memory]
    exact loaded offset within

theorem latch_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (index bound : Word) (flags : BitVec 32) (placed : origin.address.toInt = base + 1276)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 1762 < (2 ^ 47 : Int))
    (indexKnown : lookup native 10 = some index) (boundKnown : lookup native 9 = some bound)
    (flagsKnown : native.regs.get? .rflags = some flags) (quiet : native.regs.get? .log_register_writes = some false)
    (loaded : X86P1LoadCapture.Loaded flatImage native base) :
    letI : OtherOpcodeHandlers := X86LoopBottomLatch.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after resultFlags, (X86FuelPrefix.fetches 3).run native = .ok () after ∧
      RegisterFrame (X86RegisterIncrement.writes 10) native after ∧ lookup after 10 = some (index + 1) ∧
      lookup after 9 = some bound ∧ after.regs.get? .rflags = some resultFlags ∧
      after.regs.get? .rip = some
        ((if (index + 1).toNat < bound.toNat then address base 1065 else address base 1289).signExtend 64) ∧
      X86P1LoadCapture.Loaded flatImage after base ∧
      ∀ count ≤ 3, ∀ reached, (X86FuelPrefix.fetches count).run native = .ok () reached →
        RegisterFrame (X86RegisterIncrement.writes 10) native reached := by
  let : OtherOpcodeHandlers := X86LoopBottomLatch.handlers other extra
  let : VectorOpcodeHandlers := vector
  let input := latchInput native base origin index bound flags placed lower upper indexKnown boundKnown flagsKnown quiet loaded
  obtain ⟨after, resultFlags, run, framed, indexRead, boundRead, finalFlags, rip, prefixes⟩ :=
    X86LoopBottomLatch.executes other extra vector native 10 9 input
  refine ⟨after, resultFlags, run, framed, indexRead, boundRead, finalFlags, ?_,
    fun offset within => by rw [framed.memory]; exact loaded offset within, prefixes⟩
  have fallthrough : X86LoopBottomLatch.position input 13 = address base 1289 := by
    change address origin.address.toInt 13 = address base 1289
    unfold address
    rw [placed]
    congr 1
    omega
  change after.regs.get? .rip = some ((if (index + 1).toNat < bound.toNat then address base 1065
    else X86LoopBottomLatch.position input 13).signExtend 64) at rip
  rw [fallthrough] at rip
  exact rip

/-- The source loop at its native sites, for the header copy at `header` landing at `body`. -/
def profile (base : Int) (header body : Nat) : Control.Loop P1Source.Reg where
  activation := 0
  entryPoint := (address base 767).signExtend 64
  headerPoint := (address base header).signExtend 64
  latchPoint := (address base 1276).signExtend 64
  bodyPoint := (address base body).signExtend 64
  exitPoint := (address base 1289).signExtend 64
  index := 6
  bound := 5
  maximum := 32

/-- The top test: the header copy ending the loop entry, landing at the hoisted test. -/
abbrev topProfile (base : Int) : Control.Loop P1Source.Reg := profile base 785 794

/-- The bottom test: the header copy inside the latch, landing at the slow body. -/
abbrev bottomProfile (base : Int) : Control.Loop P1Source.Reg := profile base 1280 1065

def SourceMatches (loop : Control.Loop P1Source.Reg) : Prop :=
  (flatImage.source.body.atPath [1,1,0,0,0,0,1]).bind (fun statement => match statement with
    | .counted index bound cap _ => some (index,bound,cap)
    | _ => none) = some (loop.index,loop.bound,BitVec.ofNat 32 loop.maximum)

theorem source_matches (base : Int) (header body : Nat) : SourceMatches (profile base header body) := source_loop

theorem header_realizes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (keys : Finset (Control.Location P1Source.Reg)) (before : Control.Location P1Source.Reg → Word)
    (flags : BitVec 32) (placed : origin.address.toInt = base + 785)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 1762 < (2 ^ 47 : Int))
    (indexKnown : lookup native 10 = some (before (.inr 6))) (boundKnown : lookup native 9 = some (before (.inr 5)))
    (flagsKnown : native.regs.get? .rflags = some flags) (quiet : native.regs.get? .log_register_writes = some false)
    (loaded : X86P1LoadCapture.Loaded flatImage native base)
    (included : (topProfile base).header.support ⊆ keys)
    (current : before (.inl 0) = (topProfile base).headerPoint)
    (ordered : (before (.inr 6)).toNat ≤ (before (.inr 5)).toNat) (bounded : (before (.inr 5)).toNat ≤ 32) :
    letI : OtherOpcodeHandlers := X86LoopHeader.handlers other extra
    letI : VectorOpcodeHandlers := vector
    SourceMatches (topProfile base) ∧ ∃ after, ∃ invocation : CellEffects.Invocation (topProfile base).header,
      CellEffects.system.Enables (Cells.encode keys before) invocation ∧
      CellEffects.system.fire (Cells.encode keys before) invocation = Cells.encode keys ((topProfile base).headerValues before) ∧
      (X86FuelPrefix.fetches 2).run native = .ok () after ∧ RegisterFrame X86LoopHeader.writes native after ∧
      after.regs.get? .rip = some ((topProfile base).headerValues before (.inl 0)) := by
  refine ⟨source_matches base 785 794, ?_⟩
  let input := headerInput native base origin (before (.inr 6)) (before (.inr 5)) flags placed lower upper
    indexKnown boundKnown flagsKnown quiet loaded
  apply X86LoopHeader.realizes other extra vector native 10 9 input (topProfile base) keys before included (by rfl)
    current (by rfl) (by rfl) ordered bounded _ (by rfl)
  change (address base 794).signExtend 64 = (address origin.address.toInt 9).signExtend 64
  apply congrArg (BitVec.signExtend 64)
  unfold address
  rw [placed]
  congr 1
  omega

theorem bottom_points (base : Int) (origin : BitVec 48) (placed : origin.toInt = base + 1276) :
    (bottomProfile base).headerPoint = (address origin.toInt 4).signExtend 64 ∧
      (bottomProfile base).exitPoint = (address origin.toInt 13).signExtend 64 := by
  constructor <;>
  · apply congrArg (BitVec.signExtend 64)
    unfold address
    rw [placed]
    congr 1
    omega

/-- Latch then header in one span: the first fetched instruction realizes the source latch and
reaches the latch's header copy at 1280; three realize the header firing after it. -/
theorem latch_then_header (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (keys : Finset (Control.Location P1Source.Reg)) (before : Control.Location P1Source.Reg → Word)
    (flags : BitVec 32) (placed : origin.address.toInt = base + 1276)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 1762 < (2 ^ 47 : Int))
    (indexKnown : lookup native 10 = some (before (.inr 6))) (boundKnown : lookup native 9 = some (before (.inr 5)))
    (flagsKnown : native.regs.get? .rflags = some flags) (quiet : native.regs.get? .log_register_writes = some false)
    (loaded : X86P1LoadCapture.Loaded flatImage native base)
    (latchScope : (bottomProfile base).latch.support ⊆ keys) (headerScope : (bottomProfile base).header.support ⊆ keys)
    (current : before (.inl 0) = (bottomProfile base).latchPoint)
    (less : (before (.inr 6)).toNat < (before (.inr 5)).toNat) (bounded : (before (.inr 5)).toNat ≤ 32) :
    letI : OtherOpcodeHandlers := X86LoopBottomLatch.handlers other extra
    letI : VectorOpcodeHandlers := vector
    SourceMatches (bottomProfile base) ∧ ∃ middle after,
      ∃ latch : CellEffects.Invocation (bottomProfile base).latch,
      ∃ header : CellEffects.Invocation (bottomProfile base).header,
      CellEffects.system.Enables (Cells.encode keys before) latch ∧
      CellEffects.system.fire (Cells.encode keys before) latch = Cells.encode keys ((bottomProfile base).latchValues before) ∧
      CellEffects.system.Enables (Cells.encode keys ((bottomProfile base).latchValues before)) header ∧
      CellEffects.system.fire (Cells.encode keys ((bottomProfile base).latchValues before)) header =
        Cells.encode keys ((bottomProfile base).headerValues ((bottomProfile base).latchValues before)) ∧
      (X86FuelPrefix.fetches 1).run native = .ok () middle ∧
      lookup middle 10 = some ((bottomProfile base).latchValues before (.inr 6)) ∧
      lookup middle 9 = some ((bottomProfile base).latchValues before (.inr 5)) ∧
      middle.regs.get? .rip = some ((bottomProfile base).latchValues before (.inl 0)) ∧
      (X86FuelPrefix.fetches 3).run native = .ok () after ∧
      RegisterFrame (X86RegisterIncrement.writes 10) native after ∧
      lookup after 10 = some ((bottomProfile base).latchValues before (.inr 6)) ∧
      lookup after 9 = some ((bottomProfile base).latchValues before (.inr 5)) ∧
      after.regs.get? .rip = some ((bottomProfile base).headerValues ((bottomProfile base).latchValues before) (.inl 0)) ∧
      (bottomProfile base).rank ((bottomProfile base).latchValues before) < (bottomProfile base).rank before ∧
      X86P1LoadCapture.Loaded flatImage after base ∧
      ∀ count ≤ 3, ∀ reached, (X86FuelPrefix.fetches count).run native = .ok () reached →
        RegisterFrame (X86RegisterIncrement.writes 10) native reached := by
  let : OtherOpcodeHandlers := X86LoopBottomLatch.handlers other extra
  let : VectorOpcodeHandlers := vector
  refine ⟨source_matches base 1280 1065, ?_⟩
  let input := latchInput native base origin (before (.inr 6)) (before (.inr 5)) flags placed lower upper
    indexKnown boundKnown flagsKnown quiet loaded
  obtain ⟨header, exit⟩ := bottom_points base origin.address placed
  obtain ⟨middle, after, latch, test, latchEnabled, latchFired, testEnabled, testFired, first, middleIndex, middleBound,
      middleRip, run, framed, indexRead, boundRead, rip, decreases, prefixes⟩ :=
    X86LoopBottomLatch.realizes other extra vector native 10 9 input (bottomProfile base) keys before latchScope headerScope
      (by rfl) current (by rfl) (by rfl) less bounded header (by rfl) exit
  exact ⟨middle, after, latch, test, latchEnabled, latchFired, testEnabled, testFired, first, middleIndex, middleBound,
    middleRip, run, framed, indexRead, boundRead, rip, decreases,
    fun offset within => by rw [framed.memory]; exact loaded offset within, prefixes⟩

/-- The source latch firing alone is the latch's first fetched instruction. -/
theorem latch_realizes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (keys : Finset (Control.Location P1Source.Reg)) (before : Control.Location P1Source.Reg → Word)
    (flags : BitVec 32) (placed : origin.address.toInt = base + 1276)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + 1762 < (2 ^ 47 : Int))
    (indexKnown : lookup native 10 = some (before (.inr 6))) (boundKnown : lookup native 9 = some (before (.inr 5)))
    (flagsKnown : native.regs.get? .rflags = some flags) (quiet : native.regs.get? .log_register_writes = some false)
    (loaded : X86P1LoadCapture.Loaded flatImage native base)
    (latchScope : (bottomProfile base).latch.support ⊆ keys) (headerScope : (bottomProfile base).header.support ⊆ keys)
    (current : before (.inl 0) = (bottomProfile base).latchPoint)
    (less : (before (.inr 6)).toNat < (before (.inr 5)).toNat) (bounded : (before (.inr 5)).toNat ≤ 32) :
    letI : OtherOpcodeHandlers := X86LoopBottomLatch.handlers other extra
    letI : VectorOpcodeHandlers := vector
    SourceMatches (bottomProfile base) ∧ ∃ middle, ∃ invocation : CellEffects.Invocation (bottomProfile base).latch,
      CellEffects.system.Enables (Cells.encode keys before) invocation ∧
      CellEffects.system.fire (Cells.encode keys before) invocation = Cells.encode keys ((bottomProfile base).latchValues before) ∧
      (X86FuelPrefix.fetches 1).run native = .ok () middle ∧
      RegisterFrame (X86RegisterIncrement.writes 10) native middle ∧
      lookup middle 10 = some ((bottomProfile base).latchValues before (.inr 6)) ∧
      lookup middle 9 = some ((bottomProfile base).latchValues before (.inr 5)) ∧
      middle.regs.get? .rip = some ((bottomProfile base).latchValues before (.inl 0)) ∧
      ((bottomProfile base).latchValues before (.inr 6)).toNat = (before (.inr 6)).toNat + 1 ∧
      (bottomProfile base).rank ((bottomProfile base).latchValues before) < (bottomProfile base).rank before := by
  let : OtherOpcodeHandlers := X86LoopBottomLatch.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨matched, middle, _, latch, _, latchEnabled, latchFired, _, _, first, middleIndex, middleBound, middleRip,
      _, _, _, _, _, decreases, _, prefixes⟩ :=
    latch_then_header other extra vector native base origin keys before flags placed lower upper indexKnown boundKnown
      flagsKnown quiet loaded latchScope headerScope current less bounded
  refine ⟨matched, middle, latch, latchEnabled, latchFired, first, prefixes 1 (by decide) middle first,
    middleIndex, middleBound, middleRip, ?_, decreases⟩
  have value : (bottomProfile base).latchValues before (.inr 6) = before (.inr 6) + 1 := by
    simp [Control.Loop.latchValues, profile]
  rw [value]
  exact Control.counter_increment_no_wrap (before (.inr 6)) (before (.inr 5)) less

end Mettapedia.Machines.TIsa.X86P1LoopCapture
