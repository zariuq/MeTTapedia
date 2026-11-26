import Mettapedia.Machines.TIsa.X86PlacedMemory
import Mettapedia.Machines.TIsa.X86PlacedWideImmediate
import Mettapedia.Machines.TIsa.X86DataLoad

/-!
# Native copy and fill of a private word array

The source of a word is either a memory load or a literal in the emitted
code. The address and the value are separate: changing the contents of a
copy source does not change the bytes for that copy. A block of placements
reads the old snapshot and fills disjoint destinations; no instruction in
this block publishes the destinations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeWords

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
open X86PlacedMemory (Encoding Cell Controls Reads CodeApart footprint)
local instance : MemoryPrimitives := X86Memory.ordinary

structure Wiring where
  readBase : Fin 16
  readNoSib : readBase.val % 8 ≠ 4
  readNoStack : readBase.val % 8 ≠ 5
  writeBase : Encoding
  scratch : Fin 16
  readPreserved : readBase ≠ scratch
  writePreserved : writeBase.base ≠ scratch

inductive Source (oldBase : Word) where
  | copy (displacement : BitVec 32) (cell : Cell oldBase displacement)
  | literal (value : Word)

def Source.bytes {oldBase : Word} (w : Wiring) : Source oldBase → List ℕ
  | .copy d _ => X86DataLoad.code true w.scratch w.readBase d
  | .literal value => X86PlacedWideImmediate.bytes w.scratch value

def Source.width {oldBase : Word} : Source oldBase → ℕ
  | .copy .. => 7
  | .literal .. => 10

theorem Source.bytes_length {oldBase : Word} (w : Wiring) (source : Source oldBase) :
    (source.bytes w).length = source.width := by
  cases source
  · exact X86DataLoad.code_length _ _ _ _
  · simp [Source.bytes, Source.width, X86PlacedWideImmediate.bytes]

def Source.Ready {oldBase : Word} (state : X86RegisterRefinement.State) : Source oldBase → Word → Prop
  | .copy _ cell, value => Reads state cell.address value
  | .literal constant, value => constant = value

def Source.uses {oldBase : Word} : Source oldBase → Finset ℕ
  | .copy _ cell => footprint cell.address
  | .literal _ => ∅

theorem Source.ready_preserved {oldBase : Word} (src : Source oldBase) {value : Word}
    {before after : X86RegisterRefinement.State} {regs : Finset Register} {bytes : Finset ℕ}
    (read : src.Ready before value) (frame : X86StateFrame.Frame regs bytes before after)
    (apart : Disjoint src.uses bytes) : src.Ready after value := by
  cases src
  · exact Reads.preserved read frame apart
  · exact read

noncomputable abbrev handlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86FrameLoad.linkedHandlers (X86FrameStore.linkedHandlers other)

abbrev touched (w : Wiring) : Finset Register := {key w.scratch, .rip}

private theorem key_not_rip (r : Fin 16) : key r ≠ .rip := by
  revert r
  decide +kernel

theorem outside_scratch (w : Wiring) (r : Fin 16) (other : r ≠ w.scratch) :
    key r ∉ touched w := by
  simp only [touched, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨fun same => other (key_injective same), key_not_rip r⟩

private theorem flags_kept (r : Fin 16) : .rflags ∉ ({key r, .rip} : Finset Register) := by
  revert r
  decide +kernel

theorem Source.fetch (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (w : Wiring)
    {oldBase : Word} (source : Source oldBase) (value : Word)
    {image : NativeImage.View} {state : X86RegisterRefinement.State} {base : BitVec 48} {start : ℕ}
    (point : At image state base start) (controls : Controls state)
    (baseRead : lookup state w.readBase = some oldBase) (ready : source.Ready state value)
    (within : start + source.width ≤ image.size) (code : Code image start (source.bytes w)) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ next, (X86FuelPrefix.fetches 1).run state = .ok () next ∧
      X86StateFrame.Frame (touched w) ∅ state next ∧
      lookup next w.scratch = some value ∧ Nonempty (At image next base (start + source.width)) := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  cases source with
  | copy displacement cell =>
    change start + 7 ≤ image.size at within
    let origin := point.basis (by omega)
    let input : X86DataLoad.Inputs state true w.scratch w.readBase displacement :=
      { toBasis := origin
        noSib := w.readNoSib
        noStack := w.readNoStack
        visible := controls.visible
        controls := controls.controls
        baseValue := oldBase
        word := value
        flags := point.flags
        dataAddress := cell.address
        baseKnown := baseRead
        controlKnown := controls.controlsKnown
        flagsKnown := point.knownFlags
        visibleKnown := controls.visibleKnown
        quiet := point.quiet
        upper := by
          change (address base.toInt start).toInt + 7 < (2^47 : Int)
          rw [point.location _ (by omega)]
          have := point.upper
          omega
        dataUpper := cell.upper
        effective := cell.effective
        safe := Or.inr cell.aligned
        loaded := point.bytes start (by omega) _ code
        dataPresent := ready }
    obtain ⟨next, fetched, frame, word, rip⟩ :=
      X86DataLoad.executes (X86FrameStore.linkedHandlers other) vector state true w.scratch w.readBase displacement input
    change next.regs.get? .rip = some ((address (address base.toInt start).toInt 7).signExtend 64) at rip
    rw [point.relative_address start 7 (by omega)] at rip
    exact ⟨next, fetched, X86StateFrame.registerOnly frame, word,
      ⟨point.advance frame (X86Immediate32.writes_data _) rip point.flags
        ((frame.registers .rflags (flags_kept w.scratch)).trans point.knownFlags)⟩⟩
  | literal constant =>
    change constant = value at ready
    subst constant
    obtain ⟨next, fetched, frame, word, follow⟩ :=
      X86PlacedWideImmediate.materializes (X86FrameLoad.linkedHandlers other) vector point within w.scratch value code
    exact ⟨next, fetched, X86StateFrame.registerOnly frame, word, follow⟩

structure Move (oldBase newBase : Word) where
  source : Source oldBase
  value : Word
  displacement : BitVec 32
  cell : Cell newBase displacement

def Move.width {oldBase newBase : Word} (w : Wiring) (move : Move oldBase newBase) : ℕ :=
  move.source.width + w.writeBase.length

def Move.bytes {oldBase newBase : Word} (w : Wiring) (move : Move oldBase newBase) : List ℕ :=
  move.source.bytes w ++ w.writeBase.bytes w.scratch move.displacement

def Move.Checked {oldBase newBase : Word} (move : Move oldBase newBase)
    (w : Wiring) (image : NativeImage.View) (start : ℕ) : Prop :=
  start + move.width w ≤ image.size ∧
    Code image start (move.source.bytes w) ∧
    Code image (start + move.source.width) (w.writeBase.bytes w.scratch move.displacement)

theorem Move.fetch (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (w : Wiring)
    {oldBase newBase : Word} (move : Move oldBase newBase)
    {image : NativeImage.View} {state : X86RegisterRefinement.State} {base : BitVec 48} {start : ℕ}
    (point : At image state base start) (controls : Controls state) (checked : move.Checked w image start)
    (readBase : lookup state w.readBase = some oldBase) (writeBase : lookup state w.writeBase.base = some newBase)
    (ready : move.source.Ready state move.value) (apart : CodeApart image base (footprint move.cell.address)) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ next, (X86FuelPrefix.fetches 2).run state = .ok () next ∧
      X86StateFrame.Frame (touched w) (footprint move.cell.address) state next ∧
      Reads next move.cell.address move.value ∧ Nonempty (At image next base (start + move.width w)) := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨fits, reading, writing⟩ := checked
  have extent : start + move.source.width + w.writeBase.length ≤ image.size := by
    simpa only [Move.width, Nat.add_assoc] using fits
  obtain ⟨middle, read, readFrame, value, ⟨atStore⟩⟩ := move.source.fetch other vector w move.value point controls
    readBase ready (by omega) reading
  obtain ⟨next, written, writeFrame, reads, finish⟩ := X86PlacedMemory.stores
    (handlers other) vector atStore (controls.transport readFrame (X86Immediate32.writes_data _))
    w.writeBase w.scratch move.displacement newBase move.value move.cell
    ((readFrame.lookup _ (outside_scratch w _ w.writePreserved)).trans writeBase) value extent writing apart
  have registers : touched w ∪ ({.rip} : Finset Register) ⊆ touched w := by simp [touched]
  refine ⟨next, X86FuelPrefix.fetches_then 1 1 state middle next read written, ?_, reads, ?_⟩
  · exact (readFrame.trans writeFrame).mono registers (by simp)
  · simpa only [Move.width, Nat.add_assoc] using finish

variable {oldBase newBase : Word}

def emitted (w : Wiring) (moves : List (Move oldBase newBase)) : List ℕ :=
  moves.flatMap (Move.bytes w ·)

def size (w : Wiring) (moves : List (Move oldBase newBase)) : ℕ :=
  (moves.map (Move.width w ·)).sum

def written : List (Move oldBase newBase) → Finset ℕ
  | [] => ∅
  | m :: rest => footprint m.cell.address ∪ written rest

def Checked (w : Wiring) (image : NativeImage.View) :
    ℕ → List (Move oldBase newBase) → Prop
  | start, [] => start ≤ image.size
  | start, m :: rest => m.Checked w image start ∧ Checked w image (start + m.width w) rest

private theorem range_succ (image : NativeImage.View) (start len : ℕ) :
    NativeImage.readRange? image start (len + 1) =
      (image.read start).bind (fun first => (NativeImage.readRange? image (start + 1) len).map (first :: ·)) := by
  unfold NativeImage.readRange?
  rw [List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
  have shift : (fun i => image.read (start + i.succ)) = fun i => image.read (start + 1 + i) := by
    funext i
    congr 1
    omega
  simp only [Function.comp_def, Nat.add_zero, shift]
  cases image.read start <;> cases (List.range len).mapM (fun i => image.read (start + 1 + i)) <;> rfl

private theorem code_of_points (image : NativeImage.View) (start : ℕ) (bytes : List ℕ)
    (read : ∀ i b, bytes[i]? = some b → image.read (start + i) = some (BitVec.ofNat 8 b)) :
    Code image start bytes := by
  induction bytes generalizing start with
  | nil => rfl
  | cons head tail ih =>
    have first := read 0 head rfl
    have more : Code image (start + 1) tail := by
      apply ih
      intro i b included
      have there := read i.succ b included
      rw [show start + i.succ = start + 1 + i by omega] at there
      exact there
    change NativeImage.readRange? image start (tail.length + 1) = _
    simp only [Nat.add_zero] at first
    simp only [range_succ, first, more, List.map_cons, Option.bind_some, Option.map_some]

theorem code_append {image : NativeImage.View} {start : ℕ} {first later : List ℕ}
    (installed : Code image start (first ++ later)) :
    Code image start first ∧ Code image (start + first.length) later := by
  have point {i b : ℕ} (within : (first ++ later)[i]? = some b) :
      image.read (start + i) = some (BitVec.ofNat 8 b) :=
    X86CodePlacement.read_range_byte _ _ _ _ installed i _
      ((List.getElem?_eq_some_iff.mp within).choose)
      (by rw [List.getElem?_map, within]; rfl)
  refine ⟨code_of_points image _ _ ?_, code_of_points image _ _ ?_⟩
  · intro i b within
    apply point
    rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp within).choose)]
    exact within
  · intro i b within
    rw [Nat.add_assoc]
    apply point
    rw [List.getElem?_append_right (by omega : first.length ≤ first.length + i)]
    rwa [Nat.add_sub_cancel_left]

theorem Move.bytes_length (w : Wiring) (m : Move oldBase newBase) :
    (m.bytes w).length = m.width w := by
  unfold Move.bytes Move.width
  rw [List.length_append, m.source.bytes_length]
  cases w.writeBase with
  | direct r _ _ => exact congrArg (m.source.width + ·) (X86DataStore.code_length true w.scratch r m.displacement)
  | r12 => exact congrArg (m.source.width + ·) (X86SibQword.code_length .store w.scratch m.displacement)

theorem emitted_size (w : Wiring) (moves : List (Move oldBase newBase)) :
    (emitted w moves).length = size w moves := by
  induction moves with
  | nil => rfl
  | cons first rest ih =>
    change (first.bytes w ++ emitted w rest).length = first.width w + size w rest
    rw [List.length_append, first.bytes_length, ih]

theorem checked_of_emitted (w : Wiring) (image : NativeImage.View) (start : ℕ) (moves : List (Move oldBase newBase))
    (inside : start + (emitted w moves).length ≤ image.size) (placed : Code image start (emitted w moves)) :
    Checked w image start moves := by
  induction moves generalizing start with
  | nil => exact inside
  | cons first later ih =>
    have installed : Code image start (first.bytes w ++ emitted w later) := placed
    obtain ⟨firstCode, laterCode⟩ := code_append installed
    obtain ⟨sourceCode, destCode⟩ := code_append
      (show Code image start (first.source.bytes w ++ w.writeBase.bytes w.scratch first.displacement) from firstCode)
    change start + (first.bytes w ++ emitted w later).length ≤ image.size at inside
    rw [List.length_append, first.bytes_length] at inside
    rw [first.bytes_length] at laterCode
    rw [first.source.bytes_length] at destCode
    exact ⟨⟨by omega, sourceCode, destCode⟩, ih _ (by omega) laterCode⟩

def Separate (moves : List (Move oldBase newBase)) : Prop :=
  moves.Pairwise (fun a b => Disjoint (footprint a.cell.address) (footprint b.cell.address))

theorem member_written {m : Move oldBase newBase} {moves : List (Move oldBase newBase)}
    (member : m ∈ moves) : footprint m.cell.address ⊆ written moves := by
  induction moves with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | found
    · exact Finset.subset_union_left
    · exact (ih found).trans Finset.subset_union_right

theorem apart_written (region : Finset ℕ) (moves : List (Move oldBase newBase))
    (apart : ∀ m ∈ moves, Disjoint region (footprint m.cell.address)) : Disjoint region (written moves) := by
  induction moves with
  | nil => simp [written]
  | cons first rest ih =>
    exact Finset.disjoint_union_right.mpr
      ⟨apart first List.mem_cons_self, ih (fun m inside => apart m (List.mem_cons_of_mem _ inside))⟩

/-- The bytes execute and every destination word is present together
at the endpoint. A write cannot change the source of a later copy,
the code being run, or an earlier destination. -/
theorem fetch_all (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (w : Wiring)
    (moves : List (Move oldBase newBase)) {image : NativeImage.View} {base : BitVec 48}
    {state : X86RegisterRefinement.State} {start : ℕ}
    (point : At image state base start) (controls : Controls state) (checked : Checked w image start moves)
    (readBase : lookup state w.readBase = some oldBase) (writeBase : lookup state w.writeBase.base = some newBase)
    (ready : ∀ m ∈ moves, m.source.Ready state m.value)
    (sources : ∀ m ∈ moves, Disjoint m.source.uses (written moves))
    (outputs : Separate moves) (codeApart : CodeApart image base (written moves)) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ next, (X86FuelPrefix.fetches (2 * moves.length)).run state = .ok () next ∧
      X86StateFrame.Frame (touched w) (written moves) state next ∧
      (∀ m ∈ moves, Reads next m.cell.address m.value) ∧ Nonempty (At image next base (start + size w moves)) := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  induction moves generalizing state start with
  | nil => exact ⟨state, X86FuelPrefix.fetches_zero state,
      X86StateFrame.Frame.refl _ _ _, fun _ h => (List.not_mem_nil h).elim, ⟨point⟩⟩
  | cons front rest ih =>
    obtain ⟨middle, fetched, frame, stored, ⟨remaining⟩⟩ := front.fetch other vector w point controls checked.1
      readBase writeBase (ready front List.mem_cons_self) (codeApart.mono Finset.subset_union_left)
    have tailReady (m : Move oldBase newBase) (inside : m ∈ rest) : m.source.Ready middle m.value := by
      have member : m ∈ front :: rest := List.mem_cons_of_mem _ inside
      exact m.source.ready_preserved (ready m member) frame
        ((sources m member).mono_right Finset.subset_union_left)
    have tailSources (m : Move oldBase newBase) (inside : m ∈ rest) :
        Disjoint m.source.uses (written rest) :=
      (sources m (List.mem_cons_of_mem _ inside)).mono_right Finset.subset_union_right
    have tailSeparate := List.pairwise_cons.mp outputs
    obtain ⟨next, tailRun, tailFrame, tailStored, follow⟩ := ih remaining
      (controls.transport frame (X86Immediate32.writes_data _)) checked.2
      ((frame.lookup _ (outside_scratch w _ w.readPreserved)).trans readBase)
      ((frame.lookup _ (outside_scratch w _ w.writePreserved)).trans writeBase)
      tailReady tailSources tailSeparate.2 (codeApart.mono Finset.subset_union_right)
    have steps : 2 + 2 * rest.length = 2 * (front :: rest).length := by simp [Nat.mul_add, Nat.add_comm]
    refine ⟨next, steps ▸ X86FuelPrefix.fetches_then 2 _ state middle next fetched tailRun,
      (frame.trans tailFrame).mono (by simp) (Finset.Subset.refl _), ?_, ?_⟩
    · intro m chosen
      rcases List.mem_cons.mp chosen with rfl | later
      · exact stored.preserved tailFrame (apart_written _ _ tailSeparate.1)
      · exact tailStored m later
    · simpa only [size, List.map_cons, List.sum_cons, Nat.add_assoc] using follow

namespace Examples

private def wiring : Wiring :=
  ⟨6, by decide, by decide, .direct 7 (by decide) (by decide), 0, by decide, by decide⟩

private def oldSlot : Cell 4096 8 :=
  ⟨4104, by decide +kernel, by decide +kernel, by decide +kernel⟩

private def newSlot : Cell 8192 16 :=
  ⟨8208, by decide +kernel, by decide +kernel, by decide +kernel⟩

private def move (word : Word) : Move 4096 8192 := ⟨.copy 8 oldSlot, word, 16, newSlot⟩

theorem emits_a_load_then_a_store (word : Word) :
    emitted wiring [move word] = [0x48, 0x8b, 0x86, 8, 0, 0, 0, 0x48, 0x89, 0x87, 16, 0, 0, 0] := by
  change emitted wiring [move 0] = _
  decide +kernel

private def view : NativeImage.View :=
  NativeImage.View.ofArray ((emitted wiring [move 42]).map (BitVec.ofNat 8)).toArray

theorem emitted_copy_checks : Checked wiring view 0 [move 42] := by
  apply checked_of_emitted
  · decide +kernel
  · rfl

private def aliased : Move 4096 4096 := ⟨.copy 8 oldSlot, 42, 8, oldSlot⟩

theorem private_destination_cannot_alias_a_copy_source :
    ¬ Disjoint aliased.source.uses (written [aliased]) := by
  intro disjoint
  have byte := X86PlacedMemory.footprint_byte oldSlot.address 0 (by decide)
  exact Finset.disjoint_left.mp disjoint byte (member_written (m := aliased) List.mem_cons_self byte)

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeWords
