import Mettapedia.Machines.TIsa.RowTableView
import Mettapedia.Machines.TIsa.X86BoundedStoreSites
import Mettapedia.Machines.TIsa.X86MemoryFailure

/-!
# Actual native stores under the published-row observer

Logical byte addresses use the original model's canonical physical-key map.
Source store firings construct real native executions. A store beyond the
published row prefix is invisible to this observer at every fetched prefix.
The frame, source representation, image and architectural endpoint remain
available to callers. This does not grant concurrent publication or custody.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86RowTableStore
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView
local instance : MemoryPrimitives := X86Memory.ordinary

def logicalBytes (native : State) : ByteMemory := fun address =>
  if address < 2 ^ 64 ∧ X86CanonicalSpan.Canonical (BitVec.ofNat 64 address) then
    native.mem.get? (X86CanonicalSpan.physicalKey (BitVec.ofNat 64 address)) else none

theorem readonly_hidden (layout : RowTableView.Layout) (before after : State) (registers : Finset Register)
    (frame : RegisterFrame registers before after) :
    RowTableView.observe layout (logicalBytes after) = RowTableView.observe layout (logicalBytes before) := by
  have same : logicalBytes after = logicalBytes before := by
    funext position
    unfold logicalBytes
    rw [frame.memory]
  rw [same]

theorem byte_framed (wide : Bool) (before after : State) (registers : Finset Register) (address other : Nat)
    (addressBound : address < 2 ^ 64)
    (area : X86CanonicalSpan.Area (BitVec.ofNat 64 address) (X86DataStore.byteCount wide))
    (frame : X86StateFrame.Frame registers (X86DataStore.writes wide (X86MemoryStore.target address)) before after)
    (outside : other < address ∨ address + X86DataStore.byteCount wide ≤ other) :
    logicalBytes after other = logicalBytes before other := by
  unfold logicalBytes
  split
  next admitted =>
    apply frame.memory
    apply X86StoreRepresentation.physical_byte_outside wide address other addressBound area admitted.1 admitted.2
    intro member
    obtain ⟨offset,within,same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    have inside := List.mem_range.mp within
    have position : address + offset = other := Memory.Key.byte.inj same
    omega
  next refused => rfl

theorem word_framed (wide : Bool) (before after : State) (registers : Finset Register) (written observed : Nat)
    (addressBound : written < 2 ^ 64)
    (area : X86CanonicalSpan.Area (BitVec.ofNat 64 written) (X86DataStore.byteCount wide))
    (frame : X86StateFrame.Frame registers (X86DataStore.writes wide (X86MemoryStore.target written)) before after)
    (apart : written + X86DataStore.byteCount wide ≤ observed ∨ observed + 8 ≤ written) :
    RowTableView.word (logicalBytes after) observed = RowTableView.word (logicalBytes before) observed := by
  apply RowTableView.word_congr
  intro offset within
  apply byte_framed wide before after registers written _ addressBound area frame
  rcases apart with first | last <;> omega

theorem prepare_hidden_frame (layout : RowTableView.Layout) (wide : Bool) (before after : State)
    (registers : Finset Register) (written : Nat) (count : Word)
    (addressBound : written < 2 ^ 64)
    (area : X86CanonicalSpan.Area (BitVec.ofNat 64 written) (X86DataStore.byteCount wide))
    (frame : X86StateFrame.Frame registers (X86DataStore.writes wide (X86MemoryStore.target written)) before after)
    (countRead : RowTableView.word (logicalBytes before) layout.count = some count)
    (beyond : layout.rows + 8 * (count.toNat * layout.width) ≤ written)
    (countApart : written + X86DataStore.byteCount wide ≤ layout.count ∨ layout.count + 8 ≤ written) :
    RowTableView.observe layout (logicalBytes after) = RowTableView.observe layout (logicalBytes before) := by
  apply RowTableView.observe_congr layout (logicalBytes before) (logicalBytes after) count countRead
  · exact (word_framed wide before after registers written layout.count addressBound area frame countApart).trans countRead
  · intro index inside
    apply RowTableView.row_congr
    intro column columnInside
    apply word_framed wide before after registers written _ addressBound area frame
    have bounds := RowTableView.row_word_inside layout count.toNat index column inside columnInside
    exact Or.inr (by omega)

theorem zeroTail_before_frame (layout : RowTableView.Layout) (wide : Bool) (before after : State)
    (registers : Finset Register) (written first capacity : Nat)
    (addressBound : written < 2 ^ 64)
    (area : X86CanonicalSpan.Area (BitVec.ofNat 64 written) (X86DataStore.byteCount wide))
    (frame : X86StateFrame.Frame registers (X86DataStore.writes wide (X86MemoryStore.target written)) before after)
    (zero : RowTableView.zeroTail layout (logicalBytes before) first capacity)
    (endsBefore : written + X86DataStore.byteCount wide ≤ layout.rows + 8 * (first * layout.width)) :
    RowTableView.zeroTail layout (logicalBytes after) first capacity := by
  intro index later inside column columnInside
  have ordered := Nat.mul_le_mul_right layout.width later
  have apart : written + X86DataStore.byteCount wide ≤ layout.address index column := by
    unfold RowTableView.Layout.address
    omega
  rw [word_framed wide before after registers written _ addressBound area frame (Or.inl apart)]
  exact zero index later inside column columnInside

structure StoreCall (program : P1Capture.Program) (span : P1Capture.Span)
    (instruction : X86BoundedStore.Instruction) (native : State) where
  member : (program,span) ∈ X86BoundedStoreCapture.sites
  decoded : X86BoundedStoreCapture.decode? program span = some instruction
  view : View
  values : Key → Word
  entry : X86BoundedStoreSites.Entry program span instruction view values native
  address : Nat
  following : World
  safe : entry.profile.enabled = false ∨ X86MemoryStore.target address &&&
    BitVec.ofNat 48 (X86DataStore.byteCount instruction.wide - 1) = (0#48)
  source : (CellEffects.profile [X86BoundedStoreSource.recipe instruction address]).theory.rewrites
    (Cells.encode view.keys values) following
  descriptors : X86MemoryStore.DescriptorsApart view native (X86DataStore.writes instruction.wide (X86MemoryStore.target address))
  codeApart : ∀ offset < program.size, ((X86Execution.address entry.base offset).signExtend 52).toNat ∉
    X86DataStore.writes instruction.wide (X86MemoryStore.target address)

theorem StoreCall.target_geometry {program : P1Capture.Program} {span : P1Capture.Span}
    {instruction : X86BoundedStore.Instruction} {native : State} (call : StoreCall program span instruction native) :
    call.address < 2 ^ 64 ∧ X86CanonicalSpan.Area (BitVec.ofNat 64 call.address) (X86DataStore.byteCount instruction.wide) := by
  obtain ⟨_produced,included,_mode,_access,_output,_endpoint⟩ :=
    (X86MemoryStore.source_store_iff (X86StoreRepresentation.width instruction.wide) instruction.region.val
      instruction.base instruction.source (X86BoundedStore.displacement instruction).toInt call.address
      call.view.keys call.values call.following).mp call.source
  have present : ∀ index < X86DataStore.byteCount instruction.wide,
      Memory.Key.byte (call.address + index) ∈ call.view.keys := by
    intro index within
    apply included
    apply Finset.mem_union_left
    simp [CellEffects.Recipe.writes,P1Memory.storeRecipe,P1Memory.storeSpec,Memory.Store.recipe,
      Memory.byteKeys,P1Memory.memoryWidth_bytes,X86StoreRepresentation.width_bytes,within]
  have positive : 0 < X86DataStore.byteCount instruction.wide := by cases instruction.wide <;> decide
  have seen := X86MemoryReadback.byte_observed call.view.modes native call.address _
    (call.entry.known (.byte call.address) (by simpa using present 0 positive))
  exact ⟨seen.1,X86MemoryStore.represented_byte_area call.view call.values native call.address _ positive
    call.entry.known present⟩

theorem StoreCall.support {program : P1Capture.Program} {span : P1Capture.Span}
    {instruction : X86BoundedStore.Instruction} {native : State} (call : StoreCall program span instruction native) :
    (X86BoundedStoreSource.recipe instruction call.address).support ⊆ call.view.keys := by
  obtain ⟨_produced,included,_mode,_access,_output,_endpoint⟩ :=
    (X86MemoryStore.source_store_iff (X86StoreRepresentation.width instruction.wide) instruction.region.val
      instruction.base instruction.source (X86BoundedStore.displacement instruction).toInt call.address
      call.view.keys call.values call.following).mp call.source
  exact included

def StoreCall.bounds_input {program : P1Capture.Program} {span : P1Capture.Span}
    {instruction : X86BoundedStore.Instruction} {native : State} (call : StoreCall program span instruction native) :
    X86Bounds.Inputs (X86BoundedStore.layout instruction) native call.entry.origin := by
  have basePresent : Memory.Key.capabilityBase instruction.region.val ∈ call.view.keys := by
    apply call.support
    simp [CellEffects.Recipe.support,X86BoundedStoreSource.recipe,P1Memory.storeRecipe,P1Memory.storeSpec,Memory.Store.recipe,Memory.capabilityKeys]
  have lengthPresent : Memory.Key.capabilityLength instruction.region.val ∈ call.view.keys := by
    apply call.support
    simp [CellEffects.Recipe.support,X86BoundedStoreSource.recipe,P1Memory.storeRecipe,P1Memory.storeSpec,Memory.Store.recipe,Memory.capabilityKeys]
  let facts := X86MemoryBounds.facts call.view call.values native (X86BoundedStore.layout instruction)
    instruction.base call.entry.profile call.entry.flags rfl call.entry.known basePresent lengthPresent
    call.entry.frameArea call.entry.frameAligned call.entry.holds call.entry.flagsKnown call.entry.quiet
  have checked := List.all_eq_true.mp X86BoundedStoreCapture.all_checked (program,span) call.member
  have valid := (X86BoundedStoreCapture.matched_info program span instruction call.decoded checked).1
  have loaded := X86BoundedStoreCapture.loaded_template program span instruction call.decoded checked native call.entry.base
    call.entry.origin call.entry.placed call.entry.loaded
  exact { facts with
    geometry := X86BoundedStoreCapture.geometry program span instruction valid call.entry.origin.address call.entry.base
      call.entry.placed call.entry.upper
    loaded := X86FetchEntry.codeLoaded_left native call.entry.origin.address.toInt _ _ loaded }

theorem StoreCall.fits {program : P1Capture.Program} {span : P1Capture.Span}
    {instruction : X86BoundedStore.Instruction} {native : State} (call : StoreCall program span instruction native) :
    (call.bounds_input.pointer - call.bounds_input.base).toNat + instruction.offset.val +
      (X86BoundedStore.layout instruction).count.val ≤ call.bounds_input.length.toNat := by
  obtain ⟨_produced,_included,_mode,access,_output,_endpoint⟩ :=
    (X86MemoryStore.source_store_iff (X86StoreRepresentation.width instruction.wide) instruction.region.val
      instruction.base instruction.source (X86BoundedStore.displacement instruction).toInt call.address
      call.view.keys call.values call.following).mp call.source
  have sized : (X86StoreRepresentation.width instruction.wide).bytes = (X86BoundedStore.layout instruction).count.val := by
    cases selected : instruction.wide <;>
      simp [X86StoreRepresentation.width,X86BoundedLoadSource.width,X86BoundedStore.layout,selected,P1Source.Width.bytes]
  have formed := (P1Memory.access?_iff_inside _ _ _ (X86BoundedStore.displacement instruction) _ call.address
    call.entry.rangeFits call.entry.pointerLower call.entry.pointerUpper).mp access
  rw [X86BoundedStore.displacement,X86BoundsArithmetic.offset_toInt] at formed
  have coordinate : call.address = (call.values (.register instruction.base)).toNat + instruction.offset.val := by omega
  have fits := (X86BoundsArithmetic.source_guard _ _ _ instruction.offset (X86BoundedStore.layout instruction).count
    call.entry.rangeFits call.entry.pointerLower call.entry.pointerUpper).mpr (by
      simpa only [sized,coordinate,X86BoundedStore.displacement] using access)
  simpa only [StoreCall.bounds_input,X86MemoryBounds.facts,X86MemoryBounds.facts_observed,X86MemoryBounds.facts_at,
    X86BoundedStore.layout] using fits

theorem StoreCall.before_store (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {program : P1Capture.Program} {span : P1Capture.Span} {instruction : X86BoundedStore.Instruction} {native : State}
    (call : StoreCall program span instruction native) (prefixCount : Nat)
    (within : prefixCount < X86BoundedStore.count instruction) (seen : State)
    (executed : letI : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
                letI : VectorOpcodeHandlers := vector
                (X86FuelPrefix.fetches prefixCount).run native = .ok () seen) :
    RegisterFrame X86Bounds.writes native seen := by
  apply X86Bounds.success_prefix_frame other extra vector (X86BoundedStore.layout instruction) native
    call.entry.origin call.bounds_input call.fits prefixCount _ seen executed
  unfold X86BoundedStore.count at within
  omega

theorem source_stages (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (program : P1Capture.Program) (span : P1Capture.Span) (instruction : X86BoundedStore.Instruction)
    (native : State) (call : StoreCall program span instruction native) (layout : RowTableView.Layout) (count : Word)
    (countRead : RowTableView.word (logicalBytes native) layout.count = some count)
    (beyond : layout.rows + 8 * (count.toNat * layout.width) ≤ call.address)
    (countApart : call.address + X86DataStore.byteCount instruction.wide ≤ layout.count ∨ layout.count + 8 ≤ call.address) :
    letI : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (X86BoundedStore.count instruction)).run native = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide (X86MemoryStore.target call.address)) native after ∧
      represents call.view call.following after ∧
      RowTableView.observe layout (logicalBytes after) = RowTableView.observe layout (logicalBytes native) ∧
      after.regs.get? .rip = some ((address call.entry.base (span.offset + span.length)).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ call.entry.profile.Holds after ∧
      X86P1LoadCapture.Loaded program after call.entry.base ∧
      ∀ prefixCount ≤ X86BoundedStore.count instruction, ∀ seen,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () seen →
          RowTableView.observe layout (logicalBytes seen) = RowTableView.observe layout (logicalBytes native) := by
  let : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨_path,after,nextFlags,run,frame,represented,_stored,rip,flagsRead,_quiet,_control,holds,image,prefixes⟩ :=
    X86BoundedStoreSites.source_executes other extra vector program span instruction call.member call.decoded
      call.view call.values native call.entry call.address call.following call.safe call.source call.descriptors call.codeApart
  obtain ⟨addressBound,area⟩ := call.target_geometry
  refine ⟨after,nextFlags,run,frame,represented,prepare_hidden_frame layout instruction.wide native after _ call.address count
    addressBound area frame countRead beyond countApart,rip,flagsRead,holds,image,?_⟩
  intro prefixCount within seen executed
  exact prepare_hidden_frame layout instruction.wide native seen _ call.address count addressBound area
    (prefixes prefixCount within seen executed) countRead beyond countApart

theorem word_written (after : State) (address : Nat) (value : Word) (addressBound : address < 2 ^ 64)
    (area : X86CanonicalSpan.Area (BitVec.ofNat 64 address) 8)
    (stored : ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress (X86MemoryStore.target address) index) =
      some (value.extractLsb' (8 * index) 8)) :
    RowTableView.word (logicalBytes after) address = some value := by
  apply RowTableView.word_known
  intro index within
  have bound : address + index < 2 ^ 64 := by
    have whole := area.1
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt addressBound] at whole
    omega
  have canonical : X86CanonicalSpan.Canonical (BitVec.ofNat 64 (address + index)) := by
    rw [BitVec.ofNat_add]
    exact area.2 index within
  unfold logicalBytes
  rw [if_pos ⟨bound,canonical⟩,X86StoreRepresentation.source_key_at true address index area within]
  have valueAt := X86StoreRepresentation.unpack64_byte value ⟨index,within⟩
  rw [valueAt]
  exact stored index within

theorem publish_frame (layout : RowTableView.Layout) (before after : State) (registers : Finset Register)
    (count : Word) (addressBound : layout.count < 2 ^ 64)
    (area : X86CanonicalSpan.Area (BitVec.ofNat 64 layout.count) 8)
    (frame : X86StateFrame.Frame registers (X86DataStore.writes true (X86MemoryStore.target layout.count)) before after)
    (stored : ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress (X86MemoryStore.target layout.count) index) =
      some ((BitVec.ofNat 64 (count.toNat + 1)).extractLsb' (8 * index) 8))
    (countRead : RowTableView.word (logicalBytes before) layout.count = some count)
    (noWrap : count.toNat + 1 < 2 ^ 64) (apart : layout.countApart (count.toNat + 1)) :
    RowTableView.observe layout (logicalBytes after) =
      (RowTableView.observe layout (logicalBytes before)).bind (fun earlier =>
        (RowTableView.row layout (logicalBytes before) count.toNat).map (fun last => earlier ++ [last])) := by
  have newCount := word_written after layout.count (BitVec.ofNat 64 (count.toNat + 1)) addressBound area stored
  have rowsSame (index : Nat) (inside : index < count.toNat + 1) :
      RowTableView.row layout (logicalBytes after) index = RowTableView.row layout (logicalBytes before) index := by
    apply RowTableView.row_congr
    intro column columnInside
    apply word_framed true before after registers layout.count _ addressBound area frame
    have bounds := RowTableView.row_word_inside layout (count.toNat + 1) index column inside columnInside
    rcases apart with first | last
    · exact Or.inl (by change layout.count + 8 ≤ _;omega)
    · exact Or.inr (by omega)
  simp only [RowTableView.observe,newCount,countRead,Option.bind_some,BitVec.toNat_ofNat,Nat.mod_eq_of_lt noWrap]
  rw [RowTableView.rowsBefore_congr layout (logicalBytes before) (logicalBytes after) _ rowsSame,
    RowTableView.rowsBefore_succ]

theorem source_publishes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (program : P1Capture.Program) (span : P1Capture.Span) (instruction : X86BoundedStore.Instruction)
    (native : State) (call : StoreCall program span instruction native) (layout : RowTableView.Layout) (count : Word)
    (wide : instruction.wide = true) (atCount : call.address = layout.count)
    (payload : call.values (.register instruction.source) = BitVec.ofNat 64 (count.toNat + 1))
    (countRead : RowTableView.word (logicalBytes native) layout.count = some count)
    (noWrap : count.toNat + 1 < 2 ^ 64) (apart : layout.countApart (count.toNat + 1)) :
    letI : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (X86BoundedStore.count instruction)).run native = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes true (X86MemoryStore.target layout.count)) native after ∧
      represents call.view call.following after ∧
      RowTableView.observe layout (logicalBytes after) =
        (RowTableView.observe layout (logicalBytes native)).bind (fun earlier =>
          (RowTableView.row layout (logicalBytes native) count.toNat).map (fun last => earlier ++ [last])) ∧
      after.regs.get? .rip = some ((address call.entry.base (span.offset + span.length)).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ call.entry.profile.Holds after ∧
      X86P1LoadCapture.Loaded program after call.entry.base ∧
      ∀ prefixCount < X86BoundedStore.count instruction, ∀ seen,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () seen →
          RowTableView.observe layout (logicalBytes seen) = RowTableView.observe layout (logicalBytes native) := by
  let : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨_path,after,nextFlags,run,frame,represented,stored,rip,flagsRead,_quiet,_control,holds,image,_prefixes⟩ :=
    X86BoundedStoreSites.source_executes other extra vector program span instruction call.member call.decoded
      call.view call.values native call.entry call.address call.following call.safe call.source call.descriptors call.codeApart
  obtain ⟨addressBound,area⟩ := call.target_geometry
  rw [wide,atCount] at frame area
  rw [wide,atCount,payload] at stored
  have observed := publish_frame layout native after X86Bounds.writes count (atCount ▸ addressBound) area
    frame stored countRead noWrap apart
  refine ⟨after,nextFlags,run,frame,represented,observed,rip,flagsRead,holds,image,?_⟩
  intro prefixCount within seen executed
  have beforeStore := call.before_store other extra vector prefixCount within seen executed
  have sameBytes : logicalBytes seen = logicalBytes native := by
    funext position
    unfold logicalBytes
    rw [beforeStore.memory]
  rw [sameBytes]

theorem source_failure_hidden (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (write : Bool) (width : P1Source.Width) (bounds : X86Bounds.Layout) (pointer : Fin 12)
    (sized : width.bytes = bounds.count.val) (keys : Finset Key) (modes : Fin 9 → Word)
    (values : Key → Word) (native : State) (entry : X86MemoryFailure.Entry bounds pointer keys modes values native)
    (following : World) (source : (CellEffects.profile [X86MemoryFailure.recipe write width bounds pointer]).theory.rewrites
      (Cells.encode keys values) following) (layout : RowTableView.Layout) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (X86MemoryFailure.count bounds pointer values)).run native = .ok () after ∧
      RegisterFrame X86Bounds.writes native after ∧
      RowTableView.observe layout (logicalBytes after) = RowTableView.observe layout (logicalBytes native) ∧
      after.regs.get? .rip = some ((X86Bounds.position entry.origin.address bounds.reject).signExtend 64) ∧
      ∀ prefixCount ≤ X86MemoryFailure.count bounds pointer values, ∀ seen,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () seen →
          RowTableView.observe layout (logicalBytes seen) = RowTableView.observe layout (logicalBytes native) := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨_unchanged,after,_flags,run,frame,_readbacks,rip,_flagsRead,_quiet,_control,_holds,prefixes⟩ :=
    X86MemoryFailure.source_executes other extra vector write width bounds pointer sized keys modes values native entry following source
  refine ⟨after,run,frame,readonly_hidden layout native after _ frame,rip,?_⟩
  intro prefixCount within seen executed
  exact readonly_hidden layout native seen _ (prefixes prefixCount within seen executed)

#print axioms prepare_hidden_frame
#print axioms source_stages
#print axioms word_written
#print axioms StoreCall.before_store
#print axioms source_publishes
#print axioms source_failure_hidden
#print axioms zeroTail_before_frame
end Mettapedia.Machines.TIsa.X86RowTableStore
