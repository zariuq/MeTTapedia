import Mettapedia.Machines.TIsa.P1EntryMemory
import Mettapedia.Machines.TIsa.X86BoundedLoadSites
import Mettapedia.Machines.TIsa.X86BoundedStoreSites
import Mettapedia.Machines.TIsa.X86FrameLoadCapture

/-!
# Micromath sub1 source memory accesses and x86 sites

Each load and store path has a checked x86 span. At an admitted region or frame
base, the memory recipes and native spans agree on the accessed bytes, the
updated state and the next instruction.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1Sub1Memory

open P1Source P1EntryMemory

private theorem sub1_in_captured_prefix : sub1 ∈ ImportedP1.programs.take 13 := by
  have within : 11 < (ImportedP1.programs.take 13).length := by
    rw [List.length_take, ImportedP1.exact_count.2]
    decide
  simpa only [List.getElem_take, sub1] using List.getElem_mem within

private theorem find_path {spans : List P1Capture.Span} {paths : List (List Nat)} {path : List Nat}
    (mapped : spans.mapM P1Capture.Span.path = some paths) (member : path ∈ paths) :
    ∃ span ∈ spans, span.path = some path := by
  induction spans generalizing paths with
  | nil =>
      change some [] = some paths at mapped
      cases mapped
      simp at member
  | cons span spans ih =>
      cases head : span.path <;> cases tail : spans.mapM P1Capture.Span.path <;>
        simp [List.mapM_cons, head, tail] at mapped
      rename_i headPath tailPaths
      subst paths
      rcases List.mem_cons.mp member with same | member
      · exact ⟨span, by simp, head.trans (congrArg some same.symm)⟩
      · obtain ⟨found, included, atPath⟩ := ih tail member
        exact ⟨found, List.mem_cons_of_mem _ included, atPath⟩

theorem load_at (path : List Nat) (pathMember : path ∈ X86BoundedLoadCapture.loadPaths sub1.source.body) :
    ∃ span instruction,
      (sub1,span) ∈ X86BoundedLoadCapture.sites ∧
      span.path = some path ∧
      X86BoundedLoadCapture.decode? sub1 span = some instruction ∧
      X86BoundedLoadCapture.Valid sub1 span instruction ∧
      sub1.source.body.atPath path = some (.instruction (X86BoundedLoadSource.p1 instruction)) ∧
      ∀ index : Fin span.length,
        sub1.view.read (span.offset + index.val) = ((X86BoundedLoad.bytes instruction)[index.val]?).map (BitVec.ofNat 8) := by
  obtain ⟨span, inSpans, atPath⟩ :=
    find_path (X86BoundedLoadCapture.source_coverage sub1 sub1_in_captured_prefix) pathMember
  have site : (sub1,span) ∈ X86BoundedLoadCapture.sites :=
    List.mem_flatMap.mpr ⟨sub1, sub1_in_captured_prefix, List.mem_map.mpr ⟨span, inSpans, rfl⟩⟩
  obtain ⟨instruction, decoded, valid, bytes⟩ := X86BoundedLoadCapture.captured_site sub1 span site
  obtain ⟨recorded, recordedPath, source⟩ := X86BoundedLoadCapture.decoded_source sub1 span instruction decoded
  have same := Option.some.inj (recordedPath.symm.trans atPath)
  exact ⟨span, instruction, site, atPath, decoded, valid, same ▸ source, bytes⟩

theorem store_at (path : List Nat) (pathMember : path ∈ X86BoundedStoreCapture.storePaths sub1.source.body) :
    ∃ span instruction,
      (sub1,span) ∈ X86BoundedStoreCapture.sites ∧
      span.path = some path ∧
      X86BoundedStoreCapture.decode? sub1 span = some instruction ∧
      X86BoundedStoreCapture.Valid sub1 span instruction ∧
      sub1.source.body.atPath path = some (.instruction (X86BoundedStoreSource.p1 instruction)) ∧
      ∀ index : Fin span.length,
        sub1.view.read (span.offset + index.val) = ((X86BoundedStore.bytes instruction)[index.val]?).map (BitVec.ofNat 8) := by
  obtain ⟨span, inSpans, atPath⟩ :=
    find_path (X86BoundedStoreCapture.source_coverage sub1 sub1_in_captured_prefix) pathMember
  have site : (sub1,span) ∈ X86BoundedStoreCapture.sites :=
    List.mem_flatMap.mpr ⟨sub1, sub1_in_captured_prefix, List.mem_map.mpr ⟨span, inSpans, rfl⟩⟩
  obtain ⟨instruction, decoded, valid, bytes⟩ := X86BoundedStoreCapture.captured_site sub1 span site
  obtain ⟨recorded, recordedPath, source⟩ := X86BoundedStoreCapture.decoded_source sub1 span instruction decoded
  have same := Option.some.inj (recordedPath.symm.trans atPath)
  exact ⟨span, instruction, site, atPath, decoded, valid, same ▸ source, bytes⟩


theorem load_address (path : List Nat) (instruction : X86BoundedLoad.Instruction)
    (located : sub1.source.body.atPath path = some (.instruction (X86BoundedLoadSource.p1 instruction)))
    (decl : RegionDecl) (region : sub1.source.regions[instruction.region.val]? = some decl)
    (base length : Word) (minimum : decl.minimum.toNat ≤ length.toNat)
    (fits : base.toNat + length.toNat < 2 ^ 64) :
    Memory.access? base length base (X86BoundedLoad.displacement instruction).toInt
      (X86BoundedLoadSource.width instruction.wide).bytes =
      some (base.toNat + (X86BoundedLoad.displacement instruction).toInt.toNat) := by
  let access : Access := ⟨instruction.region, instruction.base,
    X86BoundedLoadSource.width instruction.wide, X86BoundedLoad.displacement instruction, false⟩
  exact sub1_access_at_path path _ access located
    (by simp [access, X86BoundedLoadSource.p1, accesses]) decl region base length minimum fits

theorem store_address (path : List Nat) (instruction : X86BoundedStore.Instruction)
    (located : sub1.source.body.atPath path = some (.instruction (X86BoundedStoreSource.p1 instruction)))
    (decl : RegionDecl) (region : sub1.source.regions[instruction.region.val]? = some decl)
    (base length : Word) (minimum : decl.minimum.toNat ≤ length.toNat)
    (fits : base.toNat + length.toNat < 2 ^ 64) :
    Memory.access? base length base (X86BoundedStore.displacement instruction).toInt
      (X86BoundedStoreSource.width instruction.wide).bytes =
      some (base.toNat + (X86BoundedStore.displacement instruction).toInt.toNat) := by
  let access : Access := ⟨instruction.region, instruction.base,
    X86BoundedStoreSource.width instruction.wide, X86BoundedStore.displacement instruction, true⟩
  exact sub1_access_at_path path _ access located
    (by simp [access, X86BoundedStoreSource.p1, accesses]) decl region base length minimum fits

theorem explicit_site_counts :
    (X86BoundedLoadCapture.loadPaths sub1.source.body).length = 18 ∧
    (X86BoundedStoreCapture.storePaths sub1.source.body).length = 4 := by
  constructor <;> kernel_reflexivity


open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView
local instance : MemoryPrimitives := X86Memory.ordinary

/-- The live capability cells and the borrowed pointer agree with the source declaration. -/
structure EntryRegion (region : Region) (pointer : Reg) (values : Key → Word) where
  declaration : RegionDecl
  declared : sub1.source.regions[region.val]? = some declaration
  pointerAtBase : values (.register pointer) = values (.capabilityBase region.val)
  minimum : declaration.minimum.toNat ≤ (values (.capabilityLength region.val)).toNat
  fits : (values (.capabilityBase region.val)).toNat + (values (.capabilityLength region.val)).toNat < 2 ^ 64
  mode : values (.capabilityMode region.val) = BitVec.ofNat 64 declaration.mode.number
  aligned : (values (.capabilityBase region.val)).toNat % 8 = 0

def EntryRegion.address {region : Region} {pointer : Reg} {values : Key → Word}
    (_region : EntryRegion region pointer values) (displacement : BitVec 32) : Nat :=
  (values (.capabilityBase region.val)).toNat + displacement.toInt.toNat

private theorem declared_qword (access : Access) (member : access ∈ accesses sub1.source.body) :
    access.width = .word64 ∧ access.displacement.toInt.toNat % 8 = 0 := by
  have checked : (accesses sub1.source.body).all
      (fun site => decide (site.width = .word64 ∧ site.displacement.toInt.toNat % 8 = 0)) = true := by
    kernel_reflexivity
  exact of_decide_eq_true (List.all_eq_true.mp checked access member)

private theorem admitted_access (values : Key → Word) (access : Access)
    (member : access ∈ accesses sub1.source.body)
    (layout : EntryRegion access.region access.pointer values) :
    access.width = .word64 ∧
    (if access.write then values (.capabilityMode access.region.val) = 2
     else values (.capabilityMode access.region.val) = 1 ∨ values (.capabilityMode access.region.val) = 2) ∧
    Memory.access? (values (.capabilityBase access.region.val)) (values (.capabilityLength access.region.val))
      (values (.register access.pointer)) access.displacement.toInt 8 = some (layout.address access.displacement) ∧
    layout.address access.displacement % 8 = 0 := by
  have checked := List.all_eq_true.mp sub1_accesses_checked access member
  have mode := (access.checked sub1.source layout.declaration layout.declared checked).2.1
  obtain ⟨width, offsetAligned⟩ := declared_qword access member
  refine ⟨width, ?_, ?_, ?_⟩
  · cases write : access.write <;> cases decl : layout.declaration.mode <;>
      simp [write, decl, layout.mode, Mode.number] at mode ⊢
  · simpa only [layout.pointerAtBase, width, P1Source.Width.bytes, EntryRegion.address] using
      access.address_at_base sub1.source layout.declaration layout.declared checked
        (values (.capabilityBase access.region.val)) (values (.capabilityLength access.region.val))
        layout.minimum layout.fits
  · rw [EntryRegion.address, Nat.add_mod, layout.aligned, offsetAligned]

private theorem aligned_readback (view : View) (values : Key → Word) (native : State) (address : Nat)
    (known : ∀ key ∈ view.keys, readback view.modes native key = some (values key))
    (present : Memory.Key.byte address ∈ view.keys) (aligned : address % 8 = 0) :
    X86CanonicalSpan.narrow (BitVec.ofNat 64 address) &&& (7#48) = (0#48) := by
  obtain ⟨bound, canonical, _⟩ :=
    X86MemoryReadback.byte_observed view.modes native address _ (known _ present)
  apply X86CanonicalSpan.narrow_aligned _ canonical
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using aligned

theorem load_from_entry_region
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (span : P1Capture.Span) (instruction : X86BoundedLoad.Instruction)
    (site : (sub1,span) ∈ X86BoundedLoadCapture.sites)
    (decoded : X86BoundedLoadCapture.decode? sub1 span = some instruction)
    (view : View) (values : Key → Word) (native : State)
    (entry : X86BoundedLoadSites.Entry sub1 span instruction view values native)
    (layout : EntryRegion instruction.region instruction.base values)
    (included : (X86BoundedLoadSource.recipe instruction
      (layout.address (X86BoundedLoad.displacement instruction))).support ⊆ view.keys) :
    letI : OtherOpcodeHandlers := X86BoundedLoad.handlers other extra
    letI : VectorOpcodeHandlers := vector
    let address := layout.address (X86BoundedLoad.displacement instruction)
    ∃ value after flags,
      (CellEffects.profile [X86BoundedLoadSource.recipe instruction address]).theory.rewrites
        (Cells.encode view.keys values)
        (Cells.encode view.keys (Function.update values (.register instruction.destination) value)) ∧
      (X86FuelPrefix.fetches (X86BoundedLoad.count instruction)).run native = .ok () after ∧
      X86Execution.RegisterFrame (X86BoundedLoad.writes instruction) native after ∧
      represents view
        (Cells.encode view.keys (Function.update values (.register instruction.destination) value)) after ∧
      after.regs.get? .rip = some ((X86Execution.address entry.base (span.offset + span.length)).signExtend 64) ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧ entry.profile.Holds after ∧
      X86P1LoadCapture.Loaded sub1 after entry.base := by
  let : OtherOpcodeHandlers := X86BoundedLoad.handlers other extra
  let : VectorOpcodeHandlers := vector
  let address := layout.address (X86BoundedLoad.displacement instruction)
  obtain ⟨path, _, located⟩ := X86BoundedLoadCapture.decoded_source sub1 span instruction decoded
  let access : Access := ⟨instruction.region, instruction.base,
    X86BoundedLoadSource.width instruction.wide, X86BoundedLoad.displacement instruction, false⟩
  have member : access ∈ accesses sub1.source.body :=
    mem_accesses_of_atPath located (by simp [access, X86BoundedLoadSource.p1, accesses])
  obtain ⟨width, mode, accessOK, aligned⟩ := admitted_access values access member layout
  have wide : instruction.wide = true := by
    cases narrow : instruction.wide <;> simp [access, X86BoundedLoadSource.width, narrow] at width ⊢
  have present (offset : Nat) (inside : offset < 8) : Memory.Key.byte (address + offset) ∈ view.keys := by
    apply included
    simp [X86BoundedLoadSource.recipe, X86BoundedLoadSource.width, wide, P1Memory.loadRecipe,
      CellEffects.Recipe.support, CellEffects.Recipe.writes, Memory.capabilityKeys, Memory.byteKeys,
      P1Source.Width.bytes]
    exact ⟨offset, inside, rfl⟩
  obtain ⟨bytes, observed, _, _⟩ :=
    X86MemoryReadback.byte_words_observed view values native address entry.known present
  let value := packBytes bytes
  let updated := Cells.encode view.keys (Function.update values (.register instruction.destination) value)
  have rewritten : (CellEffects.profile [X86BoundedLoadSource.recipe instruction address]).theory.rewrites
      (Cells.encode view.keys values) updated := by
    unfold X86BoundedLoadSource.recipe
    rw [wide]
    apply (P1Memory.load_rewrite_iff .u64 .word64 instruction.region.val instruction.destination
      instruction.base (X86BoundedLoad.displacement instruction).toInt address view.keys values updated).mpr
    refine ⟨value, ?_, mode, accessOK, ?_, rfl⟩
    · simpa only [X86BoundedLoadSource.recipe, wide, X86BoundedLoadSource.tag, X86BoundedLoadSource.width, if_true] using included
    · change P1Memory.loadValue .u64 ((Memory.byteKeys address 8).map values) = some value
      rw [observed, P1Memory.load_byteWords]
      rfl
  have safe : entry.profile.enabled = false ∨ X86CanonicalSpan.narrow (BitVec.ofNat 64 address) &&&
      BitVec.ofNat 48 (X86DataLoad.byteCount instruction.wide - 1) = (0#48) := by
    right
    have presentFirst : Memory.Key.byte address ∈ view.keys := by simpa only [Nat.add_zero] using present 0 (by decide)
    simpa only [wide, X86DataLoad.byteCount, if_true] using
      aligned_readback view values native address entry.known presentFirst aligned
  obtain ⟨_, after, flags, run, frame, represented, rip, changedFlags, quiet, controls, holds, loaded, _⟩ :=
    X86BoundedLoadSites.source_executes other extra vector sub1 span instruction site decoded
      view values native entry address updated safe rewritten
  exact ⟨value, after, flags, rewritten, run, frame, represented, rip, changedFlags, quiet, controls, holds, loaded⟩


theorem store_from_entry_region
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (span : P1Capture.Span) (instruction : X86BoundedStore.Instruction)
    (site : (sub1,span) ∈ X86BoundedStoreCapture.sites)
    (decoded : X86BoundedStoreCapture.decode? sub1 span = some instruction)
    (view : View) (values : Key → Word) (native : State)
    (entry : X86BoundedStoreSites.Entry sub1 span instruction view values native)
    (layout : EntryRegion instruction.region instruction.base values)
    (included : (X86BoundedStoreSource.recipe instruction
      (layout.address (X86BoundedStore.displacement instruction))).support ⊆ view.keys)
    (descriptors : X86MemoryStore.DescriptorsApart view native
      (X86DataStore.writes instruction.wide (X86MemoryStore.target
        (layout.address (X86BoundedStore.displacement instruction)))))
    (codeApart : ∀ offset < sub1.size, ((X86Execution.address entry.base offset).signExtend 52).toNat ∉
      X86DataStore.writes instruction.wide (X86MemoryStore.target
        (layout.address (X86BoundedStore.displacement instruction)))) :
    letI : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
    letI : VectorOpcodeHandlers := vector
    let address := layout.address (X86BoundedStore.displacement instruction)
    ∃ following after flags,
      (CellEffects.profile [X86BoundedStoreSource.recipe instruction address]).theory.rewrites
        (Cells.encode view.keys values) following ∧
      (X86FuelPrefix.fetches (X86BoundedStore.count instruction)).run native = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes
        (X86DataStore.writes instruction.wide (X86MemoryStore.target address)) native after ∧
      represents view following after ∧
      (∀ index < 8,
        after.mem.get? (X86WriteWords.physicalAddress (X86MemoryStore.target address) index) =
          some ((values (.register instruction.source)).extractLsb' (8 * index) 8)) ∧
      after.regs.get? .rip = some ((X86Execution.address entry.base (span.offset + span.length)).signExtend 64) ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧ entry.profile.Holds after ∧
      X86P1LoadCapture.Loaded sub1 after entry.base := by
  let : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
  let : VectorOpcodeHandlers := vector
  let address := layout.address (X86BoundedStore.displacement instruction)
  obtain ⟨path, _, located⟩ := X86BoundedStoreCapture.decoded_source sub1 span instruction decoded
  let access : Access := ⟨instruction.region, instruction.base,
    X86BoundedStoreSource.width instruction.wide, X86BoundedStore.displacement instruction, true⟩
  have member : access ∈ accesses sub1.source.body :=
    mem_accesses_of_atPath located (by simp [access, X86BoundedStoreSource.p1, accesses])
  obtain ⟨width, mode, accessOK, aligned⟩ := admitted_access values access member layout
  have wide : instruction.wide = true := by
    cases narrow : instruction.wide <;> simp [access, X86BoundedLoadSource.width, narrow] at width ⊢
  let payload := values (.register instruction.source)
  let produced : Key → Word := fun key => match key with
    | .byte other => (payload.extractLsb' (8 * (other - address)) 8).zeroExtend 64
    | _ => values key
  let recipe := X86BoundedStoreSource.recipe instruction address
  let following := Cells.encode view.keys (CellEffects.overwrite recipe.writes values produced)
  have output : (Memory.byteKeys address 8).map produced = Memory.byteWords (unpackBytes 8 payload) := by
    apply List.ext_getElem
    · simp [Memory.byteKeys, Memory.byteWords, unpackBytes_length]
    · intro index lhsBound rhsBound
      have within : index < 8 := by simpa [Memory.byteKeys] using lhsBound
      simp only [Memory.byteKeys, Memory.byteWords, List.getElem_map, List.getElem_range,
        produced, Nat.add_sub_cancel_left, X86StoreRepresentation.unpack64_byte payload ⟨index, within⟩]
  have rewritten : (CellEffects.profile [recipe]).theory.rewrites (Cells.encode view.keys values) following := by
    unfold recipe X86BoundedStoreSource.recipe
    rw [wide]
    apply (X86MemoryStore.source_store_iff .word64 instruction.region.val instruction.base
      instruction.source (X86BoundedStore.displacement instruction).toInt address view.keys values following).mpr
    refine ⟨produced, ?_, mode, accessOK, output, ?_⟩
    · simpa only [X86BoundedStoreSource.recipe, wide, X86BoundedLoadSource.width, if_true] using included
    · simp only [following, recipe, X86BoundedStoreSource.recipe, wide, X86BoundedLoadSource.width, if_true]
  have presentFirst : Memory.Key.byte address ∈ view.keys := by
    apply included
    change Memory.Key.byte address ∈ recipe.support
    simp [recipe, X86BoundedStoreSource.recipe, wide, X86BoundedLoadSource.width, P1Memory.storeRecipe,
      P1Memory.storeSpec, Memory.Store.recipe, CellEffects.Recipe.support, CellEffects.Recipe.writes,
      Memory.capabilityKeys, Memory.byteKeys, P1Memory.memoryWidth, Memory.Width.bytes]
  have safe : entry.profile.enabled = false ∨ X86MemoryStore.target address &&&
      BitVec.ofNat 48 (X86DataStore.byteCount instruction.wide - 1) = (0#48) := by
    right
    simpa only [X86MemoryStore.target, wide, X86DataStore.byteCount, if_true] using
      aligned_readback view values native address entry.known presentFirst aligned
  obtain ⟨_, after, flags, run, frame, represented, stored, rip, changedFlags, quiet, controls, holds, loaded, _⟩ :=
    X86BoundedStoreSites.source_executes other extra vector sub1 span instruction site decoded
      view values native entry address following safe rewritten descriptors codeApart
  exact ⟨following, after, flags, rewritten, run, frame, represented,
    by simpa only [wide, X86DataStore.byteCount, if_true] using stored,
    rip, changedFlags, quiet, controls, holds, loaded⟩

namespace FrameReads

open X86Execution

structure Site where
  span : P1Capture.Span
  path : List Nat
  destination : Reg
  slot : Fin 24
  deriving DecidableEq, Repr

def Site.decode? (program : P1Capture.Program) (span : P1Capture.Span) : Option Site := do
  let path ← span.path
  match program.source.body.atPath path with
  | some (.instruction (.loadFrame .u64 destination slot)) => some ⟨span, path, destination, slot⟩
  | _ => none

abbrev Site.code (site : Site) : List Nat :=
  X86FrameLoadCapture.expected (Registers.logicalSlot site.destination) (8 * site.slot.val)

def Site.checkOn (program : P1Capture.Program) (site : Site) (image : NativeImage.View) : Bool :=
  decide (site.span.length = 7 ∧ site.span.offset + 7 ≤ program.size ∧ site.destination ≠ 0 ∧
    program.source.body.atPath site.path = some (.instruction (.loadFrame .u64 site.destination site.slot))) &&
  (List.range 7).all (fun index =>
    image.read (site.span.offset + index) == (site.code[index]?).map (BitVec.ofNat 8))

noncomputable def spans : List P1Capture.Span := sub1.spans.filter (fun span => span.kind == "LOAD-FRAME")

noncomputable def sites : List Site := (spans.mapM (Site.decode? sub1)).getD []

theorem exact_sites : spans.mapM (Site.decode? sub1) = some sites := by kernel_reflexivity

theorem slots : sites.map (fun site => (site.destination, site.slot)) = [(6,22),(8,23)] := by
  kernel_reflexivity

theorem checked_sites : sites.all (fun site => site.checkOn sub1 sub1.view) = true := by kernel_reflexivity

private noncomputable def changeSlot (site : Site) : NativeImage.View :=
  ⟨sub1.size, fun offset =>
    if offset = site.span.offset + 3 then some (0xa0#8) else sub1.view.read offset⟩

theorem changed_slot_rejected : sites.all (fun site => !(site.checkOn sub1 (changeSlot site))) = true := by
  kernel_reflexivity

theorem Site.bytes (site : Site) (member : site ∈ sites) :
    site.span.length = 7 ∧ site.span.offset + 7 ≤ sub1.size ∧ site.destination ≠ 0 ∧
    sub1.source.body.atPath site.path = some (.instruction (.loadFrame .u64 site.destination site.slot)) ∧
    ∀ index < 7, sub1.view.read (site.span.offset + index) = (site.code[index]?).map (BitVec.ofNat 8) := by
  have checked := List.all_eq_true.mp checked_sites site member
  simp only [checkOn, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at checked
  exact ⟨checked.1.1, checked.1.2.1, checked.1.2.2.1, checked.1.2.2.2,
    fun index inside => beq_iff_eq.mp (checked.2 index inside)⟩

def Site.sourceAddress (site : Site) (values : Key → Word) : Nat :=
  (values (.register 0)).toNat + 8 * site.slot.val

def Site.recipe (site : Site) (values : Key → Word) : CellEffects.Recipe Key :=
  P1Memory.loadRecipe .u64 .word64 255 site.destination 0 (8 * site.slot.val) (site.sourceAddress values)

structure Entry (site : Site) (view : View) (values : Key → Word) (native : State) where
  base : Int
  origin : X86LegacyFetch.Basis native
  upper : base + sub1.size + 3 < (2 ^ 47 : Int)
  placed : origin.address.toInt = base + site.span.offset
  loaded : X86P1LoadCapture.Loaded sub1 native base
  known : ∀ cell ∈ view.keys, readback view.modes native cell = some (values cell)
  fits : (values (.register 0)).toNat + 192 < 2 ^ 64
  aligned : (values (.register 0)).toNat % 8 = 0
  profile : X86Readiness.Profile
  holds : profile.Holds native
  flags : BitVec 32
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false

private theorem loaded_bytes (site : Site) (member : site ∈ sites) (view : View) (values : Key → Word)
    (native : State) (entry : Entry site view values native) : codeLoaded native entry.origin.address.toInt site.code := by
  intro index byte present
  have within : index < 7 := by
    simpa [Site.code, X86FrameLoadCapture.expected] using (List.getElem?_eq_some_iff.mp present).1
  have coordinates : address entry.origin.address.toInt index = address entry.base (site.span.offset + index) := by
    unfold address
    rw [entry.placed]
    congr 1
    omega
  have finish := (site.bytes member).2.1
  rw [coordinates, entry.loaded _ (by omega), (site.bytes member).2.2.2.2 index within, present]
  rfl

private theorem frame_displacement : ∀ slot : Fin 24,
    (P1Memory.frameDisplacement slot).signExtend 64 = BitVec.ofNat 64 (8 * slot.val) := by
  decide

/-- Both captured argument loads read the bytes of the source frame slot. -/
theorem executes
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (site : Site) (member : site ∈ sites) (view : View) (values : Key → Word)
    (native : State) (entry : Entry site view values native)
    (included : (site.recipe values).support ⊆ view.keys) :
    letI : OtherOpcodeHandlers := X86BoundedLoad.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ value after,
      (CellEffects.profile [site.recipe values]).theory.rewrites
        (Cells.encode view.keys values)
        (Cells.encode view.keys (Function.update values (.register site.destination) value)) ∧
      (X86FuelPrefix.fetches 1).run native = .ok () after ∧
      RegisterFrame {key (X86MemoryFieldLoad.physical site.destination),.rip} native after ∧
      represents view (Cells.encode view.keys (Function.update values (.register site.destination) value)) after ∧
      after.regs.get? .rip = some ((address entry.base (site.span.offset + 7)).signExtend 64) ∧
      after.regs.get? .rflags = some entry.flags ∧ after.regs.get? .log_register_writes = some false ∧
      entry.profile.Holds after ∧ X86P1LoadCapture.Loaded sub1 after entry.base := by
  let : OtherOpcodeHandlers := X86BoundedLoad.handlers other extra
  let : VectorOpcodeHandlers := vector
  let source := site.sourceAddress values
  let baseWord := values (.register 0)
  have finish := (site.bytes member).2.1
  have unlocked := (site.bytes member).2.2.1
  have frameKnown : lookup native 7 = some baseWord := entry.known _ (view.registers 0)
  have layoutBase : values (.capabilityBase 255) = baseWord := by
    have read := entry.known (.capabilityBase 255) (included (by simp [Site.recipe, P1Memory.loadRecipe,
      CellEffects.Recipe.support, Memory.capabilityKeys]))
    exact Option.some.inj (read.symm.trans frameKnown)
  have layoutLength : values (.capabilityLength 255) = 192 := by
    have read := entry.known (.capabilityLength 255) (included (by simp [Site.recipe, P1Memory.loadRecipe,
      CellEffects.Recipe.support, Memory.capabilityKeys]))
    exact (Option.some.inj read).symm
  have layoutMode : values (.capabilityMode 255) = 1 := by
    have read := entry.known (.capabilityMode 255) (included (by simp [Site.recipe, P1Memory.loadRecipe,
      CellEffects.Recipe.support, Memory.capabilityKeys]))
    exact (Option.some.inj read).symm
  have access : Memory.access? (values (.capabilityBase 255)) (values (.capabilityLength 255))
      baseWord (8 * site.slot.val) 8 = some source := by
    rw [layoutBase, layoutLength]
    exact P1Memory.frame_access baseWord site.slot entry.fits
  have present : ∀ index < 8, Memory.Key.byte (source + index) ∈ view.keys := by
    intro index within
    apply included
    simp [Site.recipe, P1Memory.loadRecipe, CellEffects.Recipe.support, Memory.capabilityKeys,
      CellEffects.Recipe.writes, Memory.byteKeys, Width.bytes]
    exact ⟨index, within, rfl⟩
  obtain ⟨bytes, observed, _, read⟩ := X86MemoryReadback.byte_words_observed
    view values native source entry.known present
  let value := packBytes bytes
  have rewritten : (CellEffects.profile [site.recipe values]).theory.rewrites
      (Cells.encode view.keys values)
      (Cells.encode view.keys (Function.update values (.register site.destination) value)) := by
    apply (P1Memory.load_rewrite_iff .u64 .word64 255 site.destination 0 (8 * site.slot.val) source
      view.keys values _).mpr
    exact ⟨value, included, Or.inl layoutMode, access,
      by rw [show (Memory.byteKeys source Width.word64.bytes).map values = Memory.byteWords bytes from observed,
        P1Memory.load_byteWords]; rfl, rfl⟩
  let pointer := BitVec.ofNat 64 source
  let target := X86CanonicalSpan.narrow pointer
  obtain ⟨representedPointer, dataUpper, dataBytes⟩ :=
    X86MemoryReadback.wordAt?_narrow_bytes native pointer value read
  have effective : baseWord + (P1Memory.frameDisplacement site.slot).signExtend 64 = target.signExtend 64 := by
    rw [frame_displacement, ← representedPointer]
    simp only [pointer, source, Site.sourceAddress, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, baseWord]
  have aligned : source % 8 = 0 := by
    rw [show source = baseWord.toNat + 8 * site.slot.val by rfl, Nat.add_mod, entry.aligned]
    simp
  have safe := aligned_readback view values native source entry.known
    (by simpa only [Nat.add_zero] using present 0 (by decide)) aligned
  have upper : entry.origin.address.toInt + 7 < (2 ^ 47 : Int) := by
    rw [entry.placed]
    have := entry.upper
    omega
  let position := address entry.origin.address.toInt
  have positionExact (index : Nat) (within : index ≤ 7) :
      (position index).toInt = entry.origin.address.toInt + index :=
    address_toInt _ (by simpa using BitVec.le_toInt entry.origin.address) upper index within
  let start := rebase native native entry.origin (RegisterFrame.refl dataRegisters native) upper 0 (by decide)
    (by simpa [address] using entry.origin.rip)
  let destination := X86MemoryFieldLoad.physical site.destination
  let displacement := P1Memory.frameDisplacement site.slot
  have bytesLoaded := loaded_bytes site member view values native entry
  have dispBytes : ∀ index < 4,
      native.mem.get? ((address start.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8) := by
    intro index within
    change native.mem.get? ((address (position 3).toInt index).signExtend 52).toNat = _
    rw [positionExact 3 (by decide), show address (entry.origin.address.toInt + (3 : Nat)) index =
        address entry.origin.address.toInt (3 + index) by simp only [address, Int.natCast_add, Int.add_assoc]]
    have readByte := bytesLoaded (3 + index) (displacement.extractLsb' (8 * index) 8).toNat
      (by interval_cases index <;> rfl)
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using readByte
  have run := X86FrameLoad.fetched_frame (X86BoundedLoad.handlers other extra) vector native destination
    start (position 7) target entry.profile.visible entry.profile.controls baseWord value entry.flags
    displacement
    (by change (position 3).toInt + 4 = (position 7).toInt; rw [positionExact 3 (by decide), positionExact 7 (by decide)]; omega)
    dataUpper frameKnown entry.holds.1 entry.flagsKnown entry.holds.2.1 entry.quiet effective safe
    (by
      change native.mem.get? ((position 0).signExtend 52).toNat = _
      simpa only [position, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        bytesLoaded 0 (X86FrameLoad.frameRex destination).toNat rfl)
    (bytesLoaded 1 139 rfl)
    (by
      change native.mem.get? ((position 2).signExtend 52).toNat = _
      simpa only [position, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        bytesLoaded 2 (X86FrameLoad.frameModRM destination).toNat rfl)
    dispBytes dataBytes
  let after := X86Move.putPointer (put native destination value) (position 7)
  have step : Step native after := run
  have frame : RegisterFrame {key destination,.rip} native after :=
    (put_frame native destination value).trans (pointer_frame _ _)
  have result : lookup after destination = some value := by
    rw [X86Move.lookup_putPointer, lookup_put_same]
  have inBounds : {key destination,.rip} ⊆ insert (key destination) X86Bounds.writes := by
    intro register present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl <;> simp [X86Bounds.writes]
  have flags : after.regs.get? .rflags = some entry.flags := by
    apply Eq.trans (frame.registers _ _) entry.flagsKnown
    dsimp only [destination]
    generalize site.destination = destination
    fin_cases destination <;> decide
  have finalPosition : position 7 = address entry.base (site.span.offset + 7) := by
    unfold position address
    rw [entry.placed]
    congr 1
    omega
  refine ⟨value, after, rewritten, X86FuelPrefix.fetches_one _ _ step, frame,
    X86MemoryFieldLoad.load_represents view values native after site.destination unlocked value
      entry.known (frame.mono inBounds) result, ?_, flags, ?_, ?_, ?_⟩
  · change (X86Move.putPointer (put native destination value) (position 7)).regs.get? .rip = _
    rw [X86FuelPrefix.pointer_rip, finalPosition]
  · apply Eq.trans (frame.registers _ _) entry.quiet
    dsimp only [destination]
    generalize site.destination = destination
    fin_cases destination <;> decide
  · apply entry.profile.after_frame native after _ _ (X86StateFrame.registerOnly frame) _ entry.flags
      entry.flags entry.flagsKnown flags rfl entry.holds
    intro register present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl
    · exact data_key destination
    · simp [dataRegisters]
  · intro offset within
    rw [frame.memory]
    exact entry.loaded offset within

end FrameReads

end Mettapedia.Machines.TIsa.X86P1Sub1Memory
