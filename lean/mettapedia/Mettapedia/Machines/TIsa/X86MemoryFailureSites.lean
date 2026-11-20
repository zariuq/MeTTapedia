import Mettapedia.Machines.TIsa.X86MemoryFailure
import Mettapedia.Machines.TIsa.X86MemoryContinuation

/-!
# Error-control edges at actual emitted load and store sites

Captured source paths, complete block bytes and checked branch destinations
construct the native rejection entry. A genuine controlled failure firing
then reaches that same invalid-input successor in the original x86 model.
The source data, all native bytes and every represented observation survive;
no target-memory, payload, alignment or store-separation premises are added.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86MemoryFailureSites
open _root_.X86Registers X86RegisterRefinement X86Execution X86FetchEntry X86MemoryView Cells CellEffects Control
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev Location := Control.Location Key
abbrev ControlledWorld := Multiset (Cell Location)

def edge (activation : Nat) (program : P1Capture.Program) (span : P1Capture.Span)
    (write : Bool) (width : P1Source.Width) (layout : X86Bounds.Layout) (pointer : Fin 12) : Edge Key :=
  ⟨activation,BitVec.ofNat 64 span.offset,BitVec.ofNat 64 (X86AssemblerCapture.invalidAt program),
    X86MemoryFailure.recipe write width layout pointer⟩

theorem load_edge_in_source (activation address : Nat) (program : P1Capture.Program) (span : P1Capture.Span)
    (instruction : X86BoundedLoad.Instruction) :
    ∃ edges, P1Memory.memoryEdges? (X86BoundedLoadSource.p1 instruction) address activation
      (BitVec.ofNat 64 span.offset) (BitVec.ofNat 64 (span.offset + span.length))
      (BitVec.ofNat 64 (X86AssemblerCapture.invalidAt program)) = some edges ∧
      edge activation program span false (X86BoundedLoadSource.width instruction.wide)
        (X86BoundedLoad.layout instruction) instruction.base ∈ edges := by
  refine ⟨_,rfl,?_⟩
  simp [edge,X86MemoryFailure.recipe,X86BoundedLoad.layout,X86BoundedLoad.displacement]

theorem store_edge_in_source (activation address : Nat) (program : P1Capture.Program) (span : P1Capture.Span)
    (instruction : X86BoundedStore.Instruction) :
    ∃ edges, P1Memory.memoryEdges? (X86BoundedStoreSource.p1 instruction) address activation
      (BitVec.ofNat 64 span.offset) (BitVec.ofNat 64 (span.offset + span.length))
      (BitVec.ofNat 64 (X86AssemblerCapture.invalidAt program)) = some edges ∧
      edge activation program span true (X86StoreRepresentation.width instruction.wide)
        (X86BoundedStore.layout instruction) instruction.base ∈ edges := by
  refine ⟨_,rfl,?_⟩
  simp [edge,X86MemoryFailure.recipe,X86BoundedStore.layout,X86BoundedStore.displacement]

structure Site (program : P1Capture.Program) (span : P1Capture.Span) (layout : X86Bounds.Layout)
    (pointer : Fin 12) (keys : Finset Key) (modes : Fin 9 → Word) (values : Key → Word) (native : State) where
  base : Int
  entry : X86MemoryFailure.Entry layout pointer keys modes values native
  placed : entry.origin.address.toInt = base + span.offset
  target : span.offset + layout.reject = X86AssemblerCapture.invalidAt program
  image : X86P1LoadCapture.Loaded program native base

def Rejected (activation : Nat) (program : P1Capture.Program) (span : P1Capture.Span) (layout : X86Bounds.Layout)
    (pointer : Fin 12) (keys : Finset Key) (modes : Fin 9 → Word) (before : Location → Word)
    (native : State) (base : Int) (profile : X86Readiness.Profile) (following : ControlledWorld)
    [OtherOpcodeHandlers] [VectorOpcodeHandlers] : Prop :=
  before (.inl activation) = BitVec.ofNat 64 span.offset ∧
  ∃ afterValues : Location → Word,
    following = encode (scopedKeys activation keys) afterValues ∧
    afterValues (.inl activation) = BitVec.ofNat 64 (X86AssemblerCapture.invalidAt program) ∧
    encode keys (dataValues afterValues) = encode keys (dataValues before) ∧
    ∃ after nextFlags, (X86FuelPrefix.fetches (X86MemoryFailure.count layout pointer (dataValues before))).run native = .ok () after ∧
      RegisterFrame X86Bounds.writes native after ∧
      (∀ key, readback modes after key = readback modes native key) ∧
      after.regs.get? .rip = some ((address base (X86AssemblerCapture.invalidAt program)).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧ profile.Holds after ∧ X86P1LoadCapture.Loaded program after base ∧
      ∀ prefixCount ≤ X86MemoryFailure.count layout pointer (dataValues before), ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed → RegisterFrame X86Bounds.writes native observed

theorem controlled_at (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (activation : Nat) (program : P1Capture.Program) (span : P1Capture.Span) (write : Bool) (width : P1Source.Width)
    (layout : X86Bounds.Layout) (pointer : Fin 12) (sized : width.bytes = layout.count.val)
    (keys : Finset Key) (modes : Fin 9 → Word) (before : Location → Word) (native : State)
    (site : Site program span layout pointer keys modes (dataValues before) native) (following : ControlledWorld)
    (source : (CellEffects.profile [(edge activation program span write width layout pointer).recipe]).theory.rewrites
      (encode (scopedKeys activation keys) before) following) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    Rejected activation program span layout pointer keys modes before native site.base site.entry.profile following := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨afterValues,point,next,endpoint,dataStep⟩ :=
    (edge activation program span write width layout pointer).project_firing keys before following source
  obtain ⟨unchanged,after,nextFlags,run,frame,readbacks,rip,flagsRead,quiet,control,holds,prefixes⟩ :=
    X86MemoryFailure.source_executes other extra vector write width layout pointer sized keys modes (dataValues before)
      native site.entry (encode keys (dataValues afterValues)) dataStep
  have destination : X86Bounds.position site.entry.origin.address layout.reject = address site.base (X86AssemblerCapture.invalidAt program) := by
    unfold X86Bounds.position address
    rw [site.placed]
    congr 1
    have target : (span.offset : Int) + layout.reject = ((X86AssemblerCapture.invalidAt program : Nat) : Int) := by exact_mod_cast site.target
    omega
  refine ⟨point,afterValues,endpoint,next,unchanged,after,nextFlags,run,frame,readbacks,?_,flagsRead,quiet,control,holds,?_,prefixes⟩
  · simpa only [destination] using rip
  · intro offset within
    rw [frame.memory]
    exact site.image offset within

def load_site (program : P1Capture.Program) (span : P1Capture.Span) (instruction : X86BoundedLoad.Instruction)
    (member : (program,span) ∈ X86BoundedLoadCapture.sites)
    (decoded : X86BoundedLoadCapture.decode? program span = some instruction)
    (view : View) (values : Key → Word) (native : State)
    (input : X86BoundedLoadSites.Entry program span instruction view values native) :
    Site program span (X86BoundedLoad.layout instruction) instruction.base view.keys view.modes values native := by
  have checked := List.all_eq_true.mp X86BoundedLoadCapture.all_checked (program,span) member
  have valid := (X86BoundedLoadCapture.matched_info program span instruction decoded checked).1
  have loaded := X86BoundedLoadCapture.loaded_template program span instruction decoded checked native input.base input.origin input.placed input.loaded
  exact {
    base := input.base
    entry := {
      origin := input.origin
      profile := input.profile
      flags := input.flags
      mapped := rfl
      known := input.known
      frameKnown := input.known (.register 0) (view.registers 0)
      frameArea := input.frameArea
      frameAligned := input.frameAligned
      holds := input.holds
      flagsKnown := input.flagsKnown
      quiet := input.quiet
      geometry := X86BoundedLoadCapture.geometry program span instruction valid input.origin.address input.base input.placed input.upper
      loaded := codeLoaded_left native input.origin.address.toInt _ _ loaded
      rangeFits := input.rangeFits }
    placed := input.placed
    target := valid.2.2.1
    image := input.loaded }

theorem load_refuses (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (activation : Nat) (program : P1Capture.Program) (span : P1Capture.Span) (instruction : X86BoundedLoad.Instruction)
    (member : (program,span) ∈ X86BoundedLoadCapture.sites)
    (decoded : X86BoundedLoadCapture.decode? program span = some instruction)
    (view : View) (before : Location → Word) (native : State)
    (input : X86BoundedLoadSites.Entry program span instruction view (dataValues before) native)
    (following : ControlledWorld)
    (source : (CellEffects.profile [(edge activation program span false (X86BoundedLoadSource.width instruction.wide)
      (X86BoundedLoad.layout instruction) instruction.base).recipe]).theory.rewrites
        (encode (scopedKeys activation view.keys) before) following) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    (∃ path, span.path = some path ∧ program.source.body.atPath path = some (.instruction (X86BoundedLoadSource.p1 instruction))) ∧
    Rejected activation program span (X86BoundedLoad.layout instruction) instruction.base view.keys view.modes
      before native input.base input.profile following := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  refine ⟨X86BoundedLoadCapture.decoded_source program span instruction decoded,?_⟩
  have sized : (X86BoundedLoadSource.width instruction.wide).bytes = (X86BoundedLoad.layout instruction).count.val := by
    cases selected : instruction.wide <;> simp [X86BoundedLoadSource.width,X86BoundedLoad.layout,selected,P1Source.Width.bytes]
  exact controlled_at other extra vector activation program span false (X86BoundedLoadSource.width instruction.wide)
    (X86BoundedLoad.layout instruction) instruction.base sized view.keys view.modes before native
    (load_site program span instruction member decoded view (dataValues before) native input) following source

def store_site (program : P1Capture.Program) (span : P1Capture.Span) (instruction : X86BoundedStore.Instruction)
    (member : (program,span) ∈ X86BoundedStoreCapture.sites)
    (decoded : X86BoundedStoreCapture.decode? program span = some instruction)
    (view : View) (values : Key → Word) (native : State)
    (input : X86BoundedStoreSites.Entry program span instruction view values native) :
    Site program span (X86BoundedStore.layout instruction) instruction.base view.keys view.modes values native := by
  have checked := List.all_eq_true.mp X86BoundedStoreCapture.all_checked (program,span) member
  have valid := (X86BoundedStoreCapture.matched_info program span instruction decoded checked).1
  have loaded := X86BoundedStoreCapture.loaded_template program span instruction decoded checked native input.base input.origin input.placed input.loaded
  exact {
    base := input.base
    entry := {
      origin := input.origin
      profile := input.profile
      flags := input.flags
      mapped := rfl
      known := input.known
      frameKnown := input.known (.register 0) (view.registers 0)
      frameArea := input.frameArea
      frameAligned := input.frameAligned
      holds := input.holds
      flagsKnown := input.flagsKnown
      quiet := input.quiet
      geometry := X86BoundedStoreCapture.geometry program span instruction valid input.origin.address input.base input.placed input.upper
      loaded := codeLoaded_left native input.origin.address.toInt _ _ loaded
      rangeFits := input.rangeFits }
    placed := input.placed
    target := valid.2.2.1
    image := input.loaded }

theorem store_refuses (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (activation : Nat) (program : P1Capture.Program) (span : P1Capture.Span) (instruction : X86BoundedStore.Instruction)
    (member : (program,span) ∈ X86BoundedStoreCapture.sites)
    (decoded : X86BoundedStoreCapture.decode? program span = some instruction)
    (view : View) (before : Location → Word) (native : State)
    (input : X86BoundedStoreSites.Entry program span instruction view (dataValues before) native)
    (following : ControlledWorld)
    (source : (CellEffects.profile [(edge activation program span true (X86StoreRepresentation.width instruction.wide)
      (X86BoundedStore.layout instruction) instruction.base).recipe]).theory.rewrites
        (encode (scopedKeys activation view.keys) before) following) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    (∃ path, span.path = some path ∧ program.source.body.atPath path = some (.instruction (X86BoundedStoreSource.p1 instruction))) ∧
    Rejected activation program span (X86BoundedStore.layout instruction) instruction.base view.keys view.modes
      before native input.base input.profile following := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  refine ⟨X86BoundedStoreCapture.decoded_source program span instruction decoded,?_⟩
  have sized : (X86StoreRepresentation.width instruction.wide).bytes = (X86BoundedStore.layout instruction).count.val := by
    cases selected : instruction.wide <;> simp [X86StoreRepresentation.width,X86BoundedLoadSource.width,X86BoundedStore.layout,selected,P1Source.Width.bytes]
  exact controlled_at other extra vector activation program span true (X86StoreRepresentation.width instruction.wide)
    (X86BoundedStore.layout instruction) instruction.base sized view.keys view.modes before native
    (store_site program span instruction member decoded view (dataValues before) native input) following source

#print axioms controlled_at
#print axioms load_edge_in_source
#print axioms store_edge_in_source
#print axioms load_refuses
#print axioms store_refuses
end Mettapedia.Machines.TIsa.X86MemoryFailureSites
