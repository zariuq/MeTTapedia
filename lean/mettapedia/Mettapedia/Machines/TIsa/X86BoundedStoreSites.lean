import Mettapedia.Machines.TIsa.X86BoundedStoreCapture

/-!
# Source store contracts at actual native consumer sites

Checked source paths and emitted bytes instantiate the complete native store.
Source firing determines every written byte. Descriptor and code exclusions
are explicit, while all other observations follow from the native frame and
the canonical byte representation. This is not a whole-consumer theorem.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86BoundedStoreSites
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView X86BoundedStore
open X86BoundedStoreCapture
local instance : MemoryPrimitives := X86Memory.ordinary

structure Entry (program : P1Capture.Program) (span : P1Capture.Span) (instruction : Instruction)
    (view : View) (values : Key → Word) (native : State) where
  base : Int
  origin : X86LegacyFetch.Basis native
  profile : X86Readiness.Profile
  flags : BitVec 32
  known : ∀ location ∈ view.keys, readback view.modes native location = some (values location)
  frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size
  frameAligned : (values (.register 0)).toNat % 8 = 0
  holds : profile.Holds native
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false
  placed : origin.address.toInt = base + span.offset
  upper : base + program.size + 3 < (2 ^ 47 : Int)
  loaded : X86P1LoadCapture.Loaded program native base
  rangeFits : (values (.capabilityBase instruction.region.val)).toNat +
    (values (.capabilityLength instruction.region.val)).toNat < 2 ^ 64
  pointerLower : (values (.capabilityBase instruction.region.val)).toNat ≤ (values (.register instruction.base)).toNat
  pointerUpper : (values (.register instruction.base)).toNat ≤ (values (.capabilityBase instruction.region.val)).toNat +
    (values (.capabilityLength instruction.region.val)).toNat

theorem source_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (program : P1Capture.Program) (span : P1Capture.Span) (instruction : Instruction)
    (member : (program,span) ∈ sites) (decoded : decode? program span = some instruction)
    (view : View) (values : Key → Word) (native : State) (entry : Entry program span instruction view values native)
    (address : Nat) (following : World)
    (safe : entry.profile.enabled = false ∨ X86MemoryStore.target address &&&
      BitVec.ofNat 48 (X86DataStore.byteCount instruction.wide - 1) = (0#48))
    (source : (CellEffects.profile [X86BoundedStoreSource.recipe instruction address]).theory.rewrites
      (Cells.encode view.keys values) following)
    (descriptors : X86MemoryStore.DescriptorsApart view native (X86DataStore.writes instruction.wide (X86MemoryStore.target address)))
    (codeApart : ∀ offset < program.size, ((X86Execution.address entry.base offset).signExtend 52).toNat ∉
      X86DataStore.writes instruction.wide (X86MemoryStore.target address)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    (∃ path, span.path = some path ∧ program.source.body.atPath path =
      some (.instruction (X86BoundedStoreSource.p1 instruction))) ∧
    ∃ after nextFlags, (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide (X86MemoryStore.target address)) native after ∧
      represents view following after ∧
      (∀ index < X86DataStore.byteCount instruction.wide,
        after.mem.get? (X86WriteWords.physicalAddress (X86MemoryStore.target address) index) =
          some ((values (.register instruction.source)).extractLsb' (8 * index) 8)) ∧
      after.regs.get? .rip = some ((X86Execution.address entry.base (span.offset + span.length)).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧ entry.profile.Holds after ∧
      X86P1LoadCapture.Loaded program after entry.base ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
          X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide (X86MemoryStore.target address)) native observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have checked := List.all_eq_true.mp all_checked (program,span) member
  obtain ⟨valid,_bytes⟩ := matched_info program span instruction decoded checked
  let scope := geometry program span instruction valid entry.origin.address entry.base entry.placed entry.upper
  have scopeTail := geometry_tail program span instruction valid entry.origin.address entry.base entry.placed entry.upper
  have loaded := loaded_template program span instruction decoded checked native entry.base entry.origin entry.placed entry.loaded
  obtain ⟨after,nextFlags,run,frame,represented,stored,rip,flagsRead,quiet,control,holds,prefixes⟩ :=
    X86BoundedStoreSource.from_source other extra vector instruction view values native entry.origin entry.profile entry.flags
      entry.known entry.frameArea entry.frameAligned entry.holds entry.flagsKnown entry.quiet scope scopeTail loaded
      entry.rangeFits entry.pointerLower entry.pointerUpper address following safe source descriptors
  refine ⟨decoded_source program span instruction decoded,after,nextFlags,run,frame,represented,stored,?_,
    flagsRead,quiet,control,holds,?_,prefixes⟩
  · have endAt : X86Execution.address entry.origin.address.toInt (bytes instruction).length =
        X86Execution.address entry.base (span.offset + span.length) := by
      rw [entry.placed,valid.2.1]
      simp only [X86Execution.address,Int.natCast_add,Int.add_assoc]
    simpa only [endAt] using rip
  · intro offset within
    rw [frame.memory _ (codeApart offset within)]
    exact entry.loaded offset within

#print axioms source_executes
end Mettapedia.Machines.TIsa.X86BoundedStoreSites
