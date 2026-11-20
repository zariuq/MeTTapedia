import Mettapedia.Machines.TIsa.ContinuationProjection
import Mettapedia.Machines.TIsa.X86BoundedLoadSites
import Mettapedia.Machines.TIsa.X86BoundedStoreSites

/-!
# Controlled load and store firings at actual native sites

Existing continuation edges supply the source control token and data effect.
Their genuine source firing projects to the established memory recipe, whose
native certificate supplies the execution. The source successor and actual
native endpoint are both retained, together with byte and prefix frames.
No new instruction interpreter or assumed native execution is introduced.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86MemoryContinuation
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView
open Cells CellEffects Control
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev Location := Control.Location Key
abbrev ControlledWorld := Multiset (Cell Location)

def loadEdge (activation : Nat) (span : P1Capture.Span) (instruction : X86BoundedLoad.Instruction) (address : Nat) : Edge Key :=
  ⟨activation,BitVec.ofNat 64 span.offset,BitVec.ofNat 64 (span.offset + span.length),X86BoundedLoadSource.recipe instruction address⟩
def storeEdge (activation : Nat) (span : P1Capture.Span) (instruction : X86BoundedStore.Instruction) (address : Nat) : Edge Key :=
  ⟨activation,BitVec.ofNat 64 span.offset,BitVec.ofNat 64 (span.offset + span.length),X86BoundedStoreSource.recipe instruction address⟩

theorem load_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (activation : Nat) (program : P1Capture.Program) (span : P1Capture.Span) (instruction : X86BoundedLoad.Instruction)
    (member : (program,span) ∈ X86BoundedLoadCapture.sites)
    (decoded : X86BoundedLoadCapture.decode? program span = some instruction)
    (view : View) (before : Location → Word) (native : State)
    (entry : X86BoundedLoadSites.Entry program span instruction view (dataValues before) native)
    (address : Nat) (following : ControlledWorld)
    (safe : entry.profile.enabled = false ∨ X86CanonicalSpan.narrow (BitVec.ofNat 64 address) &&&
      BitVec.ofNat 48 (X86DataLoad.byteCount instruction.wide - 1) = (0#48))
    (source : (profile [(loadEdge activation span instruction address).recipe]).theory.rewrites
      (encode (scopedKeys activation view.keys) before) following) :
    letI : OtherOpcodeHandlers := X86BoundedLoad.handlers other extra
    letI : VectorOpcodeHandlers := vector
    before (.inl activation) = BitVec.ofNat 64 span.offset ∧
    ∃ afterValues : Location → Word,
      following = encode (scopedKeys activation view.keys) afterValues ∧
      afterValues (.inl activation) = BitVec.ofNat 64 (span.offset + span.length) ∧
      ∃ after nextFlags, (X86FuelPrefix.fetches (X86BoundedLoad.count instruction)).run native = .ok () after ∧
        RegisterFrame (X86BoundedLoad.writes instruction) native after ∧
        represents view (encode view.keys (dataValues afterValues)) after ∧
        after.regs.get? .rip = some ((X86Execution.address entry.base (span.offset + span.length)).signExtend 64) ∧
        after.regs.get? .rflags = some nextFlags ∧ entry.profile.Holds after ∧
        X86P1LoadCapture.Loaded program after entry.base ∧
        ∀ prefixCount ≤ X86BoundedLoad.count instruction, ∀ observed,
          (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
            RegisterFrame (X86BoundedLoad.writes instruction) native observed := by
  let : OtherOpcodeHandlers := X86BoundedLoad.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨afterValues,point,next,endpoint,dataStep⟩ :=
    (loadEdge activation span instruction address).project_firing view.keys before following source
  obtain ⟨_sourcePath,after,nextFlags,run,frame,represented,rip,flagsRead,_quiet,_control,holds,image,prefixes⟩ :=
    X86BoundedLoadSites.source_executes other extra vector program span instruction member decoded view
      (dataValues before) native entry address (encode view.keys (dataValues afterValues)) safe dataStep
  exact ⟨point,afterValues,endpoint,next,after,nextFlags,run,frame,represented,rip,flagsRead,holds,image,prefixes⟩

theorem store_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (activation : Nat) (program : P1Capture.Program) (span : P1Capture.Span) (instruction : X86BoundedStore.Instruction)
    (member : (program,span) ∈ X86BoundedStoreCapture.sites)
    (decoded : X86BoundedStoreCapture.decode? program span = some instruction)
    (view : View) (before : Location → Word) (native : State)
    (entry : X86BoundedStoreSites.Entry program span instruction view (dataValues before) native)
    (address : Nat) (following : ControlledWorld)
    (safe : entry.profile.enabled = false ∨ X86MemoryStore.target address &&&
      BitVec.ofNat 48 (X86DataStore.byteCount instruction.wide - 1) = (0#48))
    (source : (profile [(storeEdge activation span instruction address).recipe]).theory.rewrites
      (encode (scopedKeys activation view.keys) before) following)
    (descriptors : X86MemoryStore.DescriptorsApart view native (X86DataStore.writes instruction.wide (X86MemoryStore.target address)))
    (codeApart : ∀ offset < program.size, ((X86Execution.address entry.base offset).signExtend 52).toNat ∉
      X86DataStore.writes instruction.wide (X86MemoryStore.target address)) :
    letI : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
    letI : VectorOpcodeHandlers := vector
    before (.inl activation) = BitVec.ofNat 64 span.offset ∧
    ∃ afterValues : Location → Word,
      following = encode (scopedKeys activation view.keys) afterValues ∧
      afterValues (.inl activation) = BitVec.ofNat 64 (span.offset + span.length) ∧
      ∃ after nextFlags, (X86FuelPrefix.fetches (X86BoundedStore.count instruction)).run native = .ok () after ∧
        X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide (X86MemoryStore.target address)) native after ∧
        represents view (encode view.keys (dataValues afterValues)) after ∧
        (∀ index < X86DataStore.byteCount instruction.wide,
          after.mem.get? (X86WriteWords.physicalAddress (X86MemoryStore.target address) index) =
            some ((dataValues before (.register instruction.source)).extractLsb' (8 * index) 8)) ∧
        after.regs.get? .rip = some ((X86Execution.address entry.base (span.offset + span.length)).signExtend 64) ∧
        after.regs.get? .rflags = some nextFlags ∧ entry.profile.Holds after ∧
        X86P1LoadCapture.Loaded program after entry.base ∧
        ∀ prefixCount ≤ X86BoundedStore.count instruction, ∀ observed,
          (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
            X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide (X86MemoryStore.target address)) native observed := by
  let : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨afterValues,point,next,endpoint,dataStep⟩ :=
    (storeEdge activation span instruction address).project_firing view.keys before following source
  obtain ⟨_sourcePath,after,nextFlags,run,frame,represented,stored,rip,flagsRead,_quiet,_control,holds,image,prefixes⟩ :=
    X86BoundedStoreSites.source_executes other extra vector program span instruction member decoded view
      (dataValues before) native entry address (encode view.keys (dataValues afterValues)) safe dataStep descriptors codeApart
  exact ⟨point,afterValues,endpoint,next,after,nextFlags,run,frame,represented,stored,rip,flagsRead,holds,image,prefixes⟩

theorem wrong_control_refused (edge : Edge Key) (keys : Finset Key) (before : Location → Word)
    (following : ControlledWorld) (different : before (.inl edge.activation) ≠ edge.point) :
    ¬ (profile [edge.recipe]).theory.rewrites (encode (scopedKeys edge.activation keys) before) following := by
  intro step
  obtain ⟨_after,point,_next,_endpoint,_data⟩ := edge.project_firing keys before following step
  exact different point

namespace Controls
private noncomputable abbrev fixture := X86MemoryFieldLoad.entryFixture
private noncomputable def fieldSite : P1Capture.Program × P1Capture.Span :=
  X86BoundedLoadCapture.sites[8]'(by rw [X86BoundedLoadCapture.site_count];decide)
private def instruction : X86BoundedLoad.Instruction := ⟨true,6,1,0,⟨8,by decide⟩,330,by decide,by decide,by decide⟩
private noncomputable def beforeValues : Location → Word
  | .inl _ => 260
  | .inr key => fixture.values key
private noncomputable def fieldEntry : X86BoundedLoadSites.Entry fieldSite.1 fieldSite.2 instruction
    fixture.view (dataValues beforeValues) fixture.native where
  base := fixture.base
  origin := fixture.origin
  profile := fixture.profile
  flags := fixture.flags
  known := fixture.known
  frameArea := fixture.frameArea
  frameAligned := fixture.frameAligned
  holds := fixture.holds
  flagsKnown := fixture.flagsKnown
  quiet := fixture.quiet
  placed := fixture.placed
  upper := by change (4096 : Int) + 647 + 3 < 2 ^ 47;decide
  loaded := fixture.loaded
  rangeFits := fixture.rangeFits
  pointerLower := fixture.pointerLower
  pointerUpper := fixture.pointerUpper

theorem controlled_field_load (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86BoundedLoad.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ afterValues : Location → Word, ∃ after,
      (profile [(loadEdge 0 fieldSite.2 instruction fixture.address).recipe]).theory.rewrites
        (encode (scopedKeys 0 fixture.view.keys) beforeValues) (encode (scopedKeys 0 fixture.view.keys) afterValues) ∧
      afterValues (.inl 0) = (316#64) ∧
      (X86FuelPrefix.fetches 10).run fixture.native = .ok () after ∧
      after.regs.get? .rip = some (4412#64) := by
  let : OtherOpcodeHandlers := X86BoundedLoad.handlers other extra
  let : VectorOpcodeHandlers := vector
  let edge := loadEdge 0 fieldSite.2 instruction fixture.address
  have point : beforeValues (.inl 0) = edge.point := by dsimp only [edge];kernel_reflexivity
  have dataStep : (profile [edge.effect]).theory.rewrites (encode fixture.view.keys (dataValues beforeValues))
      (encode fixture.view.keys (Function.update fixture.values (.register 6) (0x80000001000000ff#64))) :=
    X86MemoryFieldLoad.Controls.source_firing
  obtain ⟨chosen,_next,_data,step⟩ := edge.lift_firing fixture.view.keys beforeValues _ point dataStep
  have member : fieldSite ∈ X86BoundedLoadCapture.sites := List.getElem_mem (by rw [X86BoundedLoadCapture.site_count];decide)
  have decoded : X86BoundedLoadCapture.decode? fieldSite.1 fieldSite.2 = some instruction := by kernel_reflexivity
  obtain ⟨_point,afterValues,endpoint,next,after,_flags,run,_frame,_represented,rip,_flagsRead,_holds,_image,_prefixes⟩ :=
    load_executes other extra vector 0 fieldSite.1 fieldSite.2 instruction member decoded fixture.view beforeValues
      fixture.native fieldEntry fixture.address (encode (scopedKeys 0 fixture.view.keys) chosen) (Or.inr (by decide)) step
  have transported : (profile [edge.recipe]).theory.rewrites
      (encode (scopedKeys 0 fixture.view.keys) beforeValues) (encode (scopedKeys 0 fixture.view.keys) afterValues) :=
    Eq.mp (congrArg (fun world : ControlledWorld => (profile [edge.recipe]).theory.rewrites
      (encode (scopedKeys 0 fixture.view.keys) beforeValues) world) endpoint) step
  refine ⟨afterValues,after,transported,?_,run,?_⟩
  · have successor : BitVec.ofNat 64 (fieldSite.2.offset + fieldSite.2.length) = (316#64) := by kernel_reflexivity
    simpa only [successor] using next
  · have target : X86Execution.address fieldEntry.base (fieldSite.2.offset + fieldSite.2.length) = (4412#48) := by kernel_reflexivity
    have wide : (4412#48).signExtend 64 = (4412#64) := by decide
    simpa only [target,wide] using rip

theorem wrong_field_token_refused (following : ControlledWorld) :
    ¬ (profile [(loadEdge 0 fieldSite.2 instruction fixture.address).recipe]).theory.rewrites
      (encode (scopedKeys 0 fixture.view.keys) (Function.update beforeValues (.inl 0) 0)) following := by
  apply wrong_control_refused
  have point : (loadEdge 0 fieldSite.2 instruction fixture.address).point = (260#64) := by kernel_reflexivity
  change (Function.update beforeValues (.inl 0) 0 (.inl 0)) ≠ (loadEdge 0 fieldSite.2 instruction fixture.address).point
  rw [Function.update_self,point]
  decide
end Controls

#print axioms load_executes
#print axioms store_executes
#print axioms wrong_control_refused
#print axioms Controls.controlled_field_load
#print axioms Controls.wrong_field_token_refused
end Mettapedia.Machines.TIsa.X86MemoryContinuation
