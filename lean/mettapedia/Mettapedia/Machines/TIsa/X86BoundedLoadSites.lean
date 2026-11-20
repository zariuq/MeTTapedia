import Mettapedia.Machines.TIsa.X86BoundedLoadCapture

/-!
# Source-to-native load contracts at actual consumer sites

An entry contains memory/register observations and placement facts. The checked
source path, emitted bytes and branch geometry are obtained from the captured
site. A real source load firing supplies the value and byte allocation. The
result includes the whole-image preservation and every fetched prefix frame.
This is a contract for consumer load sites, not a whole-consumer theorem.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86BoundedLoadSites
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView X86BoundedLoad
open X86BoundedLoadCapture
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
    (safe : entry.profile.enabled = false ∨ X86CanonicalSpan.narrow (BitVec.ofNat 64 address) &&&
      BitVec.ofNat 48 (X86DataLoad.byteCount instruction.wide - 1) = (0#48))
    (source : (CellEffects.profile [X86BoundedLoadSource.recipe instruction address]).theory.rewrites
      (Cells.encode view.keys values) following) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    (∃ path, span.path = some path ∧ program.source.body.atPath path =
      some (.instruction (X86BoundedLoadSource.p1 instruction))) ∧
    ∃ after nextFlags, (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧ represents view following after ∧
      after.regs.get? .rip = some ((X86Execution.address entry.base (span.offset + span.length)).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧ entry.profile.Holds after ∧
      X86P1LoadCapture.Loaded program after entry.base ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed → RegisterFrame (writes instruction) native observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have checked := List.all_eq_true.mp all_checked (program,span) member
  obtain ⟨valid,_bytes⟩ := matched_info program span instruction decoded checked
  let scope := geometry program span instruction valid entry.origin.address entry.base entry.placed entry.upper
  have scopeTail := geometry_tail program span instruction valid entry.origin.address entry.base entry.placed entry.upper
  have loaded := loaded_template program span instruction decoded checked native entry.base entry.origin entry.placed entry.loaded
  obtain ⟨after,nextFlags,run,frame,represented,rip,flagsRead,quiet,control,holds,prefixes⟩ :=
    X86BoundedLoadSource.from_source other extra vector instruction view values native entry.origin entry.profile entry.flags
      entry.known entry.frameArea entry.frameAligned entry.holds entry.flagsKnown entry.quiet scope scopeTail loaded
      entry.rangeFits entry.pointerLower entry.pointerUpper address following safe source
  refine ⟨decoded_source program span instruction decoded,after,nextFlags,run,frame,represented,?_,
    flagsRead,quiet,control,holds,?_,prefixes⟩
  · have endAt : X86Execution.address entry.origin.address.toInt (bytes instruction).length =
        X86Execution.address entry.base (span.offset + span.length) := by
      rw [entry.placed,valid.2.1]
      simp only [X86Execution.address,Int.natCast_add,Int.add_assoc]
    simpa only [endAt] using rip
  · intro offset within
    rw [frame.memory]
    exact entry.loaded offset within

namespace Controls

private noncomputable abbrev fixture := X86MemoryFieldLoad.entryFixture
private noncomputable def fieldSite : P1Capture.Program × P1Capture.Span := sites[8]'(by rw [site_count];decide)
private def fieldInstruction : Instruction := ⟨true,6,1,0,⟨8,by decide⟩,330,by decide,by decide,by decide⟩
private def fieldValue : Word := 0x80000001000000ff

theorem field_is_captured : fieldSite ∈ sites := List.getElem_mem (by rw [site_count];decide)
theorem field_decoded : decode? fieldSite.1 fieldSite.2 = some fieldInstruction := by kernel_reflexivity
theorem field_counts : count fieldInstruction = 10 ∧ (bytes fieldInstruction).length = 56 := by decide

private noncomputable def fieldEntry : Entry fieldSite.1 fieldSite.2 fieldInstruction fixture.view fixture.values fixture.native where
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

private theorem field_source :
    (CellEffects.profile [X86BoundedLoadSource.recipe fieldInstruction fixture.address]).theory.rewrites
      (Cells.encode fixture.view.keys fixture.values)
      (Cells.encode fixture.view.keys (Function.update fixture.values (.register 6) fieldValue)) :=
  X86MemoryFieldLoad.Controls.source_firing

theorem actual_field_site (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 10).run fixture.native = .ok () after ∧
      lookup after 10 = some fieldValue ∧ after.regs.get? .rip = some (4412#64) ∧
      lookup after 4 = lookup fixture.native 4 ∧ lookup after 7 = lookup fixture.native 7 ∧
      X86P1LoadCapture.Loaded fieldSite.1 after fixture.base ∧ fixture.profile.Holds after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨_source,after,_flags,run,frame,⟨assigned,encoded,observed⟩,rip,_flagsRead,_quiet,_control,holds,image,_prefixes⟩ :=
    source_executes other extra vector fieldSite.1 fieldSite.2 fieldInstruction field_is_captured field_decoded
      fixture.view fixture.values fixture.native fieldEntry fixture.address _ (Or.inr (by decide)) field_source
  have same := ((Cells.encode_le_iff fixture.view.keys fixture.view.keys assigned
      (Function.update fixture.values (.register 6) fieldValue)).mp (le_of_eq encoded.symm)).2
  have result := (observed (.register 6) (fixture.view.registers 6)).trans
    (congrArg some (same (.register 6) (fixture.view.registers 6)))
  refine ⟨after,run,?_,?_,frame.lookup 4 (by decide),frame.lookup 7 (by decide),image,holds⟩
  · change lookup after 10 = some ((Function.update fixture.values (.register 6) fieldValue) (.register 6)) at result
    simpa only [Function.update_self] using result
  · have endpoint : X86Execution.address fieldEntry.base (fieldSite.2.offset + fieldSite.2.length) = (4412#48) := by
      kernel_reflexivity
    have wide : (4412#48).signExtend 64 = (4412#64) := by decide
    simpa only [endpoint,wide] using rip

theorem truncated_field_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (candidate : State)
    (run : letI : OtherOpcodeHandlers := handlers other extra
           letI : VectorOpcodeHandlers := vector
           (X86FuelPrefix.fetches 10).run fixture.native = .ok () candidate) : lookup candidate 10 ≠ some (0xff#64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,executed,result,_rest⟩ := actual_field_site other extra vector
  have same := X86FuelPrefix.fetches_deterministic 10 fixture.native after candidate executed run
  subst candidate
  rw [result]
  decide

end Controls

#print axioms source_executes
#print axioms Controls.actual_field_site
#print axioms Controls.truncated_field_refused
end Mettapedia.Machines.TIsa.X86BoundedLoadSites
