import Mettapedia.Machines.TIsa.X86ScalarLibrary
import Mettapedia.Machines.TIsa.X86ExecutionProfile

/-!
# Preserved entry profiles in the existing native block compiler

Readiness strengthening retains source actions, emitted bytes, instruction
counts and footprints. A local stability proof carries the added invariant
through each component, after which the common compiler's WP theorem reuses
its established execution and layout proof.

The concrete profile records actual control registers, segment selectors and
AC, with either AC value permitted. Copy, ADD/SUB and AND/OR/XOR preserve it
through the original fetched instructions. Logical AF choices are quantified
independently. Reading the alignment predicate agrees with this profile.

The inhabited fifteen-byte mixed block takes five fetches, preserves enabled
alignment checking and memory, and computes its high-word result. Conditional
composition retains the profile through both arms and the join jump, using
the gate's protected flag bits. Controls reject clearing AC and a changed
branch opcode. Memory operations, remaining loop families and public ABI
composition retain separate obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86Readiness
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary
universe u v s

variable {Op : Type u} {Source : Type s}

def strengthen (spec : X86BlockCompiler.Spec Op Source) (invariant : State → Prop) :
    X86BlockCompiler.Spec Op Source :=
  { spec with ready := fun native => spec.ready native ∧ invariant native }

theorem code_strengthen (spec : X86BlockCompiler.Spec Op Source) (invariant : State → Prop)
    (program : X86BlockCompiler.Program Op) :
    X86BlockCompiler.code (strengthen spec invariant) program = X86BlockCompiler.code spec program := by
  induction program with
  | ret value => rfl
  | call op next ih =>
    change spec.bytes op ++ X86BlockCompiler.code (strengthen spec invariant) (next ()) =
      spec.bytes op ++ X86BlockCompiler.code spec (next ())
    rw [ih ()]

theorem steps_strengthen (spec : X86BlockCompiler.Spec Op Source) (invariant : State → Prop)
    (program : X86BlockCompiler.Program Op) :
    X86BlockCompiler.steps (strengthen spec invariant) program = X86BlockCompiler.steps spec program := by
  induction program with
  | ret value => rfl
  | call op next ih =>
    change spec.count op + X86BlockCompiler.steps (strengthen spec invariant) (next ()) =
      spec.count op + X86BlockCompiler.steps spec (next ())
    rw [ih ()]

def strengthen_at (spec : X86BlockCompiler.Spec Op Source) (invariant : State → Prop)
    (stop : Int) (program : X86BlockCompiler.Program Op) (source : Source) (native : State)
    (input : X86BlockCompiler.At spec stop program source native) (holds : invariant native) :
    X86BlockCompiler.At (strengthen spec invariant) stop program source native where
  origin := input.origin
  placed := by rw [code_strengthen]; exact input.placed
  upper := input.upper
  represented := input.represented
  ready := ⟨input.ready,holds⟩
  loaded := by rw [code_strengthen]; exact input.loaded
  outside := by rw [code_strengthen]; exact input.outside

section Machine
variable [OtherOpcodeHandlers] [VectorOpcodeHandlers]

def Stable (spec : X86BlockCompiler.Spec Op Source) (invariant : State → Prop) : Prop :=
  ∀ op source following native (origin : X86LegacyFetch.Basis native),
    (spec.action op).Safe source → (spec.action op).Step source () following →
    spec.represents source native → spec.ready native → invariant native →
    origin.address.toInt + (((spec.bytes op).length + 3 : Nat) : Int) < (2 ^ 47 : Int) →
    codeLoaded native origin.address.toInt (spec.bytes op) →
    (∀ index byte, (spec.bytes op)[index]? = some byte →
      ((address origin.address.toInt index).signExtend 52).toNat ∉ spec.byteWrites) →
    ∀ after, (X86FuelPrefix.fetches (spec.count op)).run native = .ok () after → invariant after

theorem correct (spec : X86BlockCompiler.Spec Op Source) (invariant : State → Prop)
    (certified : X86BlockCompiler.Correct spec) (stable : Stable spec invariant) :
    X86BlockCompiler.Correct (strengthen spec invariant) where
  dataOnly := certified.dataOnly
  execute op source following native origin safe step represented prepared upper loaded outside := by
    obtain ⟨after,run,frame,representedAfter,readyAfter,rip,prefixes⟩ :=
      certified.execute op source following native origin safe step represented prepared.1 upper loaded outside
    exact ⟨after,run,frame,representedAfter,
      ⟨readyAfter,stable op source following native origin safe step represented prepared.1 prepared.2
        upper loaded outside after run⟩,rip,prefixes⟩

end Machine

def compatible (profile : Profile) (condition : Fin 12) :
    X86Conditional.Compatible (strengthen X86ScalarLibrary.spec profile.Holds) where
  condition := (X86ScalarLibrary.compatible condition).condition
  value := (X86ScalarLibrary.compatible condition).value
  read := (X86ScalarLibrary.compatible condition).read
  prepared := fun native ready => (X86ScalarLibrary.compatible condition).prepared native ready.1
  stable := by
    intro source before after represented ready framed control flagsPresent
    have retained := (X86ScalarLibrary.compatible condition).stable source before after represented ready.1
      framed control flagsPresent
    exact ⟨retained.1,retained.2,profile.after_control before after _ _
      (X86StateFrame.registerOnly framed) X86BranchGate.writes_data control flagsPresent ready.2⟩

theorem word_stable (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (profile : Profile) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Stable X86WordLibrary.spec profile.Holds := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  intro instruction source following native origin safe step represented prepared holds upper loaded _outside after run
  cases instruction with
  | copy instruction =>
    obtain ⟨values,sourceEq,registersKnown⟩ := represented
    obtain ⟨flags,flagsKnown,quiet⟩ := prepared
    change origin.address.toInt + (((X86CopyBlock.emit instruction).length + 3 : Nat) : Int) < (2 ^ 47 : Int) at upper
    change codeLoaded native origin.address.toInt (X86CopyBlock.emit instruction) at loaded
    let one : X86CopyBlock.Program := .call instruction fun _ => .ret ()
    let stop : Int := origin.address.toInt + (X86CopyBlock.emit instruction).length
    let input : X86CopyBlock.At stop one source native := {
      origin := origin
      placed := by simp only [one,X86CopyBlock.code,List.append_nil]; dsimp only [stop]; omega
      upper := by dsimp only [stop]; omega
      values := values
      source := sourceEq
      registers := registersKnown
      loaded := by simpa only [one,X86CopyBlock.code,List.append_nil] using loaded
      quiet := quiet }
    have oneSafe : one.Safe X86CopyBlock.action source := ⟨safe,by intros; trivial⟩
    have oneRun : one.Runs X86CopyBlock.action source () following := ⟨(),following,step,rfl,rfl⟩
    obtain ⟨target,executed,framed,_outputValues,_encoded,_outputRegisters,_pointer⟩ :=
      (X86CopyBlock.counted_boundary stop).realizes one source following native () oneSafe ⟨input⟩ oneRun
    change (X86FuelPrefix.fetches (X86CopyBlock.steps one)).run native = .ok () target at executed
    have targetRun : (X86FuelPrefix.fetches (X86WordLibrary.count (.copy instruction))).run native = .ok () target := by
      simpa only [one,X86CopyBlock.steps,X86WordLibrary.count,Nat.add_zero] using executed
    have same := X86FuelPrefix.fetches_deterministic _ native after target run targetRun
    rw [same]
    exact profile.after_frame native target _ _ framed X86CopyBlock.writes_data flags flags flagsKnown
      ((framed.registers .rflags (by decide)).trans flagsKnown) rfl holds
  | binary operation destination left right unlocked =>
    obtain ⟨values,_sourceEq,registersKnown⟩ := represented
    obtain ⟨flags,flagsKnown,quiet⟩ := prepared
    change codeLoaded native origin.address.toInt (X86WordLibrary.binaryBytes operation destination left right) at loaded
    rw [X86WordLibrary.binaryBytes_exact] at loaded
    have byteLength : (X86WordLibrary.spec.bytes (.binary operation destination left right unlocked)).length = 9 := by
      change (X86WordLibrary.binaryBytes operation destination left right).length = 9
      rw [X86WordLibrary.binaryBytes_exact]
      rfl
    rw [byteLength] at upper
    have bounded : origin.address.toInt + 9 < (2 ^ 47 : Int) := by omega
    obtain ⟨output,first,second,one,two,three,_firstFrame,_secondFrame,lastFrame⟩ :=
      X86BinBlock.expected_trace other vector (X86BinCapture.decodeOperation operation.val) destination left right
        native origin bounded loaded (values left) (values right) flags
        (registersKnown left (Finset.mem_univ _)) (registersKnown right (Finset.mem_univ _)) flagsKnown quiet
    let target := X86BinBlock.finished native origin.address.toInt (X86BinCapture.decodeOperation operation.val)
      destination (values left) (values right) flags output
    have targetRun : (X86FuelPrefix.fetches 3).run native = .ok () target :=
      X86FuelPrefix.fetches_cons 2 native first target one
        (X86FuelPrefix.fetches_cons 1 first second target two (X86FuelPrefix.fetches_one second target three))
    have same := X86FuelPrefix.fetches_deterministic 3 native after target run targetRun
    rw [same]
    exact profile.after_frame native target _ _ (X86StateFrame.registerOnly lastFrame)
      (X86BinBlock.clobbers_data destination) (X86Flags.mergeFlags flags output) flags flagsKnown
      (X86BinBlock.finished_flags _ _ _ _ _ _ _ _) (X86Alignment.arithmetic_preserves_ac flags output) holds

theorem word_correct (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (profile : Profile) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    X86BlockCompiler.Correct (strengthen X86WordLibrary.spec profile.Holds) := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  exact correct X86WordLibrary.spec profile.Holds (X86WordLibrary.correct other vector) (word_stable other vector profile)

theorem logical_preserves_ac (flags result : BitVec 32) (auxiliary : BitVec 1) :
    Functions._get_rflagsbits_ac (X86LogicalFlags.merged flags result auxiliary) =
      Functions._get_rflagsbits_ac flags := by
  simp [X86LogicalFlags.merged,Functions._get_rflagsbits_ac,Functions._update_rflagsbits_cf,
    Functions._update_rflagsbits_pf,Functions._update_rflagsbits_af,Functions._update_rflagsbits_zf,
    Functions._update_rflagsbits_sf,Functions._update_rflagsbits_of]
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  (interval_cases index;
    simp [Sail.BitVec.extractLsb,Sail.BitVec.updateSubrange,Sail.BitVec.updateSubrange',BitVec.extractLsb])

theorem logical_stable (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (profile : Profile) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Stable X86LogicalLibrary.spec profile.Holds := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  intro instruction source _following native origin _safe _step represented prepared holds upper loaded _outside after run
  obtain ⟨values,_sourceEq,registersKnown⟩ := represented
  obtain ⟨flags,flagsKnown,quiet⟩ := prepared
  have three : (X86LogicalLibrary.spec.bytes instruction).length = 3 := rfl
  have bounded : origin.address.toInt + 3 < (2 ^ 47 : Int) := by rw [three] at upper; omega
  let beginning := rebase native native origin (RegisterFrame.refl dataRegisters native)
    bounded 0 (by decide) (by simpa [address] using origin.rip)
  let site : X86LegacyFetch.Window native (X86LogicalWord.opcode instruction.operation) true
      (X86CopyBlock.physical instruction.source) (X86CopyBlock.physical instruction.destination) := {
    toBasis := beginning
    prefixByte := by
      simpa only [beginning,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
        loaded 0 (X86RegisterEncoding.rex true (X86CopyBlock.physical instruction.source)
          (X86CopyBlock.physical instruction.destination)).toNat (by rfl)
    opcodeByte := by
      simpa only [beginning,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
        loaded 1 (X86LogicalWord.opcode instruction.operation).toNat (by rfl)
    modrmByte := by
      simpa only [beginning,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
        loaded 2 (X86RegisterEncoding.modRM (X86CopyBlock.physical instruction.source)
          (X86CopyBlock.physical instruction.destination)).toNat (by rfl) }
  obtain ⟨output,executed⟩ := X86LogicalWord.fetched other vector instruction.operation native
    (X86CopyBlock.physical instruction.source) (X86CopyBlock.physical instruction.destination) site
    (values instruction.destination) (values instruction.source) flags
    (registersKnown instruction.source (Finset.mem_univ _))
    (registersKnown instruction.destination (Finset.mem_univ _)) flagsKnown quiet
  let newFlags := X86LogicalFlags.merged flags output (0#1)
  let target := X86Move.putPointer (X86Flags.putFlags
    (put native (X86CopyBlock.physical instruction.destination)
      (X86LogicalWord.result instruction.operation (values instruction.destination) (values instruction.source)))
    newFlags) site.next
  have targetRun : (X86FuelPrefix.fetches 1).run native = .ok () target :=
    X86FuelPrefix.fetches_one native target executed
  have same := X86FuelPrefix.fetches_deterministic 1 native after target run targetRun
  rw [same]
  have framed := X86LogicalWord.result_frame instruction.operation native
    (X86CopyBlock.physical instruction.destination) (values instruction.destination)
    (values instruction.source) flags output site.next
  apply profile.after_frame native target _ _ (X86StateFrame.registerOnly framed)
    (X86LogicalWord.writes_data _) newFlags flags flagsKnown
  · rw [(pointer_frame _ site.next).registers .rflags (by decide)]
    simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self]
  · exact logical_preserves_ac flags output (0#1)
  · exact holds

theorem sum_stable {Left : Type u} {Right : Type v} {World : Type s}
    [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (left : X86BlockCompiler.Spec Left World) (right : X86BlockCompiler.Spec Right World)
    (invariant : State → Prop) (leftStable : Stable left invariant) (rightStable : Stable right invariant)
    (sameRepresentation : right.represents = left.represents) (sameReady : right.ready = left.ready) :
    Stable (X86LibrarySum.combine left right) invariant := by
  intro instruction source following native origin safe step represented prepared holds upper loaded outside after run
  cases instruction with
  | inl instruction =>
    exact leftStable instruction source following native origin safe step represented prepared holds upper loaded
      (fun index byte present member => outside index byte present (Finset.mem_union_left _ member)) after run
  | inr instruction =>
    have representedRight : right.represents source native := by rw [sameRepresentation]; exact represented
    have preparedRight : right.ready native := by rw [sameReady]; exact prepared
    exact rightStable instruction source following native origin safe step representedRight preparedRight holds upper loaded
      (fun index byte present member => outside index byte present (Finset.mem_union_right _ member)) after run

theorem scalar_stable (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (profile : Profile) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Stable X86ScalarLibrary.spec profile.Holds := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  exact sum_stable X86WordLibrary.spec X86LogicalLibrary.spec profile.Holds
    (word_stable other vector profile) (logical_stable other vector profile) rfl rfl

theorem scalar_correct (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (profile : Profile) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    X86BlockCompiler.Correct (strengthen X86ScalarLibrary.spec profile.Holds) := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  exact correct X86ScalarLibrary.spec profile.Holds (X86ScalarLibrary.correct other vector)
    (scalar_stable other vector profile)

theorem scalar_compile_wp (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (profile : Profile) (stop : Int) (program : X86ScalarLibrary.Program)
    (source : X86ScalarLibrary.World) (native : State)
    (input : X86BlockCompiler.At (strengthen X86ScalarLibrary.spec profile.Holds) stop program source native)
    (post : Unit → X86ScalarLibrary.World → Prop) (wp : program.wp X86ScalarLibrary.spec.action post source) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ following after, program.Runs X86ScalarLibrary.spec.action source () following ∧ post () following ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps X86ScalarLibrary.spec program)).run native = .ok () after ∧
      X86StateFrame.Frame X86ScalarLibrary.spec.registerWrites X86ScalarLibrary.spec.byteWrites native after ∧
      X86BlockCompiler.Observed (strengthen X86ScalarLibrary.spec profile.Holds) stop () following after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have checked := X86BlockCompiler.compile_wp (strengthen X86ScalarLibrary.spec profile.Holds)
    (scalar_correct other vector profile) X86ScalarLibrary.progress stop program source native input post wp
  rw [steps_strengthen] at checked
  simpa only [strengthen] using checked

def conditional_at (profile : Profile) (condition : Fin 12)
    (yes no : X86ScalarLibrary.Program) (source : X86ScalarLibrary.World) (native : State)
    (input : X86Conditional.At X86ScalarLibrary.spec (X86ScalarLibrary.compatible condition) yes no source native)
    (holds : profile.Holds native) :
    X86Conditional.At (strengthen X86ScalarLibrary.spec profile.Holds)
      (compatible profile condition) yes no source native where
  origin := input.origin
  yesFits := by rw [code_strengthen]; exact input.yesFits
  noFits := by rw [code_strengthen]; exact input.noFits
  upper := by simpa only [code_strengthen,compatible] using input.upper
  loaded := by simpa only [code_strengthen,compatible] using input.loaded
  represented := input.represented
  ready := ⟨input.ready,holds⟩
  outside := by
    rw [code_strengthen,code_strengthen]
    exact input.outside

theorem conditional_wp (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (profile : Profile) (condition : Fin 12) (yes no : X86ScalarLibrary.Program) (source : X86ScalarLibrary.World) (native : State)
    (input : X86Conditional.At (strengthen X86ScalarLibrary.spec profile.Holds) (compatible profile condition) yes no source native)
    (choice : Bool) (chosen : RegisterProfile.truth ((compatible profile condition).value source) = some choice)
    (post : Unit → X86ScalarLibrary.World → Prop) (wp : (if choice then yes else no).wp X86ScalarLibrary.spec.action post source) :
    letI : OtherOpcodeHandlers := X86Conditional.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ following after,
      (if choice then yes else no).Runs X86ScalarLibrary.spec.action source () following ∧ post () following ∧
      (X86FuelPrefix.fetches (2 + X86BlockCompiler.steps X86ScalarLibrary.spec (if choice then yes else no) +
        (if choice then 1 else 0))).run native = .ok () after ∧
      X86StateFrame.Frame (X86ScalarLibrary.spec.registerWrites ∪ X86BranchGate.writes) X86ScalarLibrary.spec.byteWrites native after ∧
      X86BlockCompiler.Observed (strengthen X86ScalarLibrary.spec profile.Holds) (input.layout.address.toInt +
        (X86Conditional.code (compatible profile condition).condition (X86BlockCompiler.code X86ScalarLibrary.spec yes)
          (X86BlockCompiler.code X86ScalarLibrary.spec no)).length) () following after ∧
      ∀ count ≤ 2 + X86BlockCompiler.steps X86ScalarLibrary.spec (if choice then yes else no) + (if choice then 1 else 0),
        ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
          X86StateFrame.Frame (X86ScalarLibrary.spec.registerWrites ∪ X86BranchGate.writes) X86ScalarLibrary.spec.byteWrites native observed := by
  let : OtherOpcodeHandlers := X86Conditional.handlers other extra
  let : VectorOpcodeHandlers := vector
  have checked := X86Conditional.compile_wp other extra vector
    (strengthen X86ScalarLibrary.spec profile.Holds) (compatible profile condition)
    (scalar_correct (X86Conditional.handlers other extra) vector profile) X86ScalarLibrary.progress
    yes no source native input choice chosen post wp
  simp only [steps_strengthen,code_strengthen] at checked
  simpa only [strengthen] using checked

namespace Controls
open X86ScalarLibrary
private def copy : Instruction := .inl (.copy ⟨1,2,by decide⟩)
private def mask : Instruction := .inr ⟨.and,3,2,by decide⟩
private def add : Instruction := .inl (.binary 0 4 2 3 (by decide))
private def program : Program := Prog.bind (Prog.prim copy) fun _ =>
  Prog.bind (Prog.prim mask) fun _ => Prog.prim add
private def value : Word := 0x80000001000000ff#64
private def maskWord : Word := 0xffffffff000000f0#64
private def values (register : Fin 12) : Word :=
  if register = 1 then value else if register = 3 then maskWord else 0
private def copied : Fin 12 → Word := Function.update values 2 value
private def masked : Fin 12 → Word := Function.update copied 2 (value &&& maskWord)
private def finalValues : Fin 12 → Word := Function.update masked 4 ((value &&& maskWord) + maskWord)
private def raw : List Nat :=
  [0x48,0x89,0xf2,0x48,0x21,0xca,0x49,0x89,0xd6,0x49,0x01,0xce,0x4d,0x89,0xf0]

theorem compiled_bytes : X86BlockCompiler.code spec program = raw := by
  unfold program
  rw [X86BlockCompiler.code_bind,X86BlockCompiler.code_bind,X86BlockCompiler.code_prim,
    X86BlockCompiler.code_prim,X86BlockCompiler.code_prim]
  simp only [spec,X86LibrarySum.combine,copy,mask,add,Sum.elim_inl,Sum.elim_inr,
    X86WordLibrary.spec,X86LogicalLibrary.spec,X86WordLibrary.bytes]
  rw [X86CopyBlock.emit_distinct _ (by decide),X86WordLibrary.binaryBytes_exact]
  rfl

theorem compiled_steps : X86BlockCompiler.steps spec program = 5 := rfl

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 15).map fun index => (4096 + index,BitVec.ofNat 8 ((raw[index]?).getD 0))
private def profile : Profile where
  controls := Vector.ofFn (fun index => if index.val = 0 then (0x40000#64) else 0)
  visible := Vector.ofFn (fun index => if index.val = 1 then (3#16) else 0)
  ac := 1#1

private def before : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .rdi (values 0)
  let registers := registers.insert .rsi (values 1)
  let registers := registers.insert .rdx (values 2)
  let registers := registers.insert .rcx (values 3)
  let registers := registers.insert .r8 (values 4)
  let registers := registers.insert .r9 (values 5)
  let registers := registers.insert .r10 (values 6)
  let registers := registers.insert .r11 (values 7)
  let registers := registers.insert .rax (values 8)
  let registers := registers.insert .rbx (values 9)
  let registers := registers.insert .r12 (values 10)
  let registers := registers.insert .r13 (values 11)
  let registers := registers.insert .rsp (16384#64)
  let registers := registers.insert .ctrs profile.controls
  let registers := registers.insert .seg_visibles profile.visible
  let registers := registers.insert .rflags (0x40246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList cells,(),0,#[]⟩

private def origin : X86LegacyFetch.Basis before where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [before,Std.ExtDHashMap.get?_insert]
  fault := by simp [before,Std.ExtDHashMap.get?_insert]
  msrs := by simp [before,Std.ExtDHashMap.get?_insert]
  segments := by simp [before,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before,Std.ExtDHashMap.get?_insert]
  rip := by simp [before,Std.ExtDHashMap.get?_insert]

private theorem cell (address : Nat) (byte : BitVec 8) (present : (address,byte) ∈ cells) :
    before.mem.get? address = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (by decide) present

private def input : X86BlockCompiler.At spec 4111 program (Cells.encode Finset.univ values) before where
  origin := origin
  placed := by rw [compiled_bytes]; decide
  upper := by decide
  represented := by
    refine ⟨values,rfl,?_⟩
    intro register _
    fin_cases register <;>
      simp [lookup,placed,Registers.canonical,Registers.Placement.resolve,Registers.logicalSlot,
        key,before,Std.ExtDHashMap.get?_insert] <;> rfl
  ready := ⟨0x40246#32,by simp [before,Std.ExtDHashMap.get?_insert],by simp [before]⟩
  loaded := by
    intro index byte present
    rw [compiled_bytes] at present
    have within : index < 15 := (List.getElem?_eq_some_iff.mp present).1
    interval_cases index <;>
      simp only [raw,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] at present <;>
      subst byte <;> apply cell <;> decide
  outside := by intros; simp [spec,X86LibrarySum.combine,X86WordLibrary.spec,X86LogicalLibrary.spec]

private theorem source_wp : program.wp spec.action
    (fun _ world => world = Cells.encode Finset.univ finalValues) (Cells.encode Finset.univ values) := by
  unfold program
  rw [wp_bind]
  apply source_wp_step copy values value rfl
  rw [wp_bind]
  apply source_wp_step mask copied (value &&& maskWord) rfl
  exact source_wp_step add masked ((value &&& maskWord) + maskWord) rfl _ rfl
private theorem profile_before : profile.Holds before := by
  refine ⟨?_,?_,0x40246#32,?_,?_⟩
  · simp [before,Std.ExtDHashMap.get?_insert]
  · simp [before,Std.ExtDHashMap.get?_insert]
  · simp [before,Std.ExtDHashMap.get?_insert]
  · decide

theorem enabled_at_entry :
    X86FrameLoad.alignmentEnabled profile.controls (0x40246#32) profile.visible = true := by decide

theorem alignment_readback :
    (Functions.alignment_checking_enabled_p ()).run before = .ok true before := by
  have read := profile.alignment_exact before profile_before
  simpa only [show profile.enabled = true from by decide] using read

theorem copy_mask_add_profile (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ native after, (X86FuelPrefix.fetches 5).run native = .ok () after ∧
      lookup after (X86CopyBlock.physical 4) = some (0x80000000000001e0#64) ∧
      after.regs.get? .ctrs = some profile.controls ∧ after.regs.get? .seg_visibles = some profile.visible ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (1#1) ∧
      ∀ address, after.mem.get? address = native.mem.get? address := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let strengthened := strengthen_at spec profile.Holds 4111 program _ before input profile_before
  obtain ⟨following,after,_sourceRun,expected,run,frame,⟨outputValues,encoded,outputRegisters⟩,
      ⟨_prepared,controls,visible,flags,flagsKnown,acKnown⟩,_rip⟩ :=
    scalar_compile_wp other vector profile 4111 program _ before strengthened _ source_wp
  have equalValues := (Cells.encode_le_iff Finset.univ Finset.univ outputValues finalValues).mp
    (le_of_eq (encoded.symm.trans expected))
  have read := outputRegisters 4 (Finset.mem_univ _)
  rw [equalValues.2 4 (Finset.mem_univ _)] at read
  have expectedWord : finalValues 4 = (0x80000000000001e0#64) := by decide
  rw [expectedWord] at read
  refine ⟨before,after,run,read,controls,visible,?_,?_⟩
  · rw [flagsKnown]
    simpa only [Option.map_some,profile] using congrArg some acKnown
  · intro address
    exact frame.memory address (by simp [spec,X86LibrarySum.combine,X86WordLibrary.spec,X86LogicalLibrary.spec])

theorem cleared_ac_rejected (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ native, ∀ after, (after.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (0#1) →
      (X86FuelPrefix.fetches 5).run native ≠ .ok () after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨native,proved,run,_word,_controls,_visible,ac,_memory⟩ := copy_mask_add_profile other vector
  refine ⟨native,?_⟩
  intro after cleared executed
  have same := X86FuelPrefix.fetches_deterministic 5 native proved after run executed
  rw [same,cleared] at ac
  exact (by decide : (some (0#1) : Option (BitVec 1)) ≠ some (1#1)) ac

private def fallback : Program := Prog.prim (.inl (.copy ⟨1,4,by decide⟩))
private def branchValues (choice : Bool) (register : Fin 12) : Word :=
  if register = 7 then booleanWord choice else values register
private def branchFinal (choice : Bool) : Fin 12 → Word :=
  if choice then
    Function.update (Function.update (Function.update (branchValues choice) 2 value) 2 (value &&& maskWord))
      4 ((value &&& maskWord) + maskWord)
  else Function.update (branchValues choice) 4 value
private def branchRaw : List Nat :=
  [0x4d,0x85,0xdb,0x0f,0x84,20,0,0,0] ++ raw ++ [0xe9,3,0,0,0,0x49,0x89,0xf0]

theorem branch_compiled_bytes : X86Conditional.code (X86ScalarLibrary.compatible 7).condition
    (X86BlockCompiler.code spec program) (X86BlockCompiler.code spec fallback) = branchRaw := by
  rw [compiled_bytes]
  have fallbackBytes : X86BlockCompiler.code spec fallback = [0x49,0x89,0xf0] := by
    rw [fallback,X86BlockCompiler.code_prim]
    change X86CopyBlock.emit ⟨1,4,by decide⟩ = _
    rw [X86CopyBlock.emit_distinct _ (by decide)]
    rfl
  rw [fallbackBytes]
  rfl

private def branchCells : List (Nat × BitVec 8) :=
  (List.range 32).map fun index => (4096 + index,BitVec.ofNat 8 ((branchRaw[index]?).getD 0))
private def branchBefore (choice : Bool) : State :=
  {before with regs := before.regs.insert .r11 (booleanWord choice),mem := Std.ExtHashMap.ofList branchCells}

private def branchOrigin (choice : Bool) : X86LegacyFetch.Basis (branchBefore choice) where
  address := origin.address
  opcodeAddress := origin.opcodeAddress
  modrmAddress := origin.modrmAddress
  next := origin.next
  control := origin.control
  attributes := origin.attributes
  step1 := origin.step1
  step2 := origin.step2
  step3 := origin.step3
  status := by simpa [branchBefore,Std.ExtDHashMap.get?_insert] using origin.status
  fault := by simpa [branchBefore,Std.ExtDHashMap.get?_insert] using origin.fault
  msrs := by simpa [branchBefore,Std.ExtDHashMap.get?_insert] using origin.msrs
  segments := by simpa [branchBefore,Std.ExtDHashMap.get?_insert] using origin.segments
  longMode := origin.longMode
  codeMode := origin.codeMode
  application := by simpa [branchBefore,Std.ExtDHashMap.get?_insert] using origin.application
  rip := by simpa [branchBefore,Std.ExtDHashMap.get?_insert] using origin.rip

private theorem branchCell (choice : Bool) (address : Nat) (byte : BitVec 8)
    (present : (address,byte) ∈ branchCells) : (branchBefore choice).mem.get? address = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (by decide) present

private def branchInput (choice : Bool) : X86Conditional.At spec (X86ScalarLibrary.compatible 7) program fallback
    (Cells.encode Finset.univ (branchValues choice)) (branchBefore choice) where
  origin := branchOrigin choice
  yesFits := by rw [compiled_bytes]; decide
  noFits := by change (X86CopyBlock.emit ⟨1,4,by decide⟩).length < 2 ^ 31; rw [X86CopyBlock.emit_distinct _ (by decide)]; decide
  upper := by
    rw [branch_compiled_bytes]
    change (4096 : Int) + (branchRaw.length + 3 : Nat) < 2 ^ 47
    decide
  loaded := by
    rw [branch_compiled_bytes]
    change codeLoaded (branchBefore choice) 4096 branchRaw
    intro index byte present
    have within : index < 32 := (List.getElem?_eq_some_iff.mp present).1
    interval_cases index <;>
      simp only [branchRaw,raw,List.cons_append,List.nil_append,
        List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] at present <;>
      subst byte <;> apply branchCell <;> decide
  represented := by
    refine ⟨branchValues choice,rfl,?_⟩
    intro register _
    fin_cases register <;>
      simp [lookup,placed,Registers.canonical,Registers.Placement.resolve,Registers.logicalSlot,
        key,branchBefore,before,branchValues,Std.ExtDHashMap.get?_insert] <;> rfl
  ready := ⟨0x40246#32,by simp [branchBefore,before,Std.ExtDHashMap.get?_insert],
    by simp [branchBefore,before,Std.ExtDHashMap.get?_insert]⟩
  outside := by intros; simp [spec,X86LibrarySum.combine,X86WordLibrary.spec,X86LogicalLibrary.spec]

private theorem branch_source_wp (choice : Bool) : (if choice then program else fallback).wp spec.action
    (fun _ world => world = Cells.encode Finset.univ (branchFinal choice))
    (Cells.encode Finset.univ (branchValues choice)) := by
  cases choice with
  | false =>
    change (Prog.prim (.inl (.copy ⟨1,4,by decide⟩))).wp spec.action _ _
    exact source_wp_step _ (branchValues false) value rfl _ rfl
  | true =>
    change program.wp spec.action _ _
    unfold program
    rw [wp_bind]
    apply source_wp_step copy (branchValues true) value rfl
    rw [wp_bind]
    apply source_wp_step mask (Function.update (branchValues true) 2 value) (value &&& maskWord) rfl
    exact source_wp_step add _ ((value &&& maskWord) + maskWord) rfl _ rfl

private theorem branch_profile (choice : Bool) : profile.Holds (branchBefore choice) := by
  refine ⟨?_,?_,0x40246#32,?_,?_⟩
  · simp [branchBefore,before,Std.ExtDHashMap.get?_insert]
  · simp [branchBefore,before,Std.ExtDHashMap.get?_insert]
  · simp [branchBefore,before,Std.ExtDHashMap.get?_insert]
  · decide

theorem branch_copy_mask_add_profile (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (choice : Bool) :
    letI : OtherOpcodeHandlers := X86Conditional.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ native after, (X86FuelPrefix.fetches (if choice then 8 else 3)).run native = .ok () after ∧
      lookup after (X86CopyBlock.physical 4) = some (if choice then (0x80000000000001e0#64) else value) ∧
      after.regs.get? .rip = some (4128#64) ∧ profile.Holds after ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (1#1) ∧
      ∀ address, after.mem.get? address = native.mem.get? address := by
  let : OtherOpcodeHandlers := X86Conditional.handlers other extra
  let : VectorOpcodeHandlers := vector
  have chosen : RegisterProfile.truth ((X86Readiness.compatible profile 7).value
      (Cells.encode Finset.univ (branchValues choice))) = some choice := by
    change RegisterProfile.truth (X86Conditional.wordValue 7 (Cells.encode Finset.univ (branchValues choice))) = some choice
    rw [X86Conditional.wordValue_encode]
    cases choice <;> rfl
  let prepared := conditional_at profile 7 program fallback _ (branchBefore choice) (branchInput choice) (branch_profile choice)
  obtain ⟨following,after,_sourceRun,expected,run,frame,
      ⟨⟨outputValues,encoded,outputRegisters⟩,⟨_ready,holds⟩,rip⟩,_prefixes⟩ :=
    X86Readiness.conditional_wp other extra vector profile 7 program fallback _ (branchBefore choice)
      prepared choice chosen _ (branch_source_wp choice)
  have equalValues := (Cells.encode_le_iff Finset.univ Finset.univ outputValues (branchFinal choice)).mp
    (le_of_eq (encoded.symm.trans expected))
  have read := outputRegisters 4 (Finset.mem_univ _)
  rw [equalValues.2 4 (Finset.mem_univ _)] at read
  have expectedWord : branchFinal choice 4 = (if choice then (0x80000000000001e0#64) else value) := by
    cases choice <;> decide
  rw [expectedWord] at read
  refine ⟨branchBefore choice,after,?_,read,?_,holds,?_,?_⟩
  · cases choice <;> exact run
  · have length : (X86Conditional.code (X86Readiness.compatible profile 7).condition
        (X86BlockCompiler.code spec program) (X86BlockCompiler.code spec fallback)).length = 32 := by
      change (X86Conditional.code (X86ScalarLibrary.compatible 7).condition
        (X86BlockCompiler.code spec program) (X86BlockCompiler.code spec fallback)).length = 32
      rw [branch_compiled_bytes]
      rfl
    have start : prepared.layout.address.toInt = 4096 := rfl
    rw [length,start] at rip
    exact rip
  · obtain ⟨_controls,_visible,flags,flagsKnown,acKnown⟩ := holds
    rw [flagsKnown]
    simpa only [Option.map_some,profile] using congrArg some acKnown
  · intro address
    exact frame.memory address (by simp [spec,X86LibrarySum.combine,X86WordLibrary.spec,X86LogicalLibrary.spec])

theorem branch_cleared_ac_rejected (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (choice : Bool) :
    letI : OtherOpcodeHandlers := X86Conditional.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ native, ∀ after, (after.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (0#1) →
      (X86FuelPrefix.fetches (if choice then 8 else 3)).run native ≠ .ok () after := by
  let : OtherOpcodeHandlers := X86Conditional.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨native,proved,run,_word,_rip,_profile,ac,_memory⟩ := branch_copy_mask_add_profile other extra vector choice
  refine ⟨native,?_⟩
  intro after cleared executed
  have same := X86FuelPrefix.fetches_deterministic _ native proved after run executed
  rw [same,cleared] at ac
  exact (by decide : (some (0#1) : Option (BitVec 1)) ≠ some (1#1)) ac

theorem nonboolean_condition_refused :
    RegisterProfile.truth ((X86Readiness.compatible profile 7).value (Cells.encode Finset.univ
      (Function.update (branchValues false) 7 (2#64)))) = none := by
  change RegisterProfile.truth (X86Conditional.wordValue 7 (Cells.encode Finset.univ
    (Function.update (branchValues false) 7 (2#64)))) = none
  rw [X86Conditional.wordValue_encode]
  rfl

theorem branch_opcode_rejected (choice : Bool) :
    let changed : State := {branchBefore choice with mem := (branchBefore choice).mem.insert 4100 (0x85#8)}
    ¬Nonempty (X86Conditional.At (strengthen spec profile.Holds) (X86Readiness.compatible profile 7)
      program fallback (Cells.encode Finset.univ (branchValues choice)) changed) := by
  let changed : State := {branchBefore choice with mem := (branchBefore choice).mem.insert 4100 (0x85#8)}
  change ¬Nonempty (X86Conditional.At (strengthen spec profile.Holds) (X86Readiness.compatible profile 7)
    program fallback (Cells.encode Finset.univ (branchValues choice)) changed)
  rintro ⟨candidate⟩
  have actual : changed.regs.get? .rip = some (4096#64) := by
    simp [changed,branchBefore,before,Std.ExtDHashMap.get?_insert]
  have equal : candidate.origin.address.signExtend 64 = (4096#64) :=
    Option.some.inj (candidate.origin.rip.symm.trans actual)
  have intEqual := congrArg BitVec.toInt equal
  rw [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64)] at intEqual
  have entry : candidate.origin.address.toInt = 4096 := intEqual
  have expected := candidate.loaded 4 0x84 (by
    rw [code_strengthen,code_strengthen]
    change (X86Conditional.code (X86ScalarLibrary.compatible 7).condition
      (X86BlockCompiler.code spec program) (X86BlockCompiler.code spec fallback))[4]? = some 0x84
    rw [branch_compiled_bytes]
    rfl)
  rw [entry] at expected
  change changed.mem.get? 4100 = some (0x84#8) at expected
  have modified : changed.mem.get? 4100 = some (0x85#8) := by simp [changed]
  rw [modified] at expected
  exact (by decide : (some (0x85#8) : Option (BitVec 8)) ≠ some (0x84#8)) expected

end Controls

end Mettapedia.Machines.TIsa.X86Readiness
