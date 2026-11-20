import Mettapedia.Machines.TIsa.X86CountedWordProgram
import Mettapedia.Machines.TIsa.X86Readiness
/-!
# Architectural profiles through complete counted word programs

Actual CMP/JAE headers, word-body compiler runs, ADD/JMP latches and entry
cap/zeroing instructions retain the control-register, segment and AC profile.
The existing rank-decreasing loop and source resource-firing semantics supply
the iteration schedule; native determinism transfers the stronger profile.

The full program includes cap validation, counter initialization, zero through
all admitted iterations, final header exit and excessive-bound rejection.
Its bytes and exact counts are unchanged. Controls use a dirty old counter and
AC enabled, cover bounds zero through ten and excess eleven, and reject clearing
AC or changed cap/body bytes. Memory/other body libraries, FUND, early exits,
public status/ABI, admission/hosting and emitter correspondence retain their
separate composition obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86LoopReadiness
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86WordLibrary X86CountedWordLoop
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

theorem word_run (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (profile : X86Readiness.Profile) (stop : Int) (program : X86WordBody.Program)
    (source : World) (native after : State)
    (input : X86BlockCompiler.At spec stop program source native)
    (safe : program.Safe action source) (holds : profile.Holds native)
    (run : letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches (X86BlockCompiler.steps spec program)).run native = .ok () after) :
    profile.Holds after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let post : Unit → World → Prop := fun reply following => program.Runs action source reply following
  have wp : program.wp action post source := ⟨safe,fun _ _ executed => executed⟩
  let stronger := X86Readiness.strengthen_at spec profile.Holds stop program source native input holds
  obtain ⟨_following,target,_sourceRun,_reachable,executed,_frame,observed⟩ :=
    X86BlockCompiler.compile_wp (X86Readiness.strengthen spec profile.Holds)
      (X86Readiness.word_correct other vector profile) progress stop program source native stronger post wp
  rw [X86Readiness.steps_strengthen] at executed
  have same := X86FuelPrefix.fetches_deterministic _ native after target run executed
  rw [same]
  exact observed.2.1.2

theorem header_run (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (profile : X86Readiness.Profile) (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program)
    (base : Int) (context : Context loop body base) (values : X86CountedWordLoop.Location → Word) (native after : State)
    (input : At loop body base 0 values native) (holds : profile.Holds native)
    (run : letI : OtherOpcodeHandlers := handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches 2).run native = .ok () after) : profile.Holds after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let head := headInput loop body base context values native input
  obtain ⟨target,flags,executed,frame,_index,_bound,flagsKnown,_rip,control⟩ :=
    X86LoopHeader.executes_control (X86LoopLatch.handlers other) extra vector native _ _ head
  have same := X86FuelPrefix.fetches_deterministic 2 native after target run executed
  rw [same]
  exact profile.after_control native target _ _ (X86StateFrame.registerOnly frame)
    (by decide) control ⟨flags,flagsKnown⟩ holds

theorem latch_run (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (profile : X86Readiness.Profile) (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program)
    (base : Int) (context : Context loop body base) (values : X86CountedWordLoop.Location → Word) (native after : State)
    (input : At loop body base (latchOffset body) values native) (holds : profile.Holds native)
    (run : letI : OtherOpcodeHandlers := handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches 2).run native = .ok () after) : profile.Holds after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let latch := latchInput loop body base context values native input
  obtain ⟨target,flags,executed,frame,_value,flagsKnown,_rip,control,_prefixes⟩ :=
    X86LoopLatch.executes_control (handlers other extra) vector native _ latch
  have same := X86FuelPrefix.fetches_deterministic 2 native after target run executed
  rw [same]
  exact profile.after_control native target _ _ (X86StateFrame.registerOnly frame)
    (X86RegisterIncrement.writes_data _) control ⟨flags,flagsKnown⟩ holds

theorem body_run (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (profile : X86Readiness.Profile) (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program)
    (base : Int) (context : Context loop body base) (values : X86CountedWordLoop.Location → Word) (native after : State)
    (input : At loop body base 9 values native) (holds : profile.Holds native)
    (run : letI : OtherOpcodeHandlers := handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches (X86BlockCompiler.steps spec body)).run native = .ok () after) : profile.Holds after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let bodyInput : X86BlockCompiler.At spec (base + latchOffset body) body
      (Cells.encode Finset.univ (X86WordBody.data values)) native := {
    origin := input.origin
    placed := by have := input.placed; dsimp [latchOffset,bodyBytes]; omega
    upper := by have := context.upper; dsimp [latchOffset,exitOffset] at *; omega
    represented := ⟨X86WordBody.data values,rfl,input.represented.1⟩
    ready := input.ready
    loaded := by
      rw [input.placed]
      exact X86Conditional.loaded_slice native base (code loop body) (bodyBytes body) 9 input.loaded (body_byte loop body)
    outside := by intros; simp [spec] }
  exact word_run (handlers other extra) vector profile (base + latchOffset body) body _ native after
    bodyInput (X86WordBody.all_safe body _) holds run

theorem iteration_run (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (profile : X86Readiness.Profile) (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program)
    (base : Int) (context : Context loop body base) (values : X86CountedWordLoop.Location → Word) (native after : State)
    (input : At loop body base 0 values native)
    (less : (values (.inr loop.index)).toNat < (values (.inr loop.bound)).toNat)
    (holds : profile.Holds native)
    (run : letI : OtherOpcodeHandlers := handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches (X86BlockCompiler.steps spec body + 4)).run native = .ok () after) : profile.Holds after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨headMachine,_headInvocation,_headEnabled,_headFired,headRun,_headFrame,⟨headAt⟩,_headPrefixes⟩ :=
    header_step other extra vector loop body base context values native input
  have headProfile := header_run other extra vector profile loop body base context values native headMachine input holds headRun
  have atBody : At loop body base 9 (loop.headerValues values) headMachine := by simpa only [if_pos less] using headAt
  obtain ⟨bodyValues,_bodyEntries,bodyMachine,_bodyFires,_bodySites,bodyRun,_bodyFrame,⟨bodyAt⟩,indexSame,boundSame,_bodyPrefixes⟩ :=
    body_step other extra vector loop body base context (loop.headerValues values) headMachine atBody
  have bodyProfile := body_run other extra vector profile loop body base context (loop.headerValues values)
    headMachine bodyMachine atBody headProfile bodyRun
  have bodyIndex : bodyValues (.inr loop.index) = values (.inr loop.index) := by
    simpa [Control.Loop.headerValues] using indexSame
  have bodyBound : bodyValues (.inr loop.bound) = values (.inr loop.bound) := by
    simpa [Control.Loop.headerValues] using boundSame
  have bodyLess : (bodyValues (.inr loop.index)).toNat < (bodyValues (.inr loop.bound)).toNat := by
    rw [bodyIndex,bodyBound]
    exact less
  obtain ⟨machine,_latchInvocation,_latchEnabled,_latchFired,latchRun,_latchFrame,_atHeader,_latchBound,_rankStep,_latchPrefixes⟩ :=
    latch_step other extra vector loop body base context bodyValues bodyMachine bodyAt bodyLess
  have finalProfile := latch_run other extra vector profile loop body base context bodyValues bodyMachine machine bodyAt bodyProfile latchRun
  have firstRun := X86FuelPrefix.fetches_then 2 (X86BlockCompiler.steps spec body) native headMachine bodyMachine headRun bodyRun
  have combined := X86FuelPrefix.fetches_then (2 + X86BlockCompiler.steps spec body) 2 native bodyMachine machine firstRun latchRun
  have countEq : 2 + X86BlockCompiler.steps spec body + 2 = X86BlockCompiler.steps spec body + 4 := by omega
  rw [countEq] at combined
  have same := X86FuelPrefix.fetches_deterministic _ native after machine run combined
  rw [same]
  exact finalProfile

theorem loop_run (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (profile : X86Readiness.Profile) (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program)
    (base : Int) (context : Context loop body base) (values : X86CountedWordLoop.Location → Word) (native after : State)
    (input : At loop body base 0 values native) (holds : profile.Holds native)
    (run : letI : OtherOpcodeHandlers := handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches (loop.rank values * (X86BlockCompiler.steps spec body + 4) + 2)).run native = .ok () after) :
    profile.Holds after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction values using (measure loop.rank).wf.induction generalizing native after with
  | h values ih =>
    by_cases less : (values (.inr loop.index)).toNat < (values (.inr loop.bound)).toNat
    · obtain ⟨middle,_firstEntries,middleMachine,_firstSource,_firstSites,firstRun,_firstFrame,⟨nextInput⟩,_boundSame,rankStep,_firstPrefixes⟩ :=
        iteration other extra vector loop body base context values native input less
      have nextProfile := iteration_run other extra vector profile loop body base context values native middleMachine input less holds firstRun
      have decreases : loop.rank middle < loop.rank values := by omega
      have countEq : X86BlockCompiler.steps spec body + 4 +
          (loop.rank middle * (X86BlockCompiler.steps spec body + 4) + 2) =
          loop.rank values * (X86BlockCompiler.steps spec body + 4) + 2 := by
        rw [←rankStep,Nat.add_mul,Nat.one_mul]
        omega
      rw [←countEq] at run
      obtain ⟨actual,head,tail⟩ := X86BlockCompiler.fetches_split (X86BlockCompiler.steps spec body + 4)
        (loop.rank middle * (X86BlockCompiler.steps spec body + 4) + 2) native after run
      have same := X86FuelPrefix.fetches_deterministic _ native actual middleMachine head firstRun
      rw [same] at tail
      exact ih middle decreases middleMachine after nextInput nextProfile tail
    · have equalNat : (values (.inr loop.index)).toNat = (values (.inr loop.bound)).toNat := by
        have ordered := input.valid.1
        omega
      have equal : values (.inr loop.index) = values (.inr loop.bound) := BitVec.eq_of_toNat_eq equalNat
      have rankZero : loop.rank values = 0 := by simp only [Control.Loop.rank,equal,Nat.sub_self]
      have runTwo : (X86FuelPrefix.fetches 2).run native = .ok () after := by
        simpa only [rankZero,Nat.zero_mul,Nat.zero_add] using run
      exact header_run other extra vector profile loop body base context values native after input holds runTwo

theorem entry_run (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (profile : X86Readiness.Profile) (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program)
    (base : Int) (context : X86CountedWordProgram.Context loop body base)
    (values : X86CountedWordLoop.Location → Word) (native after : State)
    (input : X86CountedWordProgram.At loop body base context values native) (holds : profile.Holds native)
    (run : letI : OtherOpcodeHandlers := X86CountedWordProgram.handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches (if (values (.inr loop.bound)).toNat ≤ loop.maximum then 4 else 3)).run native = .ok () after) :
    profile.Holds after := by
  let : OtherOpcodeHandlers := X86CountedWordProgram.handlers other extra
  let : VectorOpcodeHandlers := vector
  let prepared := X86CountedWordProgram.entryInput loop body base context values native input
  obtain ⟨target,flags,executed,frame,_index,_bound,flagsKnown,_rip,control⟩ :=
    X86LoopEntry.executes_control (X86LoopLatch.handlers (X86FrameStore.linkedHandlers other)) extra vector native
      (X86CopyBlock.physical loop.index) (X86CopyBlock.physical loop.bound) prepared
  have cost : (if prepared.boundValue.toNat ≤ prepared.cap.toNat then 4 else 3) =
      (if (values (.inr loop.bound)).toNat ≤ loop.maximum then 4 else 3) := by
    change (if (values (.inr loop.bound)).toNat ≤ (X86CountedWordProgram.cap loop).toNat then 4 else 3) = _
    rw [X86CountedWordProgram.cap_exact loop context.inner.checked]
  rw [cost] at executed
  have same := X86FuelPrefix.fetches_deterministic _ native after target run executed
  rw [same]
  exact profile.after_control native target _ _ (X86StateFrame.registerOnly frame)
    (X86LoopEntry.writes_data _) control ⟨flags,flagsKnown⟩ holds

theorem program_run (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (profile : X86Readiness.Profile) (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program)
    (base : Int) (context : X86CountedWordProgram.Context loop body base)
    (values : X86CountedWordLoop.Location → Word) (native after : State)
    (input : X86CountedWordProgram.At loop body base context values native)
    (bounded : (values (.inr loop.bound)).toNat ≤ loop.maximum) (holds : profile.Holds native)
    (run : letI : OtherOpcodeHandlers := X86CountedWordProgram.handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches (X86CountedWordProgram.instructionCount loop body values)).run native = .ok () after) :
    profile.Holds after := by
  let : OtherOpcodeHandlers := X86CountedWordProgram.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle,_invocation,_enabled,_fired,first,_firstFrame,⟨atHeader⟩,_prefixes⟩ :=
    X86CountedWordProgram.entry_step other extra vector loop body base context values native input bounded
  have middleProfile := entry_run other extra vector profile loop body base context values native middle input holds
    (by simpa only [if_pos bounded] using first)
  have cost : 4 + (loop.rank (loop.entryValues values) * (X86BlockCompiler.steps spec body + 4) + 2) =
      X86CountedWordProgram.instructionCount loop body values := by
    rw [X86CountedWordProgram.entry_rank loop values context.inner.checked]
    dsimp only [X86CountedWordProgram.instructionCount]
    omega
  rw [←cost] at run
  obtain ⟨actual,head,tail⟩ := X86BlockCompiler.fetches_split 4
    (loop.rank (loop.entryValues values) * (X86BlockCompiler.steps spec body + 4) + 2) native after run
  have same := X86FuelPrefix.fetches_deterministic 4 native actual middle head first
  rw [same] at tail
  exact loop_run (X86FrameStore.linkedHandlers other) extra vector profile loop body (base + 18) context.inner
    (loop.entryValues values) middle after atHeader middleProfile tail

theorem completes_profile (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (profile : X86Readiness.Profile) (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program)
    (base : Int) (context : X86CountedWordProgram.Context loop body base)
    (values : X86CountedWordLoop.Location → Word) (native : State)
    (input : X86CountedWordProgram.At loop body base context values native)
    (bounded : (values (.inr loop.bound)).toNat ≤ loop.maximum) (holds : profile.Holds native) :
    letI : OtherOpcodeHandlers := X86CountedWordProgram.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after : X86CountedWordLoop.Location → Word, ∃ machine, X86CountedWordProgram.SourceRun loop body values after ∧
      (X86FuelPrefix.fetches (X86CountedWordProgram.instructionCount loop body values)).run native = .ok () machine ∧
      X86StateFrame.Frame registers ∅ native machine ∧
      Nonempty (At loop body (base + 18) (exitOffset body) after machine) ∧
      after (.inr loop.bound) = values (.inr loop.bound) ∧ after (.inr loop.index) = values (.inr loop.bound) ∧
      codeLoaded machine base (X86CountedWordProgram.code loop body context.displacement) ∧ profile.Holds machine := by
  let : OtherOpcodeHandlers := X86CountedWordProgram.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,machine,source,run,frame,atExit,bound,index,loaded,_prefixes⟩ :=
    X86CountedWordProgram.completes other extra vector loop body base context values native input bounded
  exact ⟨after,machine,source,run,frame,atExit,bound,index,loaded,
    program_run other extra vector profile loop body base context values native machine input bounded holds run⟩

theorem excess_profile (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (profile : X86Readiness.Profile) (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program)
    (base : Int) (context : X86CountedWordProgram.Context loop body base)
    (values : X86CountedWordLoop.Location → Word) (native : State)
    (input : X86CountedWordProgram.At loop body base context values native)
    (excess : loop.maximum < (values (.inr loop.bound)).toNat) (holds : profile.Holds native) :
    letI : OtherOpcodeHandlers := X86CountedWordProgram.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine, (X86FuelPrefix.fetches 3).run native = .ok () machine ∧
      X86StateFrame.Frame registers ∅ native machine ∧
      lookup machine (X86CopyBlock.physical loop.index) = some (values (.inr loop.index)) ∧
      lookup machine (X86CopyBlock.physical loop.bound) = some (values (.inr loop.bound)) ∧
      machine.regs.get? .rip = some (context.rejection.signExtend 64) ∧ profile.Holds machine := by
  let : OtherOpcodeHandlers := X86CountedWordProgram.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨machine,run,frame,index,bound,rip,_loaded,_guard,_prefixes⟩ :=
    X86CountedWordProgram.excess_branch other extra vector loop body base context values native input excess
  have notBounded : ¬(values (.inr loop.bound)).toNat ≤ loop.maximum := by omega
  exact ⟨machine,run,frame,index,bound,rip,
    entry_run other extra vector profile loop body base context values native machine input holds
      (by simpa only [if_neg notBounded] using run)⟩

namespace Controls
open X86CountedWordProgram

private def add : Instruction := .binary 0 2 2 6 (by decide)
private def body : X86WordBody.Program := Prog.prim add
private def loop : Control.Loop (Fin 12) := ⟨0,4096,4114,4132,4123,4141,6,5,10⟩
private def rawBody : List Nat := [0x49,0x89,0xd6,0x4d,0x01,0xd6,0x4c,0x89,0xf2]
private def rawLoop : List Nat :=
  [0x4d,0x39,0xca,0x0f,0x83,18,0,0,0,
    0x49,0x89,0xd6,0x4d,0x01,0xd6,0x4c,0x89,0xf2,
    0x49,0x83,0xc2,1,0xe9,0xe5,0xff,0xff,0xff]
private def raw : List Nat :=
  [0x41,0xbe,10,0,0,0,0x4d,0x39,0xf1,0x0f,0x87,89,0,0,0,0x45,0x31,0xd2] ++ rawLoop

theorem body_bytes : X86CountedWordLoop.bodyBytes body = rawBody := by
  rw [X86CountedWordLoop.bodyBytes,body,X86BlockCompiler.code_prim]
  simp only [spec,bytes,add]
  rw [binaryBytes_exact]
  rfl

theorem body_steps : X86BlockCompiler.steps spec body = 3 := rfl
theorem latch_offset : X86CountedWordLoop.latchOffset body = 18 := by rw [X86CountedWordLoop.latchOffset,body_bytes]; rfl
theorem exit_offset : X86CountedWordLoop.exitOffset body = 27 := by rw [X86CountedWordLoop.exitOffset,body_bytes]; rfl

theorem loop_bytes : X86CountedWordLoop.code loop body = rawLoop := by
  unfold X86CountedWordLoop.code X86CountedWordLoop.headDisplacement X86CountedWordLoop.backDisplacement
  rw [body_bytes,exit_offset]
  rfl

theorem compiled_bytes : X86CountedWordProgram.code loop body (89#32) = raw := by
  unfold X86CountedWordProgram.code X86CountedWordProgram.entryBytes
  rw [loop_bytes]
  rfl

private def context : X86CountedWordProgram.Context loop body 4096 where
  lower := by decide
  inner := {
    lower := by decide
    upper := by rw [exit_offset]; decide
    fits := by rw [exit_offset]; decide
    checked := by decide
    indexUnlocked := by decide
    indexReadOnly := by decide
    boundReadOnly := by decide
    header := by rfl
    bodyPoint := by rfl
    latch := by rw [latch_offset]; rfl
    exit := by rw [exit_offset]; rfl }
  entry := by rfl
  displacement := 89#32
  rejection := 4200#48
  jump := by decide

private def values (bound : Word) : X86CountedWordLoop.Location → Word
  | .inl name => if name = 0 then 4096 else 777
  | .inr register => if register = 0 then 8192 else if register = 5 then bound
      else if register = 6 then 0xfedcba9876543210 else if register = 2 then 5 else 0

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 45).map (fun offset => (4096 + offset,BitVec.ofNat 8 ((raw[offset]?).getD 0))) ++ [(8192,42#8)]
private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide
private theorem address_point : ∀ offset : Fin 45,
    ((address 4096 offset.val).signExtend 52).toNat = 4096 + offset.val := by decide

private def profile : X86Readiness.Profile where
  controls := Vector.ofFn (fun index => if index.val = 0 then (0x40000#64) else 0)
  visible := Vector.ofFn (fun index => if index.val = 1 then (3#16) else 0)
  ac := 1#1

private noncomputable def native (bound : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .rdi (values bound (.inr 0))
  let registers := registers.insert .rsi (values bound (.inr 1))
  let registers := registers.insert .rdx (values bound (.inr 2))
  let registers := registers.insert .rcx (values bound (.inr 3))
  let registers := registers.insert .r8 (values bound (.inr 4))
  let registers := registers.insert .r9 (values bound (.inr 5))
  let registers := registers.insert .r10 (values bound (.inr 6))
  let registers := registers.insert .r11 (values bound (.inr 7))
  let registers := registers.insert .rax (values bound (.inr 8))
  let registers := registers.insert .rbx (values bound (.inr 9))
  let registers := registers.insert .r12 (values bound (.inr 10))
  let registers := registers.insert .r13 (values bound (.inr 11))
  let registers := registers.insert .r14 (0xdeadbeefbadcaffe#64)
  let registers := registers.insert .rsp (16384#64)
  let registers := registers.insert .ctrs profile.controls
  let registers := registers.insert .seg_visibles profile.visible
  let registers := registers.insert .rflags (0x40246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList cells,(),0,#[]⟩

private def origin (bound : Word) : X86LegacyFetch.Basis (native bound) where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [native,Std.ExtDHashMap.get?_insert]
  fault := by simp [native,Std.ExtDHashMap.get?_insert]
  msrs := by simp [native,Std.ExtDHashMap.get?_insert]
  segments := by simp [native,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [native,Std.ExtDHashMap.get?_insert]
  rip := by simp [native,Std.ExtDHashMap.get?_insert]

private def input (bound : Word) : X86CountedWordProgram.At loop body 4096 context (values bound) (native bound) where
  origin := origin bound
  placed := by rfl
  represented := by
    refine ⟨?_,?_⟩
    · intro register _
      fin_cases register <;>
        simp [lookup,placed,Registers.canonical,Registers.Placement.resolve,Registers.logicalSlot,
          key,native,Std.ExtDHashMap.get?_insert,X86WordBody.data] <;> rfl
    · simp [native,values,loop,Std.ExtDHashMap.get?_insert]
  ready := ⟨0x40246#32,by simp [native,Std.ExtDHashMap.get?_insert],by simp [native]⟩
  loaded := by
    change codeLoaded (native bound) 4096 (X86CountedWordProgram.code loop body (89#32))
    rw [compiled_bytes]
    intro offset byte present
    have within : offset < 45 := (List.getElem?_eq_some_iff.mp present).1
    have member : (4096 + offset,BitVec.ofNat 8 byte) ∈ cells := by
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨offset,List.mem_range.mpr within,by simp only [present,Option.getD_some]⟩
    rw [address_point ⟨offset,within⟩]
    exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member
private theorem native_profile (bound : Word) : profile.Holds (native bound) := by
  refine ⟨?_,?_,0x40246#32,?_,?_⟩
  · simp [native,Std.ExtDHashMap.get?_insert]
  · simp [native,Std.ExtDHashMap.get?_insert]
  · simp [native,Std.ExtDHashMap.get?_insert]
  · decide

theorem counted_profile (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (bound : Fin 11) :
    letI : OtherOpcodeHandlers := X86CountedWordProgram.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after : X86CountedWordLoop.Location → Word, ∃ machine,
      X86CountedWordProgram.SourceRun loop body (values (BitVec.ofNat 64 bound.val)) after ∧
      (X86FuelPrefix.fetches (bound.val * 7 + 6)).run (native (BitVec.ofNat 64 bound.val)) = .ok () machine ∧
      lookup machine 10 = some (BitVec.ofNat 64 bound.val) ∧ lookup machine 9 = some (BitVec.ofNat 64 bound.val) ∧
      machine.regs.get? .rip = some (4141#64) ∧ profile.Holds machine ∧
      (machine.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (1#1) ∧
      ∀ address, machine.mem.get? address = (native (BitVec.ofNat 64 bound.val)).mem.get? address := by
  let : OtherOpcodeHandlers := X86CountedWordProgram.handlers other extra
  let : VectorOpcodeHandlers := vector
  have small : bound.val < 2 ^ 64 := by have := bound.isLt; omega
  have bounded : ((values (BitVec.ofNat 64 bound.val)) (.inr loop.bound)).toNat ≤ loop.maximum := by
    change (BitVec.ofNat 64 bound.val).toNat ≤ 10
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    have := bound.isLt
    omega
  obtain ⟨after,machine,source,run,frame,⟨atExit⟩,boundSame,indexSame,_loaded,holds⟩ :=
    completes_profile other extra vector profile loop body 4096 context _ _
      (input (BitVec.ofNat 64 bound.val)) bounded (native_profile _)
  have cost : X86CountedWordProgram.instructionCount loop body (values (BitVec.ofNat 64 bound.val)) = bound.val * 7 + 6 := by
    change (BitVec.ofNat 64 bound.val).toNat * (X86BlockCompiler.steps spec body + 4) + 6 = _
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,body_steps]
  rw [cost] at run
  have indexRead := X86CountedWordLoop.physical_known loop.index after machine atExit.represented.1
  rw [indexSame] at indexRead
  have boundRead := X86CountedWordLoop.physical_known loop.bound after machine atExit.represented.1
  rw [boundSame] at boundRead
  have rip := atExit.represented.2
  rw [X86CountedWordLoop.control_at loop body (4096 + 18) _ after machine atExit,exit_offset] at rip
  refine ⟨after,machine,source,run,indexRead,boundRead,rip,holds,?_,?_⟩
  · obtain ⟨_controls,_visible,flags,flagsKnown,ac⟩ := holds
    rw [flagsKnown]
    simpa only [Option.map_some,profile] using congrArg some ac
  · intro address
    exact frame.memory address (by simp)

theorem excessive_bound_profile (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86CountedWordProgram.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine, (X86FuelPrefix.fetches 3).run (native (11#64)) = .ok () machine ∧
      lookup machine 10 = some (0xfedcba9876543210#64) ∧ lookup machine 9 = some (11#64) ∧
      machine.regs.get? .rip = some (4200#64) ∧ profile.Holds machine := by
  obtain ⟨machine,run,_frame,index,bound,rip,holds⟩ := excess_profile other extra vector profile loop body 4096 context
    (values (11#64)) (native (11#64)) (input (11#64)) (by decide) (native_profile _)
  exact ⟨machine,run,index,bound,rip,holds⟩

theorem cleared_ac_rejected (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (bound : Fin 11) :
    letI : OtherOpcodeHandlers := X86CountedWordProgram.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ initial, ∀ reached, (reached.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (0#1) →
      (X86FuelPrefix.fetches (bound.val * 7 + 6)).run initial ≠ .ok () reached := by
  let : OtherOpcodeHandlers := X86CountedWordProgram.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨_values,proved,_source,run,_index,_bound,_rip,_holds,ac,_memory⟩ := counted_profile other extra vector bound
  refine ⟨native (BitVec.ofNat 64 bound.val),?_⟩
  intro reached cleared observed
  have same := X86FuelPrefix.fetches_deterministic _ _ proved reached run observed
  rw [same,cleared] at ac
  exact (by decide : (some (0#1) : Option (BitVec 1)) ≠ some (1#1)) ac

private noncomputable def wrongCap : State := { native 0 with mem := (native 0).mem.insert 4098 (11#8) }
theorem changed_cap_refused : ¬codeLoaded wrongCap 4096 raw := by
  intro loaded
  have wrong := loaded 2 10 (by rfl)
  simp [wrongCap,address] at wrong

private noncomputable def wrongBody : State := { native 3 with mem := (native 3).mem.insert 4127 (0x29#8) }
theorem changed_body_refused : ¬codeLoaded wrongBody 4096 raw := by
  intro loaded
  have wrong := loaded 31 0x01 (by rfl)
  simp [wrongBody,address] at wrong

end Controls

end Mettapedia.Machines.TIsa.X86LoopReadiness
