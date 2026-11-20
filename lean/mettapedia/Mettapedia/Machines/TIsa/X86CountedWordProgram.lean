import Mettapedia.Machines.TIsa.X86LoopEntry
import Mettapedia.Machines.TIsa.X86CountedWordLoop

/-!
# Counted word programs from cap validation through loop exit

The eighteen-byte native entry composes with the existing captured word-body
library and header/body/latch loop proof. The counter may contain arbitrary
old bits at entry. An admitted bound initializes it to zero, executes the
exact source entry/header/body/latch recipe schedule and reaches the exit
with index equal to the retained bound. The exact native instruction count
is bound * (body_steps + 4) + 6. Every fetched prefix has the same declared
register/byte frame; the complete code image is preserved.

An excessive bound branches to the supplied rejection continuation in three
instructions, retaining the old counter and bound; its source entry guard
cannot hold. Actual status handling at that continuation is not assumed.
Reflection and source-postcondition transfer reuse native determinism and
the existing source GSLT/resource semantics.

Controls install a forty-five-byte index-reading ADD loop with a dirty old
counter. They cover all bounds zero through ten, an excessive bound, changed
cap/body bytes and an unsafe controller write. These theorems cover the word
body profile. Memory and other body families, FUND, early exits/returns,
public ABI, actual admission/hosting, emitter/frontend correspondence and
complete named consumers remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86CountedWordProgram
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86WordLibrary
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Location := X86WordBody.Location

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86CountedWordLoop.handlers (X86FrameStore.linkedHandlers other) extra

theorem entry_handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86LoopEntry.handlers (X86LoopLatch.handlers (X86FrameStore.linkedHandlers other)) extra = handlers other extra := by
  rfl

theorem physical_placement : ∀ register : Fin 12,
    X86CopyBlock.physical register = placed (Registers.canonical .x86_64)
      (Registers.canonical_admitted .x86_64) (Registers.logicalSlot register) := by decide

theorem physical_injective : Function.Injective X86CopyBlock.physical := by decide
theorem physical_not_scratch : ∀ register : Fin 12, X86CopyBlock.physical register ≠ 14 := by decide
theorem physical_not_flags : ∀ register : Fin 12, key (X86CopyBlock.physical register) ≠ .rflags := by decide
theorem physical_not_pointer : ∀ register : Fin 12, key (X86CopyBlock.physical register) ≠ .rip := by decide

theorem entry_register_outside (index register : Fin 12) (different : register ≠ index) :
    key (X86CopyBlock.physical register) ∉ X86LoopEntry.writes (X86CopyBlock.physical index) := by
  simp only [X86LoopEntry.writes,Finset.mem_insert,Finset.mem_singleton]
  rintro (same | same | same | same)
  · exact different (physical_injective (key_injective same))
  · exact physical_not_scratch register (key_injective same)
  · exact physical_not_flags register same
  · exact physical_not_pointer register same

theorem entry_writes (index : Fin 12) (unlocked : index ≠ 0) :
    X86LoopEntry.writes (X86CopyBlock.physical index) ⊆ registers := by
  intro register member
  simp only [X86LoopEntry.writes,Finset.mem_insert,Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨index,Finset.mem_erase.mpr ⟨unlocked,Finset.mem_univ _⟩,rfl⟩
  · simp [registers,key]
  · simp [registers]
  · simp [registers,X86CopyBlock.registerWrites]

def cap (loop : Control.Loop (Fin 12)) : BitVec 32 := BitVec.ofNat 32 loop.maximum

theorem cap_exact (loop : Control.Loop (Fin 12)) (checked : loop.check = true) : (cap loop).toNat = loop.maximum := by
  have small : loop.maximum < 2 ^ 32 := (of_decide_eq_true checked).2.2
  exact Nat.mod_eq_of_lt small

noncomputable def entryBytes (loop : Control.Loop (Fin 12)) (displacement : BitVec 32) : List Nat :=
  X86LoopEntry.code (X86CopyBlock.physical loop.index) (X86CopyBlock.physical loop.bound) (cap loop) displacement

noncomputable def code (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (displacement : BitVec 32) : List Nat :=
  entryBytes loop displacement ++ X86CountedWordLoop.code loop body

theorem entry_length (loop : Control.Loop (Fin 12)) (displacement : BitVec 32) : (entryBytes loop displacement).length = 18 :=
  X86LoopEntry.code_length _ _ _ _

theorem code_length (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (displacement : BitVec 32) :
    (code loop body displacement).length = 18 + X86CountedWordLoop.exitOffset body := by
  simp only [code,List.length_append,entry_length,X86CountedWordLoop.code_length]

structure Context (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) where
  lower : -(2 ^ 47 : Int) ≤ base
  inner : X86CountedWordLoop.Context loop body (base + 18)
  entry : loop.entryPoint = (address base 0).signExtend 64
  displacement : BitVec 32
  rejection : BitVec 48
  jump : rejection.toInt = base + 15 + displacement.toInt

structure At (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int)
    (context : Context loop body base) (values : Location → Word) (native : State) where
  origin : X86LegacyFetch.Basis native
  placed : origin.address.toInt = base
  represented : X86WordBody.Represents loop.activation values native
  ready : ready native
  loaded : codeLoaded native base (code loop body context.displacement)

theorem entry_scope (loop : Control.Loop (Fin 12)) : loop.entry.support ⊆ X86WordBody.scope loop.activation := by
  intro location member
  cases location with
  | inl activation =>
    have same : activation = loop.activation := by
      simpa [CellEffects.Recipe.support,CellEffects.Recipe.writes,Control.Loop.entry] using member
    subst activation
    simp [X86WordBody.scope]
  | inr register => simp [X86WordBody.scope]

theorem entry_byte (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (displacement : BitVec 32) (index byte : Nat)
    (present : (entryBytes loop displacement)[index]? = some byte) : (code loop body displacement)[index]? = some byte := by
  rw [code,List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

theorem loop_byte (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (displacement : BitVec 32) (index byte : Nat)
    (present : (X86CountedWordLoop.code loop body)[index]? = some byte) : (code loop body displacement)[18 + index]? = some byte := by
  rw [code,List.getElem?_append_right (by rw [entry_length]; omega),entry_length,Nat.add_sub_cancel_left]
  exact present

noncomputable def entryInput (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int)
    (context : Context loop body base) (values : Location → Word) (native : State)
    (input : At loop body base context values native) :
    X86LoopEntry.Inputs native (X86CopyBlock.physical loop.index) (X86CopyBlock.physical loop.bound) := {
  input.origin with
  indexValue := values (.inr loop.index)
  boundValue := values (.inr loop.bound)
  cap := cap loop
  flags := Classical.choose input.ready
  indexKnown := X86CountedWordLoop.physical_known loop.index values native input.represented.1
  boundKnown := X86CountedWordLoop.physical_known loop.bound values native input.represented.1
  flagsKnown := (Classical.choose_spec input.ready).1
  quiet := (Classical.choose_spec input.ready).2
  separateIndex := physical_not_scratch loop.index
  separateBound := physical_not_scratch loop.bound
  distinct := fun same => (of_decide_eq_true context.inner.checked).1 (physical_injective same)
  upper := by
    rw [input.placed]
    have upper := context.inner.upper
    have nonnegative := Nat.zero_le (X86CountedWordLoop.exitOffset body)
    omega
  displacement := context.displacement
  target := context.rejection
  jump := by rw [input.placed]; exact context.jump
  loaded := by
    rw [input.placed]
    exact fun index byte present => input.loaded index byte (entry_byte loop body context.displacement index byte present) }

theorem entry_data (loop : Control.Loop (Fin 12)) (values : Location → Word) (native machine : State)
    (known : X86CopyBlock.RegistersRepresented (X86WordBody.data values) native)
    (frame : RegisterFrame (X86LoopEntry.writes (X86CopyBlock.physical loop.index)) native machine)
    (indexKnown : lookup machine (X86CopyBlock.physical loop.index) = some (0#64)) :
    X86CopyBlock.RegistersRepresented (X86WordBody.data (loop.entryValues values)) machine := by
  intro register _
  rw [←physical_placement register]
  by_cases same : register = loop.index
  · subst register
    simpa [X86WordBody.data,Control.Loop.entryValues] using indexKnown
  · rw [frame.lookup _ (entry_register_outside loop.index register same)]
    simpa [X86WordBody.data,Control.Loop.entryValues,same] using X86CountedWordLoop.physical_known register values native known

theorem entry_bound (loop : Control.Loop (Fin 12)) (values : Location → Word) (checked : loop.check = true) :
    loop.entryValues values (.inr loop.bound) = values (.inr loop.bound) := by
  have different := Ne.symm (of_decide_eq_true checked).1
  simp [Control.Loop.entryValues,different]

theorem entry_rank (loop : Control.Loop (Fin 12)) (values : Location → Word) (checked : loop.check = true) :
    loop.rank (loop.entryValues values) = (values (.inr loop.bound)).toNat := by
  rw [Control.Loop.rank,entry_bound loop values checked]
  simp [Control.Loop.entryValues]

theorem entry_valid (loop : Control.Loop (Fin 12)) (values : Location → Word) (checked : loop.check = true)
    (bounded : (values (.inr loop.bound)).toNat ≤ loop.maximum) :
    X86CountedWordLoop.Valid loop (loop.entryValues values) := by
  constructor
  · simp [Control.Loop.entryValues]
  · rw [entry_bound loop values checked]
    exact bounded

theorem entry_point (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int)
    (context : Context loop body base) (values : Location → Word) (native : State)
    (input : At loop body base context values native) : values (.inl loop.activation) = loop.entryPoint := by
  have same := Option.some.inj (input.represented.2.symm.trans input.origin.rip)
  have origin : input.origin.address = address base 0 := by
    have inverse : BitVec.ofInt 48 input.origin.address.toInt = input.origin.address := BitVec.ofInt_toInt
    rw [input.placed] at inverse
    simpa only [address,Int.natCast_zero,Int.add_zero] using inverse.symm
  rw [origin,←context.entry] at same
  exact same

theorem entry_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) (context : Context loop body base)
    (values : Location → Word) (native : State) (input : At loop body base context values native)
    (bounded : (values (.inr loop.bound)).toNat ≤ loop.maximum) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine, ∃ invocation : CellEffects.Invocation loop.entry,
      CellEffects.system.Enables (Cells.encode (X86WordBody.scope loop.activation) values) invocation ∧
      CellEffects.system.fire (Cells.encode (X86WordBody.scope loop.activation) values) invocation =
        Cells.encode (X86WordBody.scope loop.activation) (loop.entryValues values) ∧
      (X86FuelPrefix.fetches 4).run native = .ok () machine ∧ X86StateFrame.Frame registers ∅ native machine ∧
      Nonempty (X86CountedWordLoop.At loop body (base + 18) 0 (loop.entryValues values) machine) ∧
      ∀ count ≤ 4, ∀ reached, (X86FuelPrefix.fetches count).run native = .ok () reached →
        X86StateFrame.Frame registers ∅ native reached := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let prepared := entryInput loop body base context values native input
  have admitted : prepared.boundValue.toNat ≤ prepared.cap.toNat := by
    change (values (.inr loop.bound)).toNat ≤ (cap loop).toNat
    rw [cap_exact loop context.inner.checked]
    exact bounded
  obtain ⟨machine,flags,executed,rawFrame,indexKnown,_,flagsKnown,rip⟩ :=
    X86LoopEntry.executes (X86LoopLatch.handlers (X86FrameStore.linkedHandlers other)) extra vector native
      (X86CopyBlock.physical loop.index) (X86CopyBlock.physical loop.bound) prepared
  rw [if_pos admitted] at executed indexKnown rip
  have frame : X86StateFrame.Frame registers ∅ native machine :=
    (X86StateFrame.registerOnly rawFrame).mono (entry_writes loop.index context.inner.indexUnlocked) (by simp)
  have headerAddress : X86LoopEntry.position prepared 18 = address (base + 18) 0 := by
    change address input.origin.address.toInt 18 = address (base + 18) 0
    rw [input.placed]
    simp only [address,Int.natCast_zero,Int.add_zero,Nat.cast_ofNat]
  rw [headerAddress] at rip
  have registersKnown := entry_data loop values native machine input.represented.1 rawFrame indexKnown
  have represented : X86WordBody.Represents loop.activation (loop.entryValues values) machine := by
    refine ⟨registersKnown,?_⟩
    simpa [Control.Loop.entryValues,context.inner.header] using rip
  have ready : X86WordLibrary.ready machine :=
    ⟨flags,flagsKnown,(frame.registers .log_register_writes (by decide)).trans (Classical.choose_spec input.ready).2⟩
  have pointExact : (address (base + 18) 0).toInt = base + 18 := by
    simpa only [Int.natCast_zero,Int.add_zero] using
      X86CountedWordLoop.address_exact loop body (base + 18) context.inner 0 (by omega)
  let headerInput : X86CountedWordLoop.At loop body (base + 18) 0 (loop.entryValues values) machine := {
    origin := X86StateFrame.basisAt native machine input.origin frame data_only (address (base + 18) 0)
      (by rw [pointExact]; have high := context.inner.upper; omega) rip
    placed := by
      change (address (base + 18) 0).toInt = (base + 18) + 0
      simpa only [Int.natCast_zero,Int.add_zero] using pointExact
    represented := represented
    ready := ready
    loaded := X86Conditional.loaded_slice machine base (code loop body context.displacement) _ 18
      (frame.codeLoaded base _ input.loaded (by intros; simp)) (loop_byte loop body context.displacement)
    valid := entry_valid loop values context.inner.checked bounded }
  obtain ⟨invocation,enabled,fired⟩ := loop.entry_realized (X86WordBody.scope loop.activation) values (entry_scope loop)
    context.inner.checked (entry_point loop body base context values native input) bounded
  refine ⟨machine,invocation,enabled,fired,executed,frame,⟨headerInput⟩,?_⟩
  intro count within reached run
  obtain ⟨proved,actual,framed⟩ := X86LoopEntry.prefix_frame
    (X86LoopLatch.handlers (X86FrameStore.linkedHandlers other)) extra vector native
    (X86CopyBlock.physical loop.index) (X86CopyBlock.physical loop.bound) prepared count
    (by simpa only [if_pos admitted] using within)
  have same := X86FuelPrefix.fetches_deterministic count native proved reached actual run
  subst reached
  exact (X86StateFrame.registerOnly framed).mono (entry_writes loop.index context.inner.indexUnlocked) (by simp)

def SourceRun (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (before after : Location → Word) : Prop :=
  ∃ entries : List (CellEffects.system (Key := Location)).Entry,
    CellEffects.system.Fires entries (Cells.encode (X86WordBody.scope loop.activation) before)
      (Cells.encode (X86WordBody.scope loop.activation) after) ∧
    entries.map Sigma.fst = loop.entry :: X86CountedWordLoop.sourceSites loop body (before (.inr loop.bound)).toNat

noncomputable def instructionCount (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (values : Location → Word) : Nat :=
  (values (.inr loop.bound)).toNat * (X86BlockCompiler.steps spec body + 4) + 6

theorem completes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) (context : Context loop body base)
    (values : Location → Word) (native : State) (input : At loop body base context values native)
    (bounded : (values (.inr loop.bound)).toNat ≤ loop.maximum) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after : Location → Word, ∃ machine, SourceRun loop body values after ∧
      (X86FuelPrefix.fetches (instructionCount loop body values)).run native = .ok () machine ∧
      X86StateFrame.Frame registers ∅ native machine ∧
      Nonempty (X86CountedWordLoop.At loop body (base + 18) (X86CountedWordLoop.exitOffset body) after machine) ∧
      after (.inr loop.bound) = values (.inr loop.bound) ∧ after (.inr loop.index) = values (.inr loop.bound) ∧
      codeLoaded machine base (code loop body context.displacement) ∧
      ∀ count ≤ instructionCount loop body values, ∀ reached,
        (X86FuelPrefix.fetches count).run native = .ok () reached → X86StateFrame.Frame registers ∅ native reached := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle,invocation,enabled,fired,first,firstFrame,⟨atHeader⟩,firstPrefixes⟩ :=
    entry_step other extra vector loop body base context values native input bounded
  obtain ⟨after,entries,machine,source,sites,last,lastFrame,atExit,boundSame,indexSame,lastPrefixes⟩ :=
    X86CountedWordLoop.completes (X86FrameStore.linkedHandlers other) extra vector loop body (base + 18) context.inner
      (loop.entryValues values) middle atHeader
  have entryFires : CellEffects.system.Fires [⟨loop.entry,invocation⟩]
      (Cells.encode (X86WordBody.scope loop.activation) values)
      (Cells.encode (X86WordBody.scope loop.activation) (loop.entryValues values)) := ⟨enabled,fired.symm⟩
  have allFires := X86WordBody.fires_append [⟨loop.entry,invocation⟩] entries
    (Cells.encode (X86WordBody.scope loop.activation) values)
    (Cells.encode (X86WordBody.scope loop.activation) (loop.entryValues values))
    (Cells.encode (X86WordBody.scope loop.activation) after) entryFires source
  have allRun := X86FuelPrefix.fetches_then 4
    (loop.rank (loop.entryValues values) * (X86BlockCompiler.steps spec body + 4) + 2) native middle machine first last
  have prefixes := X86CountedWordLoop.prefixes_append 4
    (loop.rank (loop.entryValues values) * (X86BlockCompiler.steps spec body + 4) + 2)
    native middle first firstFrame firstPrefixes lastPrefixes
  have cost : 4 + (loop.rank (loop.entryValues values) * (X86BlockCompiler.steps spec body + 4) + 2) =
      instructionCount loop body values := by
    rw [entry_rank loop values context.inner.checked]
    dsimp only [instructionCount]
    omega
  rw [cost] at allRun prefixes
  have allFrame : X86StateFrame.Frame registers ∅ native machine :=
    (firstFrame.trans lastFrame).mono (by simp) (by simp)
  refine ⟨after,machine,?_,allRun,allFrame,atExit,
    boundSame.trans (entry_bound loop values context.inner.checked),
    indexSame.trans (entry_bound loop values context.inner.checked),
    allFrame.codeLoaded base _ input.loaded (by intros; simp),prefixes⟩
  refine ⟨[⟨loop.entry,invocation⟩] ++ entries,allFires,?_⟩
  rw [List.map_append,sites,entry_rank loop values context.inner.checked]
  rfl

theorem reflects (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) (context : Context loop body base)
    (values : Location → Word) (native machine : State) (input : At loop body base context values native)
    (bounded : (values (.inr loop.bound)).toNat ≤ loop.maximum) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches (instructionCount loop body values)).run native = .ok () machine →
    ∃ after : Location → Word, SourceRun loop body values after ∧ X86StateFrame.Frame registers ∅ native machine ∧
      Nonempty (X86CountedWordLoop.At loop body (base + 18) (X86CountedWordLoop.exitOffset body) after machine) ∧
      after (.inr loop.bound) = values (.inr loop.bound) ∧ after (.inr loop.index) = values (.inr loop.bound) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  intro run
  obtain ⟨after,proved,source,executed,frame,atExit,bound,index,_,_⟩ :=
    completes other extra vector loop body base context values native input bounded
  have same := X86FuelPrefix.fetches_deterministic _ native proved machine executed run
  subst machine
  exact ⟨after,source,frame,atExit,bound,index⟩

theorem transfer_postcondition (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) (context : Context loop body base)
    (values : Location → Word) (native : State) (input : At loop body base context values native)
    (bounded : (values (.inr loop.bound)).toNat ≤ loop.maximum)
    (post : (Location → Word) → Prop) (source : ∀ after, SourceRun loop body values after → post after) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after : Location → Word, ∃ machine, SourceRun loop body values after ∧ post after ∧
      (X86FuelPrefix.fetches (instructionCount loop body values)).run native = .ok () machine ∧
      X86StateFrame.Frame registers ∅ native machine ∧
      Nonempty (X86CountedWordLoop.At loop body (base + 18) (X86CountedWordLoop.exitOffset body) after machine) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,machine,realized,run,frame,atExit,_,_,_,_⟩ := completes other extra vector loop body base context values native input bounded
  exact ⟨after,machine,realized,source after realized,run,frame,atExit⟩

theorem excess_branch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) (context : Context loop body base)
    (values : Location → Word) (native : State) (input : At loop body base context values native)
    (excess : loop.maximum < (values (.inr loop.bound)).toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine, (X86FuelPrefix.fetches 3).run native = .ok () machine ∧
      X86StateFrame.Frame registers ∅ native machine ∧
      lookup machine (X86CopyBlock.physical loop.index) = some (values (.inr loop.index)) ∧
      lookup machine (X86CopyBlock.physical loop.bound) = some (values (.inr loop.bound)) ∧
      machine.regs.get? .rip = some (context.rejection.signExtend 64) ∧
      codeLoaded machine base (code loop body context.displacement) ∧
      (∀ after, loop.entry.guard (loop.entry.inputs.map values) (loop.entry.outputs.map after) ≠ true) ∧
      ∀ count ≤ 3, ∀ reached, (X86FuelPrefix.fetches count).run native = .ok () reached →
        X86StateFrame.Frame registers ∅ native reached := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let prepared := entryInput loop body base context values native input
  obtain ⟨machine,run,rawFrame,indexKnown,boundKnown,rip,refused⟩ := X86LoopEntry.rejects_entry_guard
    (X86LoopLatch.handlers (X86FrameStore.linkedHandlers other)) extra vector native
    (X86CopyBlock.physical loop.index) (X86CopyBlock.physical loop.bound) prepared loop values rfl
    (cap_exact loop context.inner.checked).symm (by
      change (cap loop).toNat < (values (.inr loop.bound)).toNat
      rw [cap_exact loop context.inner.checked]
      exact excess)
  have frame : X86StateFrame.Frame registers ∅ native machine :=
    (X86StateFrame.registerOnly rawFrame).mono (entry_writes loop.index context.inner.indexUnlocked) (by simp)
  refine ⟨machine,run,frame,indexKnown,boundKnown,rip,
    frame.codeLoaded base _ input.loaded (by intros; simp),refused,?_⟩
  have notBounded : ¬prepared.boundValue.toNat ≤ prepared.cap.toNat := by
    change ¬(values (.inr loop.bound)).toNat ≤ (cap loop).toNat
    rw [cap_exact loop context.inner.checked]
    omega
  intro count within reached executed
  obtain ⟨proved,actual,framed⟩ := X86LoopEntry.prefix_frame
    (X86LoopLatch.handlers (X86FrameStore.linkedHandlers other)) extra vector native
    (X86CopyBlock.physical loop.index) (X86CopyBlock.physical loop.bound) prepared count
    (by simpa only [if_neg notBounded] using within)
  have same := X86FuelPrefix.fetches_deterministic count native proved reached actual executed
  subst reached
  exact (X86StateFrame.registerOnly framed).mono (entry_writes loop.index context.inner.indexUnlocked) (by simp)

namespace Controls

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

theorem compiled_bytes : code loop body (89#32) = raw := by
  unfold code entryBytes
  rw [loop_bytes]
  rfl

private def context : Context loop body 4096 where
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

private def values (bound : Word) : Location → Word
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
  let registers := registers.insert .rflags (0x246#32)
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

private def input (bound : Word) : At loop body 4096 context (values bound) (native bound) where
  origin := origin bound
  placed := by rfl
  represented := by
    refine ⟨?_,?_⟩
    · intro register _
      fin_cases register <;>
        simp [lookup,placed,Registers.canonical,Registers.Placement.resolve,Registers.logicalSlot,
          key,native,Std.ExtDHashMap.get?_insert,X86WordBody.data] <;> rfl
    · simp [native,values,loop,Std.ExtDHashMap.get?_insert]
  ready := ⟨0x246#32,by simp [native,Std.ExtDHashMap.get?_insert],by simp [native]⟩
  loaded := by
    change codeLoaded (native bound) 4096 (code loop body (89#32))
    rw [compiled_bytes]
    intro offset byte present
    have within : offset < 45 := (List.getElem?_eq_some_iff.mp present).1
    have member : (4096 + offset,BitVec.ofNat 8 byte) ∈ cells := by
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨offset,List.mem_range.mpr within,by simp only [present,Option.getD_some]⟩
    rw [address_point ⟨offset,within⟩]
    exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member

theorem counted_execution (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (bound : Fin 11) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after : Location → Word, ∃ machine, SourceRun loop body (values (BitVec.ofNat 64 bound.val)) after ∧
      (X86FuelPrefix.fetches (bound.val * 7 + 6)).run (native (BitVec.ofNat 64 bound.val)) = .ok () machine ∧
      lookup machine 10 = some (BitVec.ofNat 64 bound.val) ∧ lookup machine 9 = some (BitVec.ofNat 64 bound.val) ∧
      machine.regs.get? .rip = some (4141#64) ∧
      ∀ count ≤ bound.val * 7 + 6, ∀ reached,
        (X86FuelPrefix.fetches count).run (native (BitVec.ofNat 64 bound.val)) = .ok () reached →
        lookup reached 4 = lookup (native (BitVec.ofNat 64 bound.val)) 4 ∧
        lookup reached 7 = lookup (native (BitVec.ofNat 64 bound.val)) 7 ∧
        ∀ address, reached.mem.get? address = (native (BitVec.ofNat 64 bound.val)).mem.get? address := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have small : bound.val < 2 ^ 64 := by have := bound.isLt; omega
  have bounded : ((values (BitVec.ofNat 64 bound.val)) (.inr loop.bound)).toNat ≤ loop.maximum := by
    change (BitVec.ofNat 64 bound.val).toNat ≤ 10
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    have := bound.isLt
    omega
  obtain ⟨after,machine,source,run,_,⟨atExit⟩,boundSame,indexSame,_,prefixes⟩ :=
    completes other extra vector loop body 4096 context _ _ (input (BitVec.ofNat 64 bound.val)) bounded
  have cost : instructionCount loop body (values (BitVec.ofNat 64 bound.val)) = bound.val * 7 + 6 := by
    change (BitVec.ofNat 64 bound.val).toNat * (X86BlockCompiler.steps spec body + 4) + 6 = _
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,body_steps]
  rw [cost] at run prefixes
  have indexRead := X86CountedWordLoop.physical_known loop.index after machine atExit.represented.1
  rw [indexSame] at indexRead
  have boundRead := X86CountedWordLoop.physical_known loop.bound after machine atExit.represented.1
  rw [boundSame] at boundRead
  have rip := atExit.represented.2
  rw [X86CountedWordLoop.control_at loop body (4096 + 18) _ after machine atExit,exit_offset] at rip
  refine ⟨after,machine,source,run,indexRead,boundRead,rip,?_⟩
  intro count within reached executed
  have preserved := prefixes count within reached executed
  exact ⟨preserved.lookup 4 stack_readonly,preserved.lookup 7 frame_readonly,
    fun address => preserved.memory address (by simp)⟩

theorem excess_preserves_old_counter (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine, (X86FuelPrefix.fetches 3).run (native (11#64)) = .ok () machine ∧
      lookup machine 10 = some (0xfedcba9876543210#64) ∧ lookup machine 9 = some (11#64) ∧
      machine.regs.get? .rip = some (4200#64) ∧
      ∀ after, loop.entry.guard (loop.entry.inputs.map (values (11#64))) (loop.entry.outputs.map after) ≠ true := by
  obtain ⟨machine,run,_,index,bound,rip,_,refused,_⟩ := excess_branch other extra vector loop body 4096 context
    (values (11#64)) (native (11#64)) (input (11#64)) (by decide)
  exact ⟨machine,run,index,bound,rip,refused⟩

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

theorem unsafe_context_refused :
    ¬Nonempty (Context loop (Prog.prim (.binary 0 6 6 1 (by decide))) 4096) := by
  rintro ⟨bad⟩
  exact bad.inner.indexReadOnly (by decide)

example : (values (10#64)) (.inr loop.index) = (0xfedcba9876543210#64) := rfl
example : loop.entry.guard [4114,10] [4114,0] = false := by decide

end Controls
end Mettapedia.Machines.TIsa.X86CountedWordProgram

#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.entry_step
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.completes
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.reflects
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.transfer_postcondition
#print axioms Mettapedia.Machines.TIsa.X86CountedWordProgram.excess_branch
