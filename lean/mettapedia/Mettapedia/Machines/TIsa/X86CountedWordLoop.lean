import Mettapedia.Machines.TIsa.X86WordBody
import Mettapedia.Machines.TIsa.X86LoopHeader
import Mettapedia.Machines.TIsa.X86LoopLatch
import Mettapedia.Machines.TIsa.X86Conditional

/-!
# Counted word-loop compilation from an admitted header state

The code contains an unsigned CMP/JAE header, a certified word body, and an
ADD/JMP latch. Both signed displacements are derived from body byte length.
Canonical placement, signed32 bounds, source loop guards and exclusion of
controller/bound writes are explicit admission obligations.

Existing GSLT block programs supply body meaning. SourceRun is a trace of the
original resource system with the exact generated recipe schedule: each round
has its header, body data firings, continuation transfer and latch, followed
by the final header. It does not permit arbitrary source recipe choices.

The header/body/latch certificates compose for every admitted word body.
Induction on the existing source rank proves termination at the exit, final
index equal to the retained bound, exact fetched instruction count, source
trace realization and every-prefix register/byte frames. Native determinism
reflects executions of the witnessed length back to that source trace.

The concrete 27-byte loop reads its index in an aliased ADD body. Controls
cover bounds zero through ten, a changed jump and an unsafe counter write.
This theorem starts at a valid header. Native entry/cap validation, memory or
other body libraries, early exits/returns, FUND and public ABI, plus actual
frontend/profile correspondence, remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86CountedWordLoop
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open X86WordLibrary
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Location := X86WordBody.Location

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86LoopHeader.handlers (X86LoopLatch.handlers other) extra

noncomputable def bodyBytes (body : X86WordBody.Program) : List Nat := X86BlockCompiler.code spec body
noncomputable def latchOffset (body : X86WordBody.Program) : Nat := 9 + (bodyBytes body).length
noncomputable def exitOffset (body : X86WordBody.Program) : Nat := 18 + (bodyBytes body).length
noncomputable def headDisplacement (body : X86WordBody.Program) : BitVec 32 := BitVec.ofNat 32 ((bodyBytes body).length + 9)
noncomputable def backDisplacement (body : X86WordBody.Program) : BitVec 32 := BitVec.ofInt 32 (-(exitOffset body : Int))

noncomputable def code (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) : List Nat :=
  X86LoopHeader.code (X86CopyBlock.physical loop.index) (X86CopyBlock.physical loop.bound) (headDisplacement body) ++
    (bodyBytes body ++ X86LoopLatch.code (X86CopyBlock.physical loop.index) (backDisplacement body))

theorem code_length (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) :
    (code loop body).length = exitOffset body := by
  simp only [code,List.length_append,X86LoopHeader.code_length,X86LoopLatch.code_length,exitOffset]
  omega

structure Context (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) where
  lower : -(2 ^ 47 : Int) ≤ base
  upper : base + (((exitOffset body + 3 : Nat) : Int)) < (2 ^ 47 : Int)
  fits : exitOffset body < 2 ^ 31
  checked : loop.check = true
  indexUnlocked : loop.index ≠ 0
  indexReadOnly : loop.index ∉ X86WordBody.writes body
  boundReadOnly : loop.bound ∉ X86WordBody.writes body
  header : loop.headerPoint = (address base 0).signExtend 64
  bodyPoint : loop.bodyPoint = (address base 9).signExtend 64
  latch : loop.latchPoint = (address base (latchOffset body)).signExtend 64
  exit : loop.exitPoint = (address base (exitOffset body)).signExtend 64

def Valid (loop : Control.Loop (Fin 12)) (values : Location → Word) : Prop :=
  (values (.inr loop.index)).toNat ≤ (values (.inr loop.bound)).toNat ∧ (values (.inr loop.bound)).toNat ≤ loop.maximum

structure At (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int)
    (offset : Nat) (values : Location → Word) (native : State) where
  origin : X86LegacyFetch.Basis native
  placed : origin.address.toInt = base + offset
  represented : X86WordBody.Represents loop.activation values native
  ready : X86WordLibrary.ready native
  loaded : codeLoaded native base (code loop body)
  valid : Valid loop values

theorem physical_known (register : Fin 12) (values : Location → Word) (native : State)
    (known : X86CopyBlock.RegistersRepresented (X86WordBody.data values) native) :
    lookup native (X86CopyBlock.physical register) = some (values (.inr register)) := by
  have found := known register (Finset.mem_univ _)
  fin_cases register <;>
    simpa only [X86CopyBlock.physical,X86MovCapture.physical,placed,Registers.canonical,
      Registers.Placement.resolve,Registers.logicalSlot,X86WordBody.data] using found

theorem head_byte (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (index byte : Nat)
    (present : (X86LoopHeader.code (X86CopyBlock.physical loop.index) (X86CopyBlock.physical loop.bound)
      (headDisplacement body))[index]? = some byte) : (code loop body)[index]? = some byte := by
  rw [code,List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

theorem body_byte (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (index byte : Nat)
    (present : (bodyBytes body)[index]? = some byte) : (code loop body)[9 + index]? = some byte := by
  rw [code,List.getElem?_append_right (by rw [X86LoopHeader.code_length]; omega),X86LoopHeader.code_length,
    Nat.add_sub_cancel_left,List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

theorem latch_byte (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (index byte : Nat)
    (present : (X86LoopLatch.code (X86CopyBlock.physical loop.index) (backDisplacement body))[index]? = some byte) :
    (code loop body)[latchOffset body + index]? = some byte := by
  rw [code,List.getElem?_append_right (by rw [X86LoopHeader.code_length]; dsimp [latchOffset]; omega),X86LoopHeader.code_length]
  rw [show latchOffset body + index - 9 = (bodyBytes body).length + index by dsimp [latchOffset]; omega,
    List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  exact present

theorem address_exact (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int)
    (context : Context loop body base) (offset : Nat) (within : offset ≤ exitOffset body + 3) :
    (address base offset).toInt = base + offset :=
  address_toInt base context.lower context.upper offset within

theorem head_displacement_exact (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int)
    (context : Context loop body base) : (headDisplacement body).toInt = ((bodyBytes body).length + 9 : Nat) := by
  apply X86Conditional.displacement_exact
  have := context.fits
  dsimp [exitOffset] at this
  omega

theorem back_displacement_exact (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int)
    (context : Context loop body base) : (backDisplacement body).toInt = -(exitOffset body : Int) := by
  rw [backDisplacement,BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le <;> have := context.fits <;> omega

noncomputable def headInput (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int)
    (context : Context loop body base) (values : Location → Word) (native : State)
    (input : At loop body base 0 values native) :
    X86LoopHeader.Inputs native (X86CopyBlock.physical loop.index) (X86CopyBlock.physical loop.bound) := {
  input.origin with
  indexValue := values (.inr loop.index)
  boundValue := values (.inr loop.bound)
  flags := Classical.choose input.ready
  indexKnown := physical_known loop.index values native input.represented.1
  boundKnown := physical_known loop.bound values native input.represented.1
  flagsKnown := (Classical.choose_spec input.ready).1
  quiet := (Classical.choose_spec input.ready).2
  upper := by
    have extent : 18 ≤ exitOffset body := by dsimp [exitOffset]; omega
    have high := context.upper
    have location := input.placed
    omega
  displacement := headDisplacement body
  target := address base (exitOffset body)
  jump := by
    rw [address_exact loop body base context _ (by omega),head_displacement_exact loop body base context]
    have location := input.placed
    dsimp [exitOffset]
    omega
  loaded := by
    intro index byte present
    have found := input.loaded index byte (head_byte loop body index byte present)
    simpa only [input.placed,Int.natCast_zero,Int.add_zero] using found }

theorem control_at (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int)
    (offset : Nat) (values : Location → Word) (native : State) (input : At loop body base offset values native) :
    values (.inl loop.activation) = (address base offset).signExtend 64 := by
  have equal := Option.some.inj (input.represented.2.symm.trans input.origin.rip)
  have origin : input.origin.address = address base offset := by
    change input.origin.address = BitVec.ofInt 48 (base + offset)
    rw [←input.placed,BitVec.ofInt_toInt]
  exact equal.trans (congrArg (BitVec.signExtend 64) origin)

def advance (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int)
    (context : Context loop body base) (oldOffset offset : Nat) (within : offset ≤ exitOffset body)
    (before after : Location → Word) (native machine : State) (input : At loop body base oldOffset before native)
    (framed : X86StateFrame.Frame registers ∅ native machine)
    (represented : X86WordBody.Represents loop.activation after machine) (ready : X86WordLibrary.ready machine)
    (point : after (.inl loop.activation) = (address base offset).signExtend 64) (valid : Valid loop after) :
    At loop body base offset after machine := {
  origin := X86StateFrame.basisAt native machine input.origin framed data_only (address base offset)
    (by rw [address_exact loop body base context offset (by omega)]; have := context.upper; omega)
    (by rw [←point]; exact represented.2)
  placed := address_exact loop body base context offset (by omega)
  represented := represented
  ready := ready
  loaded := framed.codeLoaded base _ input.loaded (by intros; simp)
  valid := valid }

theorem header_scope (loop : Control.Loop (Fin 12)) : loop.header.support ⊆ X86WordBody.scope loop.activation := by
  intro location member
  cases location with
  | inl activation =>
    have same : activation = loop.activation := by
      simpa [CellEffects.Recipe.support,CellEffects.Recipe.writes,Control.Loop.header] using member
    subst activation
    simp [X86WordBody.scope]
  | inr register => simp [X86WordBody.scope]

theorem latch_scope (loop : Control.Loop (Fin 12)) : loop.latch.support ⊆ X86WordBody.scope loop.activation := by
  intro location member
  cases location with
  | inl activation =>
    have same : activation = loop.activation := by
      simpa [CellEffects.Recipe.support,CellEffects.Recipe.writes,Control.Loop.latch] using member
    subst activation
    simp [X86WordBody.scope]
  | inr register => simp [X86WordBody.scope]

theorem header_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) (context : Context loop body base)
    (values : Location → Word) (native : State) (input : At loop body base 0 values native) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine, ∃ invocation : CellEffects.Invocation loop.header,
      CellEffects.system.Enables (Cells.encode (X86WordBody.scope loop.activation) values) invocation ∧
      CellEffects.system.fire (Cells.encode (X86WordBody.scope loop.activation) values) invocation =
        Cells.encode (X86WordBody.scope loop.activation) (loop.headerValues values) ∧
      (X86FuelPrefix.fetches 2).run native = .ok () machine ∧ X86StateFrame.Frame registers ∅ native machine ∧
      Nonempty (At loop body base
        (if (values (.inr loop.index)).toNat < (values (.inr loop.bound)).toNat then 9 else exitOffset body)
        (loop.headerValues values) machine) ∧
      ∀ count ≤ 2, ∀ reached, (X86FuelPrefix.fetches count).run native = .ok () reached →
        X86StateFrame.Frame registers ∅ native reached := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have current : values (.inl loop.activation) = loop.headerPoint :=
    (control_at loop body base 0 values native input).trans context.header.symm
  obtain ⟨invocation,enabled,fired⟩ := loop.header_realized (X86WordBody.scope loop.activation) values
    (header_scope loop) context.checked current input.valid.1 input.valid.2
  let head := headInput loop body base context values native input
  obtain ⟨machine,flags,run,framed,_,_,flagsRead,rip⟩ :=
    X86LoopHeader.executes (X86LoopLatch.handlers other) extra vector native _ _ head
  let offset := if (values (.inr loop.index)).toNat < (values (.inr loop.bound)).toNat then 9 else exitOffset body
  have sourcePoint : loop.headerValues values (.inl loop.activation) = (address base offset).signExtend 64 := by
    by_cases less : (values (.inr loop.index)).toNat < (values (.inr loop.bound)).toNat
    · simp [Control.Loop.headerValues,Control.Loop.headerTarget,less,offset,context.bodyPoint]
    · simp [Control.Loop.headerValues,Control.Loop.headerTarget,less,offset,context.exit]
  have nativePoint : machine.regs.get? .rip = some ((address base offset).signExtend 64) := by
    change machine.regs.get? .rip = some
      ((if (values (.inr loop.bound)).toNat ≤ (values (.inr loop.index)).toNat then address base (exitOffset body)
      else X86LoopHeader.position head 9).signExtend 64) at rip
    have fallthrough : X86LoopHeader.position head 9 = address base 9 := by
      change address input.origin.address.toInt 9 = address base 9
      rw [input.placed,Int.natCast_zero,Int.add_zero]
    rw [fallthrough] at rip
    by_cases less : (values (.inr loop.index)).toNat < (values (.inr loop.bound)).toNat
    · have notAbove : ¬(values (.inr loop.bound)).toNat ≤ (values (.inr loop.index)).toNat := by omega
      simpa [offset,less,notAbove] using rip
    · have above : (values (.inr loop.bound)).toNat ≤ (values (.inr loop.index)).toNat := by omega
      simpa [offset,less,above] using rip
  have represented : X86WordBody.Represents loop.activation (loop.headerValues values) machine := by
    refine ⟨?_,?_⟩
    · intro register member
      rw [framed.lookup _ (by fin_cases register <;> decide)]
      simpa [X86WordBody.data,Control.Loop.headerValues] using input.represented.1 register member
    · rw [sourcePoint]
      exact nativePoint
  have ready : X86WordLibrary.ready machine :=
    ⟨flags,flagsRead,(framed.registers .log_register_writes (by decide)).trans (Classical.choose_spec input.ready).2⟩
  have valid : Valid loop (loop.headerValues values) := by simpa [Valid,Control.Loop.headerValues] using input.valid
  have globalFrame : X86StateFrame.Frame registers ∅ native machine :=
    (X86StateFrame.registerOnly framed).mono (by decide) (by simp)
  have offsetWithin : offset ≤ exitOffset body := by
    have extent : 18 ≤ exitOffset body := by dsimp [exitOffset]; omega
    dsimp [offset]
    split <;> omega
  refine ⟨machine,invocation,enabled,fired,run,globalFrame,
    ⟨advance loop body base context 0 offset offsetWithin values (loop.headerValues values) native machine input
      globalFrame represented ready sourcePoint valid⟩,?_⟩
  intro count within reached executed
  obtain ⟨proved,provedRun,preserved⟩ := X86LoopHeader.prefix_frame (X86LoopLatch.handlers other) extra vector native _ _ head count within
  have same := X86FuelPrefix.fetches_deterministic count native proved reached provedRun executed
  subst reached
  exact (X86StateFrame.registerOnly preserved).mono (by decide) (by simp)

theorem body_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) (context : Context loop body base)
    (values : Location → Word) (native : State) (input : At loop body base 9 values native) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after : Location → Word, ∃ entries : List (CellEffects.system (Key := Location)).Entry, ∃ machine,
      CellEffects.system.Fires entries (Cells.encode (X86WordBody.scope loop.activation) values)
        (Cells.encode (X86WordBody.scope loop.activation) after) ∧
      entries.map Sigma.fst = X86WordBody.recipes body ++
        [X86WordBody.transfer loop.activation loop.bodyPoint loop.latchPoint] ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps spec body)).run native = .ok () machine ∧
      X86StateFrame.Frame registers ∅ native machine ∧ Nonempty (At loop body base (latchOffset body) after machine) ∧
      after (.inr loop.index) = values (.inr loop.index) ∧ after (.inr loop.bound) = values (.inr loop.bound) ∧
      ∀ count ≤ X86BlockCompiler.steps spec body, ∀ reached, (X86FuelPrefix.fetches count).run native = .ok () reached →
        X86StateFrame.Frame registers ∅ native reached := by
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
  let post : Unit → World → Prop := fun _ world => ∃ data : Fin 12 → Word,
    world = Cells.encode Finset.univ data ∧ ∀ register ∉ X86WordBody.writes body, data register = values (.inr register)
  have wp : body.wp action post (Cells.encode Finset.univ (X86WordBody.data values)) :=
    ⟨X86WordBody.all_safe body _,fun reply following run => by cases reply; exact X86WordBody.source_frame body _ following run⟩
  have current : values (.inl loop.activation) = bodyInput.origin.address.signExtend 64 :=
    Option.some.inj (input.represented.2.symm.trans input.origin.rip)
  obtain ⟨after,entries,machine,fires,sites,_,run,framed,represented,ready,point,_,preserved,prefixes⟩ :=
    X86WordBody.execute (handlers other extra) vector loop.activation (base + latchOffset body) body values native bodyInput current post wp
  have indexSame := preserved loop.index context.indexReadOnly
  have boundSame := preserved loop.bound context.boundReadOnly
  have valid : Valid loop after := by
    change (after (.inr loop.index)).toNat ≤ (after (.inr loop.bound)).toNat ∧ _
    rw [indexSame,boundSame]
    exact input.valid
  have placedPoint : after (.inl loop.activation) = (address base (latchOffset body)).signExtend 64 := point
  have within : latchOffset body ≤ exitOffset body := by dsimp [latchOffset,exitOffset]; omega
  have sourceStart : bodyInput.origin.address.signExtend 64 = loop.bodyPoint := by
    rw [context.bodyPoint]
    apply congrArg (BitVec.signExtend 64)
    change input.origin.address = BitVec.ofInt 48 (base + 9)
    have actual : input.origin.address.toInt = base + 9 := by simpa using input.placed
    rw [←actual,BitVec.ofInt_toInt]
  have sourceStop : (BitVec.ofInt 48 (base + latchOffset body)).signExtend 64 = loop.latchPoint := context.latch.symm
  have sourceSites : entries.map Sigma.fst = X86WordBody.recipes body ++
      [X86WordBody.transfer loop.activation loop.bodyPoint loop.latchPoint] := by
    simpa only [sourceStart,sourceStop] using sites
  exact ⟨after,entries,machine,fires,sourceSites,run,framed,
    ⟨advance loop body base context 9 (latchOffset body) within values after native machine input framed represented ready placedPoint valid⟩,
    indexSame,boundSame,prefixes⟩

theorem increment_writes (loop : Control.Loop (Fin 12)) (unlocked : loop.index ≠ 0) :
    X86RegisterIncrement.writes (X86CopyBlock.physical loop.index) ⊆ registers := by
  intro register member
  simp only [X86RegisterIncrement.writes,Finset.mem_insert,Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact Finset.mem_union_left _ (X86CopyBlock.destination_written ⟨0,loop.index,unlocked⟩)
  · exact Finset.mem_union_right _ (by decide)
  · exact Finset.mem_union_left _ (by simp [X86CopyBlock.registerWrites])

theorem physical_injective : Function.Injective X86CopyBlock.physical := by decide

noncomputable def latchInput (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int)
    (context : Context loop body base) (values : Location → Word) (native : State)
    (input : At loop body base (latchOffset body) values native) : X86LoopLatch.Inputs native (X86CopyBlock.physical loop.index) := {
  input.origin with
  value := values (.inr loop.index)
  flags := Classical.choose input.ready
  valueKnown := physical_known loop.index values native input.represented.1
  flagsKnown := (Classical.choose_spec input.ready).1
  quiet := (Classical.choose_spec input.ready).2
  upper := by
    have high := context.upper
    have location := input.placed
    dsimp [latchOffset,exitOffset] at *
    omega
  displacement := backDisplacement body
  target := address base 0
  jump := by
    rw [address_exact loop body base context 0 (by omega),back_displacement_exact loop body base context]
    have location := input.placed
    dsimp [latchOffset,exitOffset] at *
    omega
  loaded := by
    rw [input.placed]
    exact X86Conditional.loaded_slice native base (code loop body) _ (latchOffset body) input.loaded (latch_byte loop body) }

theorem physical_placed (register : Fin 12) : X86CopyBlock.physical register =
    placed (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) (Registers.logicalSlot register) := by
  fin_cases register <;> rfl

theorem latch_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) (context : Context loop body base)
    (values : Location → Word) (native : State) (input : At loop body base (latchOffset body) values native)
    (less : (values (.inr loop.index)).toNat < (values (.inr loop.bound)).toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine, ∃ invocation : CellEffects.Invocation loop.latch,
      CellEffects.system.Enables (Cells.encode (X86WordBody.scope loop.activation) values) invocation ∧
      CellEffects.system.fire (Cells.encode (X86WordBody.scope loop.activation) values) invocation =
        Cells.encode (X86WordBody.scope loop.activation) (loop.latchValues values) ∧
      (X86FuelPrefix.fetches 2).run native = .ok () machine ∧ X86StateFrame.Frame registers ∅ native machine ∧
      Nonempty (At loop body base 0 (loop.latchValues values) machine) ∧
      (loop.latchValues values (.inr loop.bound)) = values (.inr loop.bound) ∧
      loop.rank (loop.latchValues values) + 1 = loop.rank values ∧
      ∀ count ≤ 2, ∀ reached, (X86FuelPrefix.fetches count).run native = .ok () reached →
        X86StateFrame.Frame registers ∅ native reached := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have current : values (.inl loop.activation) = loop.latchPoint :=
    (control_at loop body base _ values native input).trans context.latch.symm
  obtain ⟨invocation,enabled,fired,_⟩ := loop.latch_realized (X86WordBody.scope loop.activation) values
    (latch_scope loop) context.checked current less input.valid.2
  let latch := latchInput loop body base context values native input
  obtain ⟨machine,flags,run,framed,indexRead,flagsRead,rip,prefixes⟩ := X86LoopLatch.executes (handlers other extra) vector native _ latch
  have distinct : loop.index ≠ loop.bound := (of_decide_eq_true context.checked).1
  have boundSame : loop.latchValues values (.inr loop.bound) = values (.inr loop.bound) := by
    simp [Control.Loop.latchValues,Ne.symm distinct]
  have indexNext : loop.latchValues values (.inr loop.index) = values (.inr loop.index) + 1 := by simp [Control.Loop.latchValues]
  have sourcePoint : loop.latchValues values (.inl loop.activation) = (address base 0).signExtend 64 := by
    simp [Control.Loop.latchValues,context.header]
  have represented : X86WordBody.Represents loop.activation (loop.latchValues values) machine := by
    refine ⟨?_,?_⟩
    · intro register member
      rw [←physical_placed register]
      by_cases same : register = loop.index
      · subst register
        change lookup machine (X86CopyBlock.physical loop.index) = some (values (.inr loop.index) + 1) at indexRead
        simpa only [X86WordBody.data,indexNext] using indexRead
      · have different : X86CopyBlock.physical register ≠ X86CopyBlock.physical loop.index := fun equal => same (physical_injective equal)
        have kept := (framed.lookup (X86CopyBlock.physical register) (X86LoopLatch.bound_outside _ _ different)).trans
          (physical_known register values native input.represented.1)
        simpa [X86WordBody.data,Control.Loop.latchValues,same] using kept
    · rw [sourcePoint]
      exact rip
  have ready : X86WordLibrary.ready machine :=
    ⟨flags,flagsRead,((framed.mono (X86RegisterIncrement.writes_data (X86CopyBlock.physical loop.index))).registers
      .log_register_writes (by decide)).trans
      (Classical.choose_spec input.ready).2⟩
  have valid : Valid loop (loop.latchValues values) := by
    have noWrap := Control.counter_increment_no_wrap (values (.inr loop.index)) (values (.inr loop.bound)) less
    change (loop.latchValues values (.inr loop.index)).toNat ≤ (loop.latchValues values (.inr loop.bound)).toNat ∧ _
    rw [indexNext,boundSame,noWrap]
    exact ⟨by omega,input.valid.2⟩
  have rankStep := loop.latch_decreases values (loop.latchValues values)
    (loop.latchValues_guard values context.checked current less input.valid.2)
  rw [loop.latch_overwrite] at rankStep
  have globalFrame : X86StateFrame.Frame registers ∅ native machine :=
    (X86StateFrame.registerOnly framed).mono (increment_writes loop context.indexUnlocked) (by simp)
  refine ⟨machine,invocation,enabled,fired,run,globalFrame,
    ⟨advance loop body base context (latchOffset body) 0 (by omega) values (loop.latchValues values) native machine input
      globalFrame represented ready sourcePoint valid⟩,boundSame,rankStep,?_⟩
  intro count within reached executed
  exact (X86StateFrame.registerOnly (prefixes count within reached executed)).mono (increment_writes loop context.indexUnlocked) (by simp)

theorem prefixes_append [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (first second : Nat) (before middle : State)
    (firstRun : (X86FuelPrefix.fetches first).run before = .ok () middle)
    (firstFrame : X86StateFrame.Frame registers ∅ before middle)
    (one : ∀ count ≤ first, ∀ reached, (X86FuelPrefix.fetches count).run before = .ok () reached →
      X86StateFrame.Frame registers ∅ before reached)
    (two : ∀ count ≤ second, ∀ reached, (X86FuelPrefix.fetches count).run middle = .ok () reached →
      X86StateFrame.Frame registers ∅ middle reached) :
    ∀ count ≤ first + second, ∀ reached, (X86FuelPrefix.fetches count).run before = .ok () reached →
      X86StateFrame.Frame registers ∅ before reached := by
  intro count within reached run
  by_cases inside : count ≤ first
  · exact one count inside reached run
  · have divided : count = first + (count - first) := by omega
    rw [divided] at run
    obtain ⟨actual,head,tail⟩ := X86BlockCompiler.fetches_split first (count - first) before reached run
    have same := X86FuelPrefix.fetches_deterministic first before actual middle head firstRun
    subst actual
    exact (firstFrame.trans (two (count - first) (by omega) reached tail)).mono (by simp) (by simp)

def iterationSites (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) : List (CellEffects.Recipe Location) :=
  [loop.header] ++ (X86WordBody.recipes body ++ [X86WordBody.transfer loop.activation loop.bodyPoint loop.latchPoint]) ++ [loop.latch]

def sourceSites (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) : Nat → List (CellEffects.Recipe Location)
  | 0 => [loop.header]
  | count + 1 => iterationSites loop body ++ sourceSites loop body count

theorem iteration (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) (context : Context loop body base)
    (values : Location → Word) (native : State) (input : At loop body base 0 values native)
    (less : (values (.inr loop.index)).toNat < (values (.inr loop.bound)).toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after : Location → Word, ∃ entries : List (CellEffects.system (Key := Location)).Entry, ∃ machine,
      CellEffects.system.Fires entries (Cells.encode (X86WordBody.scope loop.activation) values)
        (Cells.encode (X86WordBody.scope loop.activation) after) ∧
      entries.map Sigma.fst = iterationSites loop body ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps spec body + 4)).run native = .ok () machine ∧
      X86StateFrame.Frame registers ∅ native machine ∧ Nonempty (At loop body base 0 after machine) ∧
      after (.inr loop.bound) = values (.inr loop.bound) ∧ loop.rank after + 1 = loop.rank values ∧
      ∀ count ≤ X86BlockCompiler.steps spec body + 4, ∀ reached, (X86FuelPrefix.fetches count).run native = .ok () reached →
        X86StateFrame.Frame registers ∅ native reached := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨headMachine,headInvocation,headEnabled,headFired,headRun,headFrame,⟨headAt⟩,headPrefixes⟩ :=
    header_step other extra vector loop body base context values native input
  have atBody : At loop body base 9 (loop.headerValues values) headMachine := by simpa only [if_pos less] using headAt
  obtain ⟨bodyValues,bodyEntries,bodyMachine,bodyFires,bodySiteMap,bodyRun,bodyFrame,⟨bodyAt⟩,indexSame,boundSame,bodyPrefixes⟩ :=
    body_step other extra vector loop body base context (loop.headerValues values) headMachine atBody
  have bodyIndex : bodyValues (.inr loop.index) = values (.inr loop.index) := by
    simpa [Control.Loop.headerValues] using indexSame
  have bodyBound : bodyValues (.inr loop.bound) = values (.inr loop.bound) := by
    simpa [Control.Loop.headerValues] using boundSame
  have bodyLess : (bodyValues (.inr loop.index)).toNat < (bodyValues (.inr loop.bound)).toNat := by rw [bodyIndex,bodyBound]; exact less
  obtain ⟨machine,latchInvocation,latchEnabled,latchFired,latchRun,latchFrame,atHeader,latchBound,rankStep,latchPrefixes⟩ :=
    latch_step other extra vector loop body base context bodyValues bodyMachine bodyAt bodyLess
  have headFires : CellEffects.system.Fires [⟨loop.header,headInvocation⟩]
      (Cells.encode (X86WordBody.scope loop.activation) values) (Cells.encode (X86WordBody.scope loop.activation) (loop.headerValues values)) :=
    ⟨headEnabled,headFired.symm⟩
  have latchFires : CellEffects.system.Fires [⟨loop.latch,latchInvocation⟩]
      (Cells.encode (X86WordBody.scope loop.activation) bodyValues) (Cells.encode (X86WordBody.scope loop.activation) (loop.latchValues bodyValues)) :=
    ⟨latchEnabled,latchFired.symm⟩
  have firstRun := X86FuelPrefix.fetches_then 2 (X86BlockCompiler.steps spec body) native headMachine bodyMachine headRun bodyRun
  have firstFrame : X86StateFrame.Frame registers ∅ native bodyMachine := (headFrame.trans bodyFrame).mono (by simp) (by simp)
  have firstPrefixes := prefixes_append 2 (X86BlockCompiler.steps spec body) native headMachine headRun headFrame headPrefixes bodyPrefixes
  have combined := X86FuelPrefix.fetches_then (2 + X86BlockCompiler.steps spec body) 2 native bodyMachine machine firstRun latchRun
  have combinedPrefixes := prefixes_append (2 + X86BlockCompiler.steps spec body) 2 native bodyMachine firstRun firstFrame firstPrefixes latchPrefixes
  have exactCost : 2 + X86BlockCompiler.steps spec body + 2 = X86BlockCompiler.steps spec body + 4 := by omega
  rw [exactCost] at combined combinedPrefixes
  have firstSource := X86WordBody.fires_append [⟨loop.header,headInvocation⟩] bodyEntries
    (Cells.encode (X86WordBody.scope loop.activation) values)
    (Cells.encode (X86WordBody.scope loop.activation) (loop.headerValues values))
    (Cells.encode (X86WordBody.scope loop.activation) bodyValues) headFires bodyFires
  have finalSource := X86WordBody.fires_append ([⟨loop.header,headInvocation⟩] ++ bodyEntries) [⟨loop.latch,latchInvocation⟩]
    (Cells.encode (X86WordBody.scope loop.activation) values)
    (Cells.encode (X86WordBody.scope loop.activation) bodyValues)
    (Cells.encode (X86WordBody.scope loop.activation) (loop.latchValues bodyValues)) firstSource latchFires
  refine ⟨loop.latchValues bodyValues,[⟨loop.header,headInvocation⟩] ++ bodyEntries ++ [⟨loop.latch,latchInvocation⟩],machine,
    finalSource,?_,
    combined,(firstFrame.trans latchFrame).mono (by simp) (by simp),atHeader,latchBound.trans bodyBound,?_,combinedPrefixes⟩
  · simp only [List.map_append,List.map_cons,List.map_nil,iterationSites]
    rw [bodySiteMap]
    rfl
  · simpa only [Control.Loop.rank,bodyIndex,bodyBound] using rankStep

theorem completes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) (context : Context loop body base)
    (values : Location → Word) (native : State) (input : At loop body base 0 values native) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after : Location → Word, ∃ entries : List (CellEffects.system (Key := Location)).Entry, ∃ machine,
      CellEffects.system.Fires entries (Cells.encode (X86WordBody.scope loop.activation) values)
        (Cells.encode (X86WordBody.scope loop.activation) after) ∧
      entries.map Sigma.fst = sourceSites loop body (loop.rank values) ∧
      (X86FuelPrefix.fetches (loop.rank values * (X86BlockCompiler.steps spec body + 4) + 2)).run native = .ok () machine ∧
      X86StateFrame.Frame registers ∅ native machine ∧ Nonempty (At loop body base (exitOffset body) after machine) ∧
      after (.inr loop.bound) = values (.inr loop.bound) ∧ after (.inr loop.index) = values (.inr loop.bound) ∧
      ∀ count ≤ loop.rank values * (X86BlockCompiler.steps spec body + 4) + 2, ∀ reached,
        (X86FuelPrefix.fetches count).run native = .ok () reached → X86StateFrame.Frame registers ∅ native reached := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction values using (measure loop.rank).wf.induction generalizing native with
  | h values ih =>
    by_cases less : (values (.inr loop.index)).toNat < (values (.inr loop.bound)).toNat
    · obtain ⟨middle,firstEntries,middleMachine,firstSource,firstSiteMap,firstRun,firstFrame,⟨nextInput⟩,boundSame,rankStep,firstPrefixes⟩ :=
        iteration other extra vector loop body base context values native input less
      have decreases : loop.rank middle < loop.rank values := by omega
      obtain ⟨after,lastEntries,machine,lastSource,lastSiteMap,lastRun,lastFrame,atExit,finalBound,finalIndex,lastPrefixes⟩ :=
        ih middle decreases middleMachine nextInput
      have source := X86WordBody.fires_append firstEntries lastEntries
        (Cells.encode (X86WordBody.scope loop.activation) values)
        (Cells.encode (X86WordBody.scope loop.activation) middle)
        (Cells.encode (X86WordBody.scope loop.activation) after) firstSource lastSource
      have run := X86FuelPrefix.fetches_then (X86BlockCompiler.steps spec body + 4)
        (loop.rank middle * (X86BlockCompiler.steps spec body + 4) + 2) native middleMachine machine firstRun lastRun
      have prefixes := prefixes_append (X86BlockCompiler.steps spec body + 4)
        (loop.rank middle * (X86BlockCompiler.steps spec body + 4) + 2) native middleMachine firstRun firstFrame firstPrefixes lastPrefixes
      have countEq : X86BlockCompiler.steps spec body + 4 +
          (loop.rank middle * (X86BlockCompiler.steps spec body + 4) + 2) =
          loop.rank values * (X86BlockCompiler.steps spec body + 4) + 2 := by
        rw [←rankStep,Nat.add_mul,Nat.one_mul]
        omega
      rw [countEq] at run prefixes
      refine ⟨after,firstEntries ++ lastEntries,machine,source,?_,run,(firstFrame.trans lastFrame).mono (by simp) (by simp),
        atExit,finalBound.trans boundSame,finalIndex.trans boundSame,prefixes⟩
      rw [List.map_append,firstSiteMap,lastSiteMap,←rankStep]
      rfl
    · have equalNat : (values (.inr loop.index)).toNat = (values (.inr loop.bound)).toNat := by
        have ordered := input.valid.1
        omega
      have equal : values (.inr loop.index) = values (.inr loop.bound) := BitVec.eq_of_toNat_eq equalNat
      have rankZero : loop.rank values = 0 := by simp only [Control.Loop.rank,equal,Nat.sub_self]
      obtain ⟨machine,invocation,enabled,fired,run,framed,atExit,prefixes⟩ :=
        header_step other extra vector loop body base context values native input
      rw [rankZero,Nat.zero_mul,Nat.zero_add]
      refine ⟨loop.headerValues values,[⟨loop.header,invocation⟩],machine,⟨enabled,fired.symm⟩,?_,run,framed,?_,?_,?_,prefixes⟩
      · rfl
      · simpa only [if_neg less] using atExit
      · simp [Control.Loop.headerValues]
      · simpa [Control.Loop.headerValues] using equal

def SourceRun (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (before after : Location → Word) : Prop :=
  ∃ entries : List (CellEffects.system (Key := Location)).Entry,
    CellEffects.system.Fires entries (Cells.encode (X86WordBody.scope loop.activation) before)
      (Cells.encode (X86WordBody.scope loop.activation) after) ∧ entries.map Sigma.fst = sourceSites loop body (loop.rank before)

theorem reflects (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) (context : Context loop body base)
    (values : Location → Word) (native machine : State) (input : At loop body base 0 values native) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches (loop.rank values * (X86BlockCompiler.steps spec body + 4) + 2)).run native = .ok () machine →
    ∃ after : Location → Word, SourceRun loop body values after ∧ X86StateFrame.Frame registers ∅ native machine ∧
      Nonempty (At loop body base (exitOffset body) after machine) ∧
      after (.inr loop.bound) = values (.inr loop.bound) ∧ after (.inr loop.index) = values (.inr loop.bound) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  intro run
  obtain ⟨after,entries,proved,fires,sites,executed,framed,atExit,bound,index,_⟩ :=
    completes other extra vector loop body base context values native input
  have same := X86FuelPrefix.fetches_deterministic _ native proved machine executed run
  subst machine
  exact ⟨after,⟨entries,fires,sites⟩,framed,atExit,bound,index⟩

theorem transfer_postcondition (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (loop : Control.Loop (Fin 12)) (body : X86WordBody.Program) (base : Int) (context : Context loop body base)
    (values : Location → Word) (native : State) (input : At loop body base 0 values native)
    (post : (Location → Word) → Prop) (source : ∀ after, SourceRun loop body values after → post after) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after : Location → Word, ∃ machine, SourceRun loop body values after ∧ post after ∧
      (X86FuelPrefix.fetches (loop.rank values * (X86BlockCompiler.steps spec body + 4) + 2)).run native = .ok () machine ∧
      X86StateFrame.Frame registers ∅ native machine ∧ Nonempty (At loop body base (exitOffset body) after machine) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,entries,machine,fires,sites,run,framed,atExit,_,_,_⟩ :=
    completes other extra vector loop body base context values native input
  have realized : SourceRun loop body values after := ⟨entries,fires,sites⟩
  exact ⟨after,machine,realized,source after realized,run,framed,atExit⟩

namespace Controls


private def add : Instruction := .binary 0 2 2 6 (by decide)
private def body : X86WordBody.Program := Prog.prim add
private def loop : Control.Loop (Fin 12) := ⟨0,4080,4096,4114,4105,4123,6,5,10⟩
private def rawBody : List Nat := [0x49,0x89,0xd6,0x4d,0x01,0xd6,0x4c,0x89,0xf2]
private def raw : List Nat :=
  [0x4d,0x39,0xca,0x0f,0x83,18,0,0,0,
    0x49,0x89,0xd6,0x4d,0x01,0xd6,0x4c,0x89,0xf2,
    0x49,0x83,0xc2,1,0xe9,0xe5,0xff,0xff,0xff]

theorem body_bytes : bodyBytes body = rawBody := by
  rw [bodyBytes,body,X86BlockCompiler.code_prim]
  simp only [spec,bytes,add]
  rw [binaryBytes_exact]
  rfl

theorem body_steps : X86BlockCompiler.steps spec body = 3 := rfl
theorem latch_offset : latchOffset body = 18 := by rw [latchOffset,body_bytes]; rfl
theorem exit_offset : exitOffset body = 27 := by rw [exitOffset,body_bytes]; rfl

theorem compiled_bytes : code loop body = raw := by
  unfold code headDisplacement backDisplacement
  rw [body_bytes,exit_offset]
  rfl

private theorem context : Context loop body 4096 where
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
  exit := by rw [exit_offset]; rfl

private def values (bound : Fin 11) : Location → Word
  | .inl name => if name = 0 then 4096 else 777
  | .inr register => if register = 0 then 8192 else if register = 5 then BitVec.ofNat 64 bound.val else 0

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 27).map fun offset => (4096 + offset,BitVec.ofNat 8 ((raw[offset]?).getD 0))
private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide

private noncomputable def native (bound : Fin 11) : State :=
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
  let registers := registers.insert .rsp (16384#64)
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList cells,(),0,#[]⟩

private def origin (bound : Fin 11) : X86LegacyFetch.Basis (native bound) where
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

private def input (bound : Fin 11) : At loop body 4096 0 (values bound) (native bound) where
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
    rw [compiled_bytes]
    intro offset byte present
    have within : offset < 27 := (List.getElem?_eq_some_iff.mp present).1
    have point : ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by interval_cases offset <;> decide
    have member : (4096 + offset,BitVec.ofNat 8 byte) ∈ cells :=
      List.mem_map.mpr ⟨offset,List.mem_range.mpr within,by simp only [present,Option.getD_some]⟩
    rw [point]
    exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member
  valid := by
    have small : bound.val < 2 ^ 64 := by have := bound.isLt; omega
    change 0 ≤ (BitVec.ofNat 64 bound.val).toNat ∧ (BitVec.ofNat 64 bound.val).toNat ≤ 10
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    exact ⟨Nat.zero_le _,by have := bound.isLt; omega⟩

theorem remaining (bound : Fin 11) : loop.rank (values bound) = bound.val := by
  have small : bound.val < 2 ^ 64 := by have := bound.isLt; omega
  change (BitVec.ofNat 64 bound.val).toNat - 0 = bound.val
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.sub_zero]

theorem counted_execution (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (bound : Fin 11) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after : Location → Word, ∃ machine, SourceRun loop body (values bound) after ∧
      (X86FuelPrefix.fetches (bound.val * 7 + 2)).run (native bound) = .ok () machine ∧
      lookup machine 10 = some (BitVec.ofNat 64 bound.val) ∧ lookup machine 9 = some (BitVec.ofNat 64 bound.val) ∧
      machine.regs.get? .rip = some (4123#64) ∧
      ∀ count ≤ bound.val * 7 + 2, ∀ reached, (X86FuelPrefix.fetches count).run (native bound) = .ok () reached →
        lookup reached 4 = lookup (native bound) 4 ∧ lookup reached 7 = lookup (native bound) 7 ∧
          ∀ address, reached.mem.get? address = (native bound).mem.get? address := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,entries,machine,fires,sites,run,_,⟨atExit⟩,boundSame,indexSame,prefixes⟩ :=
    completes other extra vector loop body 4096 context (values bound) (native bound) (input bound)
  have cost : loop.rank (values bound) * (X86BlockCompiler.steps spec body + 4) + 2 = bound.val * 7 + 2 := by
    rw [remaining,body_steps]
  rw [cost] at run prefixes
  have index : lookup machine 10 = some (BitVec.ofNat 64 bound.val) := by
    have found := physical_known loop.index after machine atExit.represented.1
    rw [indexSame] at found
    exact found
  have boundRead : lookup machine 9 = some (BitVec.ofNat 64 bound.val) := by
    have found := physical_known loop.bound after machine atExit.represented.1
    rw [boundSame] at found
    exact found
  have rip := atExit.represented.2
  rw [control_at loop body 4096 _ after machine atExit,exit_offset] at rip
  refine ⟨after,machine,⟨entries,fires,sites⟩,run,index,boundRead,rip,?_⟩
  intro count within reached executed
  have preserved := prefixes count within reached executed
  exact ⟨preserved.lookup 4 stack_readonly,preserved.lookup 7 frame_readonly,fun address => preserved.memory address (by simp)⟩

private noncomputable def changed : State := { native 3 with mem := (native 3).mem.insert 4101 (19#8) }
theorem changed_jump_refused : ¬codeLoaded changed 4096 raw := by
  intro loaded
  have wrong := loaded 5 18 (by rfl)
  simp [changed,address] at wrong

theorem counter_write_detected : (6 : Fin 12) ∈ X86WordBody.writes (Prog.prim (.binary 0 6 6 1 (by decide))) := by decide

end Controls
end Mettapedia.Machines.TIsa.X86CountedWordLoop
