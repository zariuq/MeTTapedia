import Mettapedia.Machines.TIsa.X86BranchGate
import Mettapedia.Machines.TIsa.X86BlockCompiler
import Mettapedia.Machines.TIsa.X86UnconditionalJump
import Mettapedia.Machines.TIsa.X86WordLibrary

/-!
# Conditional layout and native composition of certified source blocks

The lowering retains the source GSLT programs for both arms. It emits a generic
TEST/JZ gate, the true arm, a near JMP and the false arm, with displacements
computed from byte lengths. Signed displacement bounds, canonical addresses and
whole-image exclusion are explicit placement obligations.

Local compatibility proves that the tested register represents the source
condition and that arithmetic-status/RIP changes preserve the library's
representation and readiness. The gate's nonarithmetic flag preservation is
derived from its fetched execution. The compiler derives native inputs from these facts. It
transfers the selected source weakest precondition, exact instruction count and
every-prefix frame through the complete conditional to the common join.

The captured MOV/ADD/SUB library supplies a concrete compatibility/correctness
instance. Both choices, high-word wraparound, repeated operands, a changed jump,
malformed Booleans and empty-arm layout have controls. This is a fallthrough
conditional over certified straight-line arms; recursive control/loops, full
admission/hosting and public return/ABI remain separate obligations. Source
control-token firings are related to the gate in X86BranchGate.realizes.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86Conditional
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86BranchGate.handlers (X86UnconditionalJump.linked other) extra

def jumpCode (count : Nat) : List Nat :=
  [0xe9] ++ (List.range 4).map fun index => ((BitVec.ofNat 32 count).extractLsb' (8 * index) 8).toNat

def code (condition : Fin 16) (yes no : List Nat) : List Nat :=
  X86BranchGate.code condition (BitVec.ofNat 32 (yes.length + 5)) ++
    (yes ++ (jumpCode no.length ++ no))

theorem jump_length (count : Nat) : (jumpCode count).length = 5 := by simp [jumpCode]
theorem code_length (condition : Fin 16) (yes no : List Nat) :
    (code condition yes no).length = 14 + yes.length + no.length := by
  simp [code, X86BranchGate.code_length, jump_length]
  omega

theorem displacement_exact (count : Nat) (fits : count < 2 ^ 31) :
    (BitVec.ofNat 32 count).toInt = count := by
  rw [BitVec.toInt_ofNat']
  exact Int.bmod_eq_of_le (by omega) (by norm_num; exact_mod_cast fits)

theorem loaded_slice (native : State) (base : Int) (whole part : List Nat) (offset : Nat)
    (loaded : codeLoaded native base whole)
    (inside : ∀ index byte, part[index]? = some byte → whole[offset + index]? = some byte) :
    codeLoaded native (base + offset) part := by
  intro index byte present
  have found := loaded (offset + index) byte (inside index byte present)
  simpa only [address, Int.natCast_add, Int.add_assoc] using found

theorem gate_byte (condition : Fin 16) (yes no : List Nat) (index byte : Nat)
    (present : (X86BranchGate.code condition (BitVec.ofNat 32 (yes.length + 5)))[index]? = some byte) :
    (code condition yes no)[index]? = some byte := by
  rw [code, List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

theorem yes_byte (condition : Fin 16) (yes no : List Nat) (index byte : Nat)
    (present : yes[index]? = some byte) : (code condition yes no)[9 + index]? = some byte := by
  rw [code, List.getElem?_append_right (by rw [X86BranchGate.code_length]; omega),
    X86BranchGate.code_length, Nat.add_sub_cancel_left,
    List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

theorem jump_byte (condition : Fin 16) (yes no : List Nat) (index byte : Nat)
    (present : (jumpCode no.length)[index]? = some byte) :
    (code condition yes no)[9 + yes.length + index]? = some byte := by
  rw [code, List.getElem?_append_right (by rw [X86BranchGate.code_length]; omega),
    X86BranchGate.code_length]
  rw [show 9 + yes.length + index - 9 = yes.length + index by omega,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

theorem no_byte (condition : Fin 16) (yes no : List Nat) (index byte : Nat)
    (present : no[index]? = some byte) :
    (code condition yes no)[14 + yes.length + index]? = some byte := by
  rw [code, List.getElem?_append_right (by rw [X86BranchGate.code_length]; omega),
    X86BranchGate.code_length]
  rw [show 14 + yes.length + index - 9 = yes.length + (5 + index) by omega,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_right (by rw [jump_length]; omega), jump_length, Nat.add_sub_cancel_left]
  exact present

structure Inputs (native : State) (condition : Fin 16) (yes no : List Nat)
    extends X86LegacyFetch.Basis native where
  value : Word
  flags : BitVec 32
  valueKnown : lookup native condition = some value
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false
  yesFits : yes.length + 5 < 2 ^ 31
  noFits : no.length < 2 ^ 31
  upper : address.toInt + (((code condition yes no).length + 3 : Nat) : Int) < (2 ^ 47 : Int)
  loaded : codeLoaded native address.toInt (code condition yes no)

def position {native : State} {condition : Fin 16} {yes no : List Nat}
    (input : Inputs native condition yes no) (offset : Nat) : BitVec 48 := address input.address.toInt offset

theorem position_exact {native : State} {condition : Fin 16} {yes no : List Nat}
    (input : Inputs native condition yes no) (offset : Nat)
    (within : offset ≤ (code condition yes no).length + 3) :
    (position input offset).toInt = input.address.toInt + offset :=
  address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper offset within

def gateInput {native : State} {condition : Fin 16} {yes no : List Nat}
    (input : Inputs native condition yes no) : X86BranchGate.Inputs native condition := {
  input.toBasis with
  value := input.value
  flags := input.flags
  valueKnown := input.valueKnown
  flagsKnown := input.flagsKnown
  quiet := input.quiet
  upper := by have := input.upper; rw [code_length] at this; omega
  displacement := BitVec.ofNat 32 (yes.length + 5)
  target := position input (14 + yes.length)
  jump := by
    rw [position_exact input _ (by rw [code_length]; omega), displacement_exact _ input.yesFits]
    simp only [Int.natCast_add, Nat.cast_ofNat]
    omega
  loaded := by intro index byte present; exact input.loaded index byte (gate_byte condition yes no index byte present) }

theorem gate_control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (condition : Fin 16) (yes no : List Nat) (input : Inputs native condition yes no) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run native = .ok () after ∧
      RegisterFrame X86BranchGate.writes native after ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some
        ((position input (if input.value = (0#64) then 14 + yes.length else 9)).signExtend 64) ∧
      X86ControlFlags.Preserved native after := by
  obtain ⟨after, flags, run, framed, _, flagsRead, rip, control⟩ :=
    X86BranchGate.executes_control (X86UnconditionalJump.linked other) extra vector native condition (gateInput input)
  refine ⟨after, flags, run, framed, flagsRead, ?_, control⟩
  by_cases zero : input.value = (0#64) <;> simpa [gateInput, X86BranchGate.position, position, zero] using rip

theorem gate (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (condition : Fin 16) (yes no : List Nat) (input : Inputs native condition yes no) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run native = .ok () after ∧
      RegisterFrame X86BranchGate.writes native after ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some
        ((position input (if input.value = (0#64) then 14 + yes.length else 9)).signExtend 64) := by
  obtain ⟨after,flags,run,frame,read,rip,_control⟩ := gate_control other extra vector native condition yes no input
  exact ⟨after,flags,run,frame,read,rip⟩


theorem skip (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (condition : Fin 16) (yes no : List Nat) (input : Inputs native condition yes no)
    (middle : State) (registers : Finset Register) (bytes : Finset Nat)
    (framed : X86StateFrame.Frame registers bytes native middle)
    (dataOnly : registers ⊆ dataRegisters)
    (outside : ∀ index byte, (code condition yes no)[index]? = some byte →
      ((address input.address.toInt index).signExtend 52).toNat ∉ bytes)
    (rip : middle.regs.get? .rip = some ((position input (9 + yes.length)).signExtend 64))
    (quiet : middle.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, Step middle after ∧ RegisterFrame {.rip} middle after ∧
      after.regs.get? .rip = some ((position input (code condition yes no).length).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have loaded := framed.codeLoaded _ _ input.loaded outside
  have addressEq (offset index : Nat) (within : offset ≤ (code condition yes no).length + 3) :
      address (position input offset).toInt index = position input (offset + index) := by
    rw [position_exact input offset within]
    simp only [position, address, Int.natCast_add, Int.add_assoc]
  have original := X86StateFrame.basisAt native middle input.toBasis framed dataOnly
    (position input (9 + yes.length))
    (by rw [position_exact input _ (by rw [code_length]; omega)]; have := input.upper; rw [code_length] at this; omega) rip
  have displacement : ∀ index < 4,
      middle.mem.get? ((address (position input (10 + yes.length)).toInt index).signExtend 52).toNat =
        some ((BitVec.ofNat 32 no.length).extractLsb' (8 * index) 8) := by
    intro index within
    rw [addressEq _ index (by rw [code_length]; omega)]
    have present : (jumpCode no.length)[1 + index]? =
        some ((BitVec.ofNat 32 no.length).extractLsb' (8 * index) 8).toNat := by
      rw [show 1 + index = index + 1 by omega]
      simp [jumpCode, within]
    have byte := loaded _ _ (jump_byte condition yes no _ _ present)
    simpa only [position, show 9 + yes.length + (1 + index) = 10 + yes.length + index by omega,
      BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte
  have step := X86UnconditionalJump.fetched_jump (handlers other extra) vector middle
    (position input (9 + yes.length)) (position input (10 + yes.length)) (position input (14 + yes.length))
    (position input (code condition yes no).length) original.control original.attributes (BitVec.ofNat 32 no.length)
    (by rw [position_exact input _ (by rw [code_length]; omega), position_exact input _ (by rw [code_length]; omega)]; omega)
    (by rw [position_exact input _ (by rw [code_length]; omega), position_exact input _ (by rw [code_length]; omega)]; omega)
    (by rw [position_exact input _ (by omega), position_exact input _ (by rw [code_length]; omega),
       displacement_exact _ input.noFits]; rw [code_length]; simp only [Int.natCast_add, Nat.cast_ofNat]; omega)
    original.status original.fault original.msrs original.segments original.longMode original.codeMode
    original.application rip quiet
    (by
      have byte := loaded _ _ (jump_byte condition yes no 0 0xe9 (by rfl))
      simpa only [Nat.add_zero, position] using byte)
    displacement
  exact ⟨_, step, pointer_frame _ _, by simp [X86Move.putPointer]⟩

universe u s
variable {Op : Type u} {Source : Type s}

/-- Local register/readiness facts required to reuse an existing certified block library. -/
structure Compatible (spec : X86BlockCompiler.Spec Op Source) where
  condition : Fin 16
  value : Source → Word
  read : ∀ source native, spec.represents source native → lookup native condition = some (value source)
  prepared : ∀ native, spec.ready native →
    ∃ flags : BitVec 32, native.regs.get? .rflags = some flags ∧ native.regs.get? .log_register_writes = some false
  stable : ∀ source before after, spec.represents source before → spec.ready before →
    RegisterFrame X86BranchGate.writes before after →
    X86ControlFlags.Preserved before after →
    (∃ flags : BitVec 32, after.regs.get? .rflags = some flags) → spec.represents source after ∧ spec.ready after

structure At (spec : X86BlockCompiler.Spec Op Source) (compatible : Compatible spec)
    (yes no : X86BlockCompiler.Program Op) (source : Source) (native : State) where
  origin : X86LegacyFetch.Basis native
  yesFits : (X86BlockCompiler.code spec yes).length + 5 < 2 ^ 31
  noFits : (X86BlockCompiler.code spec no).length < 2 ^ 31
  upper : origin.address.toInt +
    (((code compatible.condition (X86BlockCompiler.code spec yes) (X86BlockCompiler.code spec no)).length + 3 : Nat) : Int) <
      (2 ^ 47 : Int)
  loaded : codeLoaded native origin.address.toInt
    (code compatible.condition (X86BlockCompiler.code spec yes) (X86BlockCompiler.code spec no))
  represented : spec.represents source native
  ready : spec.ready native
  outside : ∀ index byte,
    (code compatible.condition (X86BlockCompiler.code spec yes) (X86BlockCompiler.code spec no))[index]? = some byte →
    ((address origin.address.toInt index).signExtend 52).toNat ∉ spec.byteWrites

noncomputable def At.layout {spec : X86BlockCompiler.Spec Op Source} {compatible : Compatible spec}
    {yes no : X86BlockCompiler.Program Op} {source : Source} {native : State}
    (input : At spec compatible yes no source native) :
    Inputs native compatible.condition (X86BlockCompiler.code spec yes) (X86BlockCompiler.code spec no) := {
  input.origin with
  value := compatible.value source
  flags := Classical.choose (compatible.prepared native input.ready)
  valueKnown := compatible.read source native input.represented
  flagsKnown := (Classical.choose_spec (compatible.prepared native input.ready)).1
  quiet := (Classical.choose_spec (compatible.prepared native input.ready)).2
  yesFits := input.yesFits
  noFits := input.noFits
  upper := input.upper
  loaded := input.loaded }

theorem At.value {spec : X86BlockCompiler.Spec Op Source} {compatible : Compatible spec}
    {yes no : X86BlockCompiler.Program Op} {source : Source} {native : State}
    (input : At spec compatible yes no source native) : input.layout.value = compatible.value source := rfl

theorem truth_zero (word : Word) (choice : Bool) (chosen : RegisterProfile.truth word = some choice) :
    word = (0#64) ↔ choice = false := by
  by_cases zero : word = (0#64)
  · simp [RegisterProfile.truth, zero] at chosen
    simp [zero, chosen]
  · by_cases one : word = (1#64)
    · simp [RegisterProfile.truth, one] at chosen
      simp [zero, chosen]
    · simp [RegisterProfile.truth, zero, one] at chosen

theorem compile_wp (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (spec : X86BlockCompiler.Spec Op Source) (compatible : Compatible spec) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∀ (_correct : X86BlockCompiler.Correct spec) (_progress : ∀ op, (spec.action op).Progress)
      (yes no : X86BlockCompiler.Program Op) (source : Source) (native : State)
      (input : At spec compatible yes no source native) (choice : Bool)
      (_chosen : RegisterProfile.truth (compatible.value source) = some choice)
      (post : Unit → Source → Prop),
      (if choice then yes else no).wp spec.action post source →
      ∃ following after,
        (if choice then yes else no).Runs spec.action source () following ∧ post () following ∧
        (X86FuelPrefix.fetches
          (2 + X86BlockCompiler.steps spec (if choice then yes else no) + (if choice then 1 else 0))).run native = .ok () after ∧
        X86StateFrame.Frame (spec.registerWrites ∪ X86BranchGate.writes) spec.byteWrites native after ∧
        X86BlockCompiler.Observed spec
          (input.layout.address.toInt +
            (code compatible.condition (X86BlockCompiler.code spec yes) (X86BlockCompiler.code spec no)).length)
          () following after ∧
        ∀ count ≤ 2 + X86BlockCompiler.steps spec (if choice then yes else no) + (if choice then 1 else 0),
          ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
            X86StateFrame.Frame (spec.registerWrites ∪ X86BranchGate.writes) spec.byteWrites native observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  intro correct progress yes no source native input choice chosen post wp
  let left := X86BlockCompiler.code spec yes
  let right := X86BlockCompiler.code spec no
  let raw := code compatible.condition left right
  let base := input.layout.address.toInt
  let offset := if choice then 9 else 14 + left.length
  let stopOffset := if choice then 9 + left.length else raw.length
  let picked := if choice then yes else no
  have rawUpper : base + (((raw.length + 3 : Nat) : Int)) < (2 ^ 47 : Int) := input.layout.upper
  have rawLength : raw.length = 14 + left.length + right.length := code_length _ _ _
  have zero : input.layout.value = (0#64) ↔ choice = false := by
    rw [input.value]
    exact truth_zero _ _ chosen
  obtain ⟨middle, flags, first, firstFrame, middleFlags, middleRip,middleControl⟩ :=
    gate_control other extra vector native compatible.condition left right input.layout
  have middleRip' : middle.regs.get? .rip = some ((position input.layout offset).signExtend 64) := by
    cases choice <;> simp_all only [offset, Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false]
  have offsetWithin : offset + 3 ≤ raw.length + 3 := by
    dsimp only [offset]
    cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have stopWithin : stopOffset + 3 ≤ raw.length + 3 := by
    dsimp only [stopOffset]
    cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have middleReady := compatible.stable source native middle input.represented input.ready firstFrame middleControl ⟨flags, middleFlags⟩
  have fullFrame : X86StateFrame.Frame (spec.registerWrites ∪ X86BranchGate.writes) spec.byteWrites native middle :=
    (X86StateFrame.registerOnly firstFrame).mono (by simp) (by simp)
  let origin := X86StateFrame.basisAt native middle input.layout.toBasis fullFrame
    (by intro register present; rcases Finset.mem_union.mp present with a | b; exact correct.dataOnly a; exact X86BranchGate.writes_data b)
    (position input.layout offset)
    (by
      rw [position_exact input.layout offset (by change offset ≤ raw.length + 3; omega)]
      change base + offset + 3 < (2 ^ 47 : Int)
      omega) middleRip'
  have placed : origin.address.toInt = base + offset :=
    position_exact input.layout offset (by change offset ≤ raw.length + 3; omega)
  have remaining : stopOffset = offset + (X86BlockCompiler.code spec picked).length := by
    cases choice <;> simp [stopOffset, offset, picked, raw, code_length, left, right]
  have armByte (index byte : Nat) (present : (X86BlockCompiler.code spec picked)[index]? = some byte) :
      raw[offset + index]? = some byte := by
    cases choice
    · exact no_byte compatible.condition left right index byte present
    · exact yes_byte compatible.condition left right index byte present
  have armInput : X86BlockCompiler.At spec (base + stopOffset) picked source middle := {
    origin := origin
    placed := by rw [placed, remaining]; simp only [Int.natCast_add]; omega
    upper := by omega
    represented := middleReady.1
    ready := middleReady.2
    loaded := by
      rw [placed]
      exact loaded_slice middle base raw _ offset (firstFrame.code_preserved _ _ input.layout.loaded) armByte
    outside := by
      intro index byte present
      rw [placed]
      have found := input.outside (offset + index) byte (armByte index byte present)
      change ((address base (offset + index)).signExtend 52).toNat ∉ spec.byteWrites at found
      simpa only [address, Int.natCast_add, Int.add_assoc] using found }
  obtain ⟨following, body, sourceRun, holds, bodyRun, bodyFrame, observed⟩ :=
    X86BlockCompiler.compile_wp spec correct progress (base + stopOffset) picked source middle armInput post wp
  have combined := X86FuelPrefix.fetches_then 2 (X86BlockCompiler.steps spec picked) native middle body first bodyRun
  have combinedFrame : X86StateFrame.Frame (spec.registerWrites ∪ X86BranchGate.writes) spec.byteWrites native body :=
    (fullFrame.trans bodyFrame).mono (by simp) (by simp)
  have prefixBody : ∀ count ≤ 2 + X86BlockCompiler.steps spec picked, ∀ observed,
      (X86FuelPrefix.fetches count).run native = .ok () observed →
        X86StateFrame.Frame (spec.registerWrites ∪ X86BranchGate.writes) spec.byteWrites native observed := by
    intro count within state executed
    by_cases inGate : count ≤ 2
    · obtain ⟨proved, run, framed⟩ := X86BranchGate.prefix_frame (X86UnconditionalJump.linked other) extra vector
        native compatible.condition (gateInput input.layout) count inGate
      have same := X86FuelPrefix.fetches_deterministic count native proved state run executed
      subst state
      exact (X86StateFrame.registerOnly framed).mono (by simp) (by simp)
    · have splitCount : count = 2 + (count - 2) := by omega
      rw [splitCount] at executed
      obtain ⟨reached, gateRun, rest⟩ := X86BlockCompiler.fetches_split 2 (count - 2) native state executed
      have same := X86FuelPrefix.fetches_deterministic 2 native reached middle gateRun first
      subst reached
      have restFrame := X86BlockCompiler.prefix_frame spec correct progress (base + stopOffset) picked source middle state
        armInput wp.1 (count - 2) (by omega) rest
      exact (fullFrame.trans restFrame).mono (by simp) (by simp)
  cases choice with
  | false =>
    refine ⟨following, body, sourceRun, holds, ?_, combinedFrame, observed, ?_⟩
    · simpa only [picked, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using combined
    · simpa only [picked, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using prefixBody
  | true =>
    have bodyRip : body.regs.get? .rip = some ((position input.layout (9 + left.length)).signExtend 64) := by
      simpa only [X86BlockCompiler.Observed, stopOffset, ↓reduceIte, base, position, address] using observed.2.2
    obtain ⟨bodyFlags, bodyFlagsRead, quiet⟩ := compatible.prepared body observed.2.1
    obtain ⟨after, last, lastFrame, finalRip⟩ := skip other extra vector native compatible.condition left right input.layout
      body (spec.registerWrites ∪ X86BranchGate.writes) spec.byteWrites combinedFrame
      (by intro register present; rcases Finset.mem_union.mp present with a | b; exact correct.dataOnly a; exact X86BranchGate.writes_data b)
      input.outside bodyRip quiet
    have retained := compatible.stable following body after observed.1 observed.2.1
      (lastFrame.mono (by simp [X86BranchGate.writes]))
      (X86ControlFlags.of_register_frame lastFrame (by decide))
      ⟨bodyFlags, (lastFrame.registers .rflags (by decide)).trans bodyFlagsRead⟩
    have finalRun := X86FuelPrefix.fetches_then (2 + X86BlockCompiler.steps spec yes) 1 native body after combined
      (X86FuelPrefix.fetches_one body after last)
    have finalFrame : X86StateFrame.Frame (spec.registerWrites ∪ X86BranchGate.writes) spec.byteWrites native after :=
      (combinedFrame.trans (X86StateFrame.registerOnly lastFrame)).mono
        (by simp [X86BranchGate.writes]) (by simp)
    refine ⟨following, after, sourceRun, holds, finalRun, finalFrame,
      ⟨retained.1, retained.2, finalRip⟩, ?_⟩
    intro count within state executed
    by_cases inBody : count ≤ 2 + X86BlockCompiler.steps spec yes
    · exact prefixBody count inBody state executed
    · have atEnd : count = 2 + X86BlockCompiler.steps spec yes + 1 := by simp only [↓reduceIte] at within; omega
      subst count
      have same := X86FuelPrefix.fetches_deterministic _ native after state finalRun executed
      subst state
      exact finalFrame

theorem compile_reflects (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (spec : X86BlockCompiler.Spec Op Source) (compatible : Compatible spec) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∀ (_correct : X86BlockCompiler.Correct spec) (_progress : ∀ op, (spec.action op).Progress)
      (yes no : X86BlockCompiler.Program Op) (source : Source) (native after : State)
      (input : At spec compatible yes no source native) (choice : Bool)
      (_chosen : RegisterProfile.truth (compatible.value source) = some choice)
      (post : Unit → Source → Prop),
      (if choice then yes else no).wp spec.action post source →
      (X86FuelPrefix.fetches
        (2 + X86BlockCompiler.steps spec (if choice then yes else no) + (if choice then 1 else 0))).run native = .ok () after →
      ∃ following, (if choice then yes else no).Runs spec.action source () following ∧ post () following ∧
        X86StateFrame.Frame (spec.registerWrites ∪ X86BranchGate.writes) spec.byteWrites native after ∧
        X86BlockCompiler.Observed spec
          (input.layout.address.toInt +
            (code compatible.condition (X86BlockCompiler.code spec yes) (X86BlockCompiler.code spec no)).length)
          () following after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  intro correct progress yes no source native after input choice chosen post wp run
  obtain ⟨following, proved, sourceRun, holds, executed, framed, observed, _⟩ :=
    compile_wp other extra vector spec compatible correct progress yes no source native input choice chosen post wp
  have same := X86FuelPrefix.fetches_deterministic _ native proved after executed run
  subst after
  exact ⟨following, sourceRun, holds, framed, observed⟩

def wordValue (condition : Fin 12) (world : X86WordLibrary.World) : Word :=
  BitVec.ofNat 64 ((world.map fun cell => if cell.key = condition then cell.value.toNat else 0).sum)

theorem wordValue_encode (condition : Fin 12) (values : Fin 12 → Word) :
    wordValue condition (Cells.encode Finset.univ values) = values condition := by
  fin_cases condition <;> simp [wordValue, Cells.encode]

def wordCompatible (condition : Fin 12) : Compatible X86WordLibrary.spec where
  condition := X86CopyBlock.physical condition
  value := wordValue condition
  read := by
    rintro source native ⟨values, rfl, represented⟩
    rw [wordValue_encode]
    have known := represented condition (Finset.mem_univ _)
    fin_cases condition <;>
      simpa only [X86CopyBlock.physical, X86MovCapture.physical, placed, Registers.canonical,
        Registers.Placement.resolve, Registers.logicalSlot] using known
  prepared := fun _ ready => ready
  stable := by
    rintro source before after ⟨values, same, represented⟩ ⟨_, _, quiet⟩ framed _control ⟨flags, flagsRead⟩
    refine ⟨⟨values, same, ?_⟩, flags, flagsRead, (framed.registers .log_register_writes (by decide)).trans quiet⟩
    intro register member
    rw [framed.lookup _ (by fin_cases register <;> decide)]
    exact represented register member

theorem word_correct (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    X86BlockCompiler.Correct X86WordLibrary.spec :=
  X86WordLibrary.correct (handlers other extra) vector

namespace Controls
open X86WordLibrary

private def yes : X86BlockCompiler.Program Instruction := Prog.prim (.binary 0 2 1 1 (by decide))
private def no : X86BlockCompiler.Program Instruction := Prog.prim (.binary 1 2 1 1 (by decide))
private def values (choice : Bool) (register : Fin 12) : Word :=
  if register = 0 then 8192 else if register = 1 then 0xffffffffffffffff#64
  else if register = 7 then booleanWord choice else 0
private def finalValues (choice : Bool) : Fin 12 → Word :=
  Function.update (values choice) 2 (if choice then 0xfffffffffffffffe#64 else 0)
private def raw : List Nat :=
  [0x4d,0x85,0xdb,0x0f,0x84,14,0,0,0,
    0x49,0x89,0xf6,0x49,0x01,0xf6,0x4c,0x89,0xf2,
    0xe9,9,0,0,0,
    0x49,0x89,0xf6,0x49,0x29,0xf6,0x4c,0x89,0xf2]

theorem compiled_bytes : code (wordCompatible 7).condition
    (X86BlockCompiler.code spec yes) (X86BlockCompiler.code spec no) = raw := by
  rw [yes, no, X86BlockCompiler.code_prim, X86BlockCompiler.code_prim]
  simp only [spec, bytes]
  rw [binaryBytes_exact, binaryBytes_exact]
  rfl

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 32).map fun index => (4096 + index, BitVec.ofNat 8 ((raw[index]?).getD 0))

private noncomputable def before (choice : Bool) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .rdi (values choice 0)
  let registers := registers.insert .rsi (values choice 1)
  let registers := registers.insert .rdx (values choice 2)
  let registers := registers.insert .rcx (values choice 3)
  let registers := registers.insert .r8 (values choice 4)
  let registers := registers.insert .r9 (values choice 5)
  let registers := registers.insert .r10 (values choice 6)
  let registers := registers.insert .r11 (values choice 7)
  let registers := registers.insert .rax (values choice 8)
  let registers := registers.insert .rbx (values choice 9)
  let registers := registers.insert .r12 (values choice 10)
  let registers := registers.insert .r13 (values choice 11)
  let registers := registers.insert .rsp (16384#64)
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩

private def origin (choice : Bool) : X86LegacyFetch.Basis (before choice) where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [before, Std.ExtDHashMap.get?_insert]
  fault := by simp [before, Std.ExtDHashMap.get?_insert]
  msrs := by simp [before, Std.ExtDHashMap.get?_insert]
  segments := by simp [before, Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before, Std.ExtDHashMap.get?_insert]
  rip := by simp [before, Std.ExtDHashMap.get?_insert]

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide
private theorem cell (choice : Bool) (index : Nat) (within : index < 32) (byte : Nat) (present : raw[index]? = some byte) :
    (before choice).mem.get? ((address 4096 index).signExtend 52).toNat = some (BitVec.ofNat 8 byte) := by
  have point : ((address 4096 index).signExtend 52).toNat = 4096 + index := by interval_cases index <;> decide
  have member : (4096 + index, BitVec.ofNat 8 byte) ∈ cells :=
    List.mem_map.mpr ⟨index, List.mem_range.mpr within, by simp only [present, Option.getD_some]⟩
  rw [point]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member

private def input (choice : Bool) : At spec (wordCompatible 7) yes no (Cells.encode Finset.univ (values choice)) (before choice) where
  origin := origin choice
  yesFits := by simp only [yes, X86BlockCompiler.code_prim, spec, bytes, binaryBytes_exact]; decide
  noFits := by simp only [no, X86BlockCompiler.code_prim, spec, bytes, binaryBytes_exact]; decide
  upper := by rw [compiled_bytes]; change (4096 : Int) + 35 < (2 ^ 47 : Int); decide
  loaded := by
    rw [compiled_bytes]
    intro index byte present
    exact cell choice index (List.getElem?_eq_some_iff.mp present).1 byte present
  represented := by
    refine ⟨values choice, rfl, ?_⟩
    intro register _
    fin_cases register <;>
      simp [lookup, placed, Registers.canonical, Registers.Placement.resolve, Registers.logicalSlot,
        key, before, Std.ExtDHashMap.get?_insert] <;> rfl
  ready := ⟨0x246#32, by simp [before, Std.ExtDHashMap.get?_insert], by simp [before]⟩
  outside := by intros; simp [spec]

private theorem source_wp (choice : Bool) :
    (if choice then yes else no).wp action (fun _ world => world = Cells.encode Finset.univ (finalValues choice))
      (Cells.encode Finset.univ (values choice)) := by
  cases choice
  · exact source_wp_step (.binary 1 2 1 1 (by decide)) (values false) 0 (by rfl) _ rfl
  · exact source_wp_step (.binary 0 2 1 1 (by decide)) (values true) (0xfffffffffffffffe#64) (by rfl) _ rfl

theorem conditional_wraparound (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (choice : Bool) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (if choice then 6 else 5)).run (before choice) = .ok () after ∧
      represents (Cells.encode Finset.univ (finalValues choice)) after ∧
      after.regs.get? .rip = some (4128#64) ∧
      X86StateFrame.Frame (registers ∪ X86BranchGate.writes) ∅ (before choice) after ∧
      ∀ count ≤ (if choice then 6 else 5), ∀ reached,
        (X86FuelPrefix.fetches count).run (before choice) = .ok () reached →
          lookup reached 4 = lookup (before choice) 4 ∧ lookup reached 7 = lookup (before choice) 7 ∧
            ∀ address, reached.mem.get? address = (before choice).mem.get? address := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have chosen : RegisterProfile.truth ((wordCompatible 7).value (Cells.encode Finset.univ (values choice))) = some choice := by
    change RegisterProfile.truth (wordValue 7 (Cells.encode Finset.univ (values choice))) = some choice
    rw [wordValue_encode]
    cases choice <;> rfl
  obtain ⟨following, after, _, same, run, framed, observed, prefixes⟩ :=
    compile_wp other extra vector spec (wordCompatible 7) (word_correct other extra vector) progress
      yes no _ _ (input choice) choice chosen _ (source_wp choice)
  subst following
  have count : 2 + X86BlockCompiler.steps spec (if choice then yes else no) + (if choice then 1 else 0) =
      (if choice then 6 else 5) := by cases choice <;> rfl
  rw [count] at run prefixes
  refine ⟨after, run, observed.1, ?_, framed, ?_⟩
  · have final := observed.2.2
    change after.regs.get? .rip = some ((BitVec.ofInt 48
      ((4096 : Int) + (code (wordCompatible 7).condition
        (X86BlockCompiler.code spec yes) (X86BlockCompiler.code spec no)).length)).signExtend 64) at final
    rw [compiled_bytes] at final
    exact final
  · intro count within reached executed
    have preserved := prefixes count within reached executed
    exact ⟨preserved.lookup 4 (by decide), preserved.lookup 7 (by decide), fun address => preserved.memory address (by simp [spec])⟩

private noncomputable def changed (choice : Bool) : State :=
  { before choice with mem := (before choice).mem.insert 4101 (15#8) }

theorem changed_jump_rejected (choice : Bool) : ¬codeLoaded (changed choice) 4096 raw := by
  intro loaded
  have wrong := loaded 5 14 (by rfl)
  simp [changed, address] at wrong

theorem malformed_boolean_refused : RegisterProfile.truth (wordValue 7 (Cells.encode Finset.univ (fun _ => 2))) = none := by
  rw [wordValue_encode]
  decide

theorem empty_arm_layout : code 11 [] [] =
    [0x4d,0x85,0xdb,0x0f,0x84,5,0,0,0,0xe9,0,0,0,0] := by decide

theorem overflowing_displacement_refused : ¬(2 ^ 31 : Nat) < 2 ^ 31 := by decide

end Controls
end Mettapedia.Machines.TIsa.X86Conditional
