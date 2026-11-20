import Mettapedia.Machines.TIsa.P1Memory

/-!
# Structured p1 execution over admitted qword resources

This view composes scalar evaluation with capability checks over aligned
words. An uninitialized or out-of-range access refuses before a write.
The transition budget and its receipt are part of the machine state.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1WordExecution

open P1Source
abbrev Registers := Reg → Word

structure Capability where
  base : Word
  length : Word
  mode : Mode

structure State where
  registers : Registers
  regions : Region → Capability
  frame : Fin 24 → Word
  memory : Nat → Option Word
  budget : Word
  spent : Word

def State.write (state : State) (destination : Reg) (value : Word) : State :=
  {state with registers := Function.update state.registers destination value}

def State.store (state : State) (address : Nat) (value : Word) : State :=
  {state with memory := Function.update state.memory address (some value)}

def wordAddress (cap : Capability) (pointer : Word) (displacement : BitVec 32) :
    Option Nat := do
  let address ← Memory.access? cap.base cap.length pointer displacement.toInt 8
  if address % 8 = 0 then some address else none

abbrev scalarInstruction (state : State) (code : Instr) : Except ExitStatus State :=
  match code.destination? with
  | none => .error .invalidInput
  | some destination =>
    match P1Scalar.evaluate code (code.reads.map state.registers) with
    | some value => .ok (state.write destination value)
    | none => .error .invalidInput

def instruction (state : State) (instruction : Instr) : Except ExitStatus State :=
  match instruction with
  | .loadFrame ty dst slot =>
    match P1Memory.checkedWord ty (state.frame slot) with
    | some value => .ok (state.write dst value)
    | none => .error .invalidInput
  | .address region dst base index scale displacement =>
    let cap := state.regions region
    if cap.mode = .absent then .error .invalidInput else
    let pointer := (state.registers base).toNat
    let offset := (index.map fun reg => (state.registers reg).toNat).getD 0
    match P1Memory.address? ⟨cap.base.toNat, cap.length.toNat⟩ pointer offset scale.val
        displacement.toInt with
    | some formed => .ok (state.write dst (.ofNat 64 formed))
    | none => .error .invalidInput
  | .load ty .word64 region dst pointer displacement =>
    let cap := state.regions region
    if cap.mode = .absent then .error .invalidInput else
    match (wordAddress cap (state.registers pointer) displacement).bind state.memory with
    | some word =>
      match P1Memory.checkedWord ty word with
      | some value => .ok (state.write dst value)
      | none => .error .invalidInput
    | none => .error .invalidInput
  | .store .word64 region pointer displacement value =>
    let cap := state.regions region
    if cap.mode ≠ .readWrite then .error .invalidInput else
    match wordAddress cap (state.registers pointer) displacement with
    | some address => .ok (state.store address (state.registers value))
    | none => .error .invalidInput
  | .load .. | .store .. => .error .unsupported
  | scalar => scalarInstruction state scalar

inductive Flow where
  | continuing (state : State)
  | returned (status : ExitStatus) (payload : Word) (state : State)

def Flow.after (flow : Flow) : State :=
  match flow with
  | .continuing state | .returned _ _ state => state

def Flow.thenContinue (first : Flow) (next : State → Flow) : Flow :=
  match first with
  | .continuing state => next state
  | .returned status payload state => .returned status payload state

def fail (status : ExitStatus) (state : State) : Flow := .returned status status.word state

def fund (state : State) (units : BitVec 32) : Flow :=
  let debit := units.zeroExtend 64
  if state.budget - state.spent < debit then fail .exhausted state
  else .continuing {state with spent := state.spent + debit}

def continueLoop (state : State) (guard : Option Reg) (next : State → Flow) : Flow :=
  match guard with
  | none => next state
  | some condition =>
    if state.registers condition = 1 then next state
    else if state.registers condition = 0 then .continuing state
    else fail .invalidInput state

def loop (body : State → Flow) (index : Reg) (guard : Option Reg) :
    Nat → State → Flow
  | 0, state => .continuing state
  | remaining + 1, state =>
    continueLoop state guard fun start =>
      (body start).thenContinue fun following =>
        continueLoop following guard fun next =>
          loop body index guard remaining (next.write index (next.registers index + 1))

def execute (state : State) : Stmt → Flow
  | .skip => .continuing state
  | .instruction code =>
    match instruction state code with
    | .ok following => .continuing following
    | .error status => fail status state
  | .seq first second => (execute state first).thenContinue fun next => execute next second
  | .branch condition yes no =>
    if state.registers condition = 1 then execute state yes
    else if state.registers condition = 0 then execute state no
    else fail .invalidInput state
  | .counted index bound cap body =>
    if cap.toNat < (state.registers bound).toNat then fail .unsupported state
    else loop (fun next => execute next body) index none
      (state.registers bound).toNat (state.write index 0)
  | .early index bound continuation cap body =>
    if cap.toNat < (state.registers bound).toNat then fail .unsupported state
    else loop (fun next => execute next body) index (some continuation)
      (state.registers bound).toNat (state.write index 0)
  | .fund units => fund state units
  | .ret outcome result => .returned outcome (state.registers result) state

theorem branch_bool (state : State) (reg : Reg) (flag : Bool) (yes no : Stmt)
    (read : state.registers reg = booleanWord flag) :
    execute state (.branch reg yes no) = execute state (if flag then yes else no) := by
  rw [execute, read]
  cases flag <;> rfl

theorem qword_load_continues {state following : State} (region : Region) (destination pointer : Reg)
    (offset : BitVec 32)
    (ran : execute state (.instruction (.load .u64 .word64 region destination pointer offset)) =
      .continuing following) : ∃ word, following = state.write destination word := by
  by_cases absent : (state.regions region).mode = .absent
  · simp [execute, instruction, absent, fail] at ran
  · simp only [execute, instruction, if_neg absent] at ran
    cases fetched : (wordAddress (state.regions region) (state.registers pointer) offset).bind state.memory with
    | none => simp [fetched, fail] at ran
    | some word =>
      simp [fetched, P1Memory.checkedWord, P1Scalar.boolInputs, P1Scalar.normalize] at ran
      exact ⟨word, ran.symm⟩

theorem qword_store_continues {state following : State} (region : Region) (pointer value : Reg)
    (offset : BitVec 32)
    (ran : execute state (.instruction (.store .word64 region pointer offset value)) =
      .continuing following) :
    ∃ location, following = state.store location (state.registers value) ∧
      Memory.access? (state.regions region).base (state.regions region).length (state.registers pointer)
        offset.toInt 8 = some location := by
  by_cases writable : (state.regions region).mode = .readWrite
  · simp only [execute, instruction, writable] at ran
    cases addressed : wordAddress (state.regions region) (state.registers pointer) offset with
    | none => simp [addressed, fail] at ran
    | some location =>
      simp [addressed] at ran
      obtain ⟨target, physical, aligned⟩ := Option.bind_eq_some_iff.mp addressed
      split at aligned
      · cases aligned
        exact ⟨_, ran.symm, physical⟩
      · cases aligned
  · simp [execute, instruction, writable, fail] at ran

structure Usable (cap : Capability) (extent : Nat) : Prop where
  writable : cap.mode = .readWrite
  aligned : cap.base.toNat % 8 = 0
  enough : extent ≤ cap.length.toNat
  fits : cap.base.toNat + cap.length.toNat < 2^64

/-- An aligned access through an interior pointer. Call frames use
the same region capability at different saved frame offsets. -/
structure QwordAccess (cap : Capability) (pointer : Word) (displacement : BitVec 32)
    (address : Nat) : Prop where
  fits : cap.base.toNat + cap.length.toNat < 2^64
  pointerLower : cap.base.toNat ≤ pointer.toNat
  pointerUpper : pointer.toNat ≤ cap.base.toNat + cap.length.toNat
  begins : cap.base.toNat ≤ address
  ends : address + 8 ≤ cap.base.toNat + cap.length.toNat
  exactAddress : (address : Int) = (pointer.toNat : Int) + displacement.toInt
  aligned : address % 8 = 0

private theorem QwordAccess.checkedAddress {cap : Capability} {pointer : Word}
    {displacement : BitVec 32} {address : Nat} (access : QwordAccess cap pointer displacement address) :
    wordAddress cap pointer displacement = some address := by
  have inside := (P1Memory.access?_iff_inside cap.base cap.length pointer displacement 8 address
    access.fits access.pointerLower access.pointerUpper).mpr
    (by
      rw [← access.exactAddress]
      have lower := access.begins
      have upper := access.ends
      omega)
  simp [wordAddress, inside, access.aligned]

theorem load_qword (state : State) (region : Region) (destination pointer : Reg)
    (displacement : BitVec 32) (address : Nat) (word : Word)
    (live : (state.regions region).mode ≠ .absent)
    (access : QwordAccess (state.regions region) (state.registers pointer) displacement address)
    (read : state.memory address = some word) :
    instruction state (.load .u64 .word64 region destination pointer displacement) =
      .ok (state.write destination word) := by
  simp [instruction, live, access.checkedAddress, read, P1Memory.checkedWord,
    P1Scalar.boolInputs, P1Scalar.normalize]

theorem store_qword (state : State) (region : Region) (pointer value : Reg)
    (displacement : BitVec 32) (address : Nat)
    (live : (state.regions region).mode = .readWrite)
    (access : QwordAccess (state.regions region) (state.registers pointer) displacement address) :
    instruction state (.store .word64 region pointer displacement value) =
      .ok (state.store address (state.registers value)) := by
  simp [instruction, live, access.checkedAddress]

theorem address_at_offset (base length index : Word) (capability : base.toNat + length.toNat < 2^64)
    (inside : index.toNat ≤ length.toNat) :
    P1Memory.address? ⟨base.toNat, length.toNat⟩ base.toNat index.toNat 0 0 =
      some (base.toNat + index.toNat) := by
  let range : ByteRange := ⟨base.toNat, length.toNat⟩
  let target := base.toNat + index.toNat
  have valid : range.valid64 = true := by
    change decide (base.toNat < 2^64 ∧ base.toNat + length.toNat ≤ 2^64) = true
    exact decide_eq_true ⟨base.isLt, by omega⟩
  have first : checkedAddress? range base.toNat index.toNat 0 0 = some target := by
    apply (checkedAddress?_iff _ _ _ _ _ _).mpr
    refine ⟨?_, ?_⟩
    · have small := index.isLt
      simp [AddressAdmitted, valid, range, ByteRange.stop, addressTarget, addressSum]
      omega
    · simp [target, addressTarget, addressSum]
      omega
  have second : checkedAddress? range target 0 0 0 = some target := by
    apply (checkedAddress?_iff _ _ _ _ _ _).mpr
    refine ⟨?_, ?_⟩
    · simp [AddressAdmitted, valid, range, target, ByteRange.stop, addressTarget, addressSum]
      omega
    · simp [addressTarget, addressSum]
  exact (P1Memory.address?_iff _ _ _ _ _ _).mpr ⟨target, first, second⟩

theorem address_region_base (state : State) (region : Region) (destination base index : Reg)
    (live : (state.regions region).mode ≠ .absent)
    (baseRead : state.registers base = (state.regions region).base)
    (fits : (state.regions region).base.toNat + (state.regions region).length.toNat < 2^64)
    (inside : (state.registers index).toNat ≤ (state.regions region).length.toNat) :
    execute state (.instruction (.address region destination base (some index) 0 0)) =
      .continuing (state.write destination (.ofNat 64
        ((state.regions region).base.toNat + (state.registers index).toNat))) := by
  simp only [execute, instruction, live, if_false, baseRead, Option.map_some, Option.getD_some,
    show (0 : Fin 4).val = 0 from rfl, show (0 : BitVec 32).toInt = 0 by decide]
  rw [address_at_offset _ _ _ fits inside]

theorem load_frame_pointer (state : State) (destination : Reg) (slot : Fin 24) :
    execute state (.instruction (.loadFrame .pointer destination slot)) =
      .continuing (state.write destination (state.frame slot)) := rfl

private theorem base_word (cap : Capability) (extent offset : Nat) (usable : Usable cap extent)
    (inside : offset + 8 ≤ extent) (aligned : offset % 8 = 0)
    (displacement : BitVec 32) (represents : displacement.toInt = (offset : Int)) :
    wordAddress cap cap.base displacement = some (cap.base.toNat + offset) := by
  have fits := usable.enough
  have physical : Memory.access? cap.base cap.length cap.base displacement.toInt 8 =
      some (cap.base.toNat + offset) := by
    apply (P1Memory.access?_iff_inside cap.base cap.length cap.base displacement 8 _
      usable.fits (Nat.le_refl _) (by omega)).mpr
    rw [represents]
    exact ⟨by omega, by omega, by omega⟩
  have multiple : (cap.base.toNat + offset) % 8 = 0 := by
    have first := usable.aligned
    omega
  simp [wordAddress, physical, multiple]

theorem load_base (state : State) (region : Region) (extent offset : Nat)
    (usable : Usable (state.regions region) extent) (inside : offset + 8 ≤ extent)
    (aligned : offset % 8 = 0) (dst pointer : Reg) (displacement : BitVec 32)
    (represents : displacement.toInt = (offset : Int))
    (base : state.registers pointer = (state.regions region).base)
    (word : Word) (memory : state.memory ((state.regions region).base.toNat + offset) = some word) :
    instruction state (.load .u64 .word64 region dst pointer displacement) = .ok (state.write dst word) := by
  simp [instruction, usable.writable, base, base_word _ _ _ usable inside aligned _ represents,
    memory, P1Memory.checkedWord, P1Scalar.boolInputs, P1Scalar.normalize]

theorem store_base (state : State) (region : Region) (extent offset : Nat)
    (usable : Usable (state.regions region) extent) (inside : offset + 8 ≤ extent)
    (aligned : offset % 8 = 0) (pointer value : Reg) (displacement : BitVec 32)
    (represents : displacement.toInt = (offset : Int))
    (base : state.registers pointer = (state.regions region).base) :
    instruction state (.store .word64 region pointer displacement value) =
      .ok (state.store ((state.regions region).base.toNat + offset) (state.registers value)) := by
  simp [instruction, usable.writable, base, base_word _ _ _ usable inside aligned _ represents]

theorem fund_exact (state : State) (units : BitVec 32) (valid : state.spent.toNat ≤ state.budget.toNat) :
    ((fund state units).after.spent.toNat, match fund state units with
      | .continuing _ => true | .returned .. => false) =
    if state.spent.toNat + units.toNat ≤ state.budget.toNat then
      (state.spent.toNat + units.toNat, true)
    else (state.spent.toNat, false) := by
  have debit : (units.zeroExtend 64).toNat = units.toNat := by
    simp only [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by have := units.isLt; omega)
  have difference : (state.budget - state.spent).toNat = state.budget.toNat - state.spent.toNat :=
    BitVec.toNat_sub_of_le valid
  by_cases fits : state.spent.toNat + units.toNat ≤ state.budget.toNat
  · have rest : ¬ (state.budget - state.spent) < units.zeroExtend 64 := by
      rw [BitVec.lt_def, debit, difference]
      omega
    have noWrap : state.spent.toNat + (units.zeroExtend 64).toNat < 2^64 := by
      rw [debit]
      have := state.budget.isLt
      omega
    simp only [fund, if_neg rest, Flow.after, if_pos fits, BitVec.toNat_add_of_lt noWrap, debit]
  · have rest : (state.budget - state.spent) < units.zeroExtend 64 := by
      rw [BitVec.lt_def, debit, difference]
      omega
    simp only [fund, if_pos rest, fail, Flow.after, if_neg fits]

end Mettapedia.Machines.TIsa.P1WordExecution
