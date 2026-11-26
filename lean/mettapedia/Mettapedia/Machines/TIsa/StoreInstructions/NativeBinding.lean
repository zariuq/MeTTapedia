import Mettapedia.Machines.TIsa.StoreInstructions.BindingSlots
import Mettapedia.Machines.TIsa.StoreInstructions.WordTests
import Mettapedia.Machines.TIsa.X86PlacedPairStore

/-!
# Native bind-or-compare at a private variable slot

The occupancy word is separate from the term code. In particular,
zero is a valid term code and does not mean unbound. The empty
path writes both words. The occupied path compares two term codes
and leaves the slot alone on either outcome.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeBinding

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (CompareBranch Jump)
open X86PlacedMemory (CodeApart Controls Encoding Reads)
open X86PlacedPairStore (Cells)
open Mettapedia.Logic.LP
open Derivation.FirstOrderTerms (groundTermDecidableEq)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Native := X86RegisterRefinement.State

structure Layout where
  entry : ℕ
  occupied : ℕ
  accepted : ℕ
  refused : ℕ
  encoding : Encoding
  bitReg : Fin 16
  heldReg : Fin 16
  offeredReg : Fin 16
  zeroReg : Fin 16
  oneReg : Fin 16
  valueOffset : BitVec 32
  bitOffset : BitVec 32

def Layout.writes (layout : Layout) : X86PlacedPairStore.Layout :=
  ⟨layout.entry + 9, layout.encoding, layout.offeredReg, layout.oneReg, layout.valueOffset, layout.bitOffset⟩

structure Layout.Checked (layout : Layout) (image : NativeImage.View) : Prop where
  occupancy : CompareBranch image layout.entry layout.occupied .equal layout.bitReg layout.zeroReg
  install : layout.writes.Checked image
  filled : Jump image layout.writes.finish layout.accepted
  compare : CompareBranch image layout.occupied layout.refused .equal layout.heldReg layout.offeredReg
  repeated : Jump image (layout.occupied + 9) layout.accepted

inductive Action where
  | fill | retain | refuse
  deriving DecidableEq

def action (present held offered : Word) : Action :=
  if present = 0 then .fill else if held = offered then .retain else .refuse

def Action.steps : Action → ℕ
  | .fill | .retain => 5
  | .refuse => 4

def Action.exit (layout : Layout) : Action → ℕ
  | .fill | .retain => layout.accepted
  | .refuse => layout.refused

def Action.changed (action : Action) (words : Finset ℕ) : Finset ℕ :=
  if action = .fill then words else ∅

theorem Action.changed_subset (action : Action) (words : Finset ℕ) : action.changed words ⊆ words := by
  cases action <;> simp [Action.changed]

def Action.value (action : Action) (before filled : Word) : Word :=
  if action = .fill then filled else before

structure Inputs (layout : Layout) (state : Native) (pointer bit held offered : Word) : Prop where
  base : lookup state layout.encoding.base = some pointer
  bit : lookup state layout.bitReg = some bit
  held : lookup state layout.heldReg = some held
  offered : lookup state layout.offeredReg = some offered
  zero : lookup state layout.zeroReg = some 0
  one : lookup state layout.oneReg = some 1

private theorem outside_compare : ∀ r : Fin 16, key r ∉ ({.rflags, .rip} : Finset Register) := by
  decide +kernel

private theorem compare_data : ({.rflags, .rip} : Finset Register) ⊆ dataRegisters := by decide +kernel

private theorem equal_iff (left right : Word) : Comparison.equal.evaluate left right = true ↔ left = right := by
  simp [Comparison.evaluate]

/-- Execute the actual branches and stores. On a mismatch, there is
no store at all, not even a restore of the former binding. -/
theorem fetch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (layout : Layout) {image : NativeImage.View} (checked : layout.Checked image)
    {before : Native} {base : BitVec 48} (point : At image before base layout.entry)
    (controls : Controls before) (pointer bit held offered : Word) (input : Inputs layout before pointer bit held offered)
    (cells : Cells layout.writes pointer) (safeCode : CodeApart image base cells.writes)
    (readBit : Reads before cells.second.address bit) (readValue : Reads before cells.first.address held) :
    letI : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
    letI : VectorOpcodeHandlers := vector
    let result := action bit held offered
    ∃ after,
      (X86FuelPrefix.fetches result.steps).run before = .ok () after ∧
      X86StateFrame.Frame {.rflags, .rip} (result.changed cells.writes) before after ∧
      Reads after cells.second.address (result.value bit 1) ∧
      Reads after cells.first.address (result.value held offered) ∧
      Nonempty (At image after base (result.exit layout)) := by
  let : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨decided, entered, reg, ⟨atChoice⟩⟩ := X86PlacedScalar.compare_branch other extra vector point .equal
    layout.bitReg layout.zeroReg checked.occupancy bit (0#64) input.bit input.zero
  let frame := X86StateFrame.registerOnly reg
  have unchanged (r : Fin 16) : lookup decided r = lookup before r := frame.lookup r (outside_compare r)
  by_cases empty : bit = 0
  · have choice : Comparison.equal.evaluate bit (0#64) = true := (equal_iff _ _).mpr empty
    rw [choice] at atChoice
    have fallthrough : At image decided base layout.writes.start := atChoice
    obtain ⟨filled, wrote, written, term, mark, ⟨atJump⟩⟩ :=
      X86PlacedPairStore.stores (X86PlacedScalar.handlers other extra) vector fallthrough
        (controls.transport frame compare_data) checked.install pointer offered 1 cells safeCode
        ((unchanged _).trans input.base) ((unchanged _).trans input.offered) ((unchanged _).trans input.one)
    obtain ⟨after, finished, skip, reached⟩ := X86PlacedScalar.jump other extra vector atJump checked.filled
    have sequence := X86FuelPrefix.fetches_then 2 1 decided filled after wrote finished
    have total := X86FuelPrefix.fetches_then 2 3 before decided after entered sequence
    have memory := X86StateFrame.registerOnly skip
    have scope : X86StateFrame.Frame {.rflags, .rip} cells.writes before after :=
      ((frame.trans written).trans memory).mono (by simp) (by simp)
    simpa only [action, if_pos empty, Action.steps, Action.changed, Action.value, Action.exit, if_true] using
      (show ∃ after, (X86FuelPrefix.fetches 5).run before = .ok () after ∧
          X86StateFrame.Frame {.rflags, .rip} cells.writes before after ∧
          Reads after cells.second.address 1 ∧ Reads after cells.first.address offered ∧
          Nonempty (At image after base layout.accepted) from
        ⟨after, total, scope, mark.preserved memory (by simp), term.preserved memory (by simp), reached⟩)
  · have choice : Comparison.equal.evaluate bit (0#64) = false :=
      Bool.eq_false_iff.mpr (fun yes => empty ((equal_iff _ _).mp yes))
    have otherPath : At image decided base layout.occupied := by
      rw [choice] at atChoice
      exact atChoice
    obtain ⟨compared, comparison, heldFrame, ⟨atResult⟩⟩ := X86PlacedScalar.compare_branch other extra vector
      otherPath .equal layout.heldReg layout.offeredReg checked.compare held offered
      ((unchanged _).trans input.held) ((unchanged _).trans input.offered)
    have readOnly : X86StateFrame.Frame {.rflags, .rip} ∅ before compared :=
      (frame.trans (X86StateFrame.registerOnly heldFrame)).mono (by simp) (by simp)
    by_cases agrees : held = offered
    · have outcome : Comparison.equal.evaluate held offered = true := (equal_iff _ _).mpr agrees
      have atJump : At image compared base (layout.occupied + 9) := by simpa [outcome] using atResult
      obtain ⟨after, finished, skip, reached⟩ := X86PlacedScalar.jump other extra vector atJump checked.repeated
      have sequence := X86FuelPrefix.fetches_then 2 1 decided compared after comparison finished
      have total := X86FuelPrefix.fetches_then 2 3 before decided after entered sequence
      have scope : X86StateFrame.Frame {.rflags, .rip} ∅ before after :=
        (readOnly.trans (X86StateFrame.registerOnly skip)).mono (by simp) (by simp)
      simp only [action, if_neg empty, if_pos agrees, Action.steps, Action.changed, Action.value, Action.exit, reduceCtorEq,
        if_false]
      exact ⟨after, total, scope, readBit.preserved scope (by simp), readValue.preserved scope (by simp), reached⟩
    · have outcome : Comparison.equal.evaluate held offered = false :=
        Bool.eq_false_iff.mpr (fun yes => agrees ((equal_iff _ _).mp yes))
      have decided : At image compared base layout.refused := by simpa [outcome] using atResult
      have total := X86FuelPrefix.fetches_then 2 2 before _ compared entered comparison
      simp only [action, if_neg empty, if_neg agrees, Action.steps, Action.changed, Action.value, Action.exit, reduceCtorEq,
        if_false]
      exact ⟨compared, total, readOnly, readBit.preserved readOnly (by simp),
        readValue.preserved readOnly (by simp), ⟨decided⟩⟩

variable {σ : LPSignature}

def occupancy : Option (GroundTerm σ) → Word
  | none => 0
  | some _ => 1

structure View (codes : PackedOccurrences.Codes (GroundTerm σ)) (state : Native)
    (bitAddress valueAddress : BitVec 48) (binding : Option (GroundTerm σ)) (word : Word) : Prop where
  bit : Reads state bitAddress (occupancy binding)
  value : Reads state valueAddress word
  code : ∀ term, binding = some term → codes.encode term = some word

/-- The two native words represent the actual effect on the variable.
The slot holds its own value on rejection or repetition. -/
theorem fetched_binding [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (codes : PackedOccurrences.Codes (GroundTerm σ)) (table : BindingSlots.Table σ)
    (name : σ.vars) (term : GroundTerm σ) (offered : Word) (encoded : codes.encode term = some offered)
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (layout : Layout) {image : NativeImage.View} (checked : layout.Checked image)
    {before : Native} {base : BitVec 48} (point : At image before base layout.entry)
    (controls : Controls before) (pointer held : Word) (cells : Cells layout.writes pointer)
    (safeCode : CodeApart image base cells.writes)
    (view : View codes before cells.second.address cells.first.address (table name) held)
    (regs : Inputs layout before pointer (occupancy (table name)) held offered) :
    letI : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps words,
      (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame {.rflags, .rip} words before after ∧
      words ⊆ cells.writes ∧
      match BindingSlots.bind table name term with
      | none => words = ∅ ∧ View codes after cells.second.address cells.first.address (table name) held ∧
          Nonempty (At image after base layout.refused)
      | some following => ∃ result,
          View codes after cells.second.address cells.first.address (following name) result ∧
          Nonempty (At image after base layout.accepted) := by
  let : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, ran, frame, bit, value, reached⟩ :=
    fetch other extra vector layout checked point controls pointer _ held offered regs cells safeCode view.bit view.value
  refine ⟨after, _, _, ran, frame, Action.changed_subset _ _, ?_⟩
  cases present : table name with
  | none =>
    simp only [present, occupancy, action, Action.value, Action.exit] at bit value reached
    simp only [BindingSlots.bind, present, Function.update_self]
    exact ⟨offered, ⟨bit, value, fun g same => Option.some.inj same ▸ encoded⟩, reached⟩
  | some bound =>
    have existing := view.code bound present
    have equalEncoding := WordTests.code_equality codes existing encoded
    by_cases equalTerm : bound = term
    · have sameWord := equalEncoding.mpr equalTerm
      simp only [present, occupancy, action, BitVec.ofNat_eq_ofNat, if_pos sameWord, Action.value,
        Action.exit] at bit value reached
      simp only [BindingSlots.bind, present, if_pos equalTerm]
      exact ⟨held, ⟨bit, value, fun g same => Option.some.inj same ▸ existing⟩, reached⟩
    · have different : held ≠ offered := fun same => equalTerm (equalEncoding.mp same)
      simp only [present, occupancy, action, BitVec.ofNat_eq_ofNat, if_neg different, Action.value,
        Action.exit] at bit value reached
      simp only [BindingSlots.bind, present, if_neg equalTerm, occupancy, action, BitVec.ofNat_eq_ofNat,
        if_neg different, Action.changed]
      exact ⟨rfl, ⟨bit, value, fun g same => Option.some.inj same ▸ existing⟩, reached⟩

namespace Examples

theorem zero_can_be_a_filled_term : action 1 0 0 = .retain := by decide +kernel
theorem zero_conflicts_with_a_different_term : action 1 0 9 = .refuse := by decide +kernel
theorem a_stale_term_below_an_empty_bit_is_ignored : action 0 7 0 = .fill := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeBinding
