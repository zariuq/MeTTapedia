import Mettapedia.Machines.TIsa.StoreInstructions.NativeObservationEntry

/-!
# Refusal and funding before physical publication

A failed observation never spends fuel. An accepted firing
with zero allowance likewise cannot enter publication. The
gate writes no memory and spends exactly one unit only on
the edge to the prepared successor.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeFiringGate

open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedInstruction (At)
open X86PlacedScalar (Code CompareBranch registerCode)
open X86PlacedMemory (Controls)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def chargeCode : List ℕ := registerCode (X86Arithmetic.opcode .sub) 13 14

def emit (start refuse exhausted : ℕ) : List ℕ :=
  NativeDecisions.compareBytes .notEqual 0 12 start refuse ++
    (NativeDecisions.compareBytes .lessEqualUnsigned 13 14 (start + 9) exhausted ++ chargeCode)

theorem emit_size (start refuse exhausted : ℕ) : (emit start refuse exhausted).length = 21 := by
  simp only [emit, List.length_append, NativeDecisions.compare_size, show chargeCode.length = 3 from rfl]

structure Placed (image : NativeImage.View) (start refuse exhausted : ℕ) : Prop where
  extent : start + 21 ≤ image.size
  observed : CompareBranch image start refuse .notEqual 0 12
  available : CompareBranch image (start + 9) exhausted .lessEqualUnsigned 13 14
  spends : Code image (start + 18) chargeCode

theorem placed_of_emitted (image : NativeImage.View) (start refuse exhausted : ℕ)
    (extent : start + 21 ≤ image.size) (no : refuse ≤ image.size) (shortFuel : exhausted ≤ image.size)
    (short : image.size < 2 ^ 31) (code : Code image start (emit start refuse exhausted)) :
    Placed image start refuse exhausted := by
  obtain ⟨observed, tail⟩ := NativeWords.code_append (show Code image start
    (NativeDecisions.compareBytes .notEqual 0 12 start refuse ++ _) from code)
  rw [NativeDecisions.compare_size] at tail
  obtain ⟨available, pay⟩ := NativeWords.code_append tail
  rw [NativeDecisions.compare_size] at pay
  exact ⟨extent, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) no short observed,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) shortFuel short available, pay⟩

inductive Decision where
  | refused | exhausted | paid (unspent : Word)
  deriving DecidableEq

def decideFiring (confirmed : Bool) (allowance : Word) : Decision :=
  if confirmed then if allowance < (1 : Word) then .exhausted else .paid (allowance - 1) else .refused

def Decision.target (start refuse exhausted : ℕ) : Decision → ℕ
  | .refused => refuse
  | .exhausted => exhausted
  | .paid _ => start + 21

def Decision.steps : Decision → ℕ
  | .refused => 2
  | .exhausted => 4
  | .paid _ => 5

def Decision.allowance (initial : Word) : Decision → Word
  | .paid remaining => remaining
  | _ => initial

abbrev clobbers : Finset Register := {.r14, .rflags, .rip}
private abbrev onlyBranch : Finset Register := {.rflags, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide
noncomputable abbrev handlers := X86IndexedAddress.handlers

private theorem compare_allowance (balance : Word) :
    Comparison.evaluate .lessEqualUnsigned (1 : Word) balance = decide (¬ balance < (1 : Word)) := by
  change decide ((1 : Word).toNat ≤ balance.toNat) = decide (¬ balance < (1 : Word))
  by_cases h : balance < (1 : Word)
  · have small : balance.toNat < (1 : Word).toNat := h
    exact (decide_eq_false (Nat.not_le_of_lt small)).trans (decide_eq_false (fun no => no h)).symm
  · have enough : (1 : Word).toNat ≤ balance.toNat := Nat.le_of_not_gt h
    exact (decide_eq_true enough).trans (decide_eq_true h).symm

/-- The source's refusal and funding choices agree with
the fetched branch and subtraction. On either refusal the
initial allowance is still physically present. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start refuse exhausted : ℕ} {before : Native}
    (code : Placed image start refuse exhausted) (point : At image before base start)
    (confirmed : Bool) (balance : Word)
    (bit : lookup before 0 = some (booleanWord confirmed)) (zero : lookup before 12 = some 0)
    (one : lookup before 13 = some 1) (fund : lookup before 14 = some balance) :
    let decision := decideFiring confirmed balance
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches decision.steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧ lookup after 14 = some (decision.allowance balance) ∧
      Nonempty (At image after base (decision.target start refuse exhausted)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨a, ran, tested, ⟨route⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector point .notEqual 0 12 code.observed _ _ bit zero
  have first := X86StateFrame.registerOnly tested
  cases confirmed
  · exact ⟨a, ran, first.mono (by decide) (Finset.Subset.refl _), (first.lookup 14 (by decide)).trans fund, ⟨route⟩⟩
  · have opens : At image a base (start + 9) := route
    obtain ⟨b, checked, enough, ⟨status⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
      extra vector opens .lessEqualUnsigned 13 14 code.available 1 balance
        ((first.lookup 13 (by decide)).trans one) ((first.lookup 14 (by decide)).trans fund)
    rw [compare_allowance] at status
    have framed : X86StateFrame.Frame onlyBranch ∅ before b :=
      (first.trans (X86StateFrame.registerOnly enough)).mono (by simp) (by simp)
    have through := X86FuelPrefix.fetches_then 2 2 before a b ran checked
    by_cases insufficient : balance < (1 : Word)
    · have checked : decide (¬ balance < (1 : Word)) = false := decide_eq_false (fun h => h insufficient)
      rw [checked] at status
      have failed : At image b base exhausted := status
      simp only [decideFiring, if_true, if_pos insufficient, Decision.steps, Decision.allowance, Decision.target]
      exact ⟨b, through, framed.mono (by decide) (Finset.Subset.refl _), (framed.lookup 14 (by decide)).trans fund, ⟨failed⟩⟩
    · have checked : decide (¬ balance < (1 : Word)) = true := decide_eq_true insufficient
      rw [checked] at status
      have ready : At image b base (start + 18) := status
      obtain ⟨after, paid, changed, remaining, endpoint⟩ := X86PlacedArithmetic.executes (handlers other extra)
        vector ready code.extent .sub 13 14 balance 1
        ((framed.lookup 13 (by decide)).trans one) ((framed.lookup 14 (by decide)).trans fund) code.spends
      have linked : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
      rw [linked] at paid
      have all : X86StateFrame.Frame clobbers ∅ before after :=
        (framed.trans (X86StateFrame.registerOnly changed)).mono (by decide) (by simp)
      simp only [decideFiring, if_true, if_neg insufficient, Decision.steps, Decision.allowance, Decision.target]
      exact ⟨after, X86FuelPrefix.fetches_then 4 1 before b after through paid, all, remaining, endpoint⟩

namespace Examples

theorem funded_success_spends_once : decideFiring true 9 = .paid 8 := by decide +kernel
theorem unsuccessful_observation_does_not_enter_the_write_block : decideFiring false 9 = .refused := by decide +kernel
theorem accepted_but_unfunded_never_enters_the_write_block : decideFiring true 0 = .exhausted := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeFiringGate
