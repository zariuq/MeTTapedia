import Mettapedia.Machines.TIsa.X86OpcodeDispatch

/-!
# The pinned Sail prefix scanner and its checked recursion

The imported open recursion body retains the original range checks. The
implementation makes their decreasing counter available to Lean as a subtype.
Its unfolding and uniqueness theorems connect this implementation to the
original body. Qualifying the shadowed prefix type is a syntax-only adaptation.
Instruction-memory interpretation and the complete fetch theorem are separate.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2_000_000

namespace X86Registers.Functions

abbrev PrefixScanner := proc_mode → BitVec 48 → BitVec 52 → BitVec 8 → Nat →
  SailM (BitVec 52 × BitVec 8)

def checkedPredecessor (count : Nat) : SailM {previous : Nat // previous < count} := do
  let _ ← check_range 0 15 ((count : Int) - 1)
  if positive : 0 < count then pure ⟨count - 1, by omega⟩ else throw .Unreachable

end X86Registers.Functions

section
variable [X86Registers.MemoryPrimitives]

tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/PrefixFunctions.lean.inc"
  sha256 "a41bb5aba5aaffa54e739cc5b69505e4355ca39354da5cfa6183b67870f8b569"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]

end

namespace Mettapedia.Machines.TIsa.X86Prefix

open _root_.X86Registers X86RegisterRefinement
open _root_.X86Registers.Functions

theorem checkedPredecessor_bind {α : Type} (count : Nat) (next : Nat → SailM α) :
    (checkedPredecessor count >>= fun previous => next previous.val) =
      (check_range 0 15 ((count : Int) - 1) >>= fun previous => next previous.toNat) := by
  by_cases positive : 0 < count
  · have predecessor : ((count : Int) - 1).toNat = count - 1 := by omega
    simp only [checkedPredecessor, check_range, dif_pos positive, bind_assoc, pure_bind,
      predecessor]
  · have zero : count = 0 := by omega
    subst count
    rfl

theorem unfold_original [MemoryPrimitives] (mode : proc_mode) (address : BitVec 48)
    (prefixes : BitVec 52) (rex : BitVec 8) (count : Nat) :
    get_prefixes mode address prefixes rex count =
      get_prefixes_body get_prefixes mode address prefixes rex count := by
  rw [get_prefixes.eq_def]
  simp only [get_prefixes_body, checkedPredecessor_bind]

theorem checked_continuations_congr {α : Type} (count : Nat) (left right : Nat → SailM α)
    (agree : ∀ previous, previous < count → left previous = right previous) :
    (check_range 0 15 ((count : Int) - 1) >>= fun previous => left previous.toNat) =
      (check_range 0 15 ((count : Int) - 1) >>= fun previous => right previous.toNat) := by
  rw [← checkedPredecessor_bind, ← checkedPredecessor_bind]
  congr 1
  funext previous
  exact agree previous.val previous.property

theorem body_congr [MemoryPrimitives] (left right : PrefixScanner)
    (mode : proc_mode) (address : BitVec 48) (prefixes : BitVec 52) (rex : BitVec 8) (count : Nat)
    (agree : ∀ mode address prefixes rex previous, previous < count →
      left mode address prefixes rex previous = right mode address prefixes rex previous) :
    get_prefixes_body left mode address prefixes rex count =
      get_prefixes_body right mode address prefixes rex count := by
  have step : ∀ mode address prefixes rex,
      (check_range 0 15 ((count : Int) - 1) >>= fun previous =>
        left mode address prefixes rex previous.toNat) =
      (check_range 0 15 ((count : Int) - 1) >>= fun previous =>
        right mode address prefixes rex previous.toNat) := by
    intro mode address prefixes rex
    exact checked_continuations_congr count _ _ (agree mode address prefixes rex)
  simp only [get_prefixes_body, step]

theorem unique [MemoryPrimitives] (other : PrefixScanner)
    (equation : ∀ mode address prefixes rex count,
      other mode address prefixes rex count =
        get_prefixes_body other mode address prefixes rex count)
    (mode : proc_mode) (address : BitVec 48) (prefixes : BitVec 52) (rex : BitVec 8) (count : Nat) :
    other mode address prefixes rex count = get_prefixes mode address prefixes rex count := by
  induction count using Nat.strong_induction_on generalizing mode address prefixes rex with
  | h count induction =>
    calc
      other mode address prefixes rex count =
          get_prefixes_body other mode address prefixes rex count := equation ..
      _ = get_prefixes_body get_prefixes mode address prefixes rex count := by
        apply body_congr
        intro mode address prefixes rex previous lower
        exact induction previous lower mode address prefixes rex
      _ = get_prefixes mode address prefixes rex count := (unfold_original ..).symm

namespace Controls

example (state : State) : (checkedPredecessor 15).run state =
    .ok ⟨14, by decide⟩ state := rfl

theorem zero_count_refused (state : State) : (checkedPredecessor 0).run state =
    .error (.Assertion "prelude.sail:171.23-171.24") state := rfl

theorem excessive_count_refused (state : State) : (checkedPredecessor 17).run state =
    .error (.Assertion "prelude.sail:171.23-171.24") state := rfl

theorem scan_zero [MemoryPrimitives] (state : State) (mode : proc_mode)
    (address : BitVec 48) (prefixes : BitVec 52) (rex : BitVec 8) :
    (get_prefixes mode address prefixes rex 0).run state = .ok (prefixes, rex) state := by
  rw [unfold_original]
  rfl

end Controls


end Mettapedia.Machines.TIsa.X86Prefix
