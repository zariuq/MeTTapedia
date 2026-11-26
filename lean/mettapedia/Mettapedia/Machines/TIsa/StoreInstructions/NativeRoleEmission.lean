import Mettapedia.Machines.TIsa.StoreInstructions.NativeRoleGate

/-!
# Emitting the role gate

The code consists of one identity load and a sequence of
load/compare/branch probes. Branches share a refusal target.
Images smaller than the signed rel32 range need no per-probe
displacement test once all their endpoints are placed.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeRoleEmission

open X86PlacedScalar (Code registerCode compareDelta)
open NativeRoleGate (WordAt Probe Placed Gate)
open MemoryBinding (bitWire termWire)

variable {slot candidate : Word}

private def comparison : List ℕ := registerCode 0x39 0 2

private def rejection (start refused : ℕ) : List ℕ :=
  X86NativeJcc.code (X86PreparedCompare.negative .notEqual) (compareDelta (start + 7) refused)

def probe (spot : WordAt slot) (start refused : ℕ) : List ℕ :=
  spot.source.bytes bitWire ++ (comparison ++ rejection start refused)

def scan (refused : ℕ) : ℕ → List (WordAt slot) → List ℕ
  | _, [] => []
  | start, spot :: rest => probe spot start refused ++ scan refused (start + 16) rest

def emit (identity : WordAt candidate) (spots : List (WordAt slot)) (start refused : ℕ) : List ℕ :=
  identity.source.bytes termWire ++ scan refused (start + 7) spots

private theorem load_size (spot : WordAt slot) (wiring : NativeWords.Wiring) :
    (spot.source.bytes wiring).length = 7 := spot.source.bytes_length wiring

private theorem comparison_size : comparison.length = 3 := rfl

theorem probe_size (spot : WordAt slot) (start refused : ℕ) : (probe spot start refused).length = 16 := by
  simp only [probe, List.length_append, load_size, comparison_size, rejection, X86NativeJcc.code_length]

theorem scan_size (refused : ℕ) (start : ℕ) (spots : List (WordAt slot)) :
    (scan refused start spots).length = 16 * spots.length := by
  induction spots generalizing start with
  | nil => rfl
  | cons spot rest ih =>
    rw [scan, List.length_append, probe_size, ih, List.length_cons]
    omega

theorem size (identity : WordAt candidate) (spots : List (WordAt slot)) (start refused : ℕ) :
    (emit identity spots start refused).length = 7 + 16 * spots.length := by
  simp only [emit, List.length_append, load_size, scan_size]

private theorem checked_probe (image : NativeImage.View) (start refused : ℕ) (spot : WordAt slot)
    (room : start + 16 ≤ image.size) (target : refused ≤ image.size)
    (short : image.size < 2 ^ 31) (placed : Code image start (probe spot start refused)) :
    Probe image start refused spot := by
  obtain ⟨load, rest⟩ := NativeWords.code_append (show Code image start
    (spot.source.bytes bitWire ++ (comparison ++ rejection start refused)) from placed)
  rw [load_size] at rest
  obtain ⟨test, branch⟩ := NativeWords.code_append rest
  rw [comparison_size] at branch
  refine ⟨by omega, load, ?_, target, ?_, test, branch⟩
  · omega
  · unfold compareDelta
    rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
    omega

theorem checked_scan (image : NativeImage.View) (start refused : ℕ) (spots : List (WordAt slot))
    (room : start + 16 * spots.length ≤ image.size) (target : refused ≤ image.size)
    (short : image.size < 2 ^ 31) (placed : Code image start (scan refused start spots)) :
    Placed image refused start (start + 16 * spots.length) spots := by
  induction spots generalizing start with
  | nil => exact .nil start
  | cons spot rest ih =>
    obtain ⟨head, tail⟩ := NativeWords.code_append (show Code image start
      (probe spot start refused ++ scan refused (start + 16) rest) from placed)
    rw [probe_size] at tail
    have first := checked_probe image start refused spot
      (by simp only [List.length_cons] at room; omega) target short head
    have later := ih (start + 16) (by simp only [List.length_cons] at room; omega) tail
    rw [show start + 16 * (spot :: rest).length = (start + 16) + 16 * rest.length by
      simp only [List.length_cons]; omega]
    exact .cons first later

theorem checked_of_emitted (image : NativeImage.View) (start refused : ℕ) (identity : WordAt candidate)
    (spots : List (WordAt slot)) (room : start + (emit identity spots start refused).length ≤ image.size)
    (target : refused ≤ image.size) (short : image.size < 2 ^ 31)
    (installed : Code image start (emit identity spots start refused)) :
    Gate image start (start + 7 + 16 * spots.length) refused identity spots := by
  obtain ⟨load, rest⟩ := NativeWords.code_append (show Code image start
    (identity.source.bytes termWire ++ scan refused (start + 7) spots) from installed)
  rw [load_size] at rest
  rw [size] at room
  exact ⟨by omega, load, checked_scan image (start + 7) refused spots (by omega) target short rest⟩

namespace Examples

private def offered : WordAt 0x1000 :=
  ⟨0, ⟨0x1000, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private def held : WordAt 0x2000 :=
  ⟨0, ⟨0x2000, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

private def image : NativeImage.View :=
  NativeImage.View.ofArray (((emit offered [held] 0 24) ++ [0x90]).map (BitVec.ofNat 8)).toArray

theorem one_probe_emits_a_checked_gate : Gate image 0 23 24 offered [held] :=
  checked_of_emitted image 0 24 offered [held] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem a_different_refusal_target_is_not_the_installed_code :
    ¬ Code image 0 (emit offered [held] 0 25) := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeRoleEmission
