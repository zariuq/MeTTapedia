import Mettapedia.Machines.TIsa.StoreInstructions.WordTests

/-!
# Emitting the instantiated equality block

Both branches materialize a word boolean and converge at the end of
the image. All relocations are internal. The emitted byte vector
satisfies the actual code premises of the fetched TEST proof.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.WordTestImage

open X86PlacedScalar (Code registerCode compareDelta jumpDelta)

private abbrev imageOf (numbers : List ℕ) : NativeImage.View :=
  NativeImage.View.ofArray ((numbers.map (.ofNat 8)).toArray)

private theorem range_from
    (view : NativeImage.View) (base : ℕ) (wanted : List NativeImage.Byte)
    (known : ∀ (i : ℕ) (within : i < wanted.length), view.read (base + i) = some wanted[i]) :
    NativeImage.readRange? view base wanted.length = some wanted := by
  induction wanted generalizing base with
  | nil => rfl
  | cons first later ih =>
    have firstRead := known 0 (by simp)
    change view.read (base + 0) = some first at firstRead
    have tail : ∀ (i : ℕ) (within : i < later.length), view.read (base + 1 + i) = some later[i] := by
      intro i within
      have nxt := known (i + 1) (by simp; omega)
      change view.read (base + (i + 1)) = some later[i] at nxt
      simpa only [Nat.add_assoc, Nat.add_comm i 1] using nxt
    unfold NativeImage.readRange? at *
    rw [List.length_cons, List.range_succ_eq_map, List.mapM_cons, firstRead]
    simp only [bind, Option.bind_some, List.mapM_map, Function.comp_def]
    have inc : (fun i : ℕ => view.read (base + Nat.succ i)) = (fun i => view.read (base + 1 + i)) := by
      funext i
      congr 1
      omega
    rw [inc, ih (base + 1) tail]
    rfl

private theorem code_segment (earlier piece later : List ℕ) :
    Code (imageOf (earlier ++ piece ++ later)) earlier.length piece := by
  have length : (piece.map (BitVec.ofNat 8)).length = piece.length := List.length_map _
  show NativeImage.readRange? (imageOf (earlier ++ piece ++ later)) earlier.length piece.length = _
  rw [← length]
  apply range_from
  intro i within
  have valid : i < piece.length := by simpa only [List.length_map] using within
  change ((earlier ++ piece ++ later).map (BitVec.ofNat 8)).toArray[earlier.length + i]? =
    some (piece.map (BitVec.ofNat 8))[i]
  rw [List.getElem?_toArray, List.getElem?_map, List.append_assoc,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left valid, List.getElem?_eq_getElem valid]
  simp only [Option.map_some, List.getElem_map]

private def cmp (left right : Fin 16) := registerCode 0x39 right left
private def reject := X86NativeJcc.code (X86PreparedCompare.negative .equal) (compareDelta 0 20)
private def yes (result : Fin 16) := X86Immediate32.code result 1
private def no (result : Fin 16) := X86Immediate32.code result 0
private def yesDone := X86UnconditionalJump.Block.code (jumpDelta 15 31)
private def noDone := X86UnconditionalJump.Block.code (jumpDelta 26 31)

def bytes (left right result : Fin 16) : List ℕ :=
  cmp left right ++ reject ++ yes result ++ yesDone ++ no result ++ noDone

def image (left right result : Fin 16) : NativeImage.View :=
  imageOf (bytes left right result)

theorem bytes_length (left right result : Fin 16) : (bytes left right result).length = 31 := by
  simp [bytes, cmp, registerCode, reject, yes, no, yesDone, noDone, X86NativeJcc.code_length,
    X86Immediate32.code_length, X86UnconditionalJump.Block.code_length]

theorem emitted_block (left right result : Fin 16) :
    WordTests.Block (image left right result) 0 20 31 left right result := by
  have extent : (image left right result).size = 31 := by
    simp only [image, imageOf, NativeImage.View.ofArray, List.size_toArray, List.length_map, bytes_length]
  have jumpYes : X86PlacedScalar.Jump (image left right result) 15 31 := by
    refine ⟨by omega, by omega, by decide +kernel, ?_⟩
    have here := code_segment (cmp left right ++ reject ++ yes result) yesDone (no result ++ noDone)
    simpa [image, bytes, List.append_assoc, cmp, registerCode, reject, yes, no, yesDone,
      X86NativeJcc.code_length, X86Immediate32.code_length] using here
  have jumpNo : X86PlacedScalar.Jump (image left right result) 26 31 := by
    refine ⟨by omega, by omega, by decide +kernel, ?_⟩
    have here := code_segment (cmp left right ++ reject ++ yes result ++ yesDone ++ no result) noDone []
    simpa [image, bytes, cmp, registerCode, reject, yes, no, yesDone, noDone, X86NativeJcc.code_length,
      X86Immediate32.code_length, X86UnconditionalJump.Block.code_length] using here
  refine ⟨⟨by omega, by omega, by decide +kernel, ?_, ?_⟩, by omega, by omega, ?_, ?_, jumpYes, jumpNo⟩
  · have here := code_segment [] (cmp left right) (reject ++ yes result ++ yesDone ++ no result ++ noDone)
    simpa [image, bytes, cmp, List.append_assoc] using here
  · have here := code_segment (cmp left right) reject (yes result ++ yesDone ++ no result ++ noDone)
    simpa [image, bytes, cmp, registerCode, reject, List.append_assoc] using here
  · have here := code_segment (cmp left right ++ reject) (yes result) (yesDone ++ no result ++ noDone)
    simpa [image, bytes, cmp, registerCode, reject, yes, X86NativeJcc.code_length, List.append_assoc] using here
  · have here := code_segment (cmp left right ++ reject ++ yes result ++ yesDone) (no result) noDone
    simpa [image, bytes, cmp, registerCode, reject, yes, no, yesDone, X86NativeJcc.code_length,
      X86Immediate32.code_length, X86UnconditionalJump.Block.code_length] using here

end Mettapedia.Machines.TIsa.StoreInstructions.WordTestImage
