import Mettapedia.Computability.KolmogorovComplexity.Basic
import Mettapedia.UniversalAI.TimeBoundedAIXI.ProofEnumeration
import Mathlib.Computability.Primrec.List

/-!
# Effective finite binary enumeration and fixed-width index words

The enumerators and their order are the existing proof-enumeration interface.
This adds computability, exact cardinalities and an index decoder without
creating a second binary enumeration. Fixed-width words retain leading zeros;
their index is not an arbitrary encodable natural-number representation.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FiniteBitStrings

open Mettapedia.UniversalAI.TimeBoundedAIXI

theorem bitstringsOfLength_nodup (length : Nat) : (bitstringsOfLength length).Nodup := by
  induction length with
  | zero => simp [bitstringsOfLength]
  | succ length ih =>
      rw [bitstringsOfLength, List.nodup_flatMap]
      constructor
      · intro word _member
        simp
      · exact ih.imp (by
          intro first second different
          change List.Disjoint [false :: first, true :: first] [false :: second, true :: second]
          rw [List.disjoint_left]
          intro word one two
          simp at one two
          rcases one with rfl | rfl <;> rcases two with same | same <;> simp_all)

theorem bitstringsUpTo_nodup (phase : Nat) : (bitstringsUpTo phase).Nodup := by
  induction phase with
  | zero => exact bitstringsOfLength_nodup 0
  | succ phase ih =>
      rw [bitstringsUpTo, List.nodup_append]
      refine ⟨ih, bitstringsOfLength_nodup _, ?_⟩
      intro first early second current same
      have small := length_le_of_mem_bitstringsUpTo early
      have large := length_eq_of_mem_bitstringsOfLength current
      subst second
      omega

theorem bitstringsOfLength_primrec : Primrec bitstringsOfLength := by
  have pair : Primrec fun bits : BinString => [false :: bits, true :: bits] :=
    Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const false) Primrec.id)
      (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const true) Primrec.id) (Primrec.const []))
  have step : Primrec₂ fun (_n : Nat) (previous : List BinString) =>
      previous.flatMap (fun bits => [false :: bits, true :: bits]) :=
    (Primrec.list_flatMap Primrec.snd (pair.comp Primrec.snd).to₂).to₂
  exact (Primrec.nat_rec₁ ([[]] : List BinString) step).of_eq (by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [bitstringsOfLength, ih])

theorem bitstringsUpTo_primrec : Primrec bitstringsUpTo := by
  have step : Primrec₂ fun n (previous : List BinString) => previous ++ bitstringsOfLength (n + 1) :=
    (Primrec.list_append.comp Primrec.snd
      (bitstringsOfLength_primrec.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 1)))).to₂
  exact (Primrec.nat_rec₁ ([[]] : List BinString) step).of_eq (by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [bitstringsUpTo, ih])

theorem bitstringsOfLength_length (n : Nat) : (bitstringsOfLength n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bitstringsOfLength, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

theorem bitstringsUpTo_length_add_one (n : Nat) : (bitstringsUpTo n).length + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [bitstringsUpTo, List.length_append, bitstringsOfLength_length]
      rw [pow_succ]
      omega

theorem listBEq_eq_decidable {α : Type} [DecidableEq α] : List.instBEq =
    @instBEqOfDecidableEq (List α) instDecidableEqList := by
  apply congrArg BEq.mk
  funext first second
  change (first == second) = _
  rw [Bool.eq_iff_iff, @beq_iff_eq _ (_), decide_eq_true_iff]

def fixedRank (bits : BinString) : Nat := (bitstringsOfLength bits.length).idxOf bits

theorem wordIndex_primrec : Primrec₂ fun (bits : BinString) (words : List BinString) => words.idxOf bits := by
  exact Primrec.list_idxOf.of_eq (fun bits words => congrArg
    (fun comparison : BEq BinString => @List.idxOf BinString comparison bits words)
    (listBEq_eq_decidable (α := Bool)).symm)

theorem fixedRank_primrec : Primrec fixedRank :=
  wordIndex_primrec.comp Primrec.id (bitstringsOfLength_primrec.comp Primrec.list_length)

theorem fixedRank_lt (bits : BinString) : fixedRank bits < 2 ^ bits.length := by
  rw [← bitstringsOfLength_length]
  exact List.idxOf_lt_length_iff.mpr (mem_bitstringsOfLength_self bits)

theorem fixedRank_surjective (width index : Nat) (bounded : index < 2 ^ width) :
    ∃ bits : BinString, bits.length = width ∧ fixedRank bits = index := by
  have inBounds : index < (bitstringsOfLength width).length := by
    simpa only [bitstringsOfLength_length] using bounded
  let bits := (bitstringsOfLength width)[index]
  have member : bits ∈ bitstringsOfLength width := List.getElem_mem inBounds
  have length : bits.length = width := length_eq_of_mem_bitstringsOfLength member
  refine ⟨bits, length, ?_⟩
  unfold fixedRank
  rw [length]
  exact (bitstringsOfLength_nodup width).idxOf_getElem index inBounds

theorem fixedRank_of_get {width index : Nat} {bits : BinString}
    (selected : (bitstringsOfLength width)[index]? = some bits) : bits.length = width ∧ fixedRank bits = index := by
  obtain ⟨inBounds, same⟩ := List.getElem?_eq_some_iff.mp selected
  have length : bits.length = width := length_eq_of_mem_bitstringsOfLength (List.mem_of_getElem? selected)
  refine ⟨length, ?_⟩
  unfold fixedRank
  rw [length, ← same]
  exact (bitstringsOfLength_nodup width).idxOf_getElem index inBounds

end KolmogorovComplexity.FiniteBitStrings
