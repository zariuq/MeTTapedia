import Mettapedia.Languages.Metamath.MM2CompressedProofExecution

/-!
# Exact finite cursor spine for compressed MM2 indices

The compact verifier walks heap, node, and stack positions through explicit
successor rows.  This module characterizes those rows by natural-number
occurrence, connecting the logarithmic Appendix-B atom representation to the
finite cursor GSLTs used by the semantic transformations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedIndexSpine

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution

namespace CanonicalIndexCode

/-- Canonical compact codes retain their represented natural number. -/
theorem ofNat_injective : Function.Injective CompressedIndexCode.ofNat := by
  intro left right equal
  have values := congrArg CompressedIndexCode.value equal
  simpa only [CompressedIndexCode.ofNat_value] using values

/-- The MM2 atom encoding retains both fields of a compact index code. -/
theorem atom_injective : Function.Injective CompressedIndexCode.atom := by
  rintro ⟨leftPrefix, leftTerminal⟩ ⟨rightPrefix, rightTerminal⟩ equal
  have atomsEqual := Atom.expression.inj equal
  have fieldsEqual := (List.cons.inj atomsEqual).2
  have prefixEqual := (List.cons.inj fieldsEqual).1
  have terminalEqual := (List.cons.inj (List.cons.inj fieldsEqual).2).1
  congr
  · exact MM2DataEncoding.listAtom_injective MM2DataEncoding.natAtom
      MM2DataEncoding.decodeNatAtom MM2DataEncoding.decodeNatAtom_natAtom
      prefixEqual
  · exact MM2DataEncoding.natAtom_injective terminalEqual

@[simp] theorem ofNat_succ (position : Nat) :
    CompressedIndexCode.ofNat (position + 1) =
      (CompressedIndexCode.ofNat position).next := by
  rfl

end CanonicalIndexCode

/-- Natural-number presentation of a finite compact successor spine. -/
def indexedSuccessorRowsFrom (owner : Atom) : Nat → Nat → List Atom
  | _, 0 => []
  | position, count + 1 =>
      compressedIndexSuccessorRow owner
          (CompressedIndexCode.ofNat position).atom
          (CompressedIndexCode.ofNat (position + 1)).atom ::
        indexedSuccessorRowsFrom owner (position + 1) count

/-- The executable compact-code generator is exactly the occurrence-indexed
natural-number presentation, at every starting position. -/
theorem compressedIndexSuccessorRowsFrom_ofNat (owner : Atom)
    (position count : Nat) :
    compressedIndexSuccessorRowsFrom owner count
        (CompressedIndexCode.ofNat position) =
      indexedSuccessorRowsFrom owner position count := by
  induction count generalizing position with
  | zero => rfl
  | succ count induction =>
      simp only [compressedIndexSuccessorRowsFrom,
        indexedSuccessorRowsFrom, CanonicalIndexCode.ofNat_succ]
      congr 1
      exact induction (position + 1)

theorem mem_indexedSuccessorRowsFrom_iff (owner row : Atom)
    (position count : Nat) :
    row ∈ indexedSuccessorRowsFrom owner position count ↔
      ∃ offset < count,
        row = compressedIndexSuccessorRow owner
          (CompressedIndexCode.ofNat (position + offset)).atom
          (CompressedIndexCode.ofNat (position + offset + 1)).atom := by
  induction count generalizing position with
  | zero => simp [indexedSuccessorRowsFrom]
  | succ count induction =>
      constructor
      · intro member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨0, by omega, by simp⟩
        · obtain ⟨offset, bound, exactRow⟩ :=
            (induction (position + 1)).mp member
          refine ⟨offset + 1, by omega, ?_⟩
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            exactRow
      · rintro ⟨offset, bound, exactRow⟩
        cases offset with
        | zero =>
            apply List.mem_cons.mpr
            left
            simpa using exactRow
        | succ offset =>
            apply List.mem_cons.mpr
            right
            apply (induction (position + 1)).mpr
            refine ⟨offset, by omega, ?_⟩
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              exactRow

/-- Exact membership theorem for the finite compact successor rows emitted by
the source-data transformation. -/
theorem mem_compressedIndexSuccessorRows_iff (owner row : Atom)
    (count : Nat) :
    row ∈ compressedIndexSuccessorRows owner count ↔
      ∃ position < count,
        row = compressedIndexSuccessorRow owner
          (CompressedIndexCode.ofNat position).atom
          (CompressedIndexCode.ofNat (position + 1)).atom := by
  rw [compressedIndexSuccessorRows,
    show CompressedIndexCode.zero = CompressedIndexCode.ofNat 0 from rfl,
    compressedIndexSuccessorRowsFrom_ofNat owner 0 count,
    mem_indexedSuccessorRowsFrom_iff]
  simp

/-- Positive occurrence-indexed constructor for a concrete target cursor
edge. -/
theorem compressedIndexSuccessorRow_mem (owner : Atom)
    (count position : Nat) (inBounds : position < count) :
    compressedIndexSuccessorRow owner
        (CompressedIndexCode.ofNat position).atom
        (CompressedIndexCode.ofNat (position + 1)).atom ∈
      compressedIndexSuccessorRows owner count := by
  exact (mem_compressedIndexSuccessorRows_iff owner _ count).2
    ⟨position, inBounds, rfl⟩

/-- Negative control: no successor row is emitted at the finite frontier. -/
theorem compressedIndexFrontier_has_no_successor (owner : Atom)
    (count : Nat) :
    compressedIndexSuccessorRow owner
        (CompressedIndexCode.ofNat count).atom
        (CompressedIndexCode.ofNat (count + 1)).atom ∉
      compressedIndexSuccessorRows owner count := by
  intro member
  obtain ⟨position, bound, equal⟩ :=
    (mem_compressedIndexSuccessorRows_iff owner _ count).1 member
  have currentEqual :
      (CompressedIndexCode.ofNat count).atom =
        (CompressedIndexCode.ofNat position).atom := by
    have atomsEqual := Atom.expression.inj equal
    exact (List.cons.inj (List.cons.inj (List.cons.inj atomsEqual).2).2).1
  have codeEqual :
      CompressedIndexCode.ofNat count =
        CompressedIndexCode.ofNat position :=
    CanonicalIndexCode.atom_injective currentEqual
  have positionEqual : count = position :=
    CanonicalIndexCode.ofNat_injective codeEqual
  omega

#print axioms CanonicalIndexCode.ofNat_injective
#print axioms CanonicalIndexCode.atom_injective
#print axioms compressedIndexSuccessorRowsFrom_ofNat
#print axioms mem_indexedSuccessorRowsFrom_iff
#print axioms mem_compressedIndexSuccessorRows_iff
#print axioms compressedIndexSuccessorRow_mem
#print axioms compressedIndexFrontier_has_no_successor

end Mettapedia.Languages.Metamath.MM2CompressedIndexSpine
