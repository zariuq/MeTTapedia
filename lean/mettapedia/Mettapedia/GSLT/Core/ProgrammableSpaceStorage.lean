import Mettapedia.GSLT.Core.ProgrammableSpace

/-!
# Storage representations for declared programmable spaces

The source carrier is the exact list of stored occurrences. A physical
representation supplies a read operation and a writer with a proved reading
law. Lists and arrays instantiate the contract. A support-only representation
cannot implement this occurrence contract, since it identifies duplicates.

The lifting below concerns this mathematical representation boundary. It is
not a correctness theorem about a runtime allocator or its publication code.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ProgrammableSpace

universe u

structure Storage (Atom : Type u) where
  Carrier : Type u
  read : Carrier → List Atom
  write : List Atom → Carrier
  read_write : ∀ atoms, read (write atoms) = atoms

def listStorage (Atom : Type u) : Storage Atom where
  Carrier := List Atom
  read := id
  write := id
  read_write _ := rfl

def arrayStorage (Atom : Type u) : Storage Atom where
  Carrier := Array Atom
  read := Array.toList
  write := List.toArray
  read_write _ := List.toList_toArray

variable {Atom Tag : Type u} (languages : Tag → Language Atom)
  (policies : (tag : Tag) → Policy (languages tag)) (storage : Storage Atom)

structure StoredSpace where
  carrier : storage.Carrier
  pending : List (Work languages policies)
  history : List (Record languages policies)

def StoredSpace.read (stored : StoredSpace languages policies storage) :
    Space languages policies :=
  ⟨storage.read stored.carrier, stored.pending, stored.history⟩

def StoredSpace.write (source : Space languages policies) :
    StoredSpace languages policies storage :=
  ⟨storage.write source.atoms, source.pending, source.history⟩

theorem StoredSpace.read_write (source : Space languages policies) :
    StoredSpace.read languages policies storage
      (StoredSpace.write languages policies storage source) = source := by
  cases source
  simp [StoredSpace.read, StoredSpace.write, Storage.read_write]

/-- The implementation of one represented source event writes the entire
specified store and retains the actual source session and receipt. -/
inductive StoredStep : StoredSpace languages policies storage →
    StoredSpace languages policies storage → Prop where
  | write (before : StoredSpace languages policies storage)
      (after : Space languages policies)
      (source : Step languages policies
        (StoredSpace.read languages policies storage before) after) :
      StoredStep before
        (StoredSpace.write languages policies storage after)

theorem stored_step_reflects {before after : StoredSpace languages policies storage}
    (step : StoredStep languages policies storage before after) :
    Step languages policies
      (StoredSpace.read languages policies storage before)
      (StoredSpace.read languages policies storage after) := by
  cases step with
  | write after source =>
      rw [StoredSpace.read_write]
      exact source

theorem source_step_realized (before : StoredSpace languages policies storage)
    (after : Space languages policies)
    (step : Step languages policies
      (StoredSpace.read languages policies storage before) after) :
    ∃ physicalAfter : StoredSpace languages policies storage,
      StoredStep languages policies storage before physicalAfter ∧
      StoredSpace.read languages policies storage physicalAfter = after :=
  ⟨StoredSpace.write languages policies storage after, .write before after step,
    StoredSpace.read_write languages policies storage after⟩

theorem represented_run_reflects
    {before after : StoredSpace languages policies storage}
    (run : Relation.ReflTransGen (StoredStep languages policies storage) before after) :
    Relation.ReflTransGen (Step languages policies)
      (StoredSpace.read languages policies storage before)
      (StoredSpace.read languages policies storage after) := by
  induction run with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (stored_step_reflects languages policies storage step)

theorem represented_run_realized (before : StoredSpace languages policies storage)
    (after : Space languages policies)
    (run : Relation.ReflTransGen (Step languages policies)
      (StoredSpace.read languages policies storage before) after) :
    ∃ physicalAfter : StoredSpace languages policies storage,
      Relation.ReflTransGen (StoredStep languages policies storage) before physicalAfter ∧
      StoredSpace.read languages policies storage physicalAfter = after := by
  induction run with
  | refl => exact ⟨before, .refl, rfl⟩
  | tail _ step ih =>
      obtain ⟨physical, previous, reads⟩ := ih
      obtain ⟨next, realized, nextReads⟩ :=
        source_step_realized languages policies storage physical _ (reads.symm ▸ step)
      exact ⟨next, previous.tail realized, nextReads⟩

/-- Equal finite support cannot reconstruct the list of source occurrences. -/
theorem support_cannot_recover_occurrences (atom : Atom) :
    ¬ ∃ recover : (Atom → Prop) → List Atom,
      ∀ atoms : List Atom, recover (fun candidate => candidate ∈ atoms) = atoms := by
  rintro ⟨recover, recovers⟩
  have single := recovers [atom]
  have duplicate := recovers [atom, atom]
  have same : (fun candidate => candidate ∈ [atom]) =
      (fun candidate => candidate ∈ [atom, atom]) := by
    funext candidate
    apply propext
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self]
  have lists : [atom] = [atom, atom] := single.symm.trans ((congrArg recover same).trans duplicate)
  have lengths := congrArg List.length lists
  simp at lengths

theorem arrays_retain_duplicates (atom : Atom) :
    (arrayStorage Atom).read ((arrayStorage Atom).write [atom, atom]) = [atom, atom] :=
  (arrayStorage Atom).read_write _

end Mettapedia.GSLT.Core.ProgrammableSpace
