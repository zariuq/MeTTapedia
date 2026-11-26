import Mettapedia.Languages.MeTTa.SpaceTheory.NativeRenaming

/-!
# A module reference separates instance from spelling

Two names can read one instance. A renaming acts on its current atoms
and signature, not on its identity or on the store that owns it.
Instantiating a module is a different operation, interpreted by the
host's fresh-space semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.ModuleReferences

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.IndexedOperational (OperationalTranslation)

structure Reference (Identity : Type*) where
  instanceId : Identity
  names : Equiv.Perm String

def Reference.named {Identity : Type*} (instanceId : Identity) : Reference Identity :=
  ⟨instanceId, Equiv.refl _⟩

def Reference.rename {Identity : Type*} (ref : Reference Identity) (names : Equiv.Perm String) : Reference Identity :=
  ⟨ref.instanceId, ref.names.trans names⟩

def Reference.read {Identity : Type*} (ref : Reference Identity)
    (contents : Identity → Option (List Atom)) : Option (List Atom) :=
  (contents ref.instanceId).map (List.map (Renaming.atom ref.names))

@[simp] theorem rename_shares_instance {Identity : Type*} (ref : Reference Identity) (names : Equiv.Perm String) :
    (ref.rename names).instanceId = ref.instanceId := rfl

mutual
theorem rename_atom_comp (first second : String → String) (atom : Atom) :
    Renaming.atom second (Renaming.atom first atom) = Renaming.atom (second ∘ first) atom := by
  cases atom with
  | symbol | grounded | var => rfl
  | expression children =>
    simp only [Renaming.atom, rename_children_comp first second children]
termination_by sizeOf atom

theorem rename_children_comp (first second : String → String) (children : List Atom) :
    Renaming.childrenWith second (Renaming.childrenWith first children) =
      Renaming.childrenWith (second ∘ first) children := by
  cases children with
  | nil => rfl
  | cons firstAtom rest =>
    simp only [Renaming.childrenWith, rename_atom_comp first second firstAtom,
      rename_children_comp first second rest]
termination_by sizeOf children
end

mutual
theorem rename_atom_id (atom : Atom) : Renaming.atom id atom = atom := by
  cases atom with
  | symbol | var | grounded => rfl
  | expression children =>
    simp only [Renaming.atom, rename_children_id children]
termination_by sizeOf atom

theorem rename_children_id (children : List Atom) : Renaming.childrenWith id children = children := by
  cases children with
  | nil => rfl
  | cons atom rest => simp only [Renaming.childrenWith, rename_atom_id atom, rename_children_id rest]
termination_by sizeOf children
end

@[simp] theorem named_reads_original {Identity : Type*} (instanceId : Identity)
    (contents : Identity → Option (List Atom)) :
    (Reference.named instanceId).read contents = contents instanceId := by
  unfold Reference.named Reference.read
  cases supplied : contents instanceId with
  | none => rfl
  | some atoms =>
    change some (atoms.map (Renaming.atom id)) = some atoms
    simp only [show Renaming.atom id = id from funext rename_atom_id, List.map_id]

theorem renamed_read {Identity : Type*} (ref : Reference Identity) (names : Equiv.Perm String)
    (contents : Identity → Option (List Atom)) :
    (ref.rename names).read contents = (ref.read contents).map (List.map (Renaming.atom names)) := by
  unfold Reference.rename Reference.read
  cases saved : contents ref.instanceId with
  | none => rfl
  | some atoms =>
    simp only [Option.map_some, List.map_map]
    congr 1
    apply List.map_congr_left
    intro atom _
    exact (rename_atom_comp ref.names names atom).symm

/-- A write through the shared identity is visible under every spelling
of that instance. The proof says nothing about writing through an alias:
that requires separate authority. -/
theorem reads_after_update {Identity : Type*} [DecidableEq Identity] (ref : Reference Identity)
    (contents : Identity → Option (List Atom)) (atoms : List Atom) :
    ref.read (Function.update contents ref.instanceId (some atoms)) = some (atoms.map (Renaming.atom ref.names)) := by
  simp only [Reference.read, Function.update_self, Option.map_some]

theorem reads_other_instance {Identity : Type*} [DecidableEq Identity] (ref : Reference Identity)
    (contents : Identity → Option (List Atom)) (other : Identity) (atoms : List Atom)
    (different : ref.instanceId ≠ other) :
    ref.read (Function.update contents other (some atoms)) = ref.read contents := by
  simp only [Reference.read, Function.update_of_ne different]

def interpretation {Identity : Type*} (ref : Reference Identity)
    (tokens : NativeRenaming.FixesEquations ref.names) (atoms : List Atom) (firing : Atom → Atom → Prop) :
    OperationalTranslation (AtomEquations.theory atoms firing)
      (AtomEquations.theory (atoms.map (Renaming.atom ref.names))
        (Renaming.relation (Renaming.acts ref.names) firing)) :=
  NativeRenaming.operationMap ref.names tokens atoms firing

end Mettapedia.Languages.MeTTa.SpaceTheory.ModuleReferences
