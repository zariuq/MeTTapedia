import Mettapedia.Languages.MeTTa.SpaceTheory.ModuleTheories
import Mettapedia.Languages.MeTTa.SpaceTheory.ModuleReferences

/-!
# Linked and local HE module extensions

Linking is the existing live dependency operation. Including a block of
atoms is repeated source addition to the destination's own space. The
two can contribute the same authored equations without having the same
mutation, listing, or first-answer behavior.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEModuleModes

open Mettapedia.Languages.MeTTa.HE (Space ModuleNode ModuleStore ModId)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.IndexedOperational (OperationalTranslation)
open ModuleReferences (Reference)

def includeAtoms (destination : ModuleNode) (atoms : List Atom) : ModuleNode :=
  atoms.foldl ModuleNode.addOwn destination

theorem include_listing (destination : ModuleNode) (atoms : List Atom) :
    (includeAtoms destination atoms).listing = atoms.reverse ++ destination.listing := by
  induction atoms generalizing destination with
  | nil => rfl
  | cons atom rest ih =>
    have later := ih (destination.addOwn atom)
    simpa [includeAtoms, ModuleNode.listing, ModuleNode.addOwn, Space.add, List.append_assoc] using later

@[simp] theorem include_dependencies (destination : ModuleNode) (atoms : List Atom) :
    (includeAtoms destination atoms).deps = destination.deps := by
  induction atoms generalizing destination with
  | nil => rfl
  | cons atom rest ih => exact ih (destination.addOwn atom)

theorem include_view (destination : ModuleNode) (store : ModuleStore) (atoms : List Atom) :
    (includeAtoms destination atoms).view store = atoms.reverse ++ destination.view store := by
  change (includeAtoms destination atoms).listing ++ store.depAtoms (includeAtoms destination atoms).deps =
    atoms.reverse ++ (destination.listing ++ store.depAtoms destination.deps)
  rw [include_dependencies, include_listing, List.append_assoc]

def includeFrom (destination : ModuleNode) (store : ModuleStore) (provider : ModId) : ModuleNode :=
  includeAtoms destination (store provider).atoms

theorem include_presents_union (destination : ModuleNode) (store : ModuleStore) (atoms : List Atom) :
    ModuleTheories.CoversUnion (destination.view store) atoms ((includeAtoms destination atoms).view store) := by
  intro atom
  rw [include_view, List.mem_append, List.mem_reverse, or_comm]

def includeMap (base : Atom → Atom → Prop) (destination : ModuleNode) (store : ModuleStore) (atoms : List Atom) :
    OperationalTranslation (ModuleTheories.theory base atoms)
      (ModuleTheories.theory base ((includeAtoms destination atoms).view store)) :=
  ModuleTheories.inclusion base (fun {atom} kept => (include_presents_union destination store atoms atom).mpr (Or.inr kept))

/-- Once included, the receiver owns those occurrences. A later write
to the provider is immaterial unless the receiver also has a live link. -/
theorem include_is_owned (destination : ModuleNode) (store : ModuleStore) (provider : ModId) (updated : Space)
    (notLinked : provider ∉ destination.deps) :
    (includeFrom destination store provider).view (Function.update store provider updated) =
      (includeFrom destination store provider).view store := by
  rw [includeFrom, include_view, include_view]
  simp only [ModuleNode.view, ModuleStore.depAtoms_update_of_not_mem notLinked]

def contents (store : ModuleStore) (module : ModId) : Option (List Atom) := some (store module).atoms

def instantiate (store : ModuleStore) (fresh : ModId) (initial : Space) : ModuleStore :=
  Function.update store fresh initial

theorem instantiate_reads_initial (store : ModuleStore) (fresh : ModId) (initial : Space) :
    (Reference.named fresh).read (contents (instantiate store fresh initial)) = some initial.atoms := by
  simp only [ModuleReferences.named_reads_original, contents, instantiate, Function.update_self]

theorem instantiate_keeps_prior_reference (store : ModuleStore) (fresh : ModId) (initial : Space)
    (reference : Reference ModId) (separate : reference.instanceId ≠ fresh) :
    reference.read (contents (instantiate store fresh initial)) = reference.read (contents store) := by
  simp only [Reference.read, contents, instantiate, Function.update_of_ne separate]

section Controls

private def store (_ : ModId) : Space := Space.ofList [.symbol "template"]
private def receiver : ModuleNode := ⟨Space.ofList [.symbol "local"], []⟩
private def updated : Space := Space.ofList [.symbol "changed"]

theorem local_and_linked_edits_separate :
    ((receiver.importModule 1 []).view (Function.update store 1 updated)) = [.symbol "local", .symbol "changed"] ∧
      (includeFrom receiver store 1).view (Function.update store 1 updated) = [.symbol "template", .symbol "local"] := by
  decide +kernel

theorem receiver_removes_included_not_linked_atom :
    ((receiver.importModule 1 []).removeOwn (.symbol "template")).view store =
      [.symbol "local", .symbol "template"] ∧
      ((includeFrom receiver store 1).removeOwn (.symbol "template")).view store = [.symbol "local"] := by
  decide +kernel

theorem rename_shares_the_edit_but_instantiation_does_not :
    let started := instantiate store 2 (store 1)
    let changed := Function.update started 1 updated
    let first := Reference.named 1
    let renamed := first.rename (Equiv.swap "changed" "alias")
    first.read (contents changed) = some [.symbol "changed"] ∧
      renamed.read (contents changed) = some [.symbol "alias"] ∧
      (Reference.named 2).read (contents changed) = some [.symbol "template"] := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.HEModuleModes
