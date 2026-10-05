import Mettapedia.GSLT.Distinction.PublicationBlocks
import Mettapedia.Languages.MeTTa.HE.ModuleSpace

/-!
# HE module imports as publication blocks

The generic publication block (`GSLT.Distinction.PublicationBlocks`) links an
importer to a module once.  Read per importer, its links are exactly the
dependency list that HE's `MettaMod::insert_dep` builds (`ModuleNode.importModule`
with the imported module's own dependency table left aside), so the block's
idempotent linking is HE's `contains_imported_dep` guard
(`importsOf_link_self`, `link_realizes_importModule`).

Every import attempt therefore changes an importer's HE dependency list at most
by the one insertion of HE's import, and only when the publication committed or
the module was already published (`importStep_imports_cases`): a failed
initialization or a refused reservation leaves the importer's module space
exactly as it was.

The transitive part of an HE import (the imported module's own dependency
table, whose order upstream leaves unspecified) is the module store's concern
(`ModuleSpace`, `ModuleInvalidation`); it is not modelled by the registry
links.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.ModulePublication

open Mettapedia.GSLT.Distinction.PublicationBlocks
open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {Name Token : Type} [DecidableEq Name]

/-- The modules an importer is linked to, in link order. -/
def importsOf (registry : Registry ModId Name Token) (importer : ModId) : List ModId :=
  (registry.links.filter fun link => link.1 = importer).map Prod.snd

omit [DecidableEq Name] in
theorem mem_importsOf (registry : Registry ModId Name Token) (importer module : ModId) :
    module ∈ importsOf registry importer ↔ (importer, module) ∈ registry.links := by
  simp only [importsOf, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨first, second⟩, ⟨present, same⟩, rfl⟩
    simp only at same
    subst same
    exact present
  · intro present
    exact ⟨(importer, module), ⟨present, rfl⟩, rfl⟩

omit [DecidableEq Name] in
/-- **Linking is HE's dependency insertion** for the importer. -/
theorem importsOf_link_self (registry : Registry ModId Name Token) (importer module : ModId) :
    importsOf (registry.link importer module) importer =
      ModuleNode.insertDep (importsOf registry importer) module := by
  have unfolded : importsOf (registry.link importer module) importer =
      ((registry.link importer module).links.filter fun link => link.1 = importer).map Prod.snd := rfl
  rw [unfolded, Registry.links_link]
  by_cases linked : (importer, module) ∈ registry.links
  · rw [if_pos linked, ModuleNode.insertDep_of_mem ((mem_importsOf registry importer module).mpr linked)]
    rfl
  · rw [if_neg linked, ModuleNode.insertDep_of_not_mem
      (fun inside => linked ((mem_importsOf registry importer module).mp inside))]
    simp [importsOf, List.filter_append]

omit [DecidableEq Name] in
/-- Linking one importer leaves every other importer's dependencies alone. -/
theorem importsOf_link_other (registry : Registry ModId Name Token) (importer other module : ModId)
    (different : other ≠ importer) :
    importsOf (registry.link importer module) other = importsOf registry other := by
  have unfolded : importsOf (registry.link importer module) other =
      ((registry.link importer module).links.filter fun link => link.1 = other).map Prod.snd := rfl
  rw [unfolded, Registry.links_link]
  split
  · rfl
  · simp [importsOf, List.filter_append, Ne.symm different]

omit [DecidableEq Name] in
/-- **The block's link realizes HE's import.**  When an importer's HE module
node records exactly its registry links, linking a module gives the
dependency list of `ModuleNode.importModule` with an empty dependency table. -/
theorem link_realizes_importModule (registry : Registry ModId Name Token) (node : ModuleNode)
    (importer module : ModId) (recorded : node.deps = importsOf registry importer) :
    (node.importModule module []).deps = importsOf (registry.link importer module) importer := by
  rw [importsOf_link_self, ModuleNode.deps_importModule, ← recorded]
  split
  · next present => exact (ModuleNode.insertDep_of_mem present).symm
  · rfl

/-- Installing exports does not touch links. -/
theorem importsOf_install (registry : Registry ModId Name Token) (module : ModId)
    (exports : List (Name × Token)) (importer : ModId) :
    importsOf (registry.install module exports) importer = importsOf registry importer := rfl

variable {State Effect Fault Verdict : Type}

/-- **An import attempt changes the importer's HE dependencies at most by HE's
one insertion**, and a failed attempt changes nothing. -/
theorem importStep_imports_cases
    (init : Machine State (InitEvent Name Token Effect Fault) Verdict Empty) (start : ModId → State)
    (fuel : ℕ) (importer module : ModId) (session : Session State ModId Name Token Effect Fault) :
    importsOf (Session.importStep init start fuel importer module session).registry importer =
        importsOf session.registry importer ∨
      importsOf (Session.importStep init start fuel importer module session).registry importer =
        ModuleNode.insertDep (importsOf session.registry importer) module := by
  rcases Session.registry_cases init start fuel importer module session with
    same | ⟨_, linked⟩ | ⟨exports, _, installed⟩
  · exact Or.inl (by rw [same])
  · exact Or.inr (by rw [linked, importsOf_link_self])
  · exact Or.inr (by rw [installed, importsOf_link_self, importsOf_install])

omit [DecidableEq Name] in
/-- **A repeated import is HE's guarded import**: importing again through the
block gives the same dependencies as `importModule` applied twice. -/
theorem repeated_import_realizes_guard (registry : Registry ModId Name Token) (node : ModuleNode)
    (importer module : ModId) (recorded : node.deps = importsOf registry importer) :
    ((node.importModule module []).importModule module []).deps =
      importsOf ((registry.link importer module).link importer module) importer := by
  rw [ModuleNode.importModule_importModule_self, Registry.link_link]
  exact link_realizes_importModule registry node importer module recorded

end Mettapedia.Languages.MeTTa.HE.ModulePublication
