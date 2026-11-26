import Mettapedia.Languages.MeTTa.SpaceTheory.Modules
import Mathlib.Data.List.Sigma
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.Basic

/-!
# The declaration occurrences of a shared HE module

At a fixed snapshot an origin is a module identity and an occurrence
within that module. Reading a diamond keeps the shared origins once,
even if two of them carry equal atoms. This is not a claim of position
stability across edits, or of a commutative ordered answer stream.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.ModuleOccurrences

open Mettapedia.Languages.MeTTa.HE (Space ModuleStore ModuleNode ModId)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

abbrev Origin := ModId × Nat

def atomsFrom (store : ModuleStore) (module : ModId) : List (Origin × Atom) :=
  (store module).atoms.zipIdx.map fun (atom, index) => ((module, index), atom)

def readFrom (store : ModuleStore) (modules : List ModId) : List (Origin × Atom) :=
  modules.flatMap (atomsFrom store)

def view (store : ModuleStore) (root : ModId) (node : ModuleNode) : List (Origin × Atom) :=
  readFrom store (root :: node.deps)

def atomAt (store : ModuleStore) (origin : Origin) : Option Atom :=
  (store origin.1).atoms[origin.2]?

theorem from_module_exact (store : ModuleStore) (module : ModId) (origin : Origin) (atom : Atom) :
    (origin, atom) ∈ atomsFrom store module ↔ origin.1 = module ∧ atomAt store origin = some atom := by
  rcases origin with ⟨id, index⟩
  constructor
  · intro member
    obtain ⟨⟨found, offset⟩, atSource, identity⟩ := List.mem_map.mp member
    simp only [Prod.mk.injEq] at identity
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := identity
    exact ⟨rfl, List.mk_mem_zipIdx_iff_getElem?.mp atSource⟩
  · rintro ⟨rfl, stored⟩
    exact List.mem_map.mpr ⟨(atom, index), List.mk_mem_zipIdx_iff_getElem?.mpr stored, rfl⟩

theorem read_from_exact (store : ModuleStore) (modules : List ModId) (origin : Origin) (atom : Atom) :
    (origin, atom) ∈ readFrom store modules ↔ origin.1 ∈ modules ∧ atomAt store origin = some atom := by
  simp only [readFrom, List.mem_flatMap, from_module_exact]
  constructor
  · rintro ⟨m, listed, rfl, found⟩
    exact ⟨listed, found⟩
  · rintro ⟨listed, found⟩
    exact ⟨origin.1, listed, rfl, found⟩

private theorem module_atoms (store : ModuleStore) (module : ModId) :
    (atomsFrom store module).map Prod.snd = (store module).atoms := by
  simp [atomsFrom, List.map_map, Function.comp_def]

theorem visible_values (store : ModuleStore) (root : ModId) (node : ModuleNode)
    (named : store root = node.main) :
    (view store root node).map Prod.snd = node.view store := by
  simp [view, readFrom, List.map_flatMap, module_atoms, ModuleNode.view, ModuleStore.depAtoms, named]

private theorem atom_sources_distinct (store : ModuleStore) (module : ModId) :
    ((atomsFrom store module).map Prod.fst).Nodup := by
  have indexed := (List.nodup_zipIdx_map_snd (store module).atoms).map
    (f := fun position => (module, position)) (fun _ _ same => congrArg Prod.snd same)
  simpa only [atomsFrom, List.map_map, Function.comp_def] using indexed

theorem origins_distinct (store : ModuleStore) (modules : List ModId) (once : modules.Nodup) :
    ((readFrom store modules).map Prod.fst).Nodup := by
  rw [readFrom, List.map_flatMap]
  apply List.nodup_flatMap.mpr
  refine ⟨fun module _ => atom_sources_distinct store module, once.imp ?_⟩
  intro a b different origin inA inB
  obtain ⟨⟨key, atom⟩, memberA, rfl⟩ := List.mem_map.mp inA
  obtain ⟨⟨key', atom'⟩, memberB, rfl⟩ := List.mem_map.mp inB
  exact different (((from_module_exact store a _ _).mp memberA).1.symm.trans
    ((from_module_exact store b _ _).mp memberB).1)

theorem occurrence_count_one (store : ModuleStore) (modules : List ModId) (once : modules.Nodup)
    (origin : Origin) (member : origin ∈ (readFrom store modules).map Prod.fst) :
    ((readFrom store modules).map Prod.fst).count origin = 1 := by
  have small := (List.nodup_iff_count_le_one.mp (origins_distinct store modules once)) origin
  have positive := List.count_pos_iff.mpr member
  omega

def support (store : ModuleStore) (modules : List ModId) : Set Origin :=
  {origin | origin.1 ∈ modules ∧ ∃ atom, atomAt store origin = some atom}

theorem support_exact (store : ModuleStore) (modules : List ModId) (origin : Origin) :
    origin ∈ support store modules ↔ origin ∈ (readFrom store modules).map Prod.fst := by
  constructor
  · rintro ⟨included, atom, found⟩
    exact List.mem_map.mpr ⟨(origin, atom), (read_from_exact store modules origin atom).mpr ⟨included, found⟩, rfl⟩
  · rintro seen
    obtain ⟨⟨origin', atom⟩, actual, rfl⟩ := List.mem_map.mp seen
    exact ⟨(read_from_exact store modules origin' atom).mp actual |>.1,
      atom, (read_from_exact store modules origin' atom).mp actual |>.2⟩

theorem fresh_import_support (store : ModuleStore) (root module : ModId) (before imported : ModuleNode)
    (fresh : module ∉ before.deps) :
    support store (root :: (before.importModule module imported.deps).deps) =
      support store (root :: before.deps) ∪ support store (module :: imported.deps) := by
  rw [ModuleNode.importModule_of_not_mem fresh]
  ext origin
  simp only [support, Set.mem_ofPred_eq, List.mem_cons, ModuleNode.mem_insertDeps, Set.mem_union]
  tauto

/-- The actual fresh HE import is the pushout of declaration origins
over the shared origins; interpretations can be glued uniquely exactly
when they agree there. The ordered views remain separate data. -/
theorem he_origin_pushout {Result : Type*} (store : ModuleStore) (root module : ModId)
    (before imported : ModuleNode) (fresh : module ∉ before.deps)
    (left : support store (root :: before.deps) → Result)
    (right : support store (module :: imported.deps) → Result) :
    let union := fresh_import_support store root module before imported fresh
    Modules.Agree left right ↔
      ∃! interpret : support store (root :: (before.importModule module imported.deps).deps) → Result,
        (∀ occurrence, interpret ⟨occurrence.val, union.symm ▸ Or.inl occurrence.property⟩ = left occurrence) ∧
        (∀ occurrence, interpret ⟨occurrence.val, union.symm ▸ Or.inr occurrence.property⟩ = right occurrence) :=
  Modules.support_pushout_of_union (fresh_import_support store root module before imported fresh) left right

section Controls

private def store (module : ModId) : Space :=
  Space.ofList (if module = 1 then [.symbol "left"] else if module = 2 then [.symbol "right"]
    else if module = 3 then [.symbol "shared", .symbol "shared"] else [])
private def main : ModuleNode := ⟨Space.empty, []⟩
private def leftFirst := (main.importModule 1 [3]).importModule 2 [3]
private def rightFirst := (main.importModule 2 [3]).importModule 1 [3]

/-- The shared module contributes both of its written copies, once
each. Looking at their payloads alone would identify them incorrectly. -/
theorem diamond_keeps_two_distinct_equal_occurrences :
    ((view store 0 leftFirst).filter fun entry => entry.1.1 = 3) =
      [((3, 0), .symbol "shared"), ((3, 1), .symbol "shared")] := by
  decide +kernel

theorem independent_link_orders_preserve_bag_not_first :
    (leftFirst.view store : Multiset Atom) = rightFirst.view store ∧
      (leftFirst.view store).head? ≠ (rightFirst.view store).head? := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.ModuleOccurrences
