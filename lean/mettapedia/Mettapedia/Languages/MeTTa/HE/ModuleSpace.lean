import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Machines.OrderedDependencyIds

/-!
# HE module spaces

In hyperon-experimental every loaded module has its own space.  What a module
queries is a `ModuleSpace` (`lib/src/space/module.rs`): the module's own `main`
space and an ordered list `deps` of the spaces of the modules it imported.  This
file models that structure over the list-backed `Space` of `HE.Space`.

Dependencies are held by reference (`DynSpace`), so here they are held by
identity: a `ModuleStore` gives the current `main` space of every module, and an
importer's dependencies are read through the store when the importer is queried.

## Upstream behaviour modelled

* `ModuleSpace::single_query`: the answers of `main`, then, for each dependency
  in order, the answers of that dependency's own `main` (`query_no_deps`).
* `SpaceMut::{add, remove}` and `Space::visit` (hence `get-atoms`) on a
  `ModuleSpace` act on `main` only, as do `replace` and `atom_count`, which are not
  modelled here.
* `MettaMod::import_all_from_dependency` (`lib/src/metta/runner/modules/mod.rs`):
  nothing happens when the module is already recorded (`contains_imported_dep`);
  otherwise `insert_dep` is called for the module and then for every module in its
  own dependency table, and `insert_dep` appends only identities not yet recorded.
  That table is a `HashMap`, so upstream leaves the order of the transitive
  identities unspecified; here it is a parameter, and every law holds for every
  order.

## Main results

* Ordered query composition: `ModuleNode.queryWith_toSpace`,
  `ModuleNode.queryWith_main_prefix`, `ModuleNode.getAnnotatedTypes_toSpace`.
* Local mutation: `ModuleNode.view_removeOwn_of_not_mem`,
  `ModuleNode.mem_view_removeOwn_of_mem_dep`, `ModuleNode.count_view_removeOwn`.
* Dependency stability: `ModuleNode.nodup_deps_importModule`,
  `ModuleNode.deps_prefix_importModule`, `ModuleNode.importModule_importModule_self`,
  `ModuleNode.deps_importModule_diamond`, `ModuleNode.mem_view_importModule_iff`.
* Liveness: `ModuleNode.view_update_of_mem`, `ModuleNode.view_update_of_not_mem`.

Within one space, answers follow the list order of `Space`, as everywhere in this
development.  The laws here are about the order between spaces, which upstream
fixes.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Atom-local queries -/

/-- An atom-local query: every atom of the space contributes `q atom`, in the list
order of the space.  A pattern query that matches each stored atom on its own, such
as the annotation lookup `getAnnotatedTypes`, has this form.  `queryEquations` does
not: it freshens variables by an equation's position in the space. -/
def Space.queryWith {β : Type*} (q : Atom → List β) (s : Space) : List β :=
  s.atoms.flatMap q

/-- `getAnnotatedTypes` is atom-local: its answer on a space is the concatenation of
its answers on the one-atom spaces of the atoms. -/
theorem getAnnotatedTypes_eq_queryWith (s : Space) (a : Atom) :
    getAnnotatedTypes s a = s.queryWith fun x => getAnnotatedTypes ⟨[x]⟩ a := by
  obtain ⟨xs⟩ := s
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h : getAnnotatedTypes ⟨x :: xs⟩ a =
        getAnnotatedTypes ⟨[x]⟩ a ++ getAnnotatedTypes ⟨xs⟩ a :=
      List.filterMap_append (l := [x]) (l' := xs)
    rw [h, ih]
    rfl

/-! ## Module spaces -/

/-- Module identity: upstream `ModId`, an index into the runner's module table. -/
abbrev ModId := Nat

/-- The live module handles: the current `main` space of every loaded module, by
identity.  Upstream an importer holds each dependency as a shared `DynSpace`, so it
reads whatever that dependency's `main` holds at query time. -/
abbrev ModuleStore := ModId → Space

namespace ModuleStore

/-- The atoms an importer reads through the dependency identities `ds`: each
dependency's own `main`, in order.  A dependency's own dependencies are not read
through it (`query_no_deps`); they are flattened into the importer's list when it
imports (`import_all_from_dependency`). -/
def depAtoms (store : ModuleStore) (ds : List ModId) : List Atom :=
  ds.flatMap fun d => (store d).atoms

@[simp] theorem mem_depAtoms {store : ModuleStore} {ds : List ModId} {a : Atom} :
    a ∈ store.depAtoms ds ↔ ∃ d ∈ ds, a ∈ (store d).atoms :=
  List.mem_flatMap

/-- `depAtoms` reads the store only at the identities in `ds`. -/
theorem depAtoms_congr {store₁ store₂ : ModuleStore} {ds : List ModId}
    (h : ∀ d ∈ ds, store₁ d = store₂ d) : store₁.depAtoms ds = store₂.depAtoms ds :=
  List.flatMap_congr fun d hd => congrArg Space.atoms (h d hd)

theorem depAtoms_update_of_not_mem {store : ModuleStore} {ds : List ModId} {d : ModId}
    (hd : d ∉ ds) (s : Space) : depAtoms (Function.update store d s) ds = store.depAtoms ds :=
  depAtoms_congr fun _ he => Function.update_of_ne (by rintro rfl; exact hd he) s store

end ModuleStore

/-- A module space, upstream `ModuleSpace { main, deps }`: the module's own `main`
space, and the identities of its dependencies in import order, read through a
`ModuleStore`. -/
structure ModuleNode where
  /-- The module's own space. -/
  main : Space
  /-- The identities of the imported modules, direct and transitive, in import order. -/
  deps : List ModId
  deriving Repr, Inhabited, DecidableEq

namespace ModuleNode

variable {store : ModuleStore} {m : ModuleNode} {d : ModId} {a : Atom}

/-- The atoms a query on the module space sees: `main` first, then each dependency's
own `main`, in dependency order (`ModuleSpace::single_query`). -/
def view (store : ModuleStore) (m : ModuleNode) : List Atom :=
  m.main.atoms ++ store.depAtoms m.deps

/-- The module space as one `Space`, so that the queries of `HE.Space` run on it. -/
def toSpace (store : ModuleStore) (m : ModuleNode) : Space :=
  ⟨m.view store⟩

/-! ### Ordered query composition -/

/-- An atom-local query on a module space returns the answers of `main`, then those of
each dependency's own `main`, in dependency order (`ModuleSpace::single_query`). -/
theorem queryWith_toSpace {β : Type*} (q : Atom → List β) :
    (m.toSpace store).queryWith q =
      m.main.queryWith q ++ m.deps.flatMap fun d => (store d).queryWith q := by
  simp only [toSpace, view, ModuleStore.depAtoms, Space.queryWith, List.flatMap_append,
    List.flatMap_assoc]

/-- Own answers come first: the answers of `main` are a prefix of the module's answers. -/
theorem queryWith_main_prefix {β : Type*} (q : Atom → List β) :
    m.main.queryWith q <+: (m.toSpace store).queryWith q :=
  ⟨_, (queryWith_toSpace q).symm⟩

/-- When `main` has an answer, the module's first answer is the first answer of `main`. -/
theorem head?_queryWith_toSpace {β : Type*} {q : Atom → List β}
    (h : m.main.queryWith q ≠ []) :
    ((m.toSpace store).queryWith q).head? = (m.main.queryWith q).head? := by
  obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil h
  rw [queryWith_toSpace, hb]
  rfl

/-- Annotation lookup on a module space: the annotated types of `a` in `main`, then
those in each dependency's own `main`, in dependency order. -/
theorem getAnnotatedTypes_toSpace (a : Atom) :
    getAnnotatedTypes (m.toSpace store) a =
      getAnnotatedTypes m.main a ++ m.deps.flatMap fun d => getAnnotatedTypes (store d) a := by
  rw [getAnnotatedTypes_eq_queryWith (m.toSpace store) a,
    getAnnotatedTypes_eq_queryWith m.main a, queryWith_toSpace]
  congr 1
  exact List.flatMap_congr fun d _ => (getAnnotatedTypes_eq_queryWith (store d) a).symm

/-! ### Local mutation -/

/-- `SpaceMut::add` on a module space: the atom goes into `main`. -/
def addOwn (m : ModuleNode) (a : Atom) : ModuleNode :=
  { m with main := m.main.add a }

/-- `SpaceMut::remove` on a module space: one occurrence is removed from `main`. -/
def removeOwn (m : ModuleNode) (a : Atom) : ModuleNode :=
  { m with main := m.main.remove a }

/-- `get-atoms` on a module space (`Space::visit`; likewise `atom_count`): the atoms
of `main` only. -/
def listing (m : ModuleNode) : List Atom :=
  m.main.atoms

@[simp] theorem main_addOwn : (m.addOwn a).main = m.main.add a := rfl

@[simp] theorem deps_addOwn : (m.addOwn a).deps = m.deps := rfl

@[simp] theorem main_removeOwn : (m.removeOwn a).main = m.main.remove a := rfl

@[simp] theorem deps_removeOwn : (m.removeOwn a).deps = m.deps := rfl

/-- An added atom is the first atom the module sees. -/
theorem view_addOwn : (m.addOwn a).view store = a :: m.view store := rfl

/-- Removal through the module touches only the `main` segment of the view. -/
theorem view_removeOwn :
    (m.removeOwn a).view store = m.main.atoms.erase a ++ store.depAtoms m.deps := rfl

/-- An atom that is not in `main`, in particular an imported one, cannot be removed
through the importer: the removal leaves the view unchanged. -/
theorem view_removeOwn_of_not_mem (h : a ∉ m.main.atoms) :
    (m.removeOwn a).view store = m.view store := by
  rw [view_removeOwn, List.erase_of_not_mem h]
  rfl

/-- A dependency's copy of an atom survives removal of that atom through the importer.
This holds whether or not `main` also holds the atom; when it does, the removal takes
the own copy (`count_view_removeOwn`). -/
theorem mem_view_removeOwn_of_mem_dep (hd : d ∈ m.deps) (ha : a ∈ (store d).atoms) :
    a ∈ (m.removeOwn a).view store := by
  rw [view_removeOwn]
  exact List.mem_append_right _ (ModuleStore.mem_depAtoms.2 ⟨d, hd, ha⟩)

/-- Erasing an atom that the list holds lowers its count by exactly one. -/
private theorem count_erase_add_one {a : Atom} :
    ∀ {l : List Atom}, a ∈ l → (l.erase a).count a + 1 = l.count a
  | [], h => absurd h List.not_mem_nil
  | b :: l, h => by
    by_cases hb : b = a
    · subst hb
      rw [List.erase_cons_head, List.count_cons_self]
    · rw [List.erase_cons_tail (by simpa using hb), List.count_cons_of_ne hb,
        List.count_cons_of_ne hb]
      exact count_erase_add_one ((List.mem_cons.1 h).resolve_left (Ne.symm hb))

/-- Removing an atom that `main` holds takes exactly one copy out of the view. -/
theorem count_view_removeOwn (h : a ∈ m.main.atoms) :
    ((m.removeOwn a).view store).count a + 1 = (m.view store).count a := by
  have := count_erase_add_one h
  rw [view_removeOwn]
  simp only [view, List.count_append]
  omega

/-- The listing reads `main` only: two module spaces with the same `main` list the same
atoms, whatever their dependencies (and the listing reads no store). -/
theorem listing_eq_of_main_eq {m₁ m₂ : ModuleNode} (h : m₁.main = m₂.main) :
    m₁.listing = m₂.listing :=
  congrArg Space.atoms h

/-- The listing is the leading segment of the view. -/
theorem listing_prefix_view : m.listing <+: m.view store :=
  List.prefix_append _ _

/-! ### Dependency stability -/

/-- `MettaMod::insert_dep`: record `d` at the end of the list unless it is already
recorded. -/
def insertDep (deps : List ModId) (d : ModId) : List ModId :=
  Mettapedia.Machines.OrderedDependencyIds.insertDep deps d

/-- `insert_dep` for each identity of `ds` in turn. -/
def insertDeps (deps ds : List ModId) : List ModId :=
  Mettapedia.Machines.OrderedDependencyIds.insertDeps deps ds

/-- `MettaMod::import_all_from_dependency`: nothing happens when `d` is already recorded
(`contains_imported_dep`); otherwise `d`, then each identity of `transitive` (the
dependency's own table), is recorded by `insert_dep`. -/
def importModule (m : ModuleNode) (d : ModId) (transitive : List ModId) : ModuleNode :=
  if d ∈ m.deps then m else { m with deps := insertDeps m.deps (d :: transitive) }

theorem insertDep_of_mem {l : List ModId} (h : d ∈ l) : insertDep l d = l :=
  if_pos h

theorem insertDep_of_not_mem {l : List ModId} (h : d ∉ l) : insertDep l d = l ++ [d] :=
  if_neg h

theorem mem_insertDep {l : List ModId} {x : ModId} : x ∈ insertDep l d ↔ x ∈ l ∨ x = d := by
  by_cases h : d ∈ l
  · rw [insertDep_of_mem h]
    exact ⟨Or.inl, fun hx => hx.elim id fun hxd => hxd ▸ h⟩
  · rw [insertDep_of_not_mem h, List.mem_append, List.mem_singleton]

theorem prefix_insertDep (l : List ModId) (d : ModId) : l <+: insertDep l d := by
  by_cases h : d ∈ l
  · rw [insertDep_of_mem h]
  · rw [insertDep_of_not_mem h]
    exact List.prefix_append l [d]

theorem nodup_insertDep {l : List ModId} (d : ModId) (h : l.Nodup) : (insertDep l d).Nodup := by
  by_cases hd : d ∈ l
  · rwa [insertDep_of_mem hd]
  · rw [insertDep_of_not_mem hd, List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    rintro x hx y hy rfl
    exact hd (List.mem_singleton.1 hy ▸ hx)

@[simp] theorem insertDeps_nil (l : List ModId) : insertDeps l [] = l := rfl

@[simp] theorem insertDeps_cons (l : List ModId) (d : ModId) (ds : List ModId) :
    insertDeps l (d :: ds) = insertDeps (insertDep l d) ds := rfl

theorem mem_insertDeps {l ds : List ModId} {x : ModId} :
    x ∈ insertDeps l ds ↔ x ∈ l ∨ x ∈ ds := by
  induction ds generalizing l with
  | nil => simp
  | cons d ds ih => rw [insertDeps_cons, ih, mem_insertDep, List.mem_cons, or_assoc]

theorem prefix_insertDeps (l ds : List ModId) : l <+: insertDeps l ds := by
  induction ds generalizing l with
  | nil => exact List.prefix_refl l
  | cons d ds ih => exact (prefix_insertDep l d).trans (ih _)

theorem nodup_insertDeps {l : List ModId} (ds : List ModId) (h : l.Nodup) :
    (insertDeps l ds).Nodup := by
  induction ds generalizing l with
  | nil => exact h
  | cons d ds ih => exact ih (nodup_insertDep d h)

/-- Identities that are all recorded already change nothing. -/
theorem insertDeps_of_forall_mem {l ds : List ModId} (h : ∀ x ∈ ds, x ∈ l) :
    insertDeps l ds = l := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [insertDeps_cons, insertDep_of_mem (h d List.mem_cons_self)]
    exact ih fun x hx => h x (List.mem_cons_of_mem d hx)

/-- `insert_dep` alone is already idempotent, without the `contains_imported_dep` guard. -/
theorem insertDeps_insertDeps_self (l ds : List ModId) :
    insertDeps (insertDeps l ds) ds = insertDeps l ds :=
  insertDeps_of_forall_mem fun _ hx => mem_insertDeps.2 (Or.inr hx)

theorem importModule_of_mem (h : d ∈ m.deps) (ts : List ModId) : m.importModule d ts = m :=
  if_pos h

theorem importModule_of_not_mem (h : d ∉ m.deps) (ts : List ModId) :
    m.importModule d ts = { m with deps := insertDeps m.deps (d :: ts) } :=
  if_neg h

@[simp] theorem main_importModule (d : ModId) (ts : List ModId) :
    (m.importModule d ts).main = m.main := by
  unfold importModule
  split <;> rfl

theorem deps_importModule (d : ModId) (ts : List ModId) :
    (m.importModule d ts).deps =
      if d ∈ m.deps then m.deps else insertDeps m.deps (d :: ts) := by
  by_cases h : d ∈ m.deps <;> simp [importModule, h]

/-- After an import the imported module is recorded. -/
theorem mem_deps_importModule_self (d : ModId) (ts : List ModId) :
    d ∈ (m.importModule d ts).deps := by
  rw [deps_importModule]
  split
  · assumption
  · exact mem_insertDeps.2 (Or.inr List.mem_cons_self)

/-- Importing keeps every module identity at most once. -/
theorem nodup_deps_importModule (h : m.deps.Nodup) (d : ModId) (ts : List ModId) :
    (m.importModule d ts).deps.Nodup := by
  rw [deps_importModule]
  split
  · exact h
  · exact nodup_insertDeps _ h

/-- Importing only appends: the old dependencies keep their order and none is removed. -/
theorem deps_prefix_importModule (d : ModId) (ts : List ModId) :
    m.deps <+: (m.importModule d ts).deps := by
  rw [deps_importModule]
  split
  · exact List.prefix_refl _
  · exact prefix_insertDeps _ _

/-- Importing the same module twice is importing it once. -/
theorem importModule_importModule_self (d : ModId) (ts : List ModId) :
    (m.importModule d ts).importModule d ts = m.importModule d ts :=
  importModule_of_mem (mem_deps_importModule_self d ts) ts

/-- Importing never changes the listing: imported atoms are not listed by `get-atoms`. -/
theorem listing_importModule (d : ModId) (ts : List ModId) :
    (m.importModule d ts).listing = m.listing :=
  listing_eq_of_main_eq (main_importModule d ts)

/-- The diamond: importing `A`, which depends on `D`, then `B`, which also depends on
`D`, records `A`, `D`, `B` in that order. -/
theorem deps_importModule_diamond {A B D : ModId} (hA : A ∉ m.deps) (hB : B ∉ m.deps)
    (hD : D ∉ m.deps) (hAD : A ≠ D) (hBA : B ≠ A) (hBD : B ≠ D) :
    ((m.importModule A [D]).importModule B [D]).deps = m.deps ++ [A, D, B] := by
  simp [importModule, insertDeps, Mettapedia.Machines.OrderedDependencyIds.insertDeps,
    Mettapedia.Machines.OrderedDependencyIds.insertDep, hA, hB, hD, hAD.symm, hBA, hBD]

/-- In the diamond, `D` is recorded once. -/
theorem count_deps_importModule_diamond {A B D : ModId} (hA : A ∉ m.deps) (hB : B ∉ m.deps)
    (hD : D ∉ m.deps) (hAD : A ≠ D) (hBA : B ≠ A) (hBD : B ≠ D) :
    ((m.importModule A [D]).importModule B [D]).deps.count D = 1 := by
  rw [deps_importModule_diamond hA hB hD hAD hBA hBD, List.count_append,
    List.count_eq_zero_of_not_mem hD]
  simp [hAD, hBD]

/-- Flattening is exact: on a first import of `d`, whose own space is `n.main` and whose
dependencies are `n.deps`, the importer comes to see exactly what it saw before together
with what `n` sees. -/
theorem mem_view_importModule_iff {n : ModuleNode} (hn : store d = n.main) (hd : d ∉ m.deps) :
    a ∈ (m.importModule d n.deps).view store ↔ a ∈ m.view store ∨ a ∈ n.view store := by
  rw [importModule_of_not_mem hd]
  simp only [view, List.mem_append, ModuleStore.mem_depAtoms, mem_insertDeps, List.mem_cons]
  constructor
  · rintro (h | ⟨e, (he | rfl | he), hae⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨e, he, hae⟩)
    · exact Or.inr (Or.inl (hn ▸ hae))
    · exact Or.inr (Or.inr ⟨e, he, hae⟩)
  · rintro ((h | ⟨e, he, hae⟩) | (h | ⟨e, he, hae⟩))
    · exact Or.inl h
    · exact Or.inr ⟨e, Or.inl he, hae⟩
    · exact Or.inr ⟨d, Or.inr (Or.inl rfl), hn ▸ h⟩
    · exact Or.inr ⟨e, Or.inr (Or.inr he), hae⟩

/-! ### Liveness -/

/-- The view reads the store only at the identities in `m.deps`. -/
theorem view_congr {store₁ store₂ : ModuleStore}
    (h : ∀ d ∈ m.deps, store₁ d = store₂ d) : m.view store₁ = m.view store₂ :=
  congrArg (m.main.atoms ++ ·) (ModuleStore.depAtoms_congr h)

/-- Isolation: a change to a module that `m` does not depend on is not seen by `m`. -/
theorem view_update_of_not_mem (hd : d ∉ m.deps) (s : Space) :
    m.view (Function.update store d s) = m.view store :=
  congrArg (m.main.atoms ++ ·) (ModuleStore.depAtoms_update_of_not_mem hd s)

/-- The view, split at a dependency `d`. -/
theorem view_eq_of_deps_eq {pre post : List ModId} (h : m.deps = pre ++ d :: post) :
    m.view store = m.main.atoms ++ store.depAtoms pre ++ (store d).atoms ++
      store.depAtoms post := by
  simp only [view, h, ModuleStore.depAtoms, List.flatMap_append, List.flatMap_cons,
    List.append_assoc]

/-- A new space for `d` replaces `d`'s segment of the view and nothing else. -/
theorem view_update_of_deps_eq {pre post : List ModId} (h : m.deps = pre ++ d :: post)
    (hpre : d ∉ pre) (hpost : d ∉ post) (s : Space) :
    m.view (Function.update store d s) =
      m.main.atoms ++ store.depAtoms pre ++ s.atoms ++ store.depAtoms post := by
  rw [view_eq_of_deps_eq h, Function.update_self,
    ModuleStore.depAtoms_update_of_not_mem hpre, ModuleStore.depAtoms_update_of_not_mem hpost]

/-- Liveness: when `d` is a dependency of `m` (recorded once, as `importModule` keeps
it), changing `d`'s space through its own handle replaces exactly `d`'s segment of `m`'s
view; `m`'s own atoms stay in front. -/
theorem view_update_of_mem (hnd : m.deps.Nodup) (hd : d ∈ m.deps) (store : ModuleStore)
    (s : Space) :
    ∃ pre post : List ModId, m.deps = pre ++ d :: post ∧
      m.view store = m.main.atoms ++ store.depAtoms pre ++ (store d).atoms ++
        store.depAtoms post ∧
      m.view (Function.update store d s) =
        m.main.atoms ++ store.depAtoms pre ++ s.atoms ++ store.depAtoms post := by
  obtain ⟨pre, post, h⟩ := List.append_of_mem hd
  have hnd' : (pre ++ d :: post).Nodup := h ▸ hnd
  rw [List.nodup_append, List.nodup_cons] at hnd'
  have hpre : d ∉ pre := fun hp => hnd'.2.2 d hp d List.mem_cons_self rfl
  exact ⟨pre, post, h, view_eq_of_deps_eq h, view_update_of_deps_eq h hpre hnd'.2.1.1 s⟩

/-- Live sharing: an atom of the new space of `d` is seen by every module that depends
on `d`. -/
theorem mem_view_update (hd : d ∈ m.deps) {s : Space} (ha : a ∈ s.atoms) :
    a ∈ m.view (Function.update store d s) := by
  refine List.mem_append_right _ (ModuleStore.mem_depAtoms.2 ⟨d, hd, ?_⟩)
  rwa [Function.update_self]

/-- The leading segment of the view is `main`, whatever the store: no change to any
module's space through the store changes the importer's own atoms. -/
theorem take_view : (m.view store).take m.main.atoms.length = m.main.atoms :=
  List.take_left

/-- What follows `main` in the view is the dependencies' atoms. -/
theorem drop_view : (m.view store).drop m.main.atoms.length = store.depAtoms m.deps :=
  List.drop_left

end ModuleNode

/-! ## Examples -/

section Examples

private def ownAtom : Atom := .symbol "own"
private def depAtom : Atom := .symbol "dep"

/-- Module `1` holds `dep`; every other module is empty. -/
private def store₀ : ModuleStore := fun d => if d = 1 then ⟨[depAtom]⟩ else Space.empty

/-- A module that owns `own` and imported module `1`. -/
private def node₀ : ModuleNode := ⟨⟨[ownAtom]⟩, [1]⟩

example : node₀.view store₀ = [ownAtom, depAtom] := by decide
example : node₀.listing = [ownAtom] := rfl
example : node₀.listing ≠ node₀.view store₀ := by decide

-- An imported atom cannot be removed through the importer.
example : (node₀.removeOwn depAtom).view store₀ = node₀.view store₀ := by decide
-- An own atom can.
example : (node₀.removeOwn ownAtom).view store₀ = [depAtom] := by decide
example : (node₀.removeOwn ownAtom).view store₀ ≠ node₀.view store₀ := by decide
-- An atom both owned and imported: one removal leaves the imported copy.
example : ((node₀.addOwn depAtom).removeOwn depAtom).view store₀ = [ownAtom, depAtom] := by
  decide

-- Annotated types: the module's own first, then the dependency's.
private def annot (t : String) : Atom := .expression [.symbol ":", .symbol "f", .symbol t]
example :
    getAnnotatedTypes
        (ModuleNode.toSpace (fun d => if d = 1 then ⟨[annot "B"]⟩ else Space.empty)
          ⟨⟨[annot "A"]⟩, [1]⟩)
        (.symbol "f") =
      [.symbol "A", .symbol "B"] := by
  decide

-- The diamond: `1` and `2` both depend on `3`, which is recorded once.
example : (((ModuleNode.mk Space.empty []).importModule 1 [3]).importModule 2 [3]).deps =
    [1, 3, 2] := by
  decide
-- A recorded module is not processed again: the transitive identities of a repeated
-- import are ignored, although `insert_dep` alone would record them.
example : (node₀.importModule 1 [2]).deps = [1] := by decide
example : ModuleNode.insertDeps [1] [1, 2] = [1, 2] := by decide

-- Liveness: an atom added to module `1` through its own handle is seen by the importer.
example : node₀.view (Function.update store₀ 1 ((store₀ 1).add ownAtom)) =
    [ownAtom, ownAtom, depAtom] := by
  decide
-- Isolation: a change to module `2`, which the importer does not depend on, is not seen.
example : node₀.view (Function.update store₀ 2 ⟨[ownAtom]⟩) = node₀.view store₀ := by
  decide

end Examples

end Mettapedia.Languages.MeTTa.HE
