import Mettapedia.Languages.MeTTa.PeTTa.LibTransformQuery
import Mettapedia.Languages.MeTTa.PeTTa.Effects

/-!
# PeTTa's space and choice primitives are transform forms

CeTTa's library `lib_petta_by_transform` writes PeTTa's own forms with `transform`:

* `(match S P T)` is `(transform S P T)`;
* `(add-atom S A)` is `(transform S () A S)`, an empty row that makes `A`;
* `(remove-atom S A)` is `(transform S (collect (take A) $c) ...)`, one firing that takes
  every match of `A`;
* `(superpose (a b c))` is `(transform S () (, a b c))`, an empty row with one instance for
  each element.

This module proves these on the library's model (`LibTransform`), against the store
operations PeTTa's own semantics uses (`Effects.insert`, `Effects.erase`,
`SpaceSemantics.query`). The model's scope is its own: one space, stored atoms that are
ground, structural matching.

* `transform_noSources`: with no source there is one branch, it fires, and its instances are
  the template's parts under no binding.
* `match_form` is `LibTransform.transform_read_eq_query`, restated here.
* `addAtom_form`: into the store itself, an empty row with the template `a` answers the
  count `1` and leaves the rows followed by `a`, which is what `Effects.insert` writes
  (`insert_rows`). The answer is the count, where `add-atom` answers `true`.
* `removeAtom_form`: `(collect (take p) C)` leaves exactly the rows `Effects.erase` leaves
  (`erase_rows`), and binds `C` to the rows it took; `removeAtom_answer` says the collection
  is empty exactly when no row was removed, which is `remove-atom`'s answer.
* `superpose_form`: an empty row with the template `(, a1 ... an)` answers `a1 ... an` in
  order and leaves the store unchanged.

Negative examples: a template headed by `,` is not one atom to add (`addAtom_comma_splits`),
and a `collect` in read mode removes nothing (`collect_read_keeps`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.TransformForms

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
  (Subst matchAtom applySubst applySubst_nil isGroundAtom)
open LibTransform

/-- `()`: no source, one empty row. -/
def noSources : Sources where
  kernel := []

theorem proposals_noSources (s : Store) : proposals s noSources = [[]] := rfl

/-- With no source the one candidate is the empty row, and it validates. -/
theorem fire_noSources (s : Store) (emit : Subst → Answers) :
    fire s [] noSources emit = some (s, emit []) := by
  have cands : candidates s [] noSources = [⟨[], [([], [])]⟩] := rfl
  have ok : valid s (Candidate.footprint ⟨[], [([], [])]⟩) = true := by
    simp [Candidate.footprint, valid]
  rw [fire_of_first cands ok]
  simp [Candidate.footprint, Candidate.instances, commit, applyTakes]

/-- **No source: one branch, which fires.** Its instances are routed once. -/
theorem transformWith_noSources {β : Type} (route : Answers → Search Store β)
    (emit : Subst → Answers) (s : Store) :
    (transformWith route noSources emit s).drain = (route (emit []) s).drain := by
  rw [transformWith_drain, proposals_noSources]
  simp [branchStep, fire_noSources]

/-- The instances of a template under no binding are its parts as written. -/
theorem instances_nil (template : Atom) : instances template [] = split template := by
  unfold instances
  exact (List.map_congr_left fun a _ => applySubst_nil a).trans (List.map_id _)

theorem transform_noSources (template : Atom) (s : Store) :
    (transform noSources template s).drain = (split template, s) := by
  rw [transform, transformWith_noSources, instances_nil, toCaller_drain]

/-! ## `match` -/

/-- **`match` is a read.** On a ground store, a pattern without the list view and a template
that is not a `,` conjunction: the transform that reads the pattern answers what PeTTa's
`match` answers and leaves the store unchanged. -/
theorem match_form (s : Store) (ground : ∀ a ∈ s, isGroundAtom a = true)
    (p template : Atom) (clear : UnifyingTransform.noListView p = true)
    (plain : ¬ IsComma template) :
    (transform (readSources [p] none) template s).drain =
      (SpaceSemantics.query s p template, s) :=
  transform_read_eq_query s ground p template clear plain

/-! ## `add-atom` -/

/-- **`add-atom` is an empty row that makes its atom.** Into the store itself the transform
answers how many atoms it made and leaves the rows followed by them. -/
theorem transformInto_noSources (template : Atom) (s : Store) :
    (transformInto noSources template s).drain =
      ([(split template).length], s ++ split template) := by
  rw [transformInto, transformWith_noSources, instances_nil]
  simp [intoStore]

theorem addAtom_form (a : Atom) (plain : ¬ IsComma a) (s : Store) :
    (transformInto noSources a s).drain = ([1], s ++ [a]) := by
  rw [transformInto_noSources, split_of_not_comma plain]
  rfl

/-- The rows `Effects.insert` writes are the rows the transform leaves. -/
theorem insert_rows (state after : Effects.State) (handle : NamedSpaces.Handle) (a : Atom)
    (rows : List Atom) (read : state.read handle = some rows)
    (inserted : Effects.insert state handle a = some after) (plain : ¬ IsComma a) :
    state.write handle ((transformInto noSources a rows).drain).2 = some after := by
  rw [addAtom_form a plain rows]
  simpa [Effects.insert, read] using inserted

/-- A template headed by `,` is not one atom to add: each part is made. -/
theorem addAtom_comma_splits (x y : Atom) (s : Store) :
    (transformInto noSources (.expression [.symbol ",", x, y]) s).drain = ([2], s ++ [x, y]) := by
  rw [transformInto_noSources]
  rfl

/-! ## `remove-atom` -/

/-- **`remove-atom` is one firing that takes every match.** The rows left are exactly the
rows that do not match the pattern. -/
theorem removeAtom_form (s : Store) (p template : Atom) (C : String) :
    ((transform (collectTake p C) template s).drain).2 =
      s.filter fun row => !(matchAtom [] p row).isSome := by
  rw [transform_collect_take]

/-- For a pattern that is an expression, those are the rows `Effects.erase` leaves. -/
theorem erase_rows (state after : Effects.State) (handle : NamedSpaces.Handle)
    (first : Atom) (rest : List Atom) (rows : List Atom) (template : Atom) (C : String)
    (read : state.read handle = some rows)
    (erased : Effects.erase state handle (.expression (first :: rest)) = some after) :
    state.write handle
      ((transform (collectTake (.expression (first :: rest)) C) template rows).drain).2 =
        some after := by
  rw [removeAtom_form]
  simpa [Effects.erase, read, Effects.removalMatches] using erased

/-- The firing binds the collection to the rows it took, so the collection is empty exactly
when the store is left as it was: `remove-atom`'s answer. -/
theorem removeAtom_answer (s : Store) (p : Atom) :
    (s.filter fun row => (matchAtom [] p row).isSome) = [] ↔
      (s.filter fun row => !(matchAtom [] p row).isSome) = s := by
  constructor
  · intro none
    refine List.filter_eq_self.mpr fun row member => ?_
    have absent := List.filter_eq_nil_iff.mp none row member
    simpa using absent
  · intro same
    refine List.filter_eq_nil_iff.mpr fun row member => ?_
    have kept := List.filter_eq_self.mp same row member
    simpa using kept

/-- A `collect` in read mode takes nothing: the store is left as it was. -/
theorem collect_read_keeps (s : Store) (p : Atom) (C : String) (emit : Subst → Answers) :
    (fire s [] ⟨[.collect .read (.one p) (.var C)], [], none⟩ emit).map Prod.fst = some s := by
  rw [fire_collect_read]
  rfl

/-! ## `superpose` -/

/-- **`superpose` is an empty row with one instance for each element.** The elements are
answered in order and the store is left unchanged. -/
theorem superpose_form (items : List Atom) (s : Store) :
    (transform noSources (.expression (.symbol "," :: items)) s).drain = (items, s) := by
  rw [transform_noSources]
  rfl

/-- `empty` is the row with no instance. -/
theorem empty_form (s : Store) :
    (transform noSources (.expression [.symbol ","]) s).drain = ([], s) :=
  superpose_form [] s

end Mettapedia.Languages.MeTTa.PeTTa.TransformForms
