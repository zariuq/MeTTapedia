import Mettapedia.Languages.MeTTa.PeTTa.RunsChained
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingGround

/-!
# On ground spaces a request carries its predicate query

The requests of `RunsAsFirings` say which occurrences a `match` reads and a `remove-atom`
takes, and nothing about the occurrences they leave. In general that cannot be said by a
predicate of the stored atom: the machine renames each row for its own use before it
unifies. On a space whose rows are ground the renaming is the identity and unification is
one-way matching (`Unifying.unify_ground`), so the selection is a predicate of the atom,
and the request can carry the observation that it selected every occurrence of its space
that satisfies it. The step checks that observation when it admits the request.

So that one observation can tell the spaces apart, the step is told an occurrence as its
atom with its space (`Supply.located`).

* `scan_ground`, `selectedRows_ground`: on ground rows the scan of a `match` and the
  selection of a removal are filters by one-way matching.
* `ground_match_query`: on a ground space, the occurrences a `match` reads are exactly
  those of the read request with its predicate query (`StoreOperations.readRequest`) for "is in
  this space and the pattern matches its atom", and the step admits that request.
* `ground_remove_query`: the same for the occurrences a `remove-atom` takes.

Negative example: `Controls.open_row_not_a_filter` (a stored row with a variable is
selected by a pattern that does not match it one way, so the filter misses it).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst matchAtom isGroundAtom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open Mettapedia.Languages.MeTTa.ContextualTransform
open PeTTaStoreSelection (atomFrames selectedRows)
open PeTTaQueryInterpretation (scan)
open Unifying (resolve)
open NamedSpaces (Handle)

/-- On ground rows the scan of a `match` is a filter by one-way matching: every row the
pattern matches, in store order, with the bindings of the match. -/
theorem scan_ground {O : Type} (label : O → Atom) {bindings : Subst} {pattern : Atom}
    (range : Unifying.GroundRange bindings) :
    ∀ (use : Nat) (rows : List O), (∀ row ∈ rows, isGroundAtom (label row) = true) →
      scan label bindings pattern use rows =
        some (rows.filterMap fun row =>
          (matchAtom bindings pattern (label row)).map fun bound => (row, bound))
  | _, [], _ => rfl
  | use, row :: rest, ground => by
      have rowGround := ground row List.mem_cons_self
      simp only [scan, scan_ground label range (use + 1) rest
        (fun item member => ground item (List.mem_cons_of_mem _ member)), Option.bind_eq_bind,
        Option.bind_some, Unifying.rename_ground use (label row) rowGround,
        Unifying.unify_ground range rowGround, List.filterMap_cons]
      cases matchAtom bindings pattern (label row) <;> rfl

/-- On ground rows the selection of a removal is a filter by one-way matching. -/
theorem selectedRows_ground {O : Type} (label : O → Atom) {first : Atom}
    {others : List Atom} :
    ∀ (use : Nat) (rows : List O), (∀ row ∈ rows, isGroundAtom (label row) = true) →
      selectedRows label (.expression (first :: others)) use rows =
        some (rows.filter fun row =>
          Effects.removalMatches (.expression (first :: others)) (label row))
  | _, [], _ => rfl
  | use, row :: rest, ground => by
      have rowGround := ground row List.mem_cons_self
      simp only [selectedRows, selectedRows_ground label (use + 1) rest
        (fun item member => ground item (List.mem_cons_of_mem _ member)), Option.bind_eq_bind,
        Option.bind_some, Unifying.rename_ground use (label row) rowGround,
        Unifying.unify_ground (bindings := []) (fun _ never => by cases never) rowGround,
        List.filter_cons, Effects.removalMatches]
      cases matchAtom [] (.expression (first :: others)) (label row) <;> simp

variable {O : Type} [DecidableEq O] (S : Supply O)

/-- An occurrence as the step is told it: its atom with its space. -/
def Supply.located (occurrence : O) : Atom :=
  .expression [Effects.handleValue (S.place occurrence), S.label occurrence]

/-- "In the space `handle`, and its atom passes `test`", as a predicate of a located atom. -/
def selectAt (handle : Handle) (test : Atom → Bool) : Atom → Bool
  | .expression [space, atom] => space == Effects.handleValue handle && test atom
  | _ => false

omit [DecidableEq O] in
theorem selectAt_located (handle : Handle) (test : Atom → Bool) (occurrence : O) :
    selectAt handle test (S.located occurrence) =
      (decide (S.place occurrence = handle) && test (S.label occurrence)) := by
  simp only [selectAt, Supply.located]
  congr 1
  by_cases same : S.place occurrence = handle
  · simp [same]
  · have different : Effects.handleValue (S.place occurrence) ≠ Effects.handleValue handle :=
      fun equal => same (Effects.handleValue_injective equal)
    simp [same, different]

omit [DecidableEq O] in
/-- The occurrences an observation of one space selects are the occurrences of that space
that pass the test. -/
theorem filter_selectAt (handle : Handle) (test : Atom → Bool) (ids : List O) :
    ids.filter (fun occurrence => selectAt handle test (S.located occurrence)) =
      (S.rowsAt handle ids).filter fun occurrence => test (S.label occurrence) := by
  simp only [Supply.rowsAt, List.filter_filter]
  apply List.filter_congr
  intro occurrence _
  rw [selectAt_located, Bool.and_comm]

omit [DecidableEq O] in
theorem fst_filterMap_map {α β : Type} (rows : List α) (found : α → Option β) :
    (rows.filterMap fun row => (found row).map fun value => (row, value)).map Prod.fst =
      rows.filter fun row => (found row).isSome := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      cases value : found row <;> simp [value, ih]

/-- The read request with its predicate query: the occurrences whose located atom passes `select`,
and the observation that they are all of them. -/
abbrev readWithQuery (select : Atom → Bool) (ids : List O) : OrderedStore.Publication Atom O :=
  StoreOperations.readRequest (Tm := fun _ : PUnit.{1} => Atom) (a := PUnit.unit) S.located
    select ids

/-- The removal request with its predicate query. -/
abbrev removeWithQuery (select : Atom → Bool) (ids : List O) :
    OrderedStore.Publication Atom O :=
  StoreOperations.removeRequest (Tm := fun _ : PUnit.{1} => Atom) (a := PUnit.unit) S.located
    select ids

variable {S}

/-- **On a ground space a `match` reads with its predicate query.** The occurrences the machine's
scan selects are exactly those of the read request that carries the observation "every
occurrence of this space whose atom the pattern matches", and the ordered-store step,
told each occurrence with its space, admits that request: its admission checks the
observation. -/
theorem ground_match_query {ids : List O} {state : Effects.State}
    (tracks : Tracks S ids state) (handle : Handle) {bindings : Subst} (pattern : Atom)
    (use : Nat) (range : Unifying.GroundRange bindings)
    (ground : ∀ occurrence ∈ S.rowsAt handle ids, isGroundAtom (S.label occurrence) = true)
    (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∃ packets, scan S.label bindings pattern use (S.rowsAt handle ids) = some packets ∧
      (readWithQuery S (selectAt handle fun atom => (matchAtom bindings pattern atom).isSome)
        ids).selection.read = packets.map Prod.fst ∧
      (OrderedStore.step atomFrames PUnit.unit S.located).Admits (s := (knowledge, ids))
        (readWithQuery S (selectAt handle fun atom => (matchAtom bindings pattern atom).isSome)
          ids) := by
  refine ⟨_, scan_ground S.label range use _ ground, ?_, ?_⟩
  · rw [fst_filterMap_map]
    exact filter_selectAt S handle _ ids
  · exact (StoreOperations.read_admits_exact atomFrames PUnit.unit S.located _ knowledge
      ids).mpr ⟨tracks.distinct, consistent⟩

/-- **On a ground space a `remove-atom` takes with its predicate query.** -/
theorem ground_remove_query {ids : List O} {state : Effects.State}
    (tracks : Tracks S ids state) (handle : Handle) (first : Atom) (others : List Atom)
    (use : Nat)
    (ground : ∀ occurrence ∈ S.rowsAt handle ids, isGroundAtom (S.label occurrence) = true)
    (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∃ taken, selectedRows S.label (.expression (first :: others)) use (S.rowsAt handle ids) =
        some taken ∧
      (removeWithQuery S
        (selectAt handle (Effects.removalMatches (.expression (first :: others))))
        ids).selection.taken = taken ∧
      (OrderedStore.step atomFrames PUnit.unit S.located).Admits (s := (knowledge, ids))
        (removeWithQuery S
          (selectAt handle (Effects.removalMatches (.expression (first :: others)))) ids) := by
  refine ⟨_, selectedRows_ground S.label use _ ground, ?_, ?_⟩
  · exact filter_selectAt S handle _ ids
  · exact (StoreOperations.remove_admits_exact atomFrames PUnit.unit S.located _ knowledge
      ids).mpr ⟨tracks.distinct, consistent⟩

namespace Controls

/-- Negative: a stored row with a variable is selected by a pattern that does not match it
one way, so on a space that is not ground the selection is not that filter. -/
theorem open_row_not_a_filter :
    (scan (fun _ : Nat => p (.var "stored")) [] (p a) 0 [7]).map (fun packets =>
        packets.map Prod.fst) = some [7] ∧
    ([7].filter fun _ : Nat => (matchAtom [] (p a) (p (.var "stored"))).isSome) = [] := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings
