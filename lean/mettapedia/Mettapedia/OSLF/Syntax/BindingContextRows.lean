import Mettapedia.OSLF.Syntax.BindingContextPositions

/-!
# Typed variables over an explicit finite declaration table

Rows determine a context by their sorts. Lookup selects a row's variable,
and projection interprets that variable by the row's existing typed value.
Duplicate-free rows give an inverse position law. Sort equality is transported
explicitly; no decision procedure on the sort carrier is required.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextRows

open ContextPositions

variable {S : Signature} {Key : Type} [DecidableEq Key]
  (sortOf : Key → S.Srt) (rows : List Key)

abbrev context : Ctx S := rows.map sortOf

def rowAt {sort : S.Srt} (position : Var (context sortOf rows) sort) : Key :=
  rows.get ⟨CommonABT.index position, by simpa [context] using CommonABT.index_lt position⟩

omit [DecidableEq Key] in
theorem rowAt_mem {sort : S.Srt} (position : Var (context sortOf rows) sort) :
    rowAt sortOf rows position ∈ rows := List.get_mem _ _

omit [DecidableEq Key] in
theorem rowSort {sort : S.Srt} (position : Var (context sortOf rows) sort) :
    sortOf (rowAt sortOf rows position) = sort := by
  have recorded := slot_sort (S := S) position
  simpa only [context, rowAt, toSlot, List.get_eq_getElem, List.getElem_map] using recorded

def project {Γ : Ctx S} (values : (key : Key) → Var Γ (sortOf key)) :
    Ren S (context sortOf rows) Γ :=
  fun _ position => castSort (rowSort sortOf rows position) (values (rowAt sortOf rows position))

def rowSlot (key : Key) (member : key ∈ rows) : Fin (context sortOf rows).length :=
  ⟨rows.idxOf key, by simpa [context] using List.idxOf_lt_length_of_mem member⟩

theorem rowSlot_sort (key : Key) (member : key ∈ rows) :
    (context sortOf rows).get (rowSlot sortOf rows key member) = sortOf key := by
  simp only [context, rowSlot, List.get_eq_getElem, List.getElem_map, List.getElem_idxOf]

def select (key : Key) (member : key ∈ rows) : Var (context sortOf rows) (sortOf key) :=
  castSort (rowSlot_sort sortOf rows key member)
    (ofSlot (context sortOf rows) (rowSlot sortOf rows key member))

theorem index_select (key : Key) (member : key ∈ rows) :
    CommonABT.index (select sortOf rows key member) = rows.idxOf key := by
  rw [select, index_castSort, index_ofSlot]
  rfl

theorem rowAt_select (key : Key) (member : key ∈ rows) :
    rowAt sortOf rows (select sortOf rows key member) = key := by
  simp only [rowAt, index_select, List.get_eq_getElem, List.getElem_idxOf]

theorem project_select {Γ : Ctx S} (values : (key : Key) → Var Γ (sortOf key))
    (key : Key) (member : key ∈ rows) :
    project sortOf rows values (sortOf key) (select sortOf rows key member) = values key := by
  have transported := castSort_heq (rowSort sortOf rows (select sortOf rows key member))
    (values (rowAt sortOf rows (select sortOf rows key member)))
  have sameRow := rowAt_select (S := S) sortOf rows key member
  have valuePair := congrArg (fun entry : Key =>
    (⟨sortOf entry, values entry⟩ : (sort : S.Srt) × Var Γ sort)) sameRow
  exact eq_of_heq (transported.trans (Sigma.mk.inj valuePair).2)

omit [DecidableEq Key] in
theorem index_project {Γ : Ctx S} (values : (key : Key) → Var Γ (sortOf key))
    {sort : S.Srt} (position : Var (context sortOf rows) sort) :
    CommonABT.index (project sortOf rows values sort position) =
      CommonABT.index (values (rowAt sortOf rows position)) :=
  index_castSort _ _

theorem index_select_rowAt (distinct : rows.Nodup) {sort : S.Srt}
    (position : Var (context sortOf rows) sort) :
    CommonABT.index (select sortOf rows (rowAt sortOf rows position) (rowAt_mem sortOf rows position)) =
      CommonABT.index position := by
  rw [index_select]
  have inside : CommonABT.index position < rows.length := by
    simpa [context] using CommonABT.index_lt position
  simpa only [rowAt, List.get_eq_getElem] using distinct.idxOf_getElem (CommonABT.index position) inside

/-- No duplicate row can silently merge two physical parameter positions. -/
theorem select_rowAt (distinct : rows.Nodup) {sort : S.Srt}
    (position : Var (context sortOf rows) sort) :
    castSort (rowSort sortOf rows position)
      (select sortOf rows (rowAt sortOf rows position) (rowAt_mem sortOf rows position)) = position := by
  apply CommonABT.index_injective (S := S)
  rw [index_castSort]
  exact index_select_rowAt sortOf rows distinct position

end Mettapedia.OSLF.Binding.ContextRows
