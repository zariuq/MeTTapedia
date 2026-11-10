import Mettapedia.Data.List.CountedErase
import Mettapedia.Languages.MeTTa.ContextualTransform.StoreSelectionPolicies

/-!
# Counted removal policies interpreted as transform effects

The source policies are independently recursive list deletion and an explicit
exact-quota wrapper. The target scans only the required prefix, retains its
selected identities and publishes their stable contraction. It never treats
equal payload values as one physical occurrence.

The correspondence is at the captured selection state. Retaining the plan
across interfering writes requires a separate source-order/dependency law.
Neither exact nor at-most quota is selected here as a default MeTTa policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.CountedStoreInterpretation

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open Mettapedia.Data.List

universe uO uT uH uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) (a : Obj) {O : Type uOcc} [DecidableEq O]
  (label : O → Tm a)

def request (select : Tm a → Bool) (count : Nat) (rows : List O) :
    OrderedStore.Publication (Tm a) O :=
  ⟨⟨(CountedErase.scan (fun occurrence => select (label occurrence)) count rows).1, [], []⟩, []⟩

theorem admitted (select : Tm a → Bool) (count : Nat) (rows : List O) (unique : rows.Nodup)
    (knowledge : EquationStore (Tm a)) (consistent : X.Solvable knowledge) :
    (OrderedStore.step X a label).Admits (s := (knowledge, rows))
      (request (a := a) label select count rows) := by
  have subset := CountedErase.prefix_sublist (fun occurrence => select (label occurrence)) count rows
  refine ⟨⟨unique, subset.nodup unique, List.nodup_nil⟩, ?_, consistent⟩
  refine ⟨?_, by simp [request, OrderedStore.Publication.commit, Selection.commit],
    by simp [request, OrderedStore.Publication.commit, Selection.commit],
    by simp [request, OrderedStore.Publication.commit, Selection.commit], ?_⟩
  · intro occurrence member
    exact List.mem_toFinset.mpr (subset.subset (List.mem_toFinset.mp member))
  · intro query member
    simp [request, OrderedStore.Publication.commit] at member

theorem up_to_correspondence (select : Tm a → Bool) (count : Nat) (rows : List O)
    (unique : rows.Nodup) (knowledge : EquationStore (Tm a))
    (permission : (OrderedStore.step X a label).Admits (s := (knowledge, rows))
      (request (a := a) label select count rows)) :
    (((OrderedStore.step X a label).result (request (a := a) label select count rows) permission).2.map label) =
      CountedErase.eraseUpTo select count (rows.map label) := by
  have contraction := congrArg (List.map label)
    (CountedErase.filter_selected (fun occurrence => select (label occurrence)) count rows unique)
  have observation := contraction.trans (CountedErase.erase_map label select count rows)
  simpa [OrderedStore.result_rows, request, OrderedStore.publish, OrderedStore.survivors] using observation

def prepareExactly (select : Tm a → Bool) (count : Nat) (rows : List O) :
    Option (OrderedStore.Publication (Tm a) O) :=
  let selected := request (a := a) label select count rows
  if selected.selection.taken.length = count then some selected else none

omit [DecidableEq O] in
theorem exact_preparation_iff (select : Tm a → Bool) (count : Nat) (rows : List O)
    (selected : OrderedStore.Publication (Tm a) O) :
    prepareExactly (a := a) label select count rows = some selected ↔
      count ≤ ((rows.map label).filter select).length ∧ selected = request (a := a) label select count rows := by
  simp [prepareExactly, request, CountedErase.prefix_length, List.filter_map,
    Function.comp_def, eq_comm]

/-- Preservation and reflection for exact quota include refusal on shortage;
an admitted shorter take is not silently substituted for the requested quota. -/
theorem exact_iff_target (select : Tm a → Bool) (count : Nat) (rows : List O)
    (unique : rows.Nodup) (knowledge : EquationStore (Tm a)) (consistent : X.Solvable knowledge)
    (kept : List (Tm a)) :
    CountedErase.eraseExactly select count (rows.map label) = some kept ↔
      ∃ selected, prepareExactly (a := a) label select count rows = some selected ∧
        ∃ permission : (OrderedStore.step X a label).Admits (s := (knowledge, rows)) selected,
          (((OrderedStore.step X a label).result selected permission).2.map label) = kept := by
  rw [CountedErase.exact_accepted_iff]
  constructor
  · rintro ⟨enough, rfl⟩
    have permission := admitted X a label select count rows unique knowledge consistent
    exact ⟨_, (exact_preparation_iff a label select count rows _).mpr ⟨enough, rfl⟩,
      permission, up_to_correspondence X a label select count rows unique knowledge permission⟩
  · rintro ⟨selected, prepared, permission, observed⟩
    obtain ⟨enough, rfl⟩ := (exact_preparation_iff a label select count rows selected).mp prepared
    exact ⟨enough, (up_to_correspondence X a label select count rows unique knowledge permission).symm.trans observed⟩

omit [DecidableEq O] in
/-- The selection's inspection count is bounded by the source prefix needed
to satisfy the quota, independently of an arbitrary unused tail. -/
theorem selection_ignores_unused_tail (select : Tm a → Bool) (count : Nat)
    (before after : List O) (enough : count ≤ ((before.map label).filter select).length) :
    CountedErase.scan (fun occurrence => select (label occurrence)) count (before ++ after) =
      CountedErase.scan (fun occurrence => select (label occurrence)) count before := by
  apply CountedErase.full_prefix_stops_before_tail
  simpa [List.filter_map, Function.comp_def] using enough

end Mettapedia.Languages.MeTTa.ContextualTransform.CountedStoreInterpretation
