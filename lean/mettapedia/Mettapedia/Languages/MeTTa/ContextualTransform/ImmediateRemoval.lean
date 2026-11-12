import Mettapedia.Machines.ImmediateStorePublication
import Mettapedia.Data.List.CountedErase
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection

/-!
# Immediate publication after dialect selection

One-occurrence deletion uses the independent ordered source operation. PeTTa
selection uses its actual scoped unifier separately at every row. Both publish
physical identities only after that selection has completed. No second
unification is part of publication. These are the selection/publication parts
of the dialect contracts, not whole typed builtin invocation theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.ImmediateRemoval

open Mettapedia.Machines
open Mettapedia.Data.List
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
open StoreAndDemand

universe u v
variable {O : Type u} [DecidableEq O] {Value : Type v}

def publishSelected (world : PreparedStoreProtocol.World O) (selected : List O) :
    ImmediateStorePublication.Reply × PreparedStoreProtocol.World O :=
  ImmediateStorePublication.immediate id world ⟨.erase selected, true⟩

theorem selected_contraction (world : PreparedStoreProtocol.World O) (selected : List O) :
    (publishSelected world selected).2.rows = OrderedStore.survivors world.rows selected := by
  simp [publishSelected, ImmediateStorePublication.immediate,
    PreparedStoreProtocol.Admissible, PreparedStoreProtocol.Operation.made,
    ImmediateStorePublication.directRows, OrderedStore.survivors]

theorem one_is_counted_one (select : Value → Bool) (rows : List Value) :
    CountedErase.eraseUpTo select 1 rows = StoreEffects.removeOne select rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      cases selected : select row <;>
        simp [CountedErase.eraseUpTo, StoreEffects.removeOne, List.eraseP, selected] at ih ⊢
      exact ih

/-- The bounded selector establishes which occurrence is first. Its
publication preserves later equal payload copies and the survivor order. -/
theorem first_source_exact (label : O → Value) (select : Value → Bool)
    (world : PreparedStoreProtocol.World O) :
    ((publishSelected world
        (CountedErase.scan (fun occurrence => select (label occurrence)) 1 world.rows).1).2.rows.map label) =
      StoreEffects.removeOne select (world.rows.map label) := by
  rw [selected_contraction]
  change (world.rows.filter (fun occurrence => decide
    (occurrence ∉ (CountedErase.scan (fun row => select (label row)) 1 world.rows).1))).map label = _
  rw [CountedErase.filter_selected _ _ _ world.unique, CountedErase.erase_map, one_is_counted_one]

section PeTTa

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
variable {Occurrence : Type} [DecidableEq Occurrence] (label : Occurrence → Atom)

/-- Each success/clash evidence belongs to its own renamed source row. The
publishing operation consumes the completed selection without combining those
bindings or invoking the source unifier again. -/
theorem scoped_selection_exact (world : PreparedStoreProtocol.World Occurrence)
    (pattern : Atom) (use : Nat) (kept taken : List Occurrence)
    (selection : PeTTaStoreSelection.Removal label pattern use world.rows kept taken) :
    (publishSelected world taken).2.rows = kept := by
  rw [selected_contraction]
  exact PeTTaStoreSelection.Removal.contracts label selection world.unique

theorem completed_preparation_has_source_result
    (world : PreparedStoreProtocol.World Occurrence) (pattern : Atom) (use : Nat)
    (taken : List Occurrence)
    (prepared : PeTTaStoreSelection.selectedRows label pattern use world.rows = some taken) :
    PeTTa.Unifying.survivors pattern use (world.rows.map label) =
      some ((publishSelected world taken).2.rows.map label) := by
  obtain ⟨kept, selection⟩ := PeTTaStoreSelection.prepared_selection label prepared
  rw [scoped_selection_exact label world pattern use kept taken selection]
  exact PeTTaStoreSelection.Removal.source label selection

end PeTTa

namespace Controls

def copies : PreparedStoreProtocol.World Nat := ⟨1, [0, 2, 1], by decide⟩
def inserted : PreparedStoreProtocol.World Nat := ⟨1, [0, 1, 2], by decide⟩

theorem first_is_not_all_equal_copies :
    (publishSelected copies (CountedErase.scan (fun n => n % 2 == 0) 1 copies.rows).1).2.rows = [2, 1] ∧
      (ImmediateStorePublication.immediate (fun n => n % 2) copies ⟨.erase [0], true⟩).2.rows = [1] := by
  decide

/-- A retained occurrence can remain present while losing its first-match
property. Presence alone does not justify reusing an ordered selection. -/
theorem insertion_can_invalidate_first_selection_without_consuming_it :
    1 ∈ inserted.rows ∧
      (publishSelected inserted [1]).2.rows ≠ StoreEffects.removeOne (fun _ => true) inserted.rows := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.ImmediateRemoval
