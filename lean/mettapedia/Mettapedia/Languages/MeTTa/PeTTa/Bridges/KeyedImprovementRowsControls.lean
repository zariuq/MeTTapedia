import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementRows
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementControls

/-! Functional distance rows, source totality and the order boundary. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementRows.Controls

open Mettapedia.Machines.KeyedImprovement
open KeyedImprovementSource.Controls (names before after program caller distance strictly_better_replaces_and_returns_key)

def store : Mettapedia.Machines.KeyedImprovement.Store Nat Nat :=
  fun key => if key = 0 then some 10 else if key = 1 then some 5 else none

theorem ordered_rows_represent : OrderedRows.Represents [(0, 10), (1, 5)] store := by
  intro key
  by_cases zero : key = 0 <;> by_cases one : key = 1 <;> simp_all [OrderedRows.fibre, store, eq_comm]

theorem before_represents : Represents "sd" before .self store := ⟨[(0, 10), (1, 5)], rfl, ordered_rows_represent⟩

theorem actual_source_improvement_is_total :
    ∃ after answers,
      Eval.Returns program caller before (KeyedImprovementSource.source names "sd") after answers ∧
      Represents "sd" after .self (improve store 0 7).1 ∧
      answers = (if (improve store 0 7).2 then [KeyedImprovementSource.number 0] else []) :=
  source_update_refines names "sd" (by decide) program .self 0 7 before store before_represents

theorem after_represents_updated_table : Represents "sd" after .self (improve store 0 7).1 := by
  obtain ⟨result, answers, completed, represented, _⟩ :=
    run_total_refines names "sd" (by decide) .self 0 7 before store before_represents
  have same := Option.some.inj (completed.symm.trans strictly_better_replaces_and_returns_key)
  cases (Prod.mk.inj same).1
  exact represented

theorem table_retains_other_distances : (improve store 0 7).1 0 = some 7 ∧ (improve store 0 7).1 1 = some 5 := by
  decide +kernel

theorem absence_is_not_a_finite_sentinel : denote store 9 = ⊤ := rfl

theorem duplicate_source_values_remain_two :
    KeyedImprovementSource.values names "sd" caller [distance 0 10, distance 0 10] =
      [KeyedImprovementSource.number 10, KeyedImprovementSource.number 10] := by kernel_reflexivity

theorem reordered_rows_have_same_table : OrderedRows.Represents [(1, 5), (0, 10)] store := by
  intro key
  by_cases zero : key = 0 <;> by_cases one : key = 1 <;> simp_all [OrderedRows.fibre, store, eq_comm]

theorem source_enumeration_distinguishes_order :
    encodeRows "sd" [(0, 10), (1, 5)] ≠ encodeRows "sd" [(1, 5), (0, 10)] := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementRows.Controls
