import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-! # Joint row readings retain shared unknowns -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreAliasControls

open Mettapedia.Logic.LP
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)

def rows : Finset (Term atoms) := {.var 0, .var 1}
def values : Finset (Term atoms) := {.const 5, .const 6}

theorem independent_unknowns_allow_distinct_values : values ∈ SetStore.readings (signature := atoms) [] rows := by
  refine ⟨(fun v => if v = 0 then .const 5 else .const 6), ?_, ?_⟩
  · intro equation inside
    cases inside
  · simp [rows, values, Subst.applyTerm]

theorem aliased_unknowns_refuse_distinct_values :
    values ∉ SetStore.readings (signature := atoms) [(.var 0, .var 1)] rows := by
  rintro ⟨assignment, solves, result⟩
  have shared : assignment 0 = assignment 1 := solves _ List.mem_cons_self
  have single : values = {assignment 0} := by
    simpa [rows, Subst.applyTerm, ← shared] using result
  have cards := congrArg Finset.card single
  have two : values.card = 2 := by decide +kernel
  rw [two, Finset.card_singleton] at cards
  omega

theorem aliases_can_merge_duplicate_rows :
    ({.const 5} : Finset (Term atoms)) ∈ SetStore.readings (signature := atoms) [(.var 0, .var 1)] rows := by
  refine ⟨(fun _ => .const 5), ?_, ?_⟩
  · intro equation inside
    obtain rfl := List.mem_singleton.mp inside
    rfl
  · simp [rows, Subst.applyTerm]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreAliasControls
