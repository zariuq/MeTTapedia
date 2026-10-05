import Mettapedia.Languages.MM0.Kernel.Support

/-! # Controls for MM0 context-relative occurrence support -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.SupportControls

open Preterm

def dependentContext : Context := [.bound 0, .regular 1 {0}]

def independentContext : Context := [.bound 0, .regular 1 ∅]

def twoBoundContext : Context := [.bound 0, .bound 0]

theorem bound_support_exact : support? dependentContext (.var 0) = some {0} := by decide

/-- A regular open variable carries its declared dependencies, not its own index. -/
theorem regular_dependency_support_exact :
    support? dependentContext (.var 1) = some {0} := by decide

theorem regular_dependency_occurs : HasVar dependentContext 0 (.var 1) :=
  .regular (by rfl) (by decide)

theorem regular_own_index_absent : ¬ HasVar dependentContext 1 (.var 1) := by
  simp [hasVar_var_iff, dependentContext]

theorem independent_regular_empty : support? independentContext (.var 1) = some ∅ := by decide

theorem independent_regular_no_bound_occurrence :
    ¬ HasVar independentContext 0 (.var 1) := by
  simp [hasVar_var_iff, independentContext]

theorem symbol_support_empty : support? dependentContext (.term 37) = some ∅ := rfl

/-- Bound arguments remain in occurrence support, even below a term symbol. -/
theorem bound_argument_retained :
    support? dependentContext (.app (.term 0) (.var 0)) = some {0} := by decide

theorem all_application_positions_retained :
    support? twoBoundContext (applyArgs (.term 0) [.var 0, .var 1]) = some {0, 1} := by decide

theorem duplicate_occurrence_not_counted_twice :
    support? dependentContext (applyArgs (.term 0) [.var 0, .var 1]) = some {0} := by decide

theorem undefined_variable_refuses : support? dependentContext (.var 2) = none := by decide

theorem undefined_child_refuses :
    support? dependentContext (.app (.var 0) (.var 2)) = none := by decide

/-- Partial occurrence evidence from a live child cannot validate the entire preterm. -/
theorem live_child_occurs_while_whole_refuses :
    HasVar dependentContext 0 (.app (.var 0) (.var 2)) ∧
      support? dependentContext (.app (.var 0) (.var 2)) = none :=
  ⟨.function (.bound (by rfl)), undefined_child_refuses⟩

theorem undefined_child_has_no_support_derivation :
    ¬ ∃ support, Supports dependentContext (.app (.var 0) (.var 2)) support :=
  (support_none_iff _ _).mp undefined_child_refuses

end Mettapedia.Languages.MM0.Kernel.SupportControls
