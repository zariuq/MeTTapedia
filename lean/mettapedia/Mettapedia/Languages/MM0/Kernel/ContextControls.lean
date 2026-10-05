import Mettapedia.Languages.MM0.Kernel.Context

/-! # Ordered dependencies and sort restrictions in MM0 contexts -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.ContextControls

private def sorts : SortSignature
  | 0 => some { free := true }
  | 1 => some { provable := true }
  | 2 => some { strict := true }
  | _ => none

theorem prior_bound_dependency_accepted :
    Context.check sorts [.bound 0, .regular 1 {0}] = true := by decide

theorem forward_dependency_rejected :
    Context.check sorts [.regular 1 {1}, .bound 0] = false := by decide

theorem self_dependency_rejected :
    Context.check sorts [.regular 1 {0}] = false := by decide

theorem regular_dependency_rejected :
    Context.check sorts [.regular 0 ∅, .regular 1 {0}] = false := by decide

theorem unknown_sort_rejected : Context.check sorts [.regular 3 ∅] = false := by decide

theorem strict_bound_rejected : Context.check sorts [.bound 2] = false := by decide

theorem strict_regular_accepted : Context.check sorts [.regular 2 ∅] = true := by decide

/-- The free-sort dummy prohibition does not forbid named bound parameters. -/
theorem free_named_parameter_accepted : Context.check sorts [.bound 0] = true := by decide

theorem forward_dependency_not_wellFormed :
    ¬ Context.WellFormed sorts [.regular 1 {1}, .bound 0] := by
  intro formed
  have checked := (Context.check_iff _ _).mpr formed
  rw [forward_dependency_rejected] at checked
  contradiction

end Mettapedia.Languages.MM0.Kernel.ContextControls
