import Mettapedia.OSLF.Syntax.VariablePosition

/-!
# The variable comparator recognizes typed identity

For variables of the same sort in the same context, the occurrence comparator
returns true precisely when the variables are equal. Its false answer records
their distinct positions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

variable {S : Signature}

private theorem eq_of_sameVar : ∀ {Γ : Ctx S} {sort : S.Srt}
    (first second : Var Γ sort), sameVar first second = true → first = second
  | _, _, .zero, .zero, _ => rfl
  | _, _, .zero, .succ _, same => by cases same
  | _, _, .succ _, .zero, same => by cases same
  | _, _, .succ first, .succ second, same =>
      congrArg Var.succ (eq_of_sameVar first second same)

theorem sameVar_eq_true_iff {Γ : Ctx S} {sort : S.Srt}
    (first second : Var Γ sort) : sameVar first second = true ↔ first = second := by
  constructor
  · exact eq_of_sameVar first second
  · rintro rfl
    exact sameVar_self first

theorem sameVar_eq_false_iff {Γ : Ctx S} {sort : S.Srt}
    (first second : Var Γ sort) : sameVar first second = false ↔ first ≠ second := by
  constructor
  · intro compared equal
    subst second
    rw [sameVar_self] at compared
    cases compared
  · intro different
    cases compared : sameVar first second with
    | false => rfl
    | true => exact False.elim (different ((sameVar_eq_true_iff first second).mp compared))

end Mettapedia.OSLF.Binding
