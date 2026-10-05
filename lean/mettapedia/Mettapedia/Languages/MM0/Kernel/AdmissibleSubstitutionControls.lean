import Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitution

/-! # Separating dependency-sensitive MM0 substitution from raw replacement -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitutionControls

private def signature : TermSignature
  | 0 => some ⟨[.regular 0 ∅], 1, ∅⟩
  | 1 => some ⟨[], 1, ∅⟩
  | 2 => some ⟨[.bound 0], 1, ∅⟩
  | _ => none

private def independent : Context := [.bound 0, .regular 1 ∅]
private def dependent : Context := [.bound 0, .regular 1 {0}]

theorem closed_image_permitted :
    Substitution.checkAdmissible signature independent [.regular 1 ∅, .bound 0]
      [.var 1, .term 1] = true := by decide

theorem formal_target_context_confusion_rejected :
    Substitution.checkAdmissible signature independent [.regular 1 ∅, .bound 0]
      [.var 1, .app (.term 0) (.var 1)] = false := by decide

theorem declared_target_dependency_rejected :
    Substitution.checkAdmissible signature independent dependent [.var 0, .var 1] = false := by decide

theorem permitted_dependency_accepted :
    Substitution.checkAdmissible signature dependent dependent [.var 0, .var 1] = true := by decide

theorem independent_target_variable_accepted :
    Substitution.checkAdmissible signature independent independent [.var 0, .var 1] = true := by decide

theorem bound_argument_occurrence_retained :
    Substitution.checkAdmissible signature independent [.bound 0]
      [.var 0, .app (.term 2) (.var 0)] = false := by decide

theorem distinct_bound_images_required :
    Substitution.checkAdmissible signature [.bound 0, .bound 0] [.bound 0]
      [.var 0, .var 0] = false := by decide

theorem separate_bound_images_accepted :
    Substitution.checkAdmissible signature [.bound 0, .bound 0] [.bound 0, .bound 0]
      [.var 1, .var 0] = true := by decide

theorem later_bound_image_fresh_for_earlier_regular_image :
    Substitution.checkAdmissible signature [.regular 1 ∅, .bound 0] dependent
      [.var 1, .var 0] = false := by decide

theorem extra_argument_rejected :
    Substitution.checkAdmissible signature independent independent
      [.var 0, .var 1, .term 1] = false := by decide

theorem missing_argument_rejected :
    Substitution.checkAdmissible signature independent independent [.var 0] = false := by decide

theorem typed_computation_returns_substituted_body :
    Substitution.instantiate signature independent [.regular 1 ∅, .bound 0]
      [.var 1, .term 1] (.var 1) = some (.term 1) := by decide

theorem unsafe_computation_refuses :
    Substitution.instantiate signature independent dependent [.var 0, .var 1] (.var 1) = none :=
  by decide

theorem unsafe_substitution_has_no_admission :
    ¬ Substitution.Admissible signature independent dependent [.var 0, .var 1] := by
  intro admitted
  have accepted := (Substitution.checkAdmissible_iff _ _ _ _).mpr admitted
  rw [declared_target_dependency_rejected] at accepted
  contradiction

end Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitutionControls
