import Mettapedia.Languages.MM0.Kernel.DeclarationAdmission

/-! # Declaration admission, free variables and sort restrictions -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.DeclarationAdmissionControls

private def sorts : SortSignature
  | 0 => some {}
  | 1 => some { provable := true }
  | 2 => some { free := true }
  | 3 => some { strict := true }
  | 4 => some { pure := true }
  | _ => none

private def signature : TermSignature
  | 0 => some ⟨[.bound 0, .regular 1 {0}], 1, ∅⟩
  | 1 => some ⟨[.regular 0 ∅], 1, ∅⟩
  | 2 => some ⟨[], 1, ∅⟩
  | 3 => some ⟨[.regular 2 ∅], 1, ∅⟩
  | 4 => some ⟨[.bound 2, .regular 1 {0}], 1, ∅⟩
  | 5 => some ⟨[], 0, ∅⟩
  | _ => none

theorem dependent_constructor_accepted :
    TermDecl.check sorts ⟨[.bound 0, .regular 1 {0}], 1, {0}⟩ = true := by decide

theorem pure_result_forbids_constructor :
    TermDecl.check sorts ⟨[], 4, ∅⟩ = false := by decide

theorem unknown_result_sort_refuses :
    TermDecl.check sorts ⟨[], 5, ∅⟩ = false := by decide

theorem forward_context_dependency_refuses :
    TermDecl.check sorts ⟨[.regular 1 {1}, .bound 0], 1, ∅⟩ = false := by decide

theorem regular_return_dependency_refuses :
    TermDecl.check sorts ⟨[.regular 1 ∅], 1, {0}⟩ = false := by decide

theorem declared_free_parameter_accepted :
    Definition.checkBody sorts signature ⟨[.bound 2], 1, {0}⟩
      ⟨[], .app (.term 3) (.var 0)⟩ = true := by decide

theorem undeclared_free_parameter_refuses :
    Definition.checkBody sorts signature ⟨[.bound 2], 1, ∅⟩
      ⟨[], .app (.term 3) (.var 0)⟩ = false := by decide

theorem nonfree_parameter_also_requires_dependency :
    Definition.checkBody sorts signature ⟨[.bound 0], 1, ∅⟩
      ⟨[], .app (.term 1) (.var 0)⟩ = false := by decide

theorem declared_nonfree_parameter_accepted :
    Definition.checkBody sorts signature ⟨[.bound 0], 1, {0}⟩
      ⟨[], .app (.term 1) (.var 0)⟩ = true := by decide

theorem bound_dummy_accepted :
    Definition.checkBody sorts signature ⟨[.bound 0], 1, ∅⟩
      ⟨[0], .applyArgs (.term 0) [.var 1, .app (.term 1) (.var 1)]⟩ = true := by decide

theorem escaping_dummy_refuses :
    Definition.checkBody sorts signature ⟨[.bound 0], 1, ∅⟩
      ⟨[0], .app (.term 1) (.var 1)⟩ = false := by decide

theorem free_dummy_refuses_even_when_bound :
    Definition.checkBody sorts signature ⟨[], 1, ∅⟩
      ⟨[2], .applyArgs (.term 4) [.var 0, .app (.term 3) (.var 0)]⟩ = false := by decide

theorem strict_dummy_refuses_even_when_unused :
    Definition.checkBody sorts signature ⟨[], 1, ∅⟩
      ⟨[3], .term 2⟩ = false := by decide

theorem unknown_dummy_sort_refuses :
    Definition.checkBody sorts signature ⟨[], 1, ∅⟩
      ⟨[10], .term 2⟩ = false := by decide

theorem wrong_body_sort_refuses :
    Definition.checkBody sorts signature ⟨[], 1, ∅⟩
      ⟨[], .term 5⟩ = false := by decide

theorem missing_prior_symbol_refuses :
    Definition.checkBody sorts signature ⟨[], 1, ∅⟩
      ⟨[], .term 99⟩ = false := by decide

theorem saturated_provable_statement_accepted :
    TheoremDecl.check sorts signature ⟨[], [.term 2], .term 2⟩ = true := by decide

theorem nonprovable_conclusion_refuses :
    TheoremDecl.check sorts signature ⟨[], [], .term 5⟩ = false := by decide

theorem nonprovable_hypothesis_refuses :
    TheoremDecl.check sorts signature ⟨[], [.term 5], .term 2⟩ = false := by decide

theorem partial_statement_refuses :
    TheoremDecl.check sorts signature ⟨[], [], .term 0⟩ = false := by decide

theorem malformed_theorem_context_refuses :
    TheoremDecl.check sorts signature ⟨[.bound 3], [], .term 2⟩ = false := by decide

end Mettapedia.Languages.MM0.Kernel.DeclarationAdmissionControls
