import Mettapedia.OSLF.Syntax.ContextualRigidTerms
import Mettapedia.OSLF.Syntax.ContextualFamilySupport

/-! # Rigid binding-term inclusion reflects equality and has empty meta support -/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualFamily.Rigid

variable {S : Signature} {V : Type} (declaration : V → MetaArity S)

mutual
theorem include_injective : ∀ {Γ : Ctx S} {sort : S.Srt}
    (first second : Term S Γ sort),
    includeTerm declaration first = includeTerm declaration second → first = second
  | _, _, .var first, .var second, same => congrArg (Term.var (S := S)) (Term.var.inj (S := signature S declaration) same)
  | _, _, .var _, .op _ _, same => by cases same
  | _, _, .op _ _, .var _, same => by cases same
  | _, _, .op operator arguments, .op other others, same => by
      have operators := Sum.inl.inj (Term.op.inj same).1
      subst other
      exact congrArg (Term.op operator)
        (includeArgs_injective arguments others (eq_of_heq (Term.op.inj same).2))

theorem includeArgs_injective : ∀ {Γ : Ctx S} {arities : List (List S.Srt × S.Srt)}
    (first second : Args S arities Γ),
    includeArgs declaration first = includeArgs declaration second → first = second
  | _, _, .nil, .nil, _ => rfl
  | _, _, .cons first rest, .cons second tail, same => by
      have components := Args.cons.inj same
      exact congrArg₂ Args.cons
        (include_injective first second components.1)
        (includeArgs_injective rest tail components.2)
end

mutual
theorem support_include : ∀ {Γ : Ctx S} {sort : S.Srt} (tree : Term S Γ sort),
    support (includeTerm declaration tree) = []
  | _, _, .var _ => rfl
  | _, _, .op _ arguments => support_includeArgs arguments

theorem support_includeArgs : ∀ {Γ : Ctx S} {arities : List (List S.Srt × S.Srt)}
    (fields : Args S arities Γ), supportArgs (includeArgs declaration fields) = []
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [includeArgs, supportArgs, support_include head,
        support_includeArgs tail, List.nil_append]
end

end Mettapedia.OSLF.Binding.ContextualFamily.Rigid
