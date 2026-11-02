import Mettapedia.Languages.Metamath.InferenceSemanticFiniteSupport

/-!
# Exact source support for Metamath substitution and identification

These laws use the existing mm-lean4 expressions and substitution. They do not
parse strings into an MM0 expression or assume correctness of a source
translator. Renaming reuses the existing typed semantic renaming operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM0Transfer.SourceSupport

open _root_.Metamath
open Mettapedia.Languages.Metamath.InferenceSemanticFiniteSupport (renameExpr renameSym)

/-- Every reference in a substituted expression comes from an occurring source
reference, and every reference of such an image really occurs in the result. -/
theorem mem_substitution_iff (reference : VR) (substitution : VR → Expr)
    (expression : Expr) :
    Sym.var reference ∈ expression.subst substitution ↔
      ∃ source, Sym.var source ∈ expression ∧
        Sym.var reference ∈ substitution source := by
  constructor
  · exact Expr.mem_subst
  · rintro ⟨source, present, image⟩
    induction expression with
    | nil => cases present
    | cons symbol tail ih =>
        cases symbol with
        | const constant =>
            have rest : Sym.var source ∈ tail := by simpa using present
            exact List.mem_cons_of_mem _ (ih rest)
        | var head =>
            rcases List.mem_cons.mp present with equal | rest
            · cases Sym.var.inj equal
              exact List.mem_append_left _ image
            · exact List.mem_append_right _ (ih rest)

/-- Support substitution is the union of the supports of the actual images. -/
theorem vars_substitution_iff (reference : VR) (substitution : VR → Expr)
    (expression : Expr) :
    reference ∈ (expression.subst substitution).vars ↔
      ∃ source ∈ expression.vars, reference ∈ (substitution source).vars := by
  simp only [Expr.mem_vars_iff, Expr.mem, mem_substitution_iff]

/-- Renaming is the original simultaneous substitution by singleton variables. -/
theorem rename_eq_substitution (rename : VR → VR) (expression : Expr) :
    renameExpr rename expression =
      expression.subst (fun reference => (rename reference).expr) := by
  induction expression with
  | nil => rfl
  | cons symbol tail ih =>
      cases symbol with
      | const constant => exact congrArg (Sym.const constant :: ·) ih
      | var reference => exact congrArg (Sym.var (rename reference) :: ·) ih

/-- Identification can merge occurrences but cannot add an unrelated reference. -/
theorem vars_rename_iff (reference : VR) (rename : VR → VR)
    (expression : Expr) :
    reference ∈ (renameExpr rename expression).vars ↔
      ∃ source ∈ expression.vars, rename source = reference := by
  rw [rename_eq_substitution, vars_substitution_iff]
  simp only [VR.expr, Expr.vars, List.mem_singleton]
  constructor <;> rintro ⟨source, present, equal⟩ <;>
    exact ⟨source, present, equal.symm⟩

/-- Images agreeing on the source support give the same substituted expression.
No agreement on unused variables is needed. -/
theorem substitution_congr_on_support (left right : VR → Expr)
    (expression : Expr)
    (same : ∀ reference ∈ expression.vars, left reference = right reference) :
    expression.subst left = expression.subst right := by
  induction expression with
  | nil => rfl
  | cons symbol tail ih =>
      cases symbol with
      | const constant =>
          exact congrArg (Sym.const constant :: ·)
            (ih (fun reference member => same reference member))
      | var reference =>
          simp only [Expr.subst]
          rw [same reference (by simp [Expr.vars]),
            ih (fun other member => same other (by simp [Expr.vars, member]))]

/-- Context support after a local reference identification is exactly its image. -/
theorem rename_congr_on_support (left right : VR → VR) (expression : Expr)
    (same : ∀ reference ∈ expression.vars, left reference = right reference) :
    renameExpr left expression = renameExpr right expression := by
  rw [rename_eq_substitution, rename_eq_substitution]
  exact substitution_congr_on_support _ _ expression
    (fun reference member => congrArg VR.expr (same reference member))

end Mettapedia.Languages.Metamath.MM0Transfer.SourceSupport
