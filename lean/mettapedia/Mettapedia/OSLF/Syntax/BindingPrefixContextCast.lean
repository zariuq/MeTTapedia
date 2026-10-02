import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# Reading a binder prefix and transporting its context

The existing renaming-based reading of a closed binder prefix agrees with
explicit transport along the empty-context equality. The comparison follows
from variable transport and the established renaming laws.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.Binding
variable {S : Signature}

/-- Reading a variable in a closed binder prefix is its canonical transport
along the empty-context equality. -/
theorem unScopeVar_contextCast :
    ∀ (bs : Ctx S) {s : S.Srt} (var : Var (bs ++ []) s),
      unScopeVar bs var = (List.append_nil bs) ▸ var
  | [], _, var => nomatch var
  | b :: bs, _, .zero => by
      change Var.zero = (congrArg (List.cons b) (List.append_nil bs)) ▸ Var.zero
      exact (eqRec_var_zero (List.append_nil bs) b).symm
  | b :: bs, _, .succ var => by
      change Var.succ (unScopeVar bs var) =
        (congrArg (List.cons b) (List.append_nil bs)) ▸ Var.succ var
      rw [eqRec_var_succ (List.append_nil bs) var]
      exact congrArg Var.succ (unScopeVar_contextCast bs var)

/-- Renaming by an equality of contexts is the established explicit term
transport, independently of the term's constructors. -/
theorem rename_contextCast {Γ Δ : Ctx S} (same : Γ = Δ) {s : S.Srt}
    (body : Term S Γ s) :
    rename (fun _ var => same ▸ var) body = castTermCtx same body := by
  cases same
  exact rename_id body

/-- Reading a complete closed binder body is the canonical context
transport. The proof reuses renaming and does not traverse the body anew. -/
theorem unScope_contextCast (bs : Ctx S) {s : S.Srt}
    (body : Term S (bs ++ []) s) :
    unScope bs body = castTermCtx (List.append_nil bs) body := by
  unfold unScope
  have renamingEq : (fun r (var : Var (bs ++ []) r) => unScopeVar bs var) =
      (fun r (var : Var (bs ++ []) r) => (List.append_nil bs) ▸ var) := by
    funext r var
    exact unScopeVar_contextCast bs var
  rw [renamingEq]
  exact rename_contextCast (List.append_nil bs) body

end Mettapedia.OSLF.Binding
