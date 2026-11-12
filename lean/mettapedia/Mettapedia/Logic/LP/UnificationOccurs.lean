import Mettapedia.Logic.LP.UnificationComplete

/-! The occurs-check obstruction follows from the proved complete derivation
system. No caller can solve a variable/application equation containing that
variable in a finite first-order term. -/

set_option autoImplicit false

namespace Mettapedia.Logic.LP

theorem unifies_var_app_occurs_false {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (model : Subst σ) (name : σ.vars) (head : σ.functionSymbols)
    (arguments : Fin (σ.functionArity head) → Term σ)
    (equal : model.applyTerm (.var name) = model.applyTerm (.app head arguments)) :
    (Term.app head arguments).occursIn name = false := by
  have derived : UnifyDerives [(.var name,.app head arguments)] :=
    unifies_to_derives ⟨model,by simpa only [Unifies,List.mem_singleton,forall_eq] using equal⟩
  cases derived with
  | var_subst _ _ _ absent tail => exact absent

end Mettapedia.Logic.LP
