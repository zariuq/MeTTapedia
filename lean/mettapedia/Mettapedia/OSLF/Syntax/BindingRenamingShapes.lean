import Mettapedia.OSLF.Syntax.BindingArgumentSlots

/-!
# Renaming cannot change a binding term's root shape

The variable case complements the existing operator-root inversion law.
Both expose the original common binding term rather than reconstructing
terms in a separate syntax.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

theorem rename_eq_variable {S : Signature} {Γ Δ : Ctx S} {sort : S.Srt} (rho : Ren S Γ Δ)
    (term : Term S Γ sort) (position : Var Δ sort) (same : rename rho term = .var position) :
    ∃ original, term = .var original ∧ rho sort original = position := by
  cases term with
  | var original => exact ⟨original, rfl, Term.var.inj same⟩
  | op _ _ => cases same

end Mettapedia.OSLF.Binding
