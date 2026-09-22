import Mettapedia.OSLF.Syntax.Strengthening

/-!
# Exact image laws for the existing strengthening operation

The operation and inverse laws are those of `Strengthener`, `strengthenT`,
and `strengthenA`. This theorem suite adds their exact image characterization;
it introduces no second variable map, traversal, or lifting implementation.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S : Signature}

/-- Successful strengthening is precisely reconstruction along the selected renaming. -/
theorem strengthenT_eq_some_iff {Γ Δ : Ctx S} {rho : Ren S Γ Δ}
    (St : Strengthener rho) {s : S.Srt} (target : Term S Δ s) (body : Term S Γ s) :
    strengthenT St target = some body ↔ rename rho body = target := by
  constructor
  · exact rename_strengthenT St target body
  · rintro rfl
    exact strengthenT_rename St body

/-- Failure is exactly absence of a body over the selected variable context. -/
theorem strengthenT_eq_none_iff {Γ Δ : Ctx S} {rho : Ren S Γ Δ}
    (St : Strengthener rho) {s : S.Srt} (target : Term S Δ s) :
    strengthenT St target = none ↔ ¬ ∃ body, rename rho body = target := by
  constructor
  · intro failure ⟨body, hb⟩
    have success := (strengthenT_eq_some_iff St target body).mpr hb
    rw [failure] at success
    cases success
  · intro absent
    cases found : strengthenT St target with
    | none => rfl
    | some body => exact False.elim (absent ⟨body, rename_strengthenT St target body found⟩)

end Mettapedia.OSLF.Binding
