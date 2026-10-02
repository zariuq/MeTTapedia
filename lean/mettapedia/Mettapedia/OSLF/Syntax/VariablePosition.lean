import Mettapedia.OSLF.Syntax.TermClone

/-!
# A typed variable is its position

Two variables of one sort in one context that occupy the same position are
the same variable.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

variable {S : Signature}

/-- The position of a variable determines it. -/
theorem varIdx_injective : ∀ {Γ : Ctx S} {s : S.Srt} (first second : Var Γ s),
    varIdx first = varIdx second → first = second
  | _, _, .zero, .zero, _ => rfl
  | _, _, .zero, .succ second, same => by
      have values := congrArg Fin.val same
      simp [varIdx] at values
  | _, _, .succ first, .zero, same => by
      have values := congrArg Fin.val same
      simp [varIdx] at values
  | _, _, .succ first, .succ second, same => by
      have inner : varIdx first = varIdx second := Fin.succ_inj.mp same
      rw [varIdx_injective first second inner]

end Mettapedia.OSLF.Binding
