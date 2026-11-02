import Mettapedia.Logic.HOL.Syntax.Subst

/-! Typed variable insertion before an existing HOL context. -/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.Rename
universe u
variable {Base : Type u} {Γ : Ctx Base}

def weakenPrefix : (leading : Ctx Base) → Rename Base Γ (leading ++ Γ)
  | [], _, entry => entry
  | _ :: rest, _, entry => .vs (weakenPrefix rest entry)

@[simp] theorem weakenPrefix_nil {type : Ty Base} (entry : Var Γ type) :
    weakenPrefix [] entry = entry := rfl

@[simp] theorem weakenPrefix_cons (head : Ty Base) (leading : Ctx Base)
    {type : Ty Base} (entry : Var Γ type) :
    weakenPrefix (head :: leading) entry = .vs (weakenPrefix leading entry) := rfl

theorem weakenPrefix_injective (leading : Ctx Base) {type : Ty Base} :
    Function.Injective (weakenPrefix leading (τ := type) : Var Γ type → Var (leading ++ Γ) type) := by
  induction leading with
  | nil => exact fun _ _ same => same
  | cons head rest hypothesis =>
      intro first second same
      exact hypothesis (Var.vs.inj same)

end Mettapedia.Logic.HOL.Rename
