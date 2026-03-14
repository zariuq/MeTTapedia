import Mettapedia.Logic.HOL.Semantics.Henkin

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace PreModel

theorem eqv_symm (M : PreModel Base Const) :
    ∀ {τ : Ty Base} {x y : Ty.denote M.Carrier τ}, Eqv M τ x y → Eqv M τ y x
  | .prop, _, _, h => h.symm
  | .base _, _, _, h => h.symm
  | .arr σ τ, _, _, h => by
      intro x hx
      exact eqv_symm M (h x hx)

theorem eqv_trans (M : PreModel Base Const) :
    ∀ {τ : Ty Base} {x y z : Ty.denote M.Carrier τ},
      Eqv M τ x y → Eqv M τ y z → Eqv M τ x z
  | .prop, _, _, _, hxy, hyz => hxy.trans hyz
  | .base _, _, _, _, hxy, hyz => hxy.trans hyz
  | .arr σ τ, _, _, _, hxy, hyz => by
      intro x hx
      exact eqv_trans M (hxy x hx) (hyz x hx)

@[simp] theorem eqv_arr_apply (M : PreModel Base Const) {σ τ : Ty Base}
    {f g : Ty.denote M.Carrier (σ ⇒ τ)} (h : Eqv M (σ ⇒ τ) f g)
    {x : Ty.denote M.Carrier σ} (hx : M.adm σ x) :
    Eqv M τ (f x) (g x) :=
  h x hx

end PreModel

namespace HenkinModel

theorem eqv_symm (M : HenkinModel Base Const) {τ : Ty Base} {x y : Ty.denote M.Carrier τ}
    (h : Eqv M τ x y) : Eqv M τ y x :=
  PreModel.eqv_symm M.toPreModel h

theorem eqv_trans (M : HenkinModel Base Const) {τ : Ty Base}
    {x y z : Ty.denote M.Carrier τ} (hxy : Eqv M τ x y) (hyz : Eqv M τ y z) :
    Eqv M τ x z :=
  PreModel.eqv_trans M.toPreModel hxy hyz

@[simp] theorem eqv_arr_apply (M : HenkinModel Base Const) {σ τ : Ty Base}
    {f g : Ty.denote M.Carrier (σ ⇒ τ)} (h : Eqv M (σ ⇒ τ) f g)
    {x : Ty.denote M.Carrier σ} (hx : M.adm σ x) :
    Eqv M τ (f x) (g x) :=
  PreModel.eqv_arr_apply M.toPreModel h hx

end HenkinModel

end Mettapedia.Logic.HOL
