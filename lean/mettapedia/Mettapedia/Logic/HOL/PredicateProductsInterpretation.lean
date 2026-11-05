import Mettapedia.Logic.HOL.PredicateProducts
import Mettapedia.Logic.HOL.Soundness

/-!
# Interpreting guarded dependent products

The denotation retains both admissibility and the domain predicate. The
codomain is interpreted in the valuation extended by the actual argument.
Neither domain nor codomain is required to be inhabited.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.PredicateProducts

universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}
  (model : HenkinModel.{u,v,w} Base Const) {Γ : Ctx Base} {σ τ : Ty Base}

theorem membership_denote (domain : Term Const Γ (σ ⇒ .prop))
    (family : Term Const (σ :: Γ) (τ ⇒ .prop))
    (function : Term Const Γ (σ ⇒ τ)) (values : model.Valuation Γ) :
    (model.denote (membership domain family function) values).down ↔
      ∀ argument, model.adm σ argument → (model.denote domain values argument).down →
        (model.denote family (model.extend values argument)
          (model.denote function values argument)).down := by
  simp only [membership,HenkinModel.denote,PreModel.denote,
    Soundness.denote_weaken,PreModel.extend]

theorem pi_apply_denote (domain : Term Const Γ (σ ⇒ .prop))
    (family : Term Const (σ :: Γ) (τ ⇒ .prop))
    (function : Ty.denote model.Carrier (σ ⇒ τ)) (values : model.Valuation Γ) :
    (model.denote (pi domain family) values function).down ↔
      ∀ argument, model.adm σ argument → (model.denote domain values argument).down →
        (model.denote family (model.extend values argument) (function argument)).down := by
  have shifted (argument : Ty.denote model.Carrier σ) :
      model.denote (weaken (weaken domain)) (model.extend (model.extend values function) argument) =
        model.denote domain values := by
    rw [Soundness.denote_weaken,Soundness.denote_weaken]
  have lifted (argument : Ty.denote model.Carrier σ) :
      model.denote (HOL.rename (Rename.lift Rename.weaken) family)
        (model.extend (model.extend values function) argument) =
      model.denote family (model.extend values argument) := by
    rw [Soundness.denote_rename]
    congr 1
    funext type index
    cases index <;> rfl
  simp only [pi,HenkinModel.denote,PreModel.denote,shifted,lifted,PreModel.extend]

theorem pi_denote (domain : Term Const Γ (σ ⇒ .prop))
    (family : Term Const (σ :: Γ) (τ ⇒ .prop))
    (function : Term Const Γ (σ ⇒ τ)) (values : model.Valuation Γ) :
    (model.denote (.app (pi domain family) function) values).down ↔
      ∀ argument, model.adm σ argument → (model.denote domain values argument).down →
        (model.denote family (model.extend values argument)
          (model.denote function values argument)).down :=
  pi_apply_denote model domain family (model.denote function values) values

#print axioms membership_denote
#print axioms pi_apply_denote
#print axioms pi_denote

end Mettapedia.Logic.HOL.PredicateProducts
