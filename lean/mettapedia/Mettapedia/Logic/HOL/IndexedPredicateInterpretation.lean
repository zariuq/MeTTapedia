import Mettapedia.Logic.HOL.IndexedPredicateInduction
import Mettapedia.Logic.HOL.Soundness

/-!
# Interpreting strengthened indexed predicates

Intersection keeps both meanings at the same point. The lifted motive
quantifies over the model's admitted index values, retaining the actual
root premise instead of choosing an index or assuming full domains.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.PredicateFixedPoint

universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (model : HenkinModel.{u,v,w} Base Const) (values : model.Valuation Γ) {space : Ty Base}

theorem intersection_denote (first second : Term Const Γ (space ⇒ .prop))
    (point : Ty.denote model.Carrier space) :
    (model.denote (intersection first second) values point).down ↔
      (model.denote first values point).down ∧ (model.denote second values point).down := by
  have shifted (term : Term Const Γ (space ⇒ .prop)) :
      model.denote (weaken term) (model.extend values point) = model.denote term values := by
    change model.denote (HOL.rename Rename.weaken term) (model.extend values point) = model.denote term values
    rw [Soundness.denote_rename, Soundness.renameVal_weaken_extend]
  simp only [intersection, HenkinModel.denote, PreModel.denote, shifted, PreModel.extend]

end Mettapedia.Logic.HOL.PredicateFixedPoint

namespace Mettapedia.Logic.HOL.IndexedPredicateInduction

universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (model : HenkinModel.{u,v,w} Base Const) (values : model.Valuation Γ) {space index : Ty Base}

theorem lift_denote (root property : Term Const Γ (space ⇒ index ⇒ .prop))
    (point : Ty.denote model.Carrier space) :
    (model.denote (lift root property) values point).down ↔
      ∀ target : Ty.denote model.Carrier index, model.adm index target →
        (model.denote root values point target).down → (model.denote property values point target).down := by
  have shifted (term : Term Const Γ (space ⇒ index ⇒ .prop)) (target : Ty.denote model.Carrier index) :
      model.denote (weaken (weaken term)) (model.extend (model.extend values point) target) =
        model.denote term values := by
    change model.denote (HOL.rename Rename.weaken (HOL.rename Rename.weaken term))
      (model.extend (model.extend values point) target) = model.denote term values
    rw [Soundness.denote_rename, Soundness.renameVal_weaken_extend,
      Soundness.denote_rename, Soundness.renameVal_weaken_extend]
  simp only [lift, HenkinModel.denote, PreModel.denote, shifted, PreModel.extend]

#print axioms lift_denote
#print axioms PredicateFixedPoint.intersection_denote

end Mettapedia.Logic.HOL.IndexedPredicateInduction
