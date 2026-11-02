import Mettapedia.Logic.HOL.ContextualConstructorAdmission
import Mettapedia.Logic.HOL.FiniteConstructorGuards
import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics

/-!
# Interpretation of generated constructor admission

The actual abstracted HOL program denotes the original shape condition and
padding outside the original activity predicate. General Henkin domains and
typed equality remain explicit; full domains yield ambient child equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.HenkinModel
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}
theorem models_iff_denote_closed (model : HenkinModel.{u,v,w} Base Const)
    (formula : ClosedFormula Const) (values : model.Valuation []) :
    model.models formula ↔ (model.denote formula values).down :=
  Iff.of_eq (congrArg ULift.down (model.denote_closed_valuation_eq formula (fun index => nomatch index) values))
end Mettapedia.Logic.HOL.HenkinModel

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
open FiniteConstructorEncoding
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (signature : Contextual Const Γ) (model : HenkinModel.{u,v,w} Base Const)

theorem constructorAdmission_denote (values : model.Valuation Γ)
    (tag : Ty.denote model.Carrier signature.number) (payload : Ty.denote model.Carrier signature.payload)
    (children : Ty.denote model.Carrier (signature.number ⇒ signature.space)) :
    (model.denote signature.constructorAdmission values tag payload children).down ↔
      (model.denote signature.validShape values tag payload).down ∧
      ∀ slot, model.adm signature.number slot →
        ¬ (model.denote signature.active values payload slot).down →
          model.Eqv signature.space (children slot) (model.denote signature.bottom values) := by
  have generated := abstractArguments_denote model
    [signature.number,signature.payload,signature.number ⇒ signature.space] signature.admissionBody
    (fun values data => ULift.up
      ((model.denote signature.validShape values data.1 data.2.1).down ∧
        ∀ slot, model.adm signature.number slot →
          ¬ (model.denote signature.active values data.2.1 slot).down →
            model.Eqv signature.space (data.2.2.1 slot) (model.denote signature.bottom values)))
    (by
      intro Δ substitution arguments later
      simp only [admissionBody,shapeAt,paddingConditions,Contextual.subst,HenkinModel.denote,
        PreModel.denote,Soundness.denote_subst,Soundness.denote_weaken,denoteArguments,
        PreModel.extend]
      rfl)
    values (tag,payload,children,PUnit.unit)
  exact Iff.of_eq (congrArg ULift.down generated)

theorem constructorAdmission_denote_full (full : model.FullDomains) (values : model.Valuation Γ)
    (tag : Ty.denote model.Carrier signature.number) (payload : Ty.denote model.Carrier signature.payload)
    (children : Ty.denote model.Carrier (signature.number ⇒ signature.space)) :
    (model.denote signature.constructorAdmission values tag payload children).down ↔
      (model.denote signature.validShape values tag payload).down ∧
      ∀ slot, ¬ (model.denote signature.active values payload slot).down →
        children slot = model.denote signature.bottom values := by
  rw [signature.constructorAdmission_denote]
  apply and_congr Iff.rfl
  constructor
  · intro padding slot inactive
    exact model.eq_of_eqv_of_fullDomains full (padding slot (full _ _) inactive)
  · intro padding slot _admitted inactive
    exact (model.eqv_iff_eq_of_fullDomains full _ _).mpr (padding slot inactive)

#print axioms constructorAdmission_denote_full

theorem constructorAdmission_models_full (signature : Contextual Const [])
    (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains) (values : model.Valuation [])
    (tag : ClosedTerm Const signature.number) (payload : ClosedTerm Const signature.payload)
    (children : ClosedTerm Const (signature.number ⇒ signature.space)) :
    model.models (GuardedConstructorProjections.admitted signature.constructorAdmission tag payload children) ↔
      (model.denote signature.validShape values (model.denote tag values) (model.denote payload values)).down ∧
      ∀ slot, ¬ (model.denote signature.active values (model.denote payload values) slot).down →
        model.denote children values slot = model.denote signature.bottom values := by
  apply (model.models_iff_denote_closed _ values).trans
  exact signature.constructorAdmission_denote_full model full values
    (model.denote tag values) (model.denote payload values) (model.denote children values)

theorem childConditions_false_no_active (signature : Contextual Const [])
    (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains) (values : model.Valuation [])
    (payload : ClosedTerm Const signature.payload) (children : ClosedTerm Const (signature.number ⇒ signature.space))
    (conditions : model.models (signature.childConditions (.lam .bot) payload children)) :
    ∀ slot, ¬ (model.denote signature.active values (model.denote payload values) slot).down := by
  have interpreted := (model.models_iff_denote_closed _ values).mp conditions
  simp only [childConditions,HenkinModel.denote,PreModel.denote,Soundness.denote_weaken,PreModel.extend] at interpreted
  intro slot active
  exact ((interpreted slot (full _ _)).1 active).2
end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual

namespace Mettapedia.Logic.HOL.GuardedConstructorProjections
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {first second third carrier : Ty Base}

theorem fieldInjective_denote_full (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)
    (constructor : Term Const Γ (ConstructorProjections.Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) (values : model.Valuation Γ) :
    (model.denote (fieldInjective constructor domain) values).down ↔
      ∀ a b c, (model.denote domain values a b c).down →
        ∀ a' b' c', (model.denote domain values a' b' c').down →
          model.denote constructor values a' b' c' = model.denote constructor values a b c → b' = b ∧ c' = c := by
  simp only [fieldInjective,components,admitted,ConstructorProjections.apply,HenkinModel.denote,
    PreModel.denote,Soundness.denote_weaken,PreModel.extend]
  constructor
  · intro injective a b c original a' b' c' candidate same
    have compared := injective a (full _ _) b (full _ _) c (full _ _) original
      a' (full _ _) b' (full _ _) c' (full _ _) candidate
      ((model.eqv_iff_eq_of_fullDomains full _ _).mpr same)
    exact ⟨model.eq_of_eqv_of_fullDomains full compared.1,model.eq_of_eqv_of_fullDomains full compared.2⟩
  · intro injective a _ b _ c _ original a' _ b' _ c' _ candidate same
    have compared := injective a b c original a' b' c' candidate (model.eq_of_eqv_of_fullDomains full same)
    exact ⟨(model.eqv_iff_eq_of_fullDomains full _ _).mpr compared.1,
      (model.eqv_iff_eq_of_fullDomains full _ _).mpr compared.2⟩
theorem fieldInjective_models_full (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)
    (constructor : ClosedTerm Const (ConstructorProjections.Constructor first second third carrier))
    (domain : ClosedTerm Const (Admission first second third)) (values : model.Valuation []) :
    model.models (fieldInjective constructor domain) ↔
      ∀ a b c, (model.denote domain values a b c).down →
        ∀ a' b' c', (model.denote domain values a' b' c').down →
          model.denote constructor values a' b' c' = model.denote constructor values a b c → b' = b ∧ c' = c := by
  exact (model.models_iff_denote_closed _ values).trans (fieldInjective_denote_full model full constructor domain values)
end Mettapedia.Logic.HOL.GuardedConstructorProjections
