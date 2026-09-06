import Mettapedia.Logic.HOL.Syntax.TypeSubstitution
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Type-derived interpretations in full-domain models

Substituting a type for a base sort induces a reduct of full-domain HOL models.
Denotation equivalences handle function types contravariantly in their domain;
the satisfaction theorem includes equality and quantification at every type.

This construction does not assert an arbitrary Henkin-model reduct. A source
base carrier contains all its ambient values, whereas a target function type
may have a restricted admissible domain.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v v' w

variable {Base Base' : Type u}
  {Const : Ty Base → Type v} {Const' : Ty Base' → Type v'}

namespace Ty

/-- Interpreting substituted types agrees with substituting their interpreted
carriers, by an equivalence rather than an equality of type expressions. -/
def denoteSubstituteEquiv (σ : Base → Ty Base')
    (Carrier : Base' → Type (max (u + 1) w)) :
    (a : Ty Base) →
      denote (fun b => denote Carrier (σ b)) a ≃ denote Carrier (substitute σ a)
  | .prop => Equiv.refl _
  | .base _ => Equiv.refl _
  | .arr a b => Equiv.arrowCongr (denoteSubstituteEquiv σ Carrier a)
      (denoteSubstituteEquiv σ Carrier b)

@[simp] theorem denoteSubstituteEquiv_prop (σ : Base → Ty Base')
    (Carrier : Base' → Type (max (u + 1) w))
    (p : ULift.{max (u + 1) w, 0} Prop) :
    denoteSubstituteEquiv σ Carrier .prop p = p := rfl

/-- The carrier equivalences preserve function application. -/
theorem denoteSubstituteEquiv_app (σ : Base → Ty Base')
    (Carrier : Base' → Type (max (u + 1) w)) {a b : Ty Base}
    (f : denote (fun c => denote Carrier (σ c)) (.arr a b))
    (x : denote (fun c => denote Carrier (σ c)) a) :
    denoteSubstituteEquiv σ Carrier b (f x) =
      denoteSubstituteEquiv σ Carrier (.arr a b) f (denoteSubstituteEquiv σ Carrier a x) := by
  change _ = denoteSubstituteEquiv σ Carrier b
    (f ((denoteSubstituteEquiv σ Carrier a).symm (denoteSubstituteEquiv σ Carrier a x)))
  exact congrArg (fun y => denoteSubstituteEquiv σ Carrier b (f y))
    ((denoteSubstituteEquiv σ Carrier a).symm_apply_apply x).symm

end Ty

namespace HenkinModel

/-- Full-domain extensional equality is exactly equality of ambient values. -/
theorem eqv_iff_eq_of_fullDomains (M : HenkinModel.{u, v, w} Base Const)
    (full : M.FullDomains) {a : Ty Base} (x y : Ty.denote M.Carrier a) :
    M.Eqv a x y ↔ x = y := by
  constructor
  · exact M.eq_of_eqv_of_fullDomains full
  · rintro rfl
    exact M.eqv_refl (full a x)

variable (σ : Base → Ty Base')
  (constants : ∀ {a}, Const a → Const' (Ty.substitute σ a))
  (M : HenkinModel.{u, v', w} Base' Const')

/-- The standard-domain source model of a type-derived interpretation.
Its satisfaction law requires full domains in the target model. -/
def standardTypeReduct : HenkinModel.{u, v, w} Base Const :=
  standard (fun b => Ty.denote M.Carrier (σ b))
    (fun {a} c => (Ty.denoteSubstituteEquiv σ M.Carrier a).symm (M.constDen (constants c)))

theorem standardTypeReduct_fullDomains : (standardTypeReduct σ constants M).FullDomains :=
  fullDomains_standard _ _

/-- Pull a typed valuation back along the term and type interpretation. -/
def typeReductValuation {Γ : Ctx Base}
    (ρ : M.Valuation (Γ.map (Ty.substitute σ))) :
    (standardTypeReduct σ constants M).Valuation Γ :=
  fun {a} x => (Ty.denoteSubstituteEquiv σ M.Carrier a).symm (ρ (x.mapTypes σ))

theorem typeReductValuation_extend {Γ : Ctx Base} {a : Ty Base}
    (ρ : M.Valuation (Γ.map (Ty.substitute σ)))
    (x : Ty.denote M.Carrier (Ty.substitute σ a)) :
    (fun {b} (y : Var (a :: Γ) b) =>
      typeReductValuation σ constants M (Γ := a :: Γ) (M.extend ρ x) y) =
      (fun {b} (y : Var (a :: Γ) b) =>
        (standardTypeReduct σ constants M).extend (typeReductValuation σ constants M ρ)
          ((Ty.denoteSubstituteEquiv σ M.Carrier a).symm x) y) := by
  funext b y
  cases y <;> rfl

theorem standardTypeReduct_eqv (full : M.FullDomains) {a : Ty Base}
    (x y : Ty.denote (standardTypeReduct σ constants M).Carrier a) :
    (standardTypeReduct σ constants M).Eqv a x y ↔
      M.Eqv (Ty.substitute σ a) (Ty.denoteSubstituteEquiv σ M.Carrier a x)
        (Ty.denoteSubstituteEquiv σ M.Carrier a y) := by
  rw [eqv_iff_eq_of_fullDomains _ (standardTypeReduct_fullDomains σ constants M),
    eqv_iff_eq_of_fullDomains _ full]
  exact (Ty.denoteSubstituteEquiv σ M.Carrier a).injective.eq_iff.symm

/-- Type-derived interpretation preserves every term's denotation in a
full-domain model, including lambda, equality, and both quantifiers. -/
theorem denote_mapTypes (full : M.FullDomains) {Γ : Ctx Base} {a : Ty Base}
    (t : Term Const Γ a) (ρ : M.Valuation (Γ.map (Ty.substitute σ))) :
    Ty.denoteSubstituteEquiv σ M.Carrier a
        ((standardTypeReduct σ constants M).denote t (typeReductValuation σ constants M ρ)) =
      M.denote (mapTypes σ constants t) ρ := by
  induction t with
  | var x => exact (Ty.denoteSubstituteEquiv σ M.Carrier _).apply_symm_apply _
  | const c => exact (Ty.denoteSubstituteEquiv σ M.Carrier _).apply_symm_apply _
  | app f t ihf iht =>
      exact (Ty.denoteSubstituteEquiv_app σ M.Carrier _ _).trans
        (congrArg₂ (fun f x => f x) (ihf ρ) (iht ρ))
  | lam t ih =>
      funext x
      have h := ih (M.extend ρ x)
      rw [typeReductValuation_extend] at h
      exact h
  | top => rfl
  | bot => rfl
  | and p q ihp ihq =>
      exact congrArg₂ (fun p q : Ty.denote M.Carrier .prop =>
        (⟨p.down ∧ q.down⟩ : Ty.denote M.Carrier .prop)) (ihp ρ) (ihq ρ)
  | or p q ihp ihq =>
      exact congrArg₂ (fun p q : Ty.denote M.Carrier .prop =>
        (⟨p.down ∨ q.down⟩ : Ty.denote M.Carrier .prop)) (ihp ρ) (ihq ρ)
  | imp p q ihp ihq =>
      exact congrArg₂ (fun p q : Ty.denote M.Carrier .prop =>
        (⟨p.down → q.down⟩ : Ty.denote M.Carrier .prop)) (ihp ρ) (ihq ρ)
  | not p ih =>
      exact congrArg (fun p : Ty.denote M.Carrier .prop =>
        (⟨¬ p.down⟩ : Ty.denote M.Carrier .prop)) (ih ρ)
  | eq t s iht ihs =>
      apply ULift.down_injective
      apply propext
      change (standardTypeReduct σ constants M).Eqv _ _ _ ↔ M.Eqv _ _ _
      rw [standardTypeReduct_eqv σ constants M full, iht ρ, ihs ρ]
  | all p ih =>
      apply ULift.down_injective
      apply propext
      change (∀ x, _ → _) ↔ ∀ y, M.adm _ y → _
      constructor
      · intro h y _
        have hp := h ((Ty.denoteSubstituteEquiv σ M.Carrier _).symm y) (by trivial)
        have he := ih (M.extend ρ y)
        rw [typeReductValuation_extend] at he
        exact congrArg ULift.down he ▸ hp
      · intro h x _
        have hp := h (Ty.denoteSubstituteEquiv σ M.Carrier _ x) (full _ _)
        have he := ih (M.extend ρ (Ty.denoteSubstituteEquiv σ M.Carrier _ x))
        rw [typeReductValuation_extend] at he
        simp only [Equiv.symm_apply_apply] at he
        exact (congrArg ULift.down he).symm ▸ hp
  | ex p ih =>
      apply ULift.down_injective
      apply propext
      change (∃ x, _ ∧ _) ↔ ∃ y, M.adm _ y ∧ _
      constructor
      · rintro ⟨x, _, hp⟩
        refine ⟨Ty.denoteSubstituteEquiv σ M.Carrier _ x, full _ _, ?_⟩
        have he := ih (M.extend ρ (Ty.denoteSubstituteEquiv σ M.Carrier _ x))
        rw [typeReductValuation_extend] at he
        simp only [Equiv.symm_apply_apply] at he
        exact congrArg ULift.down he ▸ hp
      · rintro ⟨y, _, hp⟩
        refine ⟨(Ty.denoteSubstituteEquiv σ M.Carrier _).symm y, by trivial, ?_⟩
        have he := ih (M.extend ρ y)
        rw [typeReductValuation_extend] at he
        exact (congrArg ULift.down he).symm ▸ hp

/-- The satisfaction condition for a type-derived interpretation of full
models. The model reduct runs opposite to the sentence translation. -/
theorem models_mapTypes (full : M.FullDomains) (φ : ClosedFormula Const) :
    PreModel.models (standardTypeReduct σ constants M).toPreModel φ ↔
      PreModel.models M.toPreModel (mapTypes σ constants φ) := by
  have h := denote_mapTypes σ constants M full φ (fun x => nomatch x)
  have empty : (fun {a} (x : Var ([] : Ctx Base) a) =>
      typeReductValuation σ constants M (Γ := []) (fun x => nomatch x) x) =
      ((fun {_} x => nomatch x) : (standardTypeReduct σ constants M).Valuation []) := by
    funext a x
    nomatch x
  rw [empty] at h
  simp only [propTy, Ty.denoteSubstituteEquiv_prop] at h
  have result := Iff.of_eq (congrArg (fun p : Ty.denote M.Carrier .prop => p.down) h)
  convert result using 1 <;> apply Iff.of_eq <;> unfold PreModel.models <;>
    apply congrArg ULift.down <;> congr 1
  funext a x
  exact nomatch x

#print axioms denote_mapTypes
#print axioms models_mapTypes

end HenkinModel

end Mettapedia.Logic.HOL
