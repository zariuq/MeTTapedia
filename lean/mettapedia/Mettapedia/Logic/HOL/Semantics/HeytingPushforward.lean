import Mettapedia.Logic.HOL.Semantics.HeytingGeneral
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.CompleteLattice.Basic

/-!
# Pushforward of Heyting-valued models along value-carrier morphisms

Transporting a `HeytingGeneralModel` along a structure-preserving map of value
carriers into a Mathlib `Order.Frame`.  The morphism data demands exactly what
the valuation equations need: preservation of the lattice/Heyting operations,
plus exactness for the three valuation fields that quantify over arbitrary
value elements (universal bound, existential bound, lambda-equality bound) —
these are stated relative to the source model's valuation, which is the
minimal honest requirement.

Models with a given value carrier `Ω'` arise exactly this way from existing
models; the companion file on evidence-valued models uses this to show what
algebraic constraints a carrier choice imposes on the logic.
-/

namespace Mettapedia.Logic.HOL
namespace HeytingSem

universe u v w w'

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Morphism data for pushing a Heyting-valued model forward onto a Mathlib
frame: operation preservation plus valuation-relative exactness for the three
element-quantified fields. -/
structure ModelPushforwardData (M : HeytingGeneralModel.{u, v, w} Base Const)
    (Ω' : Type w') [Order.Frame Ω'] where
  f : M.Ω → Ω'
  mono : ∀ {a b : M.Ω}, M.le a b → f a ≤ f b
  map_top : f M.top = ⊤
  map_bot : f M.bot = ⊥
  map_inf : ∀ a b, f (M.inf a b) = f a ⊓ f b
  map_sup : ∀ a b, f (M.sup a b) = f a ⊔ f b
  map_himp : ∀ a b, f (M.himp a b) = f a ⇨ f b
  all_exact :
    ∀ {σ : Ty Base} (φ : Formula Const [σ]) (ω' : Ω'),
      (∀ t : ClosedTerm Const σ, ω' ≤ f (M.val (instantiate (Base := Base) t φ))) →
        ω' ≤ f (M.val (.all φ))
  ex_exact :
    ∀ {σ : Ty Base} (φ : Formula Const [σ]) (ω' : Ω'),
      (∀ t : ClosedTerm Const σ, f (M.val (instantiate (Base := Base) t φ)) ≤ ω') →
        f (M.val (.ex φ)) ≤ ω'
  eq_lam_exact :
    ∀ {σ τ : Ty Base} (t u : Term Const [σ] τ) (ω' : Ω'),
      (∀ w : ClosedTerm Const σ,
        ω' ≤ f (M.val (.eq (instantiate (Base := Base) w t)
          (instantiate (Base := Base) w u)))) →
        ω' ≤ f (M.val (.eq (.lam t) (.lam u)))

/-- The pushforward model: values in the target frame, valuation composed with
the morphism.  Lattice laws come from the frame; valuation equations from the
preservation fields; element-quantified bounds from the exactness fields. -/
noncomputable def HeytingGeneralModel.pushforward
    (M : HeytingGeneralModel.{u, v, w} Base Const)
    {Ω' : Type w'} [Order.Frame Ω']
    (D : ModelPushforwardData (Base := Base) M Ω') :
    HeytingGeneralModel.{u, v, w'} Base Const where
  Ω := Ω'
  le a b := a ≤ b
  le_refl a := _root_.le_refl a
  le_trans h₁ h₂ := _root_.le_trans h₁ h₂
  top := ⊤
  bot := ⊥
  inf a b := a ⊓ b
  sup a b := a ⊔ b
  himp a b := a ⇨ b
  le_top a := _root_.le_top
  bot_le a := _root_.bot_le
  inf_le_left a b := _root_.inf_le_left
  inf_le_right a b := _root_.inf_le_right
  le_inf h₁ h₂ := _root_.le_inf h₁ h₂
  le_sup_left a b := _root_.le_sup_left
  le_sup_right a b := _root_.le_sup_right
  sup_le h₁ h₂ := _root_.sup_le h₁ h₂
  himp_adjoint_mp h := le_himp_iff.mp h
  himp_adjoint_intro h := le_himp_iff.mpr h
  inf_sup_distrib a b c := le_of_eq (inf_sup_left a b c)
  val φ := D.f (M.val φ)
  val_top := by rw [M.val_top, D.map_top]
  val_bot := by rw [M.val_bot, D.map_bot]
  val_and φ ψ := by rw [M.val_and, D.map_inf]
  val_or φ ψ := by rw [M.val_or, D.map_sup]
  val_imp φ ψ := by rw [M.val_imp, D.map_himp]
  val_not_le φ := by
    have h := D.mono (M.val_not_le φ)
    rwa [D.map_himp, D.map_bot] at h
  le_val_not φ := by
    have h := D.mono (M.le_val_not φ)
    rwa [D.map_himp, D.map_bot] at h
  val_all_le φ t := D.mono (M.val_all_le φ t)
  le_val_all φ ω' h := D.all_exact φ ω' h
  val_ex_le φ ω' h := D.ex_exact φ ω' h
  le_val_ex φ t := D.mono (M.le_val_ex φ t)
  val_eq_refl t := by
    have h := D.mono (M.val_eq_refl t)
    rwa [D.map_top] at h
  val_eq_symm t u := D.mono (M.val_eq_symm t u)
  val_eq_trans t u v := by
    have h := D.mono (M.val_eq_trans t u v)
    rwa [D.map_inf] at h
  val_eq_app f g t := D.mono (M.val_eq_app f g t)
  val_eq_appArg f t u := D.mono (M.val_eq_appArg f t u)
  val_eq_propI p q := by
    have h := D.mono (M.val_eq_propI p q)
    rwa [D.map_inf] at h
  val_eq_propEL p q := D.mono (M.val_eq_propEL p q)
  val_eq_propER p q := D.mono (M.val_eq_propER p q)
  val_eq_lam t u ω' h := D.eq_lam_exact t u ω' h
  val_funExt f g := D.mono (M.val_funExt f g)
  val_beta t u := by
    have h := D.mono (M.val_beta t u)
    rwa [D.map_top] at h
  val_eta f := by
    have h := D.mono (M.val_eta f)
    rwa [D.map_top] at h

/-- Semantic consequence transports along pushforward: hypothesis states that
are top-supported in the pushforward come from top-supported source states. -/
theorem pushforward_val (M : HeytingGeneralModel.{u, v, w} Base Const)
    {Ω' : Type w'} [Order.Frame Ω']
    (D : ModelPushforwardData (Base := Base) M Ω') (φ : ClosedFormula Const) :
    (M.pushforward D).val φ = D.f (M.val φ) := rfl

end HeytingSem
end Mettapedia.Logic.HOL
