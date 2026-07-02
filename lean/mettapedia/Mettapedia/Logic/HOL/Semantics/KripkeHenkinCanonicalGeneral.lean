import Mettapedia.Logic.HOL.Semantics.KripkeHenkinGeneral
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCanonical
import Mettapedia.Logic.HOL.TermModel.Denote

/-!
# The canonical Kripke-Henkin general model (in progress)

The supported presented worlds under `LevelLe` as a `KripkeHenkinGeneral`
model: base carriers are raw closed terms with membership-based world-indexed
equality, higher types are full function spaces with representability
(`RepK`) as admissibility, and closed terms denote via `tvalK` (recursion on
type, applying to reified arguments).  This is the Kripke port of the
classical `TermModel` construction; unlike the classical `termPreModel`, no
world-classicality hypothesis is used — the successor lemmas of the
supported-world construction replace it.
-/

namespace Mettapedia.Logic.HOL
namespace KripkeHenkin
namespace CanonicalGeneral

open Mettapedia.Logic.HOL.WithParams
open ClosedTheorySet
open SupportedCanonicalFrame
open scoped Classical

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The canonical frame: supported presented worlds. -/
abbrev CanWorld (Const : Ty Base → Type v) :=
  ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const

/-- Base carriers: raw closed terms at base types (equality is handled by the
membership-based `baseEq`, not by quotienting). -/
def CanCarrier (Const : Ty Base → Type v) (b : Base) : Type (max u v) :=
  ClosedTerm (WithParams Const) (.base b)

/-- Ambient values of the canonical general model. -/
abbrev CanVal (Const : Ty Base → Type v) (τ : Ty Base) : Type (max u v) :=
  Ty.denoteK (CanCarrier (Base := Base) Const) (CanWorld (Base := Base) Const) τ

/-- Global representability of a semantic value by a closed term: at
propositions, the value is the membership upset of the term; at base types the
value is the term itself; at function types, application to represented
arguments yields represented results. -/
def RepK : (τ : Ty Base) → CanVal (Base := Base) Const τ →
    ClosedTerm (WithParams Const) τ → Prop
  | .prop, S, t => ∀ W : CanWorld (Base := Base) Const, S W ↔ t ∈ W.carrier
  | .base _, d, t =>
      ∀ W : CanWorld (Base := Base) Const,
        (.eq d t : ClosedFormula (WithParams Const)) ∈ W.carrier
  | .arr σ ρ, f, t =>
      ∀ (d : CanVal (Base := Base) Const σ) (u : ClosedTerm (WithParams Const) σ),
        RepK σ d u → RepK ρ (f d) (.app t u)

/-- Admissibility: representability by some closed term. -/
def AdmK (τ : Ty Base) (v : CanVal (Base := Base) Const τ) : Prop :=
  ∃ t : ClosedTerm (WithParams Const) τ, RepK (Base := Base) (Const := Const) τ v t

/-- Reify an admissible value to a representing closed term (default parameter
constant otherwise). -/
noncomputable def treifyK (τ : Ty Base) (v : CanVal (Base := Base) Const τ) :
    ClosedTerm (WithParams Const) τ :=
  if h : AdmK (Base := Base) (Const := Const) τ v then h.choose
  else ClosedTheorySet.defaultTerm τ

theorem repK_treifyK {τ : Ty Base} {v : CanVal (Base := Base) Const τ}
    (h : AdmK (Base := Base) (Const := Const) τ v) :
    RepK (Base := Base) (Const := Const) τ v
      (treifyK (Base := Base) (Const := Const) τ v) := by
  rw [treifyK, dif_pos h]
  exact h.choose_spec

/-- Denotation of closed terms by recursion on type: membership upsets at
propositions, the term itself at base types, application to reified arguments
at function types. -/
noncomputable def tvalK : (τ : Ty Base) → ClosedTerm (WithParams Const) τ →
    CanVal (Base := Base) Const τ
  | .prop, t => fun W => t ∈ W.carrier
  | .base _, t => t
  | .arr σ ρ, t => fun d =>
      tvalK ρ (.app t (treifyK (Base := Base) (Const := Const) σ d))

@[simp] theorem tvalK_prop (t : ClosedFormula (WithParams Const))
    (W : CanWorld (Base := Base) Const) :
    tvalK (Base := Base) (Const := Const) .prop t W ↔ t ∈ W.carrier := Iff.rfl

@[simp] theorem tvalK_base {b : Base} (t : ClosedTerm (WithParams Const) (.base b)) :
    tvalK (Base := Base) (Const := Const) (.base b) t = t := rfl

/-! ## Equality bridges via the successor providers

The classical construction used world-classicality here; the Kripke port
replaces it with the level-provider successor clauses. -/

theorem eqProp_mem_of_iff_provider (P : SchedulerProvider (Base := Base) Const)
    {φ ψ : ClosedFormula (WithParams Const)}
    (h : ∀ V : CanWorld (Base := Base) Const, φ ∈ V.carrier ↔ ψ ∈ V.carrier)
    (W : CanWorld (Base := Base) Const) :
    (.eq φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  refine SupportedCanonicalMembership.eq_prop_intro_mem (W := W) ?_ ?_
  · exact (forces_imp_level_provider (Base := Base) (Const := Const) P W).mpr
      (fun V _ hφ => (h V).mp hφ)
  · exact (forces_imp_level_provider (Base := Base) (Const := Const) P W).mpr
      (fun V _ hψ => (h V).mpr hψ)

/-- Represented values transport along globally provable equality of their
representatives. -/
theorem repK_respects_eq :
    ∀ (τ : Ty Base) {v : CanVal (Base := Base) Const τ}
      {s s' : ClosedTerm (WithParams Const) τ},
      (∀ W : CanWorld (Base := Base) Const,
        (.eq s s' : ClosedFormula (WithParams Const)) ∈ W.carrier) →
      RepK (Base := Base) (Const := Const) τ v s →
      RepK (Base := Base) (Const := Const) τ v s'
  | .prop, v, s, s', heq, hrep => by
      intro W
      refine (hrep W).trans ⟨fun hs => ?_, fun hs' => ?_⟩
      · exact SupportedCanonicalMembership.imp_mp_mem
          (SupportedCanonicalMembership.eq_prop_elim_left_mem (heq W)) hs
      · exact SupportedCanonicalMembership.imp_mp_mem
          (SupportedCanonicalMembership.eq_prop_elim_right_mem (heq W)) hs'
  | .base b, v, s, s', heq, hrep => by
      intro W
      exact SupportedCanonicalMembership.eq_trans_mem (hrep W) (heq W)
  | .arr σ ρ, v, s, s', heq, hrep => by
      intro d u hdu
      refine repK_respects_eq ρ (fun W => ?_) (hrep d u hdu)
      exact SupportedCanonicalMembership.eq_app_congr_mem (heq W)
        (SupportedCanonicalMembership.eq_refl_mem u)

/-- **Realization correctness**: `tvalK τ t` is represented by `t`, and any
two representatives of one value are globally provably equal — proved together
by type induction, mirroring the classical `repCore` with the successor
providers in place of world-classicality. -/
theorem repCoreK (P : SchedulerProvider (Base := Base) Const) :
    ∀ (τ : Ty Base),
      (∀ t : ClosedTerm (WithParams Const) τ,
        RepK (Base := Base) (Const := Const) τ
          (tvalK (Base := Base) (Const := Const) τ t) t) ∧
      (∀ {v : CanVal (Base := Base) Const τ}
        {u₁ u₂ : ClosedTerm (WithParams Const) τ},
        RepK (Base := Base) (Const := Const) τ v u₁ →
        RepK (Base := Base) (Const := Const) τ v u₂ →
        ∀ W : CanWorld (Base := Base) Const,
          (.eq u₁ u₂ : ClosedFormula (WithParams Const)) ∈ W.carrier)
  | .prop => by
      refine ⟨fun t W => Iff.rfl, fun {v u₁ u₂} h1 h2 W => ?_⟩
      exact eqProp_mem_of_iff_provider P (fun V => (h1 V).symm.trans (h2 V)) W
  | .base b => by
      refine ⟨fun t W => SupportedCanonicalMembership.eq_refl_mem t,
        fun {v u₁ u₂} h1 h2 W => ?_⟩
      exact SupportedCanonicalMembership.eq_trans_mem
        (SupportedCanonicalMembership.eq_symm_mem (h1 W)) (h2 W)
  | .arr σ ρ => by
      have ihσ := repCoreK P σ
      have ihρ := repCoreK P ρ
      refine ⟨fun t => ?_, fun {v u₁ u₂} h1 h2 => ?_⟩
      · intro d u hdu
        have hadm : AdmK (Base := Base) (Const := Const) σ d := ⟨u, hdu⟩
        have heq : ∀ W : CanWorld (Base := Base) Const,
            (.eq u (treifyK (Base := Base) (Const := Const) σ d) :
              ClosedFormula (WithParams Const)) ∈ W.carrier :=
          ihσ.2 hdu (repK_treifyK hadm)
        exact repK_respects_eq ρ
          (fun W => SupportedCanonicalMembership.eq_symm_mem
            (SupportedCanonicalMembership.eq_app_congr_mem
              (SupportedCanonicalMembership.eq_refl_mem t) (heq W)))
          (ihρ.1 (.app t (treifyK (Base := Base) (Const := Const) σ d)))
      · intro W
        refine SupportedCanonicalMembership.eq_funext_mem (fun w => ?_)
        exact ihρ.2
          (h1 (tvalK (Base := Base) (Const := Const) σ w) w (ihσ.1 w))
          (h2 (tvalK (Base := Base) (Const := Const) σ w) w (ihσ.1 w)) W

/-- `tvalK τ t` is represented by `t`. -/
theorem rep_tvalK (P : SchedulerProvider (Base := Base) Const)
    {τ : Ty Base} (t : ClosedTerm (WithParams Const) τ) :
    RepK (Base := Base) (Const := Const) τ
      (tvalK (Base := Base) (Const := Const) τ t) t :=
  (repCoreK (Base := Base) (Const := Const) P τ).1 t

/-! ## The canonical Kripke premodel -/

/-- The canonical Kripke premodel: supported presented worlds under `LevelLe`,
raw closed terms at base types with membership-based world-indexed equality,
representability as (world-independent) admissibility, and `tvalK` constant
denotations. -/
noncomputable def canonicalGeneralPreModel (P : SchedulerProvider (Base := Base) Const) :
    KripkePreModel Base (WithParams Const) where
  World := CanWorld (Base := Base) Const
  le := LevelLe (Base := Base) (Const := Const)
  le_refl := levelLe_refl (Base := Base) (Const := Const)
  le_trans := fun hUV hVW => levelLe_trans (Base := Base) (Const := Const) hUV hVW
  Carrier := CanCarrier (Base := Base) Const
  baseEq := fun W _b s t => (.eq s t : ClosedFormula (WithParams Const)) ∈ W.carrier
  baseEq_mono := fun hUV h => hUV.2 h
  baseEq_refl := fun _W _b d => SupportedCanonicalMembership.eq_refl_mem d
  baseEq_symm := fun h => SupportedCanonicalMembership.eq_symm_mem h
  baseEq_trans := fun h₁ h₂ => SupportedCanonicalMembership.eq_trans_mem h₁ h₂
  adm := fun _W τ v => AdmK (Base := Base) (Const := Const) τ v
  adm_mono := fun _ h => h
  prop_adm_upset := by
    rintro W S ⟨t, ht⟩ U V hUV hS
    exact (ht V).mpr (hUV.2 ((ht U).mp hS))
  base_mem := fun _W b d =>
    ⟨d, fun W => SupportedCanonicalMembership.eq_refl_mem d⟩
  app_mem := by
    rintro W σ τ f d ⟨tf, htf⟩ ⟨td, htd⟩
    exact ⟨.app tf td, htf d td htd⟩
  constDen := fun c => tvalK (Base := Base) (Const := Const) _ (.const c)
  const_mem := fun _W {_τ} c => ⟨.const c, rep_tvalK P (.const c)⟩

end CanonicalGeneral
end KripkeHenkin
end Mettapedia.Logic.HOL
