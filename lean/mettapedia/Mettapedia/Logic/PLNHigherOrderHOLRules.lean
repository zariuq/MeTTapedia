import Mettapedia.Logic.PLNHigherOrderHOLCore

namespace Mettapedia.Logic.PLNHigherOrderHOLRules

universe u v

open Mettapedia.Logic.HOL

variable {Base : Type u} {Const : Ty Base → Type v}

abbrev HOLQuery (Const : Ty Base → Type v) :=
  Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery (Base := Base) Const

abbrev HOLProvable (φ : HOLQuery Const) : Prop :=
  Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvable (Const := Const) φ

abbrev HOLProvImp (φ ψ : HOLQuery Const) : Prop :=
  Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvImp (Const := Const) φ ψ

abbrev HOLProvEq {τ : Ty Base} (t u : Term Const [] τ) : Prop :=
  Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvEq (Const := Const) t u

/-- Provable logical equivalence for closed HOL formulas. -/
def HOLProvIff (φ ψ : HOLQuery Const) : Prop :=
  HOLProvable (Const := Const) (.and (.imp φ ψ) (.imp ψ φ))

/-- Provable pointwise equality for closed HOL functions. -/
def HOLProvPointwiseEq {σ τ : Ty Base}
    (f g : Term Const [] (σ ⇒ τ)) : Prop :=
  HOLProvable (Const := Const)
    (.all (.eq (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))
               (.app (weaken (Base := Base) (σ := σ) g) (.var .vz))))

theorem holProvIff_of_mutual {φ ψ : HOLQuery Const}
    (hφψ : HOLProvImp (Const := Const) φ ψ)
    (hψφ : HOLProvImp (Const := Const) ψ φ) :
    HOLProvIff (Const := Const) φ ψ :=
  .andI hφψ hψφ

theorem holProvIff_refl (φ : HOLQuery Const) :
    HOLProvIff (Const := Const) φ φ :=
  holProvIff_of_mutual (Const := Const)
    (Mettapedia.Logic.PLNHigherOrderHOLCore.holProvImp_refl φ)
    (Mettapedia.Logic.PLNHigherOrderHOLCore.holProvImp_refl φ)

theorem holProvIff_symm {φ ψ : HOLQuery Const}
    (h : HOLProvIff (Const := Const) φ ψ) :
    HOLProvIff (Const := Const) ψ φ :=
  .andI (.andER h) (.andEL h)

theorem holProvIff_trans {φ ψ χ : HOLQuery Const}
    (hφψ : HOLProvIff (Const := Const) φ ψ)
    (hψχ : HOLProvIff (Const := Const) ψ χ) :
    HOLProvIff (Const := Const) φ χ := by
  have hφψ_fwd : HOLProvImp (Const := Const) φ ψ := .andEL hφψ
  have hφψ_rev : HOLProvImp (Const := Const) ψ φ := .andER hφψ
  have hψχ_fwd : HOLProvImp (Const := Const) ψ χ := .andEL hψχ
  have hψχ_rev : HOLProvImp (Const := Const) χ ψ := .andER hψχ
  exact .andI
    (Mettapedia.Logic.PLNHigherOrderHOLCore.holProvImp_trans hφψ_fwd hψχ_fwd)
    (Mettapedia.Logic.PLNHigherOrderHOLCore.holProvImp_trans hψχ_rev hφψ_rev)

theorem holProvImp_and_mono {φ ψ χ δ : HOLQuery Const}
    (hφψ : HOLProvImp (Const := Const) φ ψ)
    (hχδ : HOLProvImp (Const := Const) χ δ) :
    HOLProvImp (Const := Const) (.and φ χ) (.and ψ δ) := by
  refine .impI ?_
  have hAnd : Derivation Const [.and φ χ] (.and φ χ) := .hyp (by simp)
  have hφ : Derivation Const [.and φ χ] φ := .andEL hAnd
  have hχ : Derivation Const [.and φ χ] χ := .andER hAnd
  have hψ : Derivation Const [.and φ χ] ψ :=
    .impE (Derivation.ofTheorem (Const := Const) (Δ := [.and φ χ]) hφψ) hφ
  have hδ : Derivation Const [.and φ χ] δ :=
    .impE (Derivation.ofTheorem (Const := Const) (Δ := [.and φ χ]) hχδ) hχ
  exact .andI hψ hδ

theorem holProvImp_or_mono {φ ψ χ δ : HOLQuery Const}
    (hφψ : HOLProvImp (Const := Const) φ ψ)
    (hχδ : HOLProvImp (Const := Const) χ δ) :
    HOLProvImp (Const := Const) (.or φ χ) (.or ψ δ) := by
  refine .impI ?_
  have hOr : Derivation Const [.or φ χ] (.or φ χ) := .hyp (by simp)
  refine .orE hOr ?_ ?_
  · have hφ : Derivation Const [φ, .or φ χ] φ := .hyp (by simp)
    have hψ : Derivation Const [φ, .or φ χ] ψ :=
      .impE (Derivation.ofTheorem (Const := Const) (Δ := [φ, .or φ χ]) hφψ) hφ
    exact .orIL hψ
  · have hχ : Derivation Const [χ, .or φ χ] χ := .hyp (by simp)
    have hδ : Derivation Const [χ, .or φ χ] δ :=
      .impE (Derivation.ofTheorem (Const := Const) (Δ := [χ, .or φ χ]) hχδ) hχ
    exact .orIR hδ

theorem holProvImp_and_left (φ ψ : HOLQuery Const) :
    HOLProvImp (Const := Const) (.and φ ψ) φ := by
  refine .impI ?_
  have hAnd : Derivation Const [.and φ ψ] (.and φ ψ) := .hyp (by simp)
  exact .andEL hAnd

theorem holProvImp_and_right (φ ψ : HOLQuery Const) :
    HOLProvImp (Const := Const) (.and φ ψ) ψ := by
  refine .impI ?_
  have hAnd : Derivation Const [.and φ ψ] (.and φ ψ) := .hyp (by simp)
  exact .andER hAnd

theorem holProvImp_and_intro {φ ψ χ : HOLQuery Const}
    (hφψ : HOLProvImp (Const := Const) φ ψ)
    (hφχ : HOLProvImp (Const := Const) φ χ) :
    HOLProvImp (Const := Const) φ (.and ψ χ) := by
  refine .impI ?_
  have hφ : Derivation Const [φ] φ := .hyp (by simp)
  have hψ : Derivation Const [φ] ψ :=
    .impE (Derivation.ofTheorem (Const := Const) (Δ := [φ]) hφψ) hφ
  have hχ : Derivation Const [φ] χ :=
    .impE (Derivation.ofTheorem (Const := Const) (Δ := [φ]) hφχ) hφ
  exact .andI hψ hχ

theorem holProvImp_or_intro_left (φ ψ : HOLQuery Const) :
    HOLProvImp (Const := Const) φ (.or φ ψ) := by
  refine .impI ?_
  have hφ : Derivation Const [φ] φ := .hyp (by simp)
  exact .orIL hφ

theorem holProvImp_or_intro_right (φ ψ : HOLQuery Const) :
    HOLProvImp (Const := Const) ψ (.or φ ψ) := by
  refine .impI ?_
  have hψ : Derivation Const [ψ] ψ := .hyp (by simp)
  exact .orIR hψ

theorem holProvImp_or_elim {φ ψ χ : HOLQuery Const}
    (hφχ : HOLProvImp (Const := Const) φ χ)
    (hψχ : HOLProvImp (Const := Const) ψ χ) :
    HOLProvImp (Const := Const) (.or φ ψ) χ := by
  refine .impI ?_
  have hOr : Derivation Const [.or φ ψ] (.or φ ψ) := .hyp (by simp)
  refine .orE hOr ?_ ?_
  · have hφ : Derivation Const [φ, .or φ ψ] φ := .hyp (by simp)
    exact .impE
      (Derivation.ofTheorem (Const := Const) (Δ := [φ, .or φ ψ]) hφχ) hφ
  · have hψ : Derivation Const [ψ, .or φ ψ] ψ := .hyp (by simp)
    exact .impE
      (Derivation.ofTheorem (Const := Const) (Δ := [ψ, .or φ ψ]) hψχ) hψ

theorem holProvImp_not_of {φ ψ : HOLQuery Const}
    (hψφ : HOLProvImp (Const := Const) ψ φ) :
    HOLProvImp (Const := Const) (.not φ) (.not ψ) := by
  refine .impI ?_
  refine .notI ?_
  have hNotφ : Derivation Const [ψ, .not φ] (.not φ) := .hyp (by simp)
  have hψ : Derivation Const [ψ, .not φ] ψ := .hyp (by simp)
  have hφ : Derivation Const [ψ, .not φ] φ :=
    .impE (Derivation.ofTheorem (Const := Const) (Δ := [ψ, .not φ]) hψφ) hψ
  exact .notE hNotφ hφ

theorem holProvImp_imp_mono {φ ψ χ δ : HOLQuery Const}
    (hψφ : HOLProvImp (Const := Const) ψ φ)
    (hχδ : HOLProvImp (Const := Const) χ δ) :
    HOLProvImp (Const := Const) (.imp φ χ) (.imp ψ δ) := by
  refine .impI ?_
  refine .impI ?_
  have hImp : Derivation Const [ψ, .imp φ χ] (.imp φ χ) := .hyp (by simp)
  have hψ : Derivation Const [ψ, .imp φ χ] ψ := .hyp (by simp)
  have hφ : Derivation Const [ψ, .imp φ χ] φ :=
    .impE (Derivation.ofTheorem (Const := Const) (Δ := [ψ, .imp φ χ]) hψφ) hψ
  have hχ : Derivation Const [ψ, .imp φ χ] χ := .impE hImp hφ
  exact .impE
    (Derivation.ofTheorem (Const := Const) (Δ := [ψ, .imp φ χ]) hχδ) hχ

theorem holProvEq_refl {τ : Ty Base} (t : Term Const [] τ) :
    HOLProvEq (Const := Const) t t :=
  .eqRefl t

theorem holProvEq_symm {τ : Ty Base} {t u : Term Const [] τ}
    (htu : HOLProvEq (Const := Const) t u) :
    HOLProvEq (Const := Const) u t :=
  .eqSymm htu

theorem holProvEq_trans {τ : Ty Base} {t u v : Term Const [] τ}
    (htu : HOLProvEq (Const := Const) t u)
    (huv : HOLProvEq (Const := Const) u v) :
    HOLProvEq (Const := Const) t v :=
  .eqTrans htu huv

theorem holProvEq_app {σ τ : Ty Base} {f g : Term Const [] (σ ⇒ τ)}
    (t : Term Const [] σ)
    (hfg : HOLProvEq (Const := Const) f g) :
    HOLProvEq (Const := Const) (.app f t) (.app g t) :=
  .eqApp t hfg

theorem holProvEq_beta {σ τ : Ty Base}
    (t : Term Const [] σ) (u : Term Const [σ] τ) :
    HOLProvEq (Const := Const) (.app (.lam u) t) (instantiate (Base := Base) t u) :=
  .beta t u

theorem holProvEq_eta {σ τ : Ty Base}
    (f : Term Const [] (σ ⇒ τ)) :
    HOLProvEq (Const := Const)
      (.lam (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))) f :=
  .eta f

theorem holProvEq_of_pointwise {σ τ : Ty Base} {f g : Term Const [] (σ ⇒ τ)}
    (h : HOLProvPointwiseEq (Base := Base) (Const := Const) f g) :
    HOLProvEq (Const := Const) f g :=
  .funExt h

theorem holProvIff_and_mono {φ ψ χ δ : HOLQuery Const}
    (hφψ : HOLProvIff (Const := Const) φ ψ)
    (hχδ : HOLProvIff (Const := Const) χ δ) :
    HOLProvIff (Const := Const) (.and φ χ) (.and ψ δ) :=
  holProvIff_of_mutual (Const := Const)
    (holProvImp_and_mono (Const := Const) (.andEL hφψ) (.andEL hχδ))
    (holProvImp_and_mono (Const := Const) (.andER hφψ) (.andER hχδ))

theorem holProvIff_or_mono {φ ψ χ δ : HOLQuery Const}
    (hφψ : HOLProvIff (Const := Const) φ ψ)
    (hχδ : HOLProvIff (Const := Const) χ δ) :
    HOLProvIff (Const := Const) (.or φ χ) (.or ψ δ) :=
  holProvIff_of_mutual (Const := Const)
    (holProvImp_or_mono (Const := Const) (.andEL hφψ) (.andEL hχδ))
    (holProvImp_or_mono (Const := Const) (.andER hφψ) (.andER hχδ))

theorem holProvIff_not {φ ψ : HOLQuery Const}
    (hφψ : HOLProvIff (Const := Const) φ ψ) :
    HOLProvIff (Const := Const) (.not φ) (.not ψ) :=
  holProvIff_of_mutual (Const := Const)
    (holProvImp_not_of (Const := Const) (.andER hφψ))
    (holProvImp_not_of (Const := Const) (.andEL hφψ))

theorem holProvIff_imp_mono {φ ψ χ δ : HOLQuery Const}
    (hφψ : HOLProvIff (Const := Const) φ ψ)
    (hχδ : HOLProvIff (Const := Const) χ δ) :
    HOLProvIff (Const := Const) (.imp φ χ) (.imp ψ δ) :=
  holProvIff_of_mutual (Const := Const)
    (holProvImp_imp_mono (Const := Const) (.andER hφψ) (.andEL hχδ))
    (holProvImp_imp_mono (Const := Const) (.andEL hφψ) (.andER hχδ))

theorem holProvIff_and_comm (φ ψ : HOLQuery Const) :
    HOLProvIff (Const := Const) (.and φ ψ) (.and ψ φ) := by
  refine holProvIff_of_mutual (Const := Const) ?_ ?_
  · refine .impI ?_
    have hAnd : Derivation Const [.and φ ψ] (.and φ ψ) := .hyp (by simp)
    exact .andI (.andER hAnd) (.andEL hAnd)
  · refine .impI ?_
    have hAnd : Derivation Const [.and ψ φ] (.and ψ φ) := .hyp (by simp)
    exact .andI (.andER hAnd) (.andEL hAnd)

theorem holProvIff_or_comm (φ ψ : HOLQuery Const) :
    HOLProvIff (Const := Const) (.or φ ψ) (.or ψ φ) := by
  refine holProvIff_of_mutual (Const := Const) ?_ ?_
  · refine .impI ?_
    have hOr : Derivation Const [.or φ ψ] (.or φ ψ) := .hyp (by simp)
    refine .orE hOr ?_ ?_
    · exact .orIR (.hyp (by simp))
    · exact .orIL (.hyp (by simp))
  · refine .impI ?_
    have hOr : Derivation Const [.or ψ φ] (.or ψ φ) := .hyp (by simp)
    refine .orE hOr ?_ ?_
    · exact .orIR (.hyp (by simp))
    · exact .orIL (.hyp (by simp))

end Mettapedia.Logic.PLNHigherOrderHOLRules
