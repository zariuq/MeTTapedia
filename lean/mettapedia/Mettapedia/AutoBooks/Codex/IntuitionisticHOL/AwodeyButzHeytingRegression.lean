import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzHeyting

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzHeytingRegression

open Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v} {X : Type w} [TopologicalSpace X]

theorem fullEval_weaken_of_pointwise_path
    (I : HeytingTopologicalInterpretation Base Const X)
    [HeytingTopologicalInterpretation.FullEvalPointwiseCoherent I]
    {σ : Ty Base} {Γ : Ctx Base}
    (φ : Formula Const Γ) :
    HeytingTopologicalInterpretation.fullEval I (weaken (σ := σ) φ) =
      I.evalWeaken σ Γ (HeytingTopologicalInterpretation.fullEval I φ) := by
  exact HeytingTopologicalInterpretation.fullEval_weaken (I := I) (σ := σ) φ

theorem fullEval_instantiate_of_pointwise_path
    (I : HeytingTopologicalInterpretation Base Const X)
    [HeytingTopologicalInterpretation.FullEvalPointwiseCoherent I]
    {σ : Ty Base} {Γ : Ctx Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ)) :
    HeytingTopologicalInterpretation.fullEval I (instantiate t φ) =
      I.evalInstantiate t (HeytingTopologicalInterpretation.fullEval I φ) := by
  exact HeytingTopologicalInterpretation.fullEval_instantiate (I := I) t φ

theorem fullEval_betaEtaEq_of_pointwise_path
    (I : HeytingTopologicalInterpretation Base Const X)
    [HeytingTopologicalInterpretation.FullEvalPointwiseCoherent I]
    {Γ : Ctx Base} {φ ψ : Formula Const Γ}
    (h : BetaEtaEq φ ψ) :
    HeytingTopologicalInterpretation.fullEval I φ =
      HeytingTopologicalInterpretation.fullEval I ψ := by
  exact HeytingTopologicalInterpretation.fullEval_betaEtaEq (I := I) h

theorem evalInstantiate_eq_reindex_cons_of_pointwise_path
    (I : HeytingTopologicalInterpretation Base Const X)
    [HeytingTopologicalInterpretation.FullEvalPointwiseCoherent I]
    {Γ : Ctx Base} {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ)) :
    (HeytingTopologicalInterpretation.fullEval I φ).reindex
        (TopologicalInterpretation.CtxHom.cons
          (HeytingTopologicalInterpretation.fullEval I t)
          (TopologicalInterpretation.CtxHom.id I.toTopologicalInterpretation Γ)) =
      I.evalInstantiate t (HeytingTopologicalInterpretation.fullEval I φ) := by
  exact HeytingTopologicalInterpretation.evalInstantiate_eq_reindex_cons (I := I) t φ

theorem formulaEval_beta_of_pointwise_path
    (I : HeytingTopologicalInterpretation Base Const X)
    [HeytingTopologicalInterpretation.FullEvalPointwiseCoherent I]
    {Γ : Ctx Base} {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (γ : (I.ctxSpace Γ).Carrier) :
    I.formulaEval (.app (.lam φ) t) γ =
      I.formulaEval (instantiate t φ) γ := by
  exact HeytingTopologicalInterpretation.formulaEval_beta (I := I) t φ γ

theorem fullValidSequent_beta_of_pointwise_path
    (I : HeytingTopologicalInterpretation Base Const X)
    [HeytingTopologicalInterpretation.FullEvalPointwiseCoherent I]
    {Γ : Ctx Base} (Δ : List (Formula Const Γ))
    {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (h : I.FullValidSequent Δ (instantiate t φ)) :
    I.FullValidSequent Δ (.app (.lam φ) t) := by
  exact HeytingTopologicalInterpretation.FullValidSequent.beta (I := I) (Δ := Δ) t φ h

theorem evalAntecedents_betaEtaEq_of_pointwise_path
    (I : HeytingTopologicalInterpretation Base Const X)
    [HeytingTopologicalInterpretation.FullEvalPointwiseCoherent I]
    {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)}
    (h : AntecedentsBetaEtaEq Δ Δ') :
    HeytingTopologicalInterpretation.evalAntecedents I Δ =
      HeytingTopologicalInterpretation.evalAntecedents I Δ' := by
  exact HeytingTopologicalInterpretation.evalAntecedents_betaEtaEq (I := I) h

theorem evalAntecedents_betaEtaEq_of_fullEvalCoherent_path
    (I : HeytingTopologicalInterpretation Base Const X)
    [HeytingTopologicalInterpretation.FullEvalCoherent I]
    {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)}
    (h : AntecedentsBetaEtaEq Δ Δ') :
    HeytingTopologicalInterpretation.evalAntecedents I Δ =
      HeytingTopologicalInterpretation.evalAntecedents I Δ' := by
  exact HeytingTopologicalInterpretation.evalAntecedents_betaEtaEq_of_fullEvalCoherent
    (I := I) h

theorem beta_soundness_path
    (I : HeytingTopologicalInterpretation Base Const X)
    [HeytingTopologicalInterpretation.FullEvalPointwiseCoherent I]
    {Γ : Ctx Base} (Δ : List (Formula Const Γ))
    {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (h : Derivable Const Δ (instantiate t φ)) :
    I.FullValidSequent Δ (.app (.lam φ) t) := by
  exact HeytingTopologicalInterpretation.FullValidSequent.beta (I := I) (Δ := Δ) t φ
    (HeytingTopologicalInterpretation.fullSoundness (I := I) h)

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzHeytingRegression
