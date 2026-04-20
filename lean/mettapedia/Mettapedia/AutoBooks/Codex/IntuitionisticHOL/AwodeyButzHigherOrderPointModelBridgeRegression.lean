import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzHigherOrderPointModelBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

namespace AwodeyButzHigherOrderPointModelBridgeRegression

universe u v

theorem beta_counterexample_exists_path
    {Base : Type u} {Const : Ty Base → Type v}
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent (M := M) Δ γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval (M := M) (instantiate t φ) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ (.app (.lam φ) t) := by
  exact HigherOrderPointTopologicalGlobalModelBridge.not_derivable_of_exists_beta_truth_counterexample
    t φ hCounter

theorem instantiate_truth_path
    {Base : Type u} {Const : Ty Base → Type v}
    (M : GlobalModel Base Const)
    {Γ : Ctx Base} {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := M) Γ).Carrier) :
    HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
        (M := M) (instantiate t φ) γ =
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
        (M := M) φ
        (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.consCtx
          (M := M)
          (SemilocalModel.eval M.toSemilocalModel
            (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.decodeEnv
              (M := M) γ) t)
          γ) := by
  exact HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval_instantiate
    (M := M) t φ γ

end AwodeyButzHigherOrderPointModelBridgeRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
