import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzCompletenessBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzCompletenessBridgeRegression

open Mettapedia.Logic.HOL

universe u v w w'

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

theorem soundLocalCountermodel_path
    {F : CompletenessFrontier Const Γ}
    (C : SoundLocalCountermodel (Base := Base) (Const := Const) F) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact C.awodey_butz_completeness

theorem exists_soundLocalCountermodel_path
    {F : CompletenessFrontier Const Γ}
    (C : SoundLocalCountermodel (Base := Base) (Const := Const) F) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact awodey_butz_completeness_of_exists_soundLocalCountermodel
    (Base := Base) (Const := Const) (F := F) ⟨C⟩

theorem derivation_exists_semantics_path
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact awodey_butz_completeness_of_exists_semantics
    (Base := Base) (Const := Const) D terminal branchClosed hSem

theorem derivation_candidate_semantics_path
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics
      D terminal branchClosed env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact S.awodey_butz_completeness global hM

theorem certified_candidate_semantics_path
    (C : CertifiedCountermodelCandidate Const Γ)
    {M : SemilocalModel Base Const}
    {env : SemilocalModel.Env M Γ}
    (S : C.CandidateClosedHintikkaSemantics env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents C.frontier.succedent := by
  exact S.awodey_butz_completeness global hM

theorem certified_candidate_exists_semantics_path
    (C : CertifiedCountermodelCandidate Const Γ)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty (C.CandidateClosedHintikkaSemantics env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents C.frontier.succedent := by
  exact C.awodey_butz_completeness_of_exists_candidateClosedHintikkaSemantics hSem

theorem beta_exists_truth_counterexample_path
    {Δ : List (Formula Const Γ)} {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := M) Γ).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := M) Δ γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := M) (instantiate t φ) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ (.app (.lam φ) t) := by
  exact awodey_butz_completeness_of_exists_beta_truth_counterexample
    (Base := Base) (Const := Const) t φ hCounter

theorem beta_exists_truth_counterexample_bridge_path
    {Δ : List (Formula Const Γ)} {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := M) Γ).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := M) Δ γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := M) (instantiate t φ) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ (.app (.lam φ) t) := by
  exact awodey_butz_completeness_bridge_of_exists_beta_truth_counterexample
    (Base := Base) (Const := Const) t φ hCounter

theorem frontier_beta_exists_truth_counterexample_path
    (F : CompletenessFrontier Const Γ)
    {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := M) Γ).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := M) F.antecedents γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := M) (instantiate t φ) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents (.app (.lam φ) t) := by
  exact F.awodey_butz_completeness_of_exists_beta_truth_counterexample
    (Base := Base) (Const := Const) t φ hCounter

theorem certifiedCandidate_beta_exists_truth_counterexample_path
    (C : CertifiedCountermodelCandidate Const Γ)
    {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := M) Γ).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := M) C.frontier.antecedents γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := M) (instantiate t φ) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents (.app (.lam φ) t) := by
  exact C.awodey_butz_completeness_of_exists_beta_truth_counterexample
    (Base := Base) (Const := Const) t φ hCounter

theorem closedCertifiedCandidate_beta_exists_truth_counterexample_path
    (C : CertifiedCountermodelCandidate Const [])
    {σ : Ty Base}
    (t : Term Const [] σ)
    (φ : Formula Const [σ])
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := M) []).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := M) C.frontier.antecedents γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := M) (instantiate t φ) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents (.app (.lam φ) t) := by
  exact C.awodey_butz_completeness_of_exists_closed_beta_truth_counterexample
    (Base := Base) (Const := Const) t φ hCounter

theorem closedCertifiedCandidate_exists_beta_succedent_counterexample_path
    (C : CertifiedCountermodelCandidate Const [])
    {σ : Ty Base}
    (t : Term Const [] σ)
    (φ : Formula Const [σ])
    (hSucc : C.frontier.succedent = (.app (.lam φ) t))
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := M) []).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := M) C.frontier.antecedents γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := M) (instantiate t φ) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents C.frontier.succedent := by
  exact C.awodey_butz_completeness_of_exists_closed_beta_succedent_counterexample
    (Base := Base) (Const := Const) t φ hSucc hCounter

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzCompletenessBridgeRegression
