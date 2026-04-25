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

theorem completion_candidate_semantics_path
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    {env : SemilocalModel.Env M Γ}
    (S : CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics C env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact S.awodey_butz_completeness C global hM

theorem completion_exists_semantics_path
    {F : CompletenessFrontier Const Γ}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact C.awodey_butz_completeness_of_exists_semantics hSem

theorem headPriorityCompletion_exists_semantics_path
    {F : CompletenessFrontier Const Γ}
    (C : SaturationSearchState.HeadPriorityCompletion (Const := Const) F)
    (hInitial : F.ClosedNonconflicting)
    (hCompat : C.derivation.Compatible)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact C.awodey_butz_completeness_of_exists_semantics hInitial hCompat hSem

theorem derivation_candidate_beta_exists_truth_counterexample_path
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics
      D terminal branchClosed env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M)
    {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (hCounter :
      ∃ (G : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := G) Γ).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := G) F.antecedents γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := G) (instantiate t φ) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents (.app (.lam φ) t) := by
  exact S.awodey_butz_completeness_of_exists_beta_truth_counterexample
    global hM t φ hCounter

theorem derivation_candidate_and_witness_top_of_truthValidSequent_path
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics
      D terminal branchClosed env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M)
    (φ ψ : Formula Const Γ)
    (G : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := G) F.antecedents (Term.and φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := G) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := G) F.antecedents γ = ⊤) :
    G.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := G)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := G)).fiberMeet
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := G)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := G) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := G)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := G) ψ γ))), by simp⟩)) = ⊤ := by
  exact S.awodey_butz_and_witness_top_of_truthValidSequent
    global hM φ ψ G hvalid γ hΔ

theorem derivation_candidate_or_witness_top_of_truthValidSequent_path
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics
      D terminal branchClosed env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M)
    (φ ψ : Formula Const Γ)
    (G : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := G) F.antecedents (Term.or φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := G) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := G) F.antecedents γ = ⊤) :
    G.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := G)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := G)).fiberJoin
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := G)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := G) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := G)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := G) ψ γ))), by simp⟩)) = ⊤ := by
  exact S.awodey_butz_or_witness_top_of_truthValidSequent
    global hM φ ψ G hvalid γ hΔ

theorem derivation_candidate_imp_witness_top_of_truthValidSequent_path
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics
      D terminal branchClosed env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M)
    (φ ψ : Formula Const Γ)
    (G : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := G) F.antecedents (Term.imp φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := G) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := G) F.antecedents γ = ⊤) :
    G.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := G)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := G)).fiberHimp
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := G)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := G) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := G)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := G) ψ γ))), by simp⟩)) = ⊤ := by
  exact S.awodey_butz_imp_witness_top_of_truthValidSequent
    global hM φ ψ G hvalid γ hΔ

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

theorem completion_candidate_and_witness_top_of_truthValidSequent_path
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    {env : SemilocalModel.Env M Γ}
    (S : CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics C env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M)
    (φ ψ : Formula Const Γ)
    (G : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := G) F.antecedents (Term.and φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := G) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := G) F.antecedents γ = ⊤) :
    G.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := G)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := G)).fiberMeet
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := G)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := G) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := G)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := G) ψ γ))), by simp⟩)) = ⊤ := by
  exact S.awodey_butz_and_witness_top_of_truthValidSequent
    C global hM φ ψ G hvalid γ hΔ

theorem completion_candidate_or_witness_top_of_truthValidSequent_path
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    {env : SemilocalModel.Env M Γ}
    (S : CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics C env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M)
    (φ ψ : Formula Const Γ)
    (G : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := G) F.antecedents (Term.or φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := G) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := G) F.antecedents γ = ⊤) :
    G.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := G)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := G)).fiberJoin
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := G)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := G) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := G)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := G) ψ γ))), by simp⟩)) = ⊤ := by
  exact S.awodey_butz_or_witness_top_of_truthValidSequent
    C global hM φ ψ G hvalid γ hΔ

theorem completion_candidate_imp_witness_top_of_truthValidSequent_path
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    {env : SemilocalModel.Env M Γ}
    (S : CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics C env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M)
    (φ ψ : Formula Const Γ)
    (G : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := G) F.antecedents (Term.imp φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := G) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := G) F.antecedents γ = ⊤) :
    G.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := G)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := G)).fiberHimp
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := G)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := G) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := G)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := G) ψ γ))), by simp⟩)) = ⊤ := by
  exact S.awodey_butz_imp_witness_top_of_truthValidSequent
    C global hM φ ψ G hvalid γ hΔ

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

theorem certified_candidate_raw_exists_semantics_path
    (C : CertifiedCountermodelCandidate Const Γ)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents C.frontier.succedent := by
  exact C.awodey_butz_completeness_of_exists_semantics hSem

theorem completion_candidate_beta_exists_truth_counterexample_path
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    {env : SemilocalModel.Env M Γ}
    (S : CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics C env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M)
    {σ : Ty Base}
    (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ))
    (hCounter :
      ∃ (G : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := G) Γ).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := G) F.antecedents γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := G) (instantiate t φ) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents (.app (.lam φ) t) := by
  exact S.awodey_butz_completeness_of_exists_beta_truth_counterexample
    C global hM t φ hCounter

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

theorem soundLocalCountermodel_beta_exists_truth_counterexample_path
    {F : CompletenessFrontier Const Γ}
    (C : SoundLocalCountermodel (Base := Base) (Const := Const) F)
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
  exact C.awodey_butz_completeness_of_exists_beta_truth_counterexample
    (Base := Base) (Const := Const) t φ hCounter

theorem frontier_and_witness_top_of_truthValidSequent_path
    (F : CompletenessFrontier Const Γ)
    (φ ψ : Formula Const Γ)
    (M : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) F.antecedents (Term.and φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) F.antecedents γ = ⊤) :
    M.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := M)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := M)).fiberMeet
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) ψ γ))), by simp⟩)) = ⊤ := by
  exact F.awodey_butz_and_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

theorem frontier_or_witness_top_of_truthValidSequent_path
    (F : CompletenessFrontier Const Γ)
    (φ ψ : Formula Const Γ)
    (M : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) F.antecedents (Term.or φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) F.antecedents γ = ⊤) :
    M.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := M)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := M)).fiberJoin
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) ψ γ))), by simp⟩)) = ⊤ := by
  exact F.awodey_butz_or_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

theorem certifiedCandidate_and_witness_top_of_truthValidSequent_path
    (C : CertifiedCountermodelCandidate Const Γ)
    (φ ψ : Formula Const Γ)
    (M : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) C.frontier.antecedents (Term.and φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) C.frontier.antecedents γ = ⊤) :
    M.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := M)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := M)).fiberMeet
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) ψ γ))), by simp⟩)) = ⊤ := by
  exact C.awodey_butz_and_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

theorem frontier_imp_witness_top_of_truthValidSequent_path
    (F : CompletenessFrontier Const Γ)
    (φ ψ : Formula Const Γ)
    (M : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) F.antecedents (Term.imp φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) F.antecedents γ = ⊤) :
    M.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := M)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := M)).fiberHimp
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) ψ γ))), by simp⟩)) = ⊤ := by
  exact F.awodey_butz_imp_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

theorem certifiedCandidate_or_witness_top_of_truthValidSequent_path
    (C : CertifiedCountermodelCandidate Const Γ)
    (φ ψ : Formula Const Γ)
    (M : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) C.frontier.antecedents (Term.or φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) C.frontier.antecedents γ = ⊤) :
    M.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := M)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := M)).fiberJoin
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) ψ γ))), by simp⟩)) = ⊤ := by
  exact C.awodey_butz_or_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

theorem certifiedCandidate_imp_witness_top_of_truthValidSequent_path
    (C : CertifiedCountermodelCandidate Const Γ)
    (φ ψ : Formula Const Γ)
    (M : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) C.frontier.antecedents (Term.imp φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) C.frontier.antecedents γ = ⊤) :
    M.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := M)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := M)).fiberHimp
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) ψ γ))), by simp⟩)) = ⊤ := by
  exact C.awodey_butz_imp_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

theorem soundLocalCountermodel_and_witness_top_of_truthValidSequent_path
    {F : CompletenessFrontier Const Γ}
    (C : SoundLocalCountermodel (Base := Base) (Const := Const) F)
    (φ ψ : Formula Const Γ)
    (M : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) F.antecedents (Term.and φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) F.antecedents γ = ⊤) :
    M.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := M)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := M)).fiberMeet
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) ψ γ))), by simp⟩)) = ⊤ := by
  exact C.awodey_butz_and_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

theorem soundLocalCountermodel_or_witness_top_of_truthValidSequent_path
    {F : CompletenessFrontier Const Γ}
    (C : SoundLocalCountermodel (Base := Base) (Const := Const) F)
    (φ ψ : Formula Const Γ)
    (M : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) F.antecedents (Term.or φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) F.antecedents γ = ⊤) :
    M.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := M)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := M)).fiberJoin
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) ψ γ))), by simp⟩)) = ⊤ := by
  exact C.awodey_butz_or_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

theorem soundLocalCountermodel_imp_witness_top_of_truthValidSequent_path
    {F : CompletenessFrontier Const Γ}
    (C : SoundLocalCountermodel (Base := Base) (Const := Const) F)
    (φ ψ : Formula Const Γ)
    (M : GlobalModel Base Const)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) F.antecedents (Term.imp φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
        (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) F.antecedents γ = ⊤) :
    M.truth
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := M)).decodeProp
        ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := M)).fiberHimp
          ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) φ γ)),
              ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
                (M := M)).encodeProp
                (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                  (M := M) ψ γ))), by simp⟩)) = ⊤ := by
  exact C.awodey_butz_imp_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

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

theorem closedCertifiedCandidate_exists_semantics_of_not_closedTheorySetProvable_path
    (C : CertifiedCountermodelCandidate Const [])
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          C.frontier.antecedentTheorySet C.frontier.succedent)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents C.frontier.succedent := by
  exact C.awodey_butz_completeness_of_exists_semantics_of_not_closedTheorySetProvable
    (Base := Base) (Const := Const) hNot hSem

theorem closedCertifiedCandidate_exists_semantics_of_primeSeparatingExtension_path
    (C : CertifiedCountermodelCandidate Const [])
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) C.frontier U)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents C.frontier.succedent := by
  exact C.awodey_butz_completeness_of_exists_semantics_of_primeSeparatingExtension
    (Base := Base) (Const := Const) hFU hSem

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzCompletenessBridgeRegression
