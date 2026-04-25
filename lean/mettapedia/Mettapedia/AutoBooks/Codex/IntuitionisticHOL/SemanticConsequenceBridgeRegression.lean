import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SemanticConsequenceBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SemanticConsequenceBridgeRegression

open Mettapedia.Logic.HOL

universe u v

inductive BaseSort where
  | atom
  deriving DecidableEq

def Const : Ty BaseSort → Type := fun _ => PEmpty

abbrev ClosedProp := ClosedFormula Const

def goodFrontier : CompletenessFrontier Const [] :=
  { antecedents := [(.top : ClosedProp)]
    succedent := (.top : ClosedProp) }

theorem semilocalSoundnessFloor_path
    {M : SemilocalModel.{0, 0, u, v} BaseSort Const}
    (hDer : Derivable (Base := BaseSort) (Const := Const)
      goodFrontier.antecedents goodFrontier.succedent)
    (ρ : SemilocalModel.Env M [])
    (hM : SemilocalModel.SupportsUniformRelativization M)
    (hρ : SemilocalModel.IsGlobalEnv M ρ)
    (hΔ : SemilocalModel.antecedentTruth M ρ goodFrontier.antecedents = ⊤) :
    SemilocalModel.formulaTruth M ρ goodFrontier.succedent = ⊤ := by
  exact goodFrontier.semilocalSoundnessFloor_of_derivable hDer M ρ hM hρ hΔ

theorem globalSoundnessFloor_path
    (hDer : Derivable (Base := BaseSort) (Const := Const)
      goodFrontier.antecedents goodFrontier.succedent)
    (M : GlobalModel BaseSort Const) :
    GlobalModel.ValidSequent M goodFrontier.antecedents goodFrontier.succedent := by
  exact goodFrontier.globalSoundnessFloor_of_derivable hDer M

theorem counterexample_refutes_semilocal_consequence_path
    (hCounter :
      CompletenessFrontier.HasSemilocalTruthCounterexample.{0, 0, u, v}
        (Base := BaseSort) (Const := Const) goodFrontier) :
    ¬ CompletenessFrontier.SemilocalSemanticConsequence.{0, 0, u, v}
      (Base := BaseSort) (Const := Const) goodFrontier := by
  exact CompletenessFrontier.not_semilocalSemanticConsequence_of_hasSemilocalTruthCounterexample
    (Base := BaseSort) (Const := Const) (Γ := []) goodFrontier hCounter

theorem semilocal_consequence_excludes_counterexample_path
    (hConsequence :
      CompletenessFrontier.SemilocalSemanticConsequence.{0, 0, u, v}
        (Base := BaseSort) (Const := Const) goodFrontier) :
    ¬ CompletenessFrontier.HasSemilocalTruthCounterexample.{0, 0, u, v}
      (Base := BaseSort) (Const := Const) goodFrontier := by
  exact goodFrontier.not_hasSemilocalTruthCounterexample_of_semilocalSemanticConsequence
    hConsequence

theorem stable_no_counterexample_semilocal_consequence_path
    (hStable :
      CompletenessFrontier.SemilocalTopStable.{0, 0, u, v}
        (Base := BaseSort) (Const := Const) goodFrontier)
    (hNoCounter :
      ¬ CompletenessFrontier.HasSemilocalTruthCounterexample.{0, 0, u, v}
        (Base := BaseSort) (Const := Const) goodFrontier) :
    CompletenessFrontier.SemilocalSemanticConsequence.{0, 0, u, v}
      (Base := BaseSort) (Const := Const) goodFrontier := by
  exact goodFrontier.semilocalSemanticConsequence_of_not_hasSemilocalTruthCounterexample
    hStable hNoCounter

theorem stable_semilocal_consequence_iff_no_counterexample_path
    (hStable :
      CompletenessFrontier.SemilocalTopStable.{0, 0, u, v}
        (Base := BaseSort) (Const := Const) goodFrontier) :
    CompletenessFrontier.SemilocalSemanticConsequence.{0, 0, u, v}
      (Base := BaseSort) (Const := Const) goodFrontier ↔
      ¬ CompletenessFrontier.HasSemilocalTruthCounterexample.{0, 0, u, v}
        (Base := BaseSort) (Const := Const) goodFrontier := by
  exact goodFrontier.semilocalSemanticConsequence_iff_not_hasSemilocalTruthCounterexample_of_stable
    hStable

theorem global_consequence_excludes_counterexample_path
    (hConsequence :
      CompletenessFrontier.GlobalSemanticConsequence.{0, 0, u, v}
        (Base := BaseSort) (Const := Const) goodFrontier) :
    ¬ CompletenessFrontier.HasGlobalSemanticCounterexample.{0, 0, u, v}
      (Base := BaseSort) (Const := Const) goodFrontier := by
  exact goodFrontier.not_hasGlobalSemanticCounterexample_of_globalSemanticConsequence
    hConsequence

theorem stable_no_counterexample_global_consequence_path
    (hStable :
      CompletenessFrontier.GlobalSemanticStable.{0, 0, u, v}
        (Base := BaseSort) (Const := Const) goodFrontier)
    (hNoCounter :
      ¬ CompletenessFrontier.HasGlobalSemanticCounterexample.{0, 0, u, v}
        (Base := BaseSort) (Const := Const) goodFrontier) :
    CompletenessFrontier.GlobalSemanticConsequence.{0, 0, u, v}
      (Base := BaseSort) (Const := Const) goodFrontier := by
  exact goodFrontier.globalSemanticConsequence_of_not_hasGlobalSemanticCounterexample
    hStable hNoCounter

theorem stable_global_consequence_iff_no_counterexample_path
    (hStable :
      CompletenessFrontier.GlobalSemanticStable.{0, 0, u, v}
        (Base := BaseSort) (Const := Const) goodFrontier) :
    CompletenessFrontier.GlobalSemanticConsequence.{0, 0, u, v}
      (Base := BaseSort) (Const := Const) goodFrontier ↔
      ¬ CompletenessFrontier.HasGlobalSemanticCounterexample.{0, 0, u, v}
        (Base := BaseSort) (Const := Const) goodFrontier := by
  exact goodFrontier.globalSemanticConsequence_iff_not_hasGlobalSemanticCounterexample_of_stable
    hStable

theorem derivation_exists_semantics_refutes_semilocal_consequence_path
    {F : CompletenessFrontier Const []}
    (D : CertifiedHeadPriorityDerivation Const [] F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (hSem :
      ∃ (M : SemilocalModel.{0, 0, u, v} BaseSort Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ CompletenessFrontier.SemilocalSemanticConsequence.{0, 0, u, v}
      (Base := BaseSort) (Const := Const) F := by
  exact CertifiedHeadPriorityDerivation.not_semilocalSemanticConsequence_of_exists_semantics
    (Base := BaseSort) (Const := Const) (Γ := []) D terminal branchClosed hSem

theorem completion_exists_semantics_refutes_semilocal_consequence_path
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hSem :
      ∃ (M : SemilocalModel.{0, 0, u, v} BaseSort Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ CompletenessFrontier.SemilocalSemanticConsequence.{0, 0, u, v}
      (Base := BaseSort) (Const := Const) F := by
  exact CertifiedHeadPriorityCompletion.not_semilocalSemanticConsequence_of_exists_semantics
    (Base := BaseSort) (Const := Const) (Γ := []) C hSem

theorem headPriorityCompletion_exists_semantics_refutes_semilocal_consequence_path
    {F : CompletenessFrontier Const []}
    (C : SaturationSearchState.HeadPriorityCompletion (Const := Const) F)
    (hInitial : F.ClosedNonconflicting)
    (hCompat : C.derivation.Compatible)
    (hSem :
      ∃ (M : SemilocalModel.{0, 0, u, v} BaseSort Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ CompletenessFrontier.SemilocalSemanticConsequence.{0, 0, u, v}
      (Base := BaseSort) (Const := Const) F := by
  exact SaturationSearchState.HeadPriorityCompletion.not_semilocalSemanticConsequence_of_exists_semantics
    (Base := BaseSort) (Const := Const) (Γ := []) C hInitial hCompat hSem

theorem certifiedCandidate_exists_semantics_refutes_semilocal_consequence_path
    (C : CertifiedCountermodelCandidate Const [])
    (hSem :
      ∃ (M : SemilocalModel.{0, 0, u, v} BaseSort Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ CompletenessFrontier.SemilocalSemanticConsequence.{0, 0, u, v}
      (Base := BaseSort) (Const := Const) C.frontier := by
  exact CertifiedCountermodelCandidate.not_semilocalSemanticConsequence_of_exists_semantics
    (Base := BaseSort) (Const := Const) (Γ := []) C hSem

theorem certifiedCandidate_classified_exists_semantics_refutes_semilocal_consequence_path
    (C : CertifiedCountermodelCandidate Const [])
    (hSem :
      ∃ (M : SemilocalModel.{0, 0, u, v} BaseSort Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty (C.CandidateClosedHintikkaSemantics env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ CompletenessFrontier.SemilocalSemanticConsequence.{0, 0, u, v}
      (Base := BaseSort) (Const := Const) C.frontier := by
  exact CertifiedCountermodelCandidate.not_semilocalSemanticConsequence_of_exists_candidateClosedHintikkaSemantics
    (Base := BaseSort) (Const := Const) (Γ := []) C hSem

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SemanticConsequenceBridgeRegression
