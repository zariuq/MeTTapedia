import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ConsequenceFloor

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ConsequenceFloorRegression

open Mettapedia.Logic.HOL
open CompletenessFrontier

universe u v

inductive TestBase where
  | atom
deriving DecidableEq, Repr

inductive TestConst : Ty TestBase → Type where
  | a : TestConst (.base .atom)

theorem semilocalSurface_soundness_path
    {Γ : Ctx TestBase}
    {F : CompletenessFrontier TestConst Γ}
    (hDer : Derivable (Base := TestBase) (Const := TestConst) F.antecedents F.succedent) :
    CompletenessFrontier.SemilocalSemanticConsequence.{0, 0, u, v}
      (Base := TestBase) (Const := TestConst) F :=
  F.semilocalSurface.consequence_of_goal hDer

theorem semilocalSurface_consequence_excludes_counterexample_path
    {Γ : Ctx TestBase}
    {F : CompletenessFrontier TestConst Γ}
    (hConsequence :
      CompletenessFrontier.SemilocalSemanticConsequence.{0, 0, u, v}
        (Base := TestBase) (Const := TestConst) F) :
    ¬ CompletenessFrontier.HasSemilocalTruthCounterexample.{0, 0, u, v}
      (Base := TestBase) (Const := TestConst) F :=
  F.semilocalSurface.no_counterexample_of_consequence hConsequence

theorem semilocalSurface_goal_excludes_counterexample_via_consequence_path
    {Γ : Ctx TestBase}
    {F : CompletenessFrontier TestConst Γ}
    (hDer : Derivable (Base := TestBase) (Const := TestConst) F.antecedents F.succedent) :
    ¬ CompletenessFrontier.HasSemilocalTruthCounterexample.{0, 0, u, v}
      (Base := TestBase) (Const := TestConst) F :=
  F.semilocalSurface.no_counterexample_of_goal_via_consequence hDer

theorem derivation_exists_semantics_refutes_goal_path
    {Γ : Ctx TestBase}
    {F : CompletenessFrontier TestConst Γ}
    (D : CertifiedHeadPriorityDerivation TestConst Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (hSem :
      ∃ (M : SemilocalModel.{0, 0, u, v} TestBase TestConst)
          (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula TestConst Γ},
            (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula TestConst Γ},
            (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := TestBase) (Const := TestConst) F.antecedents F.succedent :=
  CompletenessFrontier.not_derivable_of_derivation_exists_semantics
    (Base := TestBase) (Const := TestConst) D terminal branchClosed hSem

theorem completion_exists_semantics_refutes_goal_path
    {Γ : Ctx TestBase}
    {F : CompletenessFrontier TestConst Γ}
    (C : CertifiedHeadPriorityCompletion TestConst Γ F)
    (hSem :
      ∃ (M : SemilocalModel.{0, 0, u, v} TestBase TestConst)
          (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula TestConst Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula TestConst Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := TestBase) (Const := TestConst) F.antecedents F.succedent :=
  CompletenessFrontier.not_derivable_of_completion_exists_semantics
    (Base := TestBase) (Const := TestConst) C hSem

theorem headPriorityCompletion_exists_semantics_refutes_goal_path
    {Γ : Ctx TestBase}
    {F : CompletenessFrontier TestConst Γ}
    (C : SaturationSearchState.HeadPriorityCompletion F)
    (hInitial : F.ClosedNonconflicting)
    (hCompat : C.derivation.Compatible)
    (hSem :
      ∃ (M : SemilocalModel.{0, 0, u, v} TestBase TestConst)
          (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula TestConst Γ},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula TestConst Γ},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := TestBase) (Const := TestConst) F.antecedents F.succedent :=
  CompletenessFrontier.not_derivable_of_headPriorityCompletion_exists_semantics
    (Base := TestBase) (Const := TestConst) C hInitial hCompat hSem

theorem candidate_exists_semantics_refutes_goal_path
    {Γ : Ctx TestBase}
    (C : CertifiedCountermodelCandidate TestConst Γ)
    (hSem :
      ∃ (M : SemilocalModel.{0, 0, u, v} TestBase TestConst)
          (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula TestConst Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula TestConst Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        C.frontier.antecedents C.frontier.succedent :=
  CompletenessFrontier.not_derivable_of_candidate_exists_semantics
    (Base := TestBase) (Const := TestConst) C hSem

theorem candidate_classified_exists_semantics_refutes_goal_path
    {Γ : Ctx TestBase}
    (C : CertifiedCountermodelCandidate TestConst Γ)
    (hSem :
      ∃ (M : SemilocalModel.{0, 0, u, v} TestBase TestConst)
          (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty (C.CandidateClosedHintikkaSemantics env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        C.frontier.antecedents C.frontier.succedent :=
  CompletenessFrontier.not_derivable_of_candidate_exists_candidateClosedHintikkaSemantics
    (Base := TestBase) (Const := TestConst) C hSem

theorem closedWorldModelSurface_soundness_path
    {F : CompletenessFrontier TestConst []}
    (hDer : Derivable (Base := TestBase) (Const := TestConst) F.antecedents F.succedent) :
    SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F :=
  F.closedWorldModelSurface.consequence_of_goal hDer

theorem closedWorldModelSurface_counterexample_refutes_goal_path
    {F : CompletenessFrontier TestConst []}
    (hCounter : Nonempty (SingletonWorldModelCounterexample (Const := TestConst) F)) :
    ¬ Derivable (Base := TestBase) (Const := TestConst) F.antecedents F.succedent :=
  F.closedWorldModelSurface.counterexample_refutes_goal hCounter

theorem closedWorldModelSurface_consequence_excludes_counterexample_path
    {F : CompletenessFrontier TestConst []}
    (hConsequence : SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F) :
    ¬ Nonempty (SingletonWorldModelCounterexample (Const := TestConst) F) :=
  F.closedWorldModelSurface.no_counterexample_of_consequence hConsequence

theorem closedWorldModelSurface_counterexample_of_quotientRealizationSemanticCounterexample_path
    {F : CompletenessFrontier TestConst []}
    {M : HenkinModel TestBase TestConst}
    {W : ClosedTheorySet.World TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (hAnte : ∀ φ, φ ∈ F.antecedents → HenkinModel.models M φ)
    (hSucc : ¬ HenkinModel.models M F.succedent) :
    Nonempty (SingletonWorldModelCounterexample (Const := TestConst) F) :=
  F.closedWorldModelSurface_counterexample_of_quotientRealizationSemanticCounterexample
    (Base := TestBase) (Const := TestConst) R hAnte hSucc

theorem closedWorldModelSurface_refutes_goal_of_quotientRealizationSemanticCounterexample_path
    {F : CompletenessFrontier TestConst []}
    {M : HenkinModel TestBase TestConst}
    {W : ClosedTheorySet.World TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (hAnte : ∀ φ, φ ∈ F.antecedents → HenkinModel.models M φ)
    (hSucc : ¬ HenkinModel.models M F.succedent) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  F.closedWorldModelSurface_refutes_goal_of_quotientRealizationSemanticCounterexample
    (Base := TestBase) (Const := TestConst) R hAnte hSucc

theorem closedWorldModelSurface_refutes_consequence_of_quotientRealizationSemanticCounterexample_path
    {F : CompletenessFrontier TestConst []}
    {M : HenkinModel TestBase TestConst}
    {W : ClosedTheorySet.World TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (hAnte : ∀ φ, φ ∈ F.antecedents → HenkinModel.models M φ)
    (hSucc : ¬ HenkinModel.models M F.succedent) :
    ¬ SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F :=
  F.closedWorldModelSurface_refutes_consequence_of_quotientRealizationSemanticCounterexample
    (Base := TestBase) (Const := TestConst) R hAnte hSucc

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ConsequenceFloorRegression
