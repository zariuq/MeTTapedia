import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Soundness
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Completeness
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzHigherOrderPointModelBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w w'

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

namespace CompletenessFrontier

/--
Generic HOL semilocal semantic consequence: every supported global environment
that makes the antecedent sequent fully true also makes the succedent fully
true.
-/
def SemilocalSemanticConsequence
    (F : CompletenessFrontier Const Γ) : Prop :=
  ∀ (M : SemilocalModel.{u, v, w, w'} Base Const)
      (ρ : SemilocalModel.Env M Γ),
    SemilocalModel.SupportsUniformRelativization M →
      SemilocalModel.IsGlobalEnv M ρ →
      SemilocalModel.antecedentTruth M ρ F.antecedents = ⊤ →
      SemilocalModel.formulaTruth M ρ F.succedent = ⊤

/-- Generic HOL global semantic consequence: every global model validates the
frontier sequent. -/
def GlobalSemanticConsequence
    (F : CompletenessFrontier Const Γ) : Prop :=
  ∀ M : GlobalModel.{u, v, w, w'} Base Const,
    GlobalModel.ValidSequent M F.antecedents F.succedent

/-- A global semantic counterexample is a global model refuting the frontier
sequent. -/
def HasGlobalSemanticCounterexample
    (F : CompletenessFrontier Const Γ) : Prop :=
  ∃ M : GlobalModel.{u, v, w, w'} Base Const,
    ¬ GlobalModel.ValidSequent M F.antecedents F.succedent

/--
Extracted semilocal counterexample data in the exact shape produced by the
mature completeness path.
-/
def HasSemilocalTruthCounterexample
    (F : CompletenessFrontier Const Γ) : Prop :=
  ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
      (ρ : SemilocalModel.Env M Γ),
    SemilocalModel.IsGlobalEnv M ρ ∧
      SemilocalModel.antecedentTruth M ρ F.antecedents = ⊤ ∧
      SemilocalModel.formulaTruth M ρ F.succedent ≠ ⊤ ∧
      SemilocalModel.SupportsUniformRelativization M

/--
Stability principle needed to turn absence of semilocal truth counterexamples
back into positive semilocal consequence constructively. Classical models
satisfy this by excluded middle, while intuitionistic developments may prove it
from a concrete truth-value semantics.
-/
def SemilocalTopStable
    (F : CompletenessFrontier Const Γ) : Prop :=
  ∀ (M : SemilocalModel.{u, v, w, w'} Base Const)
      (ρ : SemilocalModel.Env M Γ),
    SemilocalModel.SupportsUniformRelativization M →
      SemilocalModel.IsGlobalEnv M ρ →
      SemilocalModel.antecedentTruth M ρ F.antecedents = ⊤ →
      ¬¬ SemilocalModel.formulaTruth M ρ F.succedent = ⊤ →
      SemilocalModel.formulaTruth M ρ F.succedent = ⊤

/--
Stability principle needed to turn absence of global semantic countermodels back
into positive global semantic consequence constructively.
-/
def GlobalSemanticStable
    (F : CompletenessFrontier Const Γ) : Prop :=
  ∀ M : GlobalModel.{u, v, w, w'} Base Const,
    ¬¬ GlobalModel.ValidSequent M F.antecedents F.succedent →
      GlobalModel.ValidSequent M F.antecedents F.succedent

/-- Package the semilocal soundness floor as direct truth preservation. -/
theorem semilocalSoundnessFloor_of_derivable
    (F : CompletenessFrontier Const Γ)
    (hDer : Derivable (Base := Base) (Const := Const) F.antecedents F.succedent) :
    CompletenessFrontier.SemilocalSemanticConsequence.{u, v, w, w'}
      (Base := Base) (Const := Const) F := by
  intro M ρ hM hρ hΔ
  have hValid : SemilocalModel.ValidSequent M F.antecedents F.succedent :=
    SemilocalModel.soundness_target M hM hDer
  have hLe :
      SemilocalModel.antecedentTruth M ρ F.antecedents ≤
        SemilocalModel.formulaTruth M ρ F.succedent :=
    hValid ρ hρ
  have hTopLe : (⊤ : M.Omega) ≤ SemilocalModel.formulaTruth M ρ F.succedent := by
    rw [← hΔ]
    exact hLe
  exact le_antisymm le_top hTopLe

/--
Package the global soundness floor as a direct frontier-level semantic
consequence theorem.
-/
theorem globalSoundnessFloor_of_derivable
    (F : CompletenessFrontier Const Γ)
    (hDer : Derivable (Base := Base) (Const := Const) F.antecedents F.succedent) :
    CompletenessFrontier.GlobalSemanticConsequence.{u, v, w, w'}
      (Base := Base) (Const := Const) F := by
  intro M
  exact GlobalModel.soundness_target M hDer

/-- Positive semantic consequence rules out semilocal truth counterexamples. -/
theorem not_hasSemilocalTruthCounterexample_of_semilocalSemanticConsequence
    (F : CompletenessFrontier Const Γ)
    (hConsequence :
      CompletenessFrontier.SemilocalSemanticConsequence.{u, v, w, w'}
        (Base := Base) (Const := Const) F) :
    ¬ CompletenessFrontier.HasSemilocalTruthCounterexample.{u, v, w, w'}
      (Base := Base) (Const := Const) F := by
  intro hCounter
  rcases hCounter with ⟨M, ρ, hρ, hΔ, hφ, hM⟩
  exact hφ (hConsequence M ρ hM hρ hΔ)

/--
Absence of semilocal truth counterexamples implies positive semilocal
consequence whenever the relevant top-truth equality is stable.
-/
theorem semilocalSemanticConsequence_of_not_hasSemilocalTruthCounterexample
    (F : CompletenessFrontier Const Γ)
    (hStable :
      CompletenessFrontier.SemilocalTopStable.{u, v, w, w'}
        (Base := Base) (Const := Const) F)
    (hNoCounter :
      ¬ CompletenessFrontier.HasSemilocalTruthCounterexample.{u, v, w, w'}
        (Base := Base) (Const := Const) F) :
    CompletenessFrontier.SemilocalSemanticConsequence.{u, v, w, w'}
      (Base := Base) (Const := Const) F := by
  intro M ρ hM hρ hΔ
  exact hStable M ρ hM hρ hΔ (by
    intro hNotTop
    exact hNoCounter ⟨M, ρ, hρ, hΔ, hNotTop, hM⟩)

/--
For stable semilocal truth, semantic consequence is equivalent to the absence
of semilocal truth counterexamples.
-/
theorem semilocalSemanticConsequence_iff_not_hasSemilocalTruthCounterexample_of_stable
    (F : CompletenessFrontier Const Γ)
    (hStable :
      CompletenessFrontier.SemilocalTopStable.{u, v, w, w'}
        (Base := Base) (Const := Const) F) :
    CompletenessFrontier.SemilocalSemanticConsequence.{u, v, w, w'}
      (Base := Base) (Const := Const) F ↔
      ¬ CompletenessFrontier.HasSemilocalTruthCounterexample.{u, v, w, w'}
        (Base := Base) (Const := Const) F := by
  constructor
  · exact F.not_hasSemilocalTruthCounterexample_of_semilocalSemanticConsequence
  · exact F.semilocalSemanticConsequence_of_not_hasSemilocalTruthCounterexample hStable

/-- Positive global semantic consequence rules out global countermodels. -/
theorem not_hasGlobalSemanticCounterexample_of_globalSemanticConsequence
    (F : CompletenessFrontier Const Γ)
    (hConsequence :
      CompletenessFrontier.GlobalSemanticConsequence.{u, v, w, w'}
        (Base := Base) (Const := Const) F) :
    ¬ CompletenessFrontier.HasGlobalSemanticCounterexample.{u, v, w, w'}
      (Base := Base) (Const := Const) F := by
  intro hCounter
  rcases hCounter with ⟨M, hM⟩
  exact hM (hConsequence M)

/--
Absence of global semantic countermodels implies positive global consequence
whenever global sequent validity is stable.
-/
theorem globalSemanticConsequence_of_not_hasGlobalSemanticCounterexample
    (F : CompletenessFrontier Const Γ)
    (hStable :
      CompletenessFrontier.GlobalSemanticStable.{u, v, w, w'}
        (Base := Base) (Const := Const) F)
    (hNoCounter :
      ¬ CompletenessFrontier.HasGlobalSemanticCounterexample.{u, v, w, w'}
        (Base := Base) (Const := Const) F) :
    CompletenessFrontier.GlobalSemanticConsequence.{u, v, w, w'}
      (Base := Base) (Const := Const) F := by
  intro M
  exact hStable M (by
    intro hNotValid
    exact hNoCounter ⟨M, hNotValid⟩)

/--
For stable global validity, global semantic consequence is equivalent to the
absence of global semantic countermodels.
-/
theorem globalSemanticConsequence_iff_not_hasGlobalSemanticCounterexample_of_stable
    (F : CompletenessFrontier Const Γ)
    (hStable :
      CompletenessFrontier.GlobalSemanticStable.{u, v, w, w'}
        (Base := Base) (Const := Const) F) :
    CompletenessFrontier.GlobalSemanticConsequence.{u, v, w, w'}
      (Base := Base) (Const := Const) F ↔
      ¬ CompletenessFrontier.HasGlobalSemanticCounterexample.{u, v, w, w'}
        (Base := Base) (Const := Const) F := by
  constructor
  · exact F.not_hasGlobalSemanticCounterexample_of_globalSemanticConsequence
  · exact F.globalSemanticConsequence_of_not_hasGlobalSemanticCounterexample hStable

/--
Any extracted semilocal truth counterexample already refutes derivability via
the one-point semilocal bridge.
-/
theorem not_derivable_of_hasSemilocalTruthCounterexample
    (F : CompletenessFrontier Const Γ)
    (hCounter :
      CompletenessFrontier.HasSemilocalTruthCounterexample.{u, v, w, w'}
        (Base := Base) (Const := Const) F) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  intro hDer
  rcases hCounter with ⟨M, ρ, hρ, hΔ, hφ, hM⟩
  exact hφ (F.semilocalSoundnessFloor_of_derivable hDer M ρ hM hρ hΔ)

/-- Any extracted semilocal truth counterexample refutes the generic HOL
semantic consequence wrapper directly. -/
theorem not_semilocalSemanticConsequence_of_hasSemilocalTruthCounterexample
    (F : CompletenessFrontier Const Γ)
    (hCounter :
      CompletenessFrontier.HasSemilocalTruthCounterexample.{u, v, w, w'}
        (Base := Base) (Const := Const) F) :
    ¬ CompletenessFrontier.SemilocalSemanticConsequence.{u, v, w, w'}
      (Base := Base) (Const := Const) F := by
  intro hConsequence
  rcases hCounter with ⟨M, ρ, hρ, hΔ, hφ, hM⟩
  exact hφ (hConsequence M ρ hM hρ hΔ)

/--
Derivability excludes extracted semilocal truth counterexamples.
-/
theorem not_hasSemilocalTruthCounterexample_of_derivable
    (F : CompletenessFrontier Const Γ)
    (hDer : Derivable (Base := Base) (Const := Const) F.antecedents F.succedent) :
    ¬ CompletenessFrontier.HasSemilocalTruthCounterexample.{u, v, w, w'}
      (Base := Base) (Const := Const) F := by
  intro hCounter
  exact (F.not_derivable_of_hasSemilocalTruthCounterexample hCounter) hDer

end CompletenessFrontier

namespace CertifiedHeadPriorityDerivation

theorem not_semilocalSemanticConsequence_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (D : CertifiedHeadPriorityDerivation Const Γ F)
    (terminal : D.state.IsTerminal)
    (branchClosed : D.state.hintikka.BranchClosed)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
          (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ D.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ CompletenessFrontier.SemilocalSemanticConsequence.{u, v, w, w'}
      (Base := Base) (Const := Const) F := by
  exact F.not_semilocalSemanticConsequence_of_hasSemilocalTruthCounterexample
    (show CompletenessFrontier.HasSemilocalTruthCounterexample.{u, v, w, w'}
        (Base := Base) (Const := Const) F from
      D.exists_semilocal_truth_counterexample_of_exists_semantics terminal branchClosed hSem)

end CertifiedHeadPriorityDerivation

namespace CertifiedHeadPriorityCompletion

theorem not_semilocalSemanticConsequence_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
          (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ CompletenessFrontier.SemilocalSemanticConsequence.{u, v, w, w'}
      (Base := Base) (Const := Const) F := by
  exact F.not_semilocalSemanticConsequence_of_hasSemilocalTruthCounterexample
    (show CompletenessFrontier.HasSemilocalTruthCounterexample.{u, v, w, w'}
        (Base := Base) (Const := Const) F from
      C.exists_semilocal_truth_counterexample_of_exists_semantics hSem)

end CertifiedHeadPriorityCompletion

namespace SaturationSearchState.HeadPriorityCompletion

theorem not_semilocalSemanticConsequence_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F)
    (hInitial : F.ClosedNonconflicting)
    (hCompat : C.derivation.Compatible)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
          (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ CompletenessFrontier.SemilocalSemanticConsequence.{u, v, w, w'}
      (Base := Base) (Const := Const) F := by
  exact F.not_semilocalSemanticConsequence_of_hasSemilocalTruthCounterexample
    (show CompletenessFrontier.HasSemilocalTruthCounterexample.{u, v, w, w'}
        (Base := Base) (Const := Const) F from
      C.exists_semilocal_truth_counterexample_of_exists_semantics hInitial hCompat hSem)

end SaturationSearchState.HeadPriorityCompletion

namespace CertifiedCountermodelCandidate

theorem not_semilocalSemanticConsequence_of_exists_semantics
    (C : CertifiedCountermodelCandidate Const Γ)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
          (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const Γ},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const Γ},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ CompletenessFrontier.SemilocalSemanticConsequence.{u, v, w, w'}
      (Base := Base) (Const := Const) C.frontier := by
  exact C.frontier.not_semilocalSemanticConsequence_of_hasSemilocalTruthCounterexample
    (show CompletenessFrontier.HasSemilocalTruthCounterexample.{u, v, w, w'}
        (Base := Base) (Const := Const) C.frontier from
      C.exists_semilocal_truth_counterexample_of_exists_semantics hSem)

theorem not_semilocalSemanticConsequence_of_exists_candidateClosedHintikkaSemantics
    (C : CertifiedCountermodelCandidate Const Γ)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
          (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty (C.CandidateClosedHintikkaSemantics env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ CompletenessFrontier.SemilocalSemanticConsequence.{u, v, w, w'}
      (Base := Base) (Const := Const) C.frontier := by
  exact C.frontier.not_semilocalSemanticConsequence_of_hasSemilocalTruthCounterexample
    (show CompletenessFrontier.HasSemilocalTruthCounterexample.{u, v, w, w'}
        (Base := Base) (Const := Const) C.frontier from
      C.exists_semilocal_truth_counterexample_of_exists_candidateClosedHintikkaSemantics hSem)

end CertifiedCountermodelCandidate

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
