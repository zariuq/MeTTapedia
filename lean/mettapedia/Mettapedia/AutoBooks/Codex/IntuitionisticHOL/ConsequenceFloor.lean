import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SemanticConsequenceBridge
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzCompletenessBridge
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermWorldModelCountermodel

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w w'

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

/--
A reusable consequence/counterexample interface:

- `goal` is the proof-theoretic target we ultimately care about,
- `consequence` is the positive semantic or world-model endpoint,
- `counterexample` is the negative witness endpoint.

The intended reading is:
`goal -> consequence`, `counterexample -> not goal`, and
`counterexample -> not consequence`.
-/
structure ConsequenceCounterexampleSurface
    (goal consequence counterexample : Prop) : Prop where
  consequence_of_goal : goal → consequence
  counterexample_refutes_goal : counterexample → ¬ goal
  counterexample_refutes_consequence : counterexample → ¬ consequence
  no_counterexample_of_goal : goal → ¬ counterexample

namespace ConsequenceCounterexampleSurface

variable {goal consequence counterexample : Prop}

/-- Counterexamples are incompatible with the positive consequence endpoint. -/
theorem no_counterexample_of_consequence
    (S : ConsequenceCounterexampleSurface goal consequence counterexample)
    (hConsequence : consequence) :
    ¬ counterexample := by
  intro hCounter
  exact S.counterexample_refutes_consequence hCounter hConsequence

/-- The negative endpoint can be read directly as failure of consequence. -/
theorem not_consequence_of_counterexample
    (S : ConsequenceCounterexampleSurface goal consequence counterexample)
    (hCounter : counterexample) :
    ¬ consequence :=
  S.counterexample_refutes_consequence hCounter

/-- The proof-theoretic goal excludes counterexamples through consequence. -/
theorem no_counterexample_of_goal_via_consequence
    (S : ConsequenceCounterexampleSurface goal consequence counterexample)
    (hGoal : goal) :
    ¬ counterexample :=
  S.no_counterexample_of_consequence (S.consequence_of_goal hGoal)

end ConsequenceCounterexampleSurface

namespace CompletenessFrontier

/-- Native derivability packaged as the proof-theoretic goal for a frontier. -/
abbrev DerivabilityGoal (F : CompletenessFrontier Const Γ) : Prop :=
  Derivable (Base := Base) (Const := Const) F.antecedents F.succedent

/-- Semilocal semantic consequence packaged in the reusable surface format. -/
abbrev SemilocalSurface (F : CompletenessFrontier Const Γ) : Prop :=
  ConsequenceCounterexampleSurface
    (DerivabilityGoal (Base := Base) (Const := Const) F)
    (CompletenessFrontier.SemilocalSemanticConsequence.{u, v, w, w'}
      (Base := Base) (Const := Const) F)
    (CompletenessFrontier.HasSemilocalTruthCounterexample.{u, v, w, w'}
      (Base := Base) (Const := Const) F)

/--
The mature semilocal mainline floor:
derivability implies semilocal semantic consequence, and extracted semilocal
truth counterexamples refute both derivability and that consequence endpoint.
-/
def semilocalSurface (F : CompletenessFrontier Const Γ) :
    SemilocalSurface (Base := Base) (Const := Const) (Γ := Γ) F where
  consequence_of_goal := F.semilocalSoundnessFloor_of_derivable
  counterexample_refutes_goal := F.not_derivable_of_hasSemilocalTruthCounterexample
  counterexample_refutes_consequence :=
    F.not_semilocalSemanticConsequence_of_hasSemilocalTruthCounterexample
  no_counterexample_of_goal := F.not_hasSemilocalTruthCounterexample_of_derivable

/--
Semantic floor bundling the semilocal consequence interface with the matching
global-model soundness endpoint.
-/
structure SemanticFloor (F : CompletenessFrontier Const Γ) : Prop where
  semilocal :
    SemilocalSurface.{u, v, w, w'} (Base := Base) (Const := Const) (Γ := Γ) F
  global_sound :
    DerivabilityGoal (Base := Base) (Const := Const) F →
      CompletenessFrontier.GlobalSemanticConsequence.{u, v, w, w'}
        (Base := Base) (Const := Const) F

/-- One-stop semantic floor for the mature mainline route. -/
def semanticFloor (F : CompletenessFrontier Const Γ) :
    SemanticFloor (Base := Base) (Const := Const) (Γ := Γ) F where
  semilocal := F.semilocalSurface
  global_sound := F.globalSoundnessFloor_of_derivable

/--
Top-level mainline wrapper:
raw derivation-layer extracted semantics already refute derivability through the
semantic-floor interface.
-/
theorem not_derivable_of_derivation_exists_semantics
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
    ¬ DerivabilityGoal (Base := Base) (Const := Const) F := by
  exact F.not_derivable_of_hasSemilocalTruthCounterexample
    (D.exists_semilocal_truth_counterexample_of_exists_semantics terminal branchClosed hSem)

/-- Certified completion version of the same one-stop refutation wrapper. -/
theorem not_derivable_of_completion_exists_semantics
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
    ¬ DerivabilityGoal (Base := Base) (Const := Const) F := by
  exact F.not_derivable_of_hasSemilocalTruthCounterexample
    (C.exists_semilocal_truth_counterexample_of_exists_semantics hSem)

/-- Search-state completion version of the same one-stop refutation wrapper. -/
theorem not_derivable_of_headPriorityCompletion_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (C : SaturationSearchState.HeadPriorityCompletion F)
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
    ¬ DerivabilityGoal (Base := Base) (Const := Const) F := by
  exact F.not_derivable_of_hasSemilocalTruthCounterexample
    (C.exists_semilocal_truth_counterexample_of_exists_semantics hInitial hCompat hSem)

/-- Certified-candidate raw semantics version of the same wrapper. -/
theorem not_derivable_of_candidate_exists_semantics
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
    ¬ DerivabilityGoal (Base := Base) (Const := Const) C.frontier := by
  exact C.frontier.not_derivable_of_hasSemilocalTruthCounterexample
    (C.exists_semilocal_truth_counterexample_of_exists_semantics hSem)

/-- Classified certified-candidate semantics version of the same wrapper. -/
theorem not_derivable_of_candidate_exists_candidateClosedHintikkaSemantics
    (C : CertifiedCountermodelCandidate Const Γ)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
          (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty (C.CandidateClosedHintikkaSemantics env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ DerivabilityGoal (Base := Base) (Const := Const) C.frontier := by
  exact C.frontier.not_derivable_of_hasSemilocalTruthCounterexample
    (C.exists_semilocal_truth_counterexample_of_exists_candidateClosedHintikkaSemantics hSem)

/-- Centralized Awodey-Butz derivation-layer wrapper. -/
theorem awodey_butz_not_derivable_of_derivation_exists_semantics
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
    ¬ DerivabilityGoal (Base := Base) (Const := Const) F :=
  awodey_butz_completeness_of_exists_semantics
    (Base := Base) (Const := Const) D terminal branchClosed hSem

/-- Centralized Awodey-Butz certified-completion wrapper. -/
theorem awodey_butz_not_derivable_of_completion_exists_semantics
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
    ¬ DerivabilityGoal (Base := Base) (Const := Const) F :=
  C.awodey_butz_completeness_of_exists_semantics hSem

/-- Centralized Awodey-Butz search-state completion wrapper. -/
theorem awodey_butz_not_derivable_of_headPriorityCompletion_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (C : SaturationSearchState.HeadPriorityCompletion F)
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
    ¬ DerivabilityGoal (Base := Base) (Const := Const) F :=
  C.awodey_butz_completeness_of_exists_semantics hInitial hCompat hSem

/-- Centralized Awodey-Butz certified-candidate raw semantics wrapper. -/
theorem awodey_butz_not_derivable_of_candidate_exists_semantics
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
    ¬ DerivabilityGoal (Base := Base) (Const := Const) C.frontier :=
  C.awodey_butz_completeness_of_exists_semantics hSem

/-- Centralized Awodey-Butz certified-candidate classified semantics wrapper. -/
theorem awodey_butz_not_derivable_of_candidate_exists_candidateClosedHintikkaSemantics
    (C : CertifiedCountermodelCandidate Const Γ)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
          (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty (C.CandidateClosedHintikkaSemantics env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ DerivabilityGoal (Base := Base) (Const := Const) C.frontier :=
  C.awodey_butz_completeness_of_exists_candidateClosedHintikkaSemantics hSem

/-- Closed-frontier world-model/query-strength consequence in reusable form. -/
abbrev ClosedWorldModelSurface (F : CompletenessFrontier Const []) : Prop :=
  ConsequenceCounterexampleSurface
    (DerivabilityGoal (Base := Base) (Const := Const) F)
    (SingletonStrengthConsequence (Base := Base) (Const := Const) F)
    (Nonempty (SingletonWorldModelCounterexample (Const := Const) F))

/--
Closed singleton-strength world-model floor:
derivability implies singleton query-strength consequence, and singleton
world-model counterexamples refute both derivability and that consequence.
-/
def closedWorldModelSurface (F : CompletenessFrontier Const []) :
    ClosedWorldModelSurface (Base := Base) (Const := Const) F where
  consequence_of_goal := F.singletonStrengthConsequence_of_derivable
  counterexample_refutes_goal := by
    rintro ⟨C⟩
    exact C.not_derivable
  counterexample_refutes_consequence := by
    rintro ⟨C⟩
    exact F.not_singletonStrengthConsequence_of_counterexample C
  no_counterexample_of_goal := by
    intro hDer
    exact F.not_nonempty_singletonWorldModelCounterexample_of_derivable hDer

/-- A closed-term quotient realization that semantically separates a frontier
is exactly the negative endpoint expected by the closed world-model surface. -/
theorem closedWorldModelSurface_counterexample_of_quotientRealizationSemanticCounterexample
    {F : CompletenessFrontier Const []}
    {M : HenkinModel.{u, v, w} Base Const}
    {W : ClosedTheorySet.World Const}
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (hAnte : ∀ φ, φ ∈ F.antecedents → HenkinModel.models M φ)
    (hSucc : ¬ HenkinModel.models M F.succedent) :
    Nonempty (SingletonWorldModelCounterexample (Const := Const) F) :=
  ⟨singletonWorldModelCounterexampleOfQuotientRealizationSemanticCounterexample
    (Base := Base) (Const := Const) (W := W) R hAnte hSucc⟩

/-- The closed world-model surface consumes a realized quotient separation as a
direct refutation of native derivability. -/
theorem closedWorldModelSurface_refutes_goal_of_quotientRealizationSemanticCounterexample
    {F : CompletenessFrontier Const []}
    {M : HenkinModel.{u, v, w} Base Const}
    {W : ClosedTheorySet.World Const}
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (hAnte : ∀ φ, φ ∈ F.antecedents → HenkinModel.models M φ)
    (hSucc : ¬ HenkinModel.models M F.succedent) :
    ¬ DerivabilityGoal (Base := Base) (Const := Const) F :=
  (closedWorldModelSurface (Base := Base) (Const := Const) F).counterexample_refutes_goal
    (closedWorldModelSurface_counterexample_of_quotientRealizationSemanticCounterexample
      (Base := Base) (Const := Const) (W := W) R hAnte hSucc)

/-- The closed world-model surface also consumes a realized quotient separation
as a direct refutation of singleton query-strength consequence. -/
theorem closedWorldModelSurface_refutes_consequence_of_quotientRealizationSemanticCounterexample
    {F : CompletenessFrontier Const []}
    {M : HenkinModel.{u, v, w} Base Const}
    {W : ClosedTheorySet.World Const}
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (hAnte : ∀ φ, φ ∈ F.antecedents → HenkinModel.models M φ)
    (hSucc : ¬ HenkinModel.models M F.succedent) :
    ¬ SingletonStrengthConsequence (Base := Base) (Const := Const) F :=
  (closedWorldModelSurface (Base := Base) (Const := Const) F).counterexample_refutes_consequence
    (closedWorldModelSurface_counterexample_of_quotientRealizationSemanticCounterexample
      (Base := Base) (Const := Const) (W := W) R hAnte hSucc)

/--
Closed-frontier floor bundling the mature semantic interface and the canonical
singleton-strength world-model/query-strength interface.
-/
structure ClosedFrontierFloor (F : CompletenessFrontier Const []) : Prop where
  semantic :
    SemanticFloor.{u, v, w, w'} (Base := Base) (Const := Const) (Γ := []) F
  worldModel :
    ClosedWorldModelSurface (Base := Base) (Const := Const) F

/-- One-stop floor for closed frontiers across semantic and world-model endpoints. -/
def closedFrontierFloor (F : CompletenessFrontier Const []) :
    ClosedFrontierFloor (Base := Base) (Const := Const) F where
  semantic := F.semanticFloor
  worldModel := F.closedWorldModelSurface

end CompletenessFrontier

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
