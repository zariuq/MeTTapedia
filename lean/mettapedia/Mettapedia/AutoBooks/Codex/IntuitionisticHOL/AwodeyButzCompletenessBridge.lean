import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Completeness
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.CanonicalBridge
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSemantics

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w w'

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

/--
Compose the certified completeness spine with the semilocal Awodey-Butz
counterexample consumer.

This exposes the live archive-free route from a certified `exists_semantics`
witness to semantic refutation of derivability through the Awodey-Butz
one-point bridge, without importing the topological layer into
`Completeness.lean` itself.
-/
theorem awodey_butz_completeness_of_exists_semantics
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
  exact awodey_butz_completeness_of_exists_semilocal_truth_counterexample
    (Base := Base) (Const := Const)
    (D.exists_semilocal_truth_counterexample_of_exists_semantics
      terminal branchClosed hSem)

/--
Expose the beta-specialized one-point completeness witness through the main
completeness-facing bridge module.

This keeps downstream consumers on the same archive-free bridge stack as the
generic completeness wrappers, while reusing the stronger beta-only packaging
already proved in `AwodeyButzSemantics`.
-/
theorem awodey_butz_completeness_bridge_of_exists_beta_truth_counterexample
    {antecedents : List (Formula Const Γ)}
    {σ : Ty Base}
    (t : Term Const Γ σ)
    (body : Formula Const (σ :: Γ))
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := M) Γ).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := M) antecedents γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := M) (instantiate t body) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) antecedents (.app (.lam body) t) := by
  exact awodey_butz_completeness_of_exists_beta_truth_counterexample
    (Base := Base) (Const := Const) t body hCounter

namespace CompletenessFrontier

/--
Frontier-level repackaging of the beta-specialized one-point counterexample
route.

This is the next completeness-facing wrapper above the raw bridge theorem:
consumers carrying a `CompletenessFrontier` can stay at that abstraction level
while using the proved beta-only path.
-/
theorem awodey_butz_completeness_of_exists_beta_truth_counterexample
    (F : CompletenessFrontier Const Γ)
    {σ : Ty Base}
    (t : Term Const Γ σ)
    (body : Formula Const (σ :: Γ))
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := M) Γ).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := M) F.antecedents γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := M) (instantiate t body) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents (.app (.lam body) t) := by
  exact awodey_butz_completeness_bridge_of_exists_beta_truth_counterexample
    (Base := Base) (Const := Const) t body hCounter

end CompletenessFrontier

namespace SoundLocalCountermodel

/--
Consume the current semantic frontier object directly through the verified
Awodey-Butz semilocal counterexample theorem.
-/
theorem awodey_butz_completeness
    {F : CompletenessFrontier Const Γ}
    (C : SoundLocalCountermodel (Base := Base) (Const := Const) F) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  let W := C.toLocalCountermodel.agreement
  exact awodey_butz_completeness_of_exists_semilocal_truth_counterexample
    (Base := Base) (Const := Const)
    ⟨C.model, W.env, W.global, W.antecedentTruth_eq_top, W.succedent_ne_top,
      C.supportsUniformRelativization⟩

end SoundLocalCountermodel

/--
Existential sound local countermodels can be consumed directly through the
Awodey-Butz semilocal counterexample theorem.
-/
theorem awodey_butz_completeness_of_exists_soundLocalCountermodel
    {F : CompletenessFrontier Const Γ}
    (hC :
      Nonempty (SoundLocalCountermodel (Base := Base) (Const := Const) F)) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  rcases hC with ⟨C⟩
  exact C.awodey_butz_completeness

namespace CertifiedHeadPriorityDerivation

namespace CandidateClosedHintikkaSemantics

/--
Candidate closed Hintikka semantics can be consumed directly by the Awodey-Butz
semilocal counterexample theorem.
-/
theorem awodey_butz_completeness
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact (S.toClosedSoundLocalCountermodel global hM).awodey_butz_completeness

end CandidateClosedHintikkaSemantics

end CertifiedHeadPriorityDerivation

namespace CertifiedHeadPriorityCompletion

namespace CandidateClosedHintikkaSemantics

/--
The certified completion-level candidate semantics wrapper inherits the same
direct Awodey-Butz counterexample route.
-/
theorem awodey_butz_completeness
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics C env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact
    CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics.awodey_butz_completeness
      (D := C.toCertifiedDerivation)
      (terminal := C.completion.terminal)
      (branchClosed := C.completion.branchClosed)
      (env := env)
      S global hM

end CandidateClosedHintikkaSemantics

end CertifiedHeadPriorityCompletion

namespace CertifiedCountermodelCandidate

/--
Candidate-level closed Hintikka semantics can be consumed directly by the
Awodey-Butz semilocal counterexample theorem.
-/
theorem CandidateClosedHintikkaSemantics.awodey_butz_completeness
    {C : CertifiedCountermodelCandidate Const Γ}
    {M : SemilocalModel Base Const}
    {env : SemilocalModel.Env M Γ}
    (S : C.CandidateClosedHintikkaSemantics env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents C.frontier.succedent := by
  exact (C.toClosedSoundLocalCountermodelOfSemantics env global S hM).awodey_butz_completeness

/--
Existential candidate-level semantics packages can also be consumed through the
Awodey-Butz semilocal counterexample route.
-/
theorem awodey_butz_completeness_of_exists_candidateClosedHintikkaSemantics
    (C : CertifiedCountermodelCandidate Const Γ)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M Γ),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty (C.CandidateClosedHintikkaSemantics env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents C.frontier.succedent := by
  rcases hSem with ⟨M, env, global, ⟨S⟩, hM⟩
  exact S.awodey_butz_completeness global hM

/--
Candidate-level forwarder for the beta-specialized one-point counterexample
route.

This lets downstream completeness consumers stay on the
`CertifiedCountermodelCandidate` interface while reusing the already-packaged
frontier-level beta theorem.
-/
theorem awodey_butz_completeness_of_exists_beta_truth_counterexample
    (C : CertifiedCountermodelCandidate Const Γ)
    {σ : Ty Base}
    (t : Term Const Γ σ)
    (body : Formula Const (σ :: Γ))
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := M) Γ).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := M) C.frontier.antecedents γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := M) (instantiate t body) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents (.app (.lam body) t) := by
  exact C.frontier.awodey_butz_completeness_of_exists_beta_truth_counterexample
    (Base := Base) (Const := Const) t body hCounter

/--
Closed candidate-level specialization of the beta-specialized one-point
counterexample route.

This is the next thin wrapper above the generic candidate-level theorem for the
closed-frontier completeness branch.
-/
theorem awodey_butz_completeness_of_exists_closed_beta_truth_counterexample
    (C : CertifiedCountermodelCandidate Const [])
    {σ : Ty Base}
    (t : Term Const [] σ)
    (body : Formula Const [σ])
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := M) []).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := M) C.frontier.antecedents γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := M) (instantiate t body) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents (.app (.lam body) t) := by
  exact C.awodey_butz_completeness_of_exists_beta_truth_counterexample
    (Base := Base) (Const := Const) t body hCounter

/--
Closed candidates whose succedent is literally a beta redex can consume the
beta-specialized point counterexample route directly at the frontier succedent.
-/
theorem awodey_butz_completeness_of_exists_closed_beta_succedent_counterexample
    (C : CertifiedCountermodelCandidate Const [])
    {σ : Ty Base}
    (t : Term Const [] σ)
    (body : Formula Const [σ])
    (hSucc : C.frontier.succedent = (.app (.lam body) t))
    (hCounter :
      ∃ (M : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := M) []).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := M) C.frontier.antecedents γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := M) (instantiate t body) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents C.frontier.succedent := by
  simpa [hSucc] using
    (C.awodey_butz_completeness_of_exists_closed_beta_truth_counterexample
      (Base := Base) (Const := Const) t body hCounter)

/--
Closed certified countermodel candidates can feed the Awodey-Butz semilocal
counterexample route directly from extensional closed-theory-set
non-provability.
-/
theorem awodey_butz_completeness_of_exists_semantics_of_not_closedTheorySetProvable
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
  rcases C.exists_closedLocalAgreementWitness_of_exists_semantics_of_not_closedTheorySetProvable
      hNot hSem with
    ⟨M, W, _, hM⟩
  exact awodey_butz_completeness_of_exists_semilocal_truth_counterexample
    (Base := Base) (Const := Const)
    ⟨M, W.env, W.global, W.antecedentTruth_eq_top, W.succedent_ne_top, hM⟩

/--
Closed prime separating extensions can also feed the Awodey-Butz semilocal
counterexample route directly, without unpacking the intermediate local
agreement witness by hand downstream.
-/
theorem awodey_butz_completeness_of_exists_semantics_of_primeSeparatingExtension
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
  rcases C.exists_closedLocalAgreementWitness_of_exists_semantics_of_primeSeparatingExtension
      hFU hSem with
    ⟨M, W, _, hM⟩
  exact awodey_butz_completeness_of_exists_semilocal_truth_counterexample
    (Base := Base) (Const := Const)
    ⟨M, W.env, W.global, W.antecedentTruth_eq_top, W.succedent_ne_top, hM⟩

end CertifiedCountermodelCandidate

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
