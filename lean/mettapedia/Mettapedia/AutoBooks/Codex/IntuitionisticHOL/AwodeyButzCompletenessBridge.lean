import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Completeness
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.CanonicalBridge
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSemantics
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzHeytingPointModelBridge

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

/--
Frontier-level consumer of the conjunction witness validity layer.

This closes the remaining connective gap at the frontier layer so higher
completeness-facing interfaces can reuse the full `and/or/imp` fragment
uniformly.
-/
theorem awodey_butz_and_witness_top_of_truthValidSequent
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
  exact HigherOrderPointHeytingGlobalModelBridge.and_formula_witness_top_of_truthValidSequent
    (M := M) φ ψ hvalid γ hΔ

/--
Frontier-level consumer of the connective witness validity layer.

This is the first completeness-facing theorem above the raw one-point bridge
that uses the generic `TruthValidSequent` connective witness consumer directly.
-/
theorem awodey_butz_or_witness_top_of_truthValidSequent
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
  refine
    HigherOrderPointHeytingGlobalModelBridge.connective_formula_witness_top_of_truthValidSequent
      (M := M) hvalid γ hΔ
      ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
          (M := M)).fiberJoin
        ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
              (M := M)).encodeProp
              (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                (M := M) φ γ)),
            ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
              (M := M)).encodeProp
              (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
                (M := M) ψ γ))), by simp⟩) ?_
  exact HigherOrderPointHeytingGlobalModelBridge.connective_formula_witness_truth_eq_truthEval
    (M := M) (Term.or φ ψ) γ
    ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
        (M := M)).fiberJoin
      ⟨(((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := M)).encodeProp
            (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
              (M := M) φ γ)),
          ((HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness
            (M := M)).encodeProp
            (HigherOrderPointHeytingGlobalModelBridge.pointFormulaValue
              (M := M) ψ γ))), by simp⟩)
    (HigherOrderPointHeytingGlobalModelBridge.concreteOnePointPropositionWitness_formula_or
      (M := M) φ ψ γ)

/--
Second frontier-level consumer of the connective witness validity layer.

This keeps the higher completeness-facing reuse from becoming `or`-specific by
mirroring it on implication at the same abstraction level.
-/
theorem awodey_butz_imp_witness_top_of_truthValidSequent
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
  exact HigherOrderPointHeytingGlobalModelBridge.imp_formula_witness_top_of_truthValidSequent
    (M := M) φ ψ hvalid γ hΔ

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

/--
Sound-local transitive consumer of the frontier beta-specialized point
counterexample route.
-/
theorem awodey_butz_completeness_of_exists_beta_truth_counterexample
    {F : CompletenessFrontier Const Γ}
    (C : SoundLocalCountermodel (Base := Base) (Const := Const) F)
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
    ¬ Derivable (Base := Base) (Const := Const)
      F.antecedents (.app (.lam body) t) := by
  let _ : SemilocalModel Base Const := C.model
  exact F.awodey_butz_completeness_of_exists_beta_truth_counterexample
    (Base := Base) (Const := Const) t body hCounter

/--
Sound-local transitive consumer of the frontier disjunction witness-validity
theorem.
-/
theorem awodey_butz_or_witness_top_of_truthValidSequent
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
  let _ : SemilocalModel Base Const := C.model
  exact F.awodey_butz_or_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

/--
Sound-local transitive consumer of the frontier conjunction witness-validity
theorem.
-/
theorem awodey_butz_and_witness_top_of_truthValidSequent
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
  let _ : SemilocalModel Base Const := C.model
  exact F.awodey_butz_and_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

/--
Sound-local transitive consumer of the frontier implication witness-validity
theorem.
-/
theorem awodey_butz_imp_witness_top_of_truthValidSequent
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
  let _ : SemilocalModel Base Const := C.model
  exact F.awodey_butz_imp_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

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

/--
Derivation-level transitive consumer of the sound-local beta-specialized point
counterexample route.
-/
theorem awodey_butz_completeness_of_exists_beta_truth_counterexample
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M)
    {σ : Ty Base}
    (t : Term Const Γ σ)
    (body : Formula Const (σ :: Γ))
    (hCounter :
      ∃ (G : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := G) Γ).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := G) F.antecedents γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := G) (instantiate t body) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const)
      F.antecedents (.app (.lam body) t) := by
  let CM := S.toClosedSoundLocalCountermodel global hM
  exact CM.awodey_butz_completeness_of_exists_beta_truth_counterexample
    (Base := Base) (Const := Const) t body hCounter

/--
Derivation-level transitive consumer of the sound-local conjunction
witness-validity theorem.
-/
theorem awodey_butz_and_witness_top_of_truthValidSequent
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env)
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
  let CM := S.toClosedSoundLocalCountermodel global hM
  exact CM.awodey_butz_and_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ G hvalid γ hΔ

/--
Derivation-level transitive consumer of the sound-local disjunction
witness-validity theorem.
-/
theorem awodey_butz_or_witness_top_of_truthValidSequent
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env)
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
  let CM := S.toClosedSoundLocalCountermodel global hM
  exact CM.awodey_butz_or_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ G hvalid γ hΔ

/--
Derivation-level transitive consumer of the sound-local implication
witness-validity theorem.
-/
theorem awodey_butz_imp_witness_top_of_truthValidSequent
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    {D : CertifiedHeadPriorityDerivation Const Γ F}
    {terminal : D.state.IsTerminal}
    {branchClosed : D.state.hintikka.BranchClosed}
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics D terminal branchClosed env)
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
  let CM := S.toClosedSoundLocalCountermodel global hM
  exact CM.awodey_butz_imp_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ G hvalid γ hΔ

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

/--
Certified completion-level transitive consumer of the derivation-level
beta-specialized point counterexample route.
-/
theorem awodey_butz_completeness_of_exists_beta_truth_counterexample
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics C env)
    (global : SemilocalModel.IsGlobalEnv M env)
    (hM : SemilocalModel.SupportsUniformRelativization M)
    {σ : Ty Base}
    (t : Term Const Γ σ)
    (body : Formula Const (σ :: Γ))
    (hCounter :
      ∃ (G : GlobalModel Base Const)
        (γ :
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace
            (M := G) Γ).Carrier),
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
            (M := G) F.antecedents γ = ⊤ ∧
          HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
            (M := G) (instantiate t body) γ ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const)
      F.antecedents (.app (.lam body) t) := by
  exact
    CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics.awodey_butz_completeness_of_exists_beta_truth_counterexample
      (D := C.toCertifiedDerivation)
      (terminal := C.completion.terminal)
      (branchClosed := C.completion.branchClosed)
      (env := env)
      S global hM t body hCounter

/--
Certified completion-level transitive consumer of the sound-local conjunction
witness-validity theorem.
-/
theorem awodey_butz_and_witness_top_of_truthValidSequent
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics C env)
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
  let CM := C.toClosedSoundLocalCountermodelOfSemantics env global S hM
  exact CM.awodey_butz_and_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ G hvalid γ hΔ

/--
Certified completion-level transitive consumer of the sound-local disjunction
witness-validity theorem.
-/
theorem awodey_butz_or_witness_top_of_truthValidSequent
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics C env)
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
  let CM := C.toClosedSoundLocalCountermodelOfSemantics env global S hM
  exact CM.awodey_butz_or_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ G hvalid γ hΔ

/--
Certified completion-level transitive consumer of the derivation-level
implication witness-validity theorem.
-/
theorem awodey_butz_imp_witness_top_of_truthValidSequent
    {F : CompletenessFrontier Const Γ}
    {M : SemilocalModel Base Const}
    (C : CertifiedHeadPriorityCompletion Const Γ F)
    {env : SemilocalModel.Env M Γ}
    (S : CandidateClosedHintikkaSemantics C env)
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
  exact
    CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics.awodey_butz_imp_witness_top_of_truthValidSequent
      (D := C.toCertifiedDerivation)
      (terminal := C.completion.terminal)
      (branchClosed := C.completion.branchClosed)
      (env := env)
      S global hM φ ψ G hvalid γ hΔ

end CandidateClosedHintikkaSemantics

/--
Certified completions can now feed the Awodey-Butz semilocal counterexample
consumer directly from raw closed-hull semantics, without dropping back to the
derivation layer.
-/
theorem awodey_butz_completeness_of_exists_semantics
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
  exact awodey_butz_completeness_of_exists_semilocal_truth_counterexample
    (Base := Base) (Const := Const)
    (C.exists_semilocal_truth_counterexample_of_exists_semantics hSem)

end CertifiedHeadPriorityCompletion

namespace SaturationSearchState.HeadPriorityCompletion

/--
The search-state completion layer now inherits the same direct Awodey-Butz
consumer for raw closed-hull semantics as the certified completion layer.
-/
theorem awodey_butz_completeness_of_exists_semantics
    {F : CompletenessFrontier Const Γ}
    (C : HeadPriorityCompletion F)
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
  exact awodey_butz_completeness_of_exists_semilocal_truth_counterexample
    (Base := Base) (Const := Const)
    (C.exists_semilocal_truth_counterexample_of_exists_semantics hInitial hCompat hSem)

end SaturationSearchState.HeadPriorityCompletion

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
Raw certified-candidate semantics can also be consumed directly by the
Awodey-Butz semilocal counterexample theorem, without first repackaging them as
classified candidate semantics.
-/
theorem awodey_butz_completeness_of_exists_semantics
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
  exact awodey_butz_completeness_of_exists_semilocal_truth_counterexample
    (Base := Base) (Const := Const)
    (C.exists_semilocal_truth_counterexample_of_exists_semantics hSem)

/--
Candidate-level transitive consumer of the frontier conjunction witness-validity
theorem.
-/
theorem awodey_butz_and_witness_top_of_truthValidSequent
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
  exact C.frontier.awodey_butz_and_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

/--
Candidate-level transitive consumer of the frontier disjunction witness-validity
theorem.
-/
theorem awodey_butz_or_witness_top_of_truthValidSequent
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
  exact C.frontier.awodey_butz_or_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

/--
Candidate-level transitive consumer of the frontier implication witness-validity
theorem.
-/
theorem awodey_butz_imp_witness_top_of_truthValidSequent
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
  exact C.frontier.awodey_butz_imp_witness_top_of_truthValidSequent
    (Base := Base) (Const := Const) φ ψ M hvalid γ hΔ

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
