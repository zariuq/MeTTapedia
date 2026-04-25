import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ParametricBridge
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermHenkinWorldBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL
open Mettapedia.Logic.PLNWorldModel
open ClosedTermCanonicalWorldModel
open scoped ENNReal

universe u v
universe w

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Const' : Ty Base → Type w}

namespace CompletenessFrontier

/-- A singleton world-model counterexample for a mapped frontier in an
extended signature already refutes native derivability of the original
frontier. This is the world-model/evidence analogue of the ordinary mapped
world-counterexample pullback. -/
theorem not_derivable_of_mapped_singletonWorldModelCounterexample
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {F : CompletenessFrontier Const []}
    (C :
      SingletonWorldModelCounterexample
        (Base := Base) (Const := Const') (F.mapConstants f)) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact CompletenessFrontier.not_derivable_of_mapped_world_counterexample
    (Base := Base) (Const := Const) (Const' := Const') (f := f)
    (F := F) (W := C.world)
    (fun φ hφ => C.antecedent_mem hφ)
    C.succedent_not_mem

/-- Fresh-constant implication data transports across the native empty
parameter signature. This lets a Henkin construction performed in the original
closed signature feed the parameterized countermodel endpoint. -/
def emptyParamTheorySet_constantHenkinImplicationData
    {U : ClosedTheorySet Const}
    (hImp : ClosedTheorySet.ConstantHenkinImplicationData (Const := Const) U) :
    ClosedTheorySet.ConstantHenkinImplicationData
      (Const := ParamConst (Base := Base) Const [])
      (emptyParamTheorySet (Base := Base) (Const := Const) U) where
  exConst := fun {σ} φ =>
    Sum.inl (hImp.exConst (σ := σ)
      (Mettapedia.Logic.HOL.mapConst
        (emptyParamRetraction (Base := Base) (Const := Const)) φ))
  allConst := fun {σ} φ =>
    Sum.inl (hImp.allConst (σ := σ)
      (Mettapedia.Logic.HOL.mapConst
        (emptyParamRetraction (Base := Base) (Const := Const)) φ))
  ex_imp := by
    intro σ φ
    let φ₀ : Formula Const [σ] :=
      Mettapedia.Logic.HOL.mapConst
        (emptyParamRetraction (Base := Base) (Const := Const)) φ
    change
      Mettapedia.Logic.HOL.mapClosedFormula
        (emptyParamRetraction (Base := Base) (Const := Const))
        ((.imp (.ex φ : ClosedFormula (ParamConst (Base := Base) Const []))
          (instantiate (Base := Base)
            (.const (Sum.inl (hImp.exConst (σ := σ) φ₀)))
            φ)) : ClosedFormula (ParamConst (Base := Base) Const [])) ∈ U
    simpa [φ₀, Mettapedia.Logic.HOL.mapClosedFormula,
      Mettapedia.Logic.HOL.mapConst,
      emptyParamRetraction, paramEmbedding] using hImp.ex_imp φ₀
  all_imp := by
    intro σ φ
    let φ₀ : Formula Const [σ] :=
      Mettapedia.Logic.HOL.mapConst
        (emptyParamRetraction (Base := Base) (Const := Const)) φ
    change
      Mettapedia.Logic.HOL.mapClosedFormula
        (emptyParamRetraction (Base := Base) (Const := Const))
        ((.imp
          (instantiate (Base := Base)
            (.const (Sum.inl (hImp.allConst (σ := σ) φ₀)))
            φ)
          (.all φ : ClosedFormula (ParamConst (Base := Base) Const []))) :
            ClosedFormula (ParamConst (Base := Base) Const [])) ∈ U
    simpa [φ₀, Mettapedia.Logic.HOL.mapClosedFormula,
      Mettapedia.Logic.HOL.mapConst,
      emptyParamRetraction, paramEmbedding] using hImp.all_imp φ₀

end CompletenessFrontier

namespace CertifiedHeadPriorityCompletion

/-- Parameterized prime-extension data with the fresh-constant Henkin
implication scheme, rather than already-extracted closed-term witness fields.
This is the natural production target for a Henkin/Lindenbaum construction over
the parameterized signature. -/
structure CandidateParamPrimeImplicationExtension
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F) : Type (max u v) where
  Gamma : Ctx Base
  carrier : ClosedTheorySet (ParamConst (Base := Base) Const Gamma)
  extension :
    CompletenessFrontier.PrimeSeparatingExtension
      (Const := ParamConst (Base := Base) Const Gamma)
      (F.toParam Gamma)
      carrier
  implications :
    ClosedTheorySet.ConstantHenkinImplicationData
      (Const := ParamConst (Base := Base) Const Gamma)
      carrier
  true_mem :
    ∀ {φ : ClosedFormula Const},
      (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
        Mettapedia.Logic.HOL.mapClosedFormula
          (CompletenessFrontier.paramEmbedding
            (Base := Base) (Const := Const) Gamma) φ ∈ carrier
  false_not_mem :
    ∀ {φ : ClosedFormula Const},
      (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
        Mettapedia.Logic.HOL.mapClosedFormula
          (CompletenessFrontier.paramEmbedding
            (Base := Base) (Const := Const) Gamma) φ ∉ carrier

/-- Raw search-facing data package for the implication-style parameterized
prime-extension route. It lives in `Type` because the Henkin implication scheme
contains chosen fresh constants, while several agreement fields are
proposition-valued invariants. -/
structure PrimeImplicationExtensionAgreement
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F) : Type (max u v) where
  Gamma : Ctx Base
  carrier : ClosedTheorySet (ParamConst (Base := Base) Const Gamma)
  extension :
    CompletenessFrontier.PrimeSeparatingExtension
      (Const := ParamConst (Base := Base) Const Gamma)
      (F.toParam Gamma)
      carrier
  implications :
    ClosedTheorySet.ConstantHenkinImplicationData
      (Const := ParamConst (Base := Base) Const Gamma)
      carrier
  true_mem :
    ∀ {φ : ClosedFormula Const},
      (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
        Mettapedia.Logic.HOL.mapClosedFormula
          (CompletenessFrontier.paramEmbedding
            (Base := Base) (Const := Const) Gamma) φ ∈ carrier
  false_not_mem :
    ∀ {φ : ClosedFormula Const},
      (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
        Mettapedia.Logic.HOL.mapClosedFormula
          (CompletenessFrontier.paramEmbedding
            (Base := Base) (Const := Const) Gamma) φ ∉ carrier

namespace CandidateParamPrimeImplicationExtension

/-- Extract constant Henkin witness data from the implication scheme in the
deductively closed carrier. -/
def constantHenkinWitnessData
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeImplicationExtension (Base := Base) (Const := Const) C) :
    ClosedTheorySet.ConstantHenkinWitnessData
      (Const := ParamConst (Base := Base) Const W.Gamma)
      W.carrier :=
  W.implications.toConstantHenkinWitnessData W.extension.closed

/-- The implication-style candidate has the ordinary closed-term Henkin witness
data consumed by the existing parameterized prime-extension endpoint. -/
def henkinWitnessData
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeImplicationExtension (Base := Base) (Const := Const) C) :
    ClosedTheorySet.HenkinWitnessData
      (Const := ParamConst (Base := Base) Const W.Gamma)
      W.carrier :=
  W.constantHenkinWitnessData.toHenkinWitnessData

/-- View the implication-style candidate as a prime constant-Henkin separating
extension for the parameterized frontier. -/
def toPrimeConstantHenkinSeparatingExtension
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeImplicationExtension (Base := Base) (Const := Const) C) :
    CompletenessFrontier.PrimeConstantHenkinSeparatingExtension
      (Base := Base)
      (Const := ParamConst (Base := Base) Const W.Gamma)
      (F.toParam W.Gamma) :=
  W.extension.toPrimeConstantHenkinSeparatingExtensionOfImplications W.implications

/-- Forget implication-style Henkin data into the existing production-side
candidate prime extension. -/
def toCandidateParamPrimeExtension
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeImplicationExtension (Base := Base) (Const := Const) C) :
    CandidateParamPrimeExtension (Base := Base) (Const := Const) C where
  Gamma := W.Gamma
  carrier := W.carrier
  extension := W.extension
  exists_witness := W.henkinWitnessData.exists_witness
  all_counterexample := W.henkinWitnessData.all_counterexample
  true_mem := W.true_mem
  false_not_mem := W.false_not_mem

/-- An implication-style candidate therefore yields the parameterized singleton
world-model counterexample endpoint. -/
def toParamSingletonWorldModelCounterexample
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeImplicationExtension (Base := Base) (Const := Const) C) :
    CompletenessFrontier.SingletonWorldModelCounterexample
      (Base := Base)
      (Const := ParamConst (Base := Base) Const W.Gamma)
      (F.toParam W.Gamma) :=
  W.toPrimeConstantHenkinSeparatingExtension.toSingletonWorldModelCounterexample

/-- An implication-style candidate refutes singleton-strength consequence for
the parameterized frontier. -/
theorem not_singletonStrengthConsequence_toParam
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeImplicationExtension (Base := Base) (Const := Const) C) :
    ¬ CompletenessFrontier.SingletonStrengthConsequence
      (Base := Base)
      (Const := ParamConst (Base := Base) Const W.Gamma)
      (F.toParam W.Gamma) :=
  W.toPrimeConstantHenkinSeparatingExtension.not_singletonStrengthConsequence

/-- Pull the parameterized singleton countermodel back to refute native
derivability of the original frontier. -/
theorem not_derivable_via_paramSingletonWorldModelCounterexample
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeImplicationExtension (Base := Base) (Const := Const) C) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  CompletenessFrontier.not_derivable_of_mapped_singletonWorldModelCounterexample
    (Base := Base) (Const := Const)
    (Const' := ParamConst (Base := Base) Const W.Gamma)
    (CompletenessFrontier.paramEmbedding (Base := Base) (Const := Const) W.Gamma)
    W.toParamSingletonWorldModelCounterexample

end CandidateParamPrimeImplicationExtension

end CertifiedHeadPriorityCompletion

namespace CertifiedHeadPriorityCompletion.CandidateParamPrimeExtension

/-- The raw quantifier fields of a certified parameterized prime extension are
exactly Henkin witness data for its carrier. -/
theorem henkinWitnessData
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeExtension (Base := Base) (Const := Const) C) :
    ClosedTheorySet.HenkinWitnessData
      (Const := ParamConst (Base := Base) Const W.Gamma)
      W.carrier where
  exists_witness := W.exists_witness
  all_counterexample := W.all_counterexample

/-- A certified parameterized prime extension is a prime Henkin separating
extension for the parameterized frontier. -/
def toPrimeHenkinSeparatingExtension
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeExtension (Base := Base) (Const := Const) C) :
    CompletenessFrontier.PrimeHenkinSeparatingExtension
      (Base := Base)
      (Const := ParamConst (Base := Base) Const W.Gamma)
      (F.toParam W.Gamma) where
  carrier := W.carrier
  extension := W.extension
  henkin := W.henkinWitnessData

/-- The parameterized canonical world carried by a certified parameterized
prime extension, using the shared prime-Henkin package. -/
def toParamWorld
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeExtension (Base := Base) (Const := Const) C) :
    ClosedTheorySet.World (ParamConst (Base := Base) Const W.Gamma) :=
  W.toPrimeHenkinSeparatingExtension.toWorld

@[simp]
theorem toParamWorld_carrier
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeExtension (Base := Base) (Const := Const) C) :
    W.toParamWorld.carrier = W.carrier :=
  rfl

/-- The parameterized singleton world-model counterexample generated by a
certified parameterized prime extension. -/
def toParamSingletonWorldModelCounterexample
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeExtension (Base := Base) (Const := Const) C) :
    CompletenessFrontier.SingletonWorldModelCounterexample
      (Base := Base)
      (Const := ParamConst (Base := Base) Const W.Gamma)
      (F.toParam W.Gamma) :=
  W.toPrimeHenkinSeparatingExtension.toSingletonWorldModelCounterexample

/-- A certified parameterized prime extension refutes singleton-strength
consequence for the parameterized frontier. -/
theorem not_singletonStrengthConsequence_toParam
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeExtension (Base := Base) (Const := Const) C) :
    ¬ CompletenessFrontier.SingletonStrengthConsequence
      (Base := Base)
      (Const := ParamConst (Base := Base) Const W.Gamma)
      (F.toParam W.Gamma) :=
  W.toPrimeHenkinSeparatingExtension.not_singletonStrengthConsequence

/-- The parameterized singleton world-model counterexample carried by a
certified parameterized prime extension refutes derivability of the original
frontier after pulling back along the parameter embedding. -/
theorem not_derivable_via_paramSingletonWorldModelCounterexample
    {F : CompletenessFrontier Const []}
    {C : CertifiedHeadPriorityCompletion Const [] F}
    (W : CandidateParamPrimeExtension (Base := Base) (Const := Const) C) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  CompletenessFrontier.not_derivable_of_mapped_singletonWorldModelCounterexample
    (Base := Base) (Const := Const)
    (Const' := ParamConst (Base := Base) Const W.Gamma)
    (CompletenessFrontier.paramEmbedding (Base := Base) (Const := Const) W.Gamma)
    W.toParamSingletonWorldModelCounterexample

end CertifiedHeadPriorityCompletion.CandidateParamPrimeExtension

namespace CertifiedHeadPriorityCompletion

/-- Existence of a certified parameterized prime extension produces an explicit
parameter context whose parameterized frontier has a singleton world-model
counterexample. -/
theorem exists_paramSingletonCountermodel_of_exists_candidateParamPrimeExtension
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeExtension (Base := Base) (Const := Const) C)) :
    Nonempty (Σ Gamma : Ctx Base,
      CompletenessFrontier.SingletonWorldModelCounterexample
        (Base := Base)
        (Const := ParamConst (Base := Base) Const Gamma)
        (F.toParam Gamma)) := by
  rcases hW with ⟨W⟩
  exact ⟨⟨W.Gamma, W.toParamSingletonWorldModelCounterexample⟩⟩

/-- Existence of a certified parameterized prime extension produces an explicit
parameter context where singleton-strength consequence fails. -/
theorem exists_not_singletonStrengthConsequence_toParam_of_exists_candidateParamPrimeExtension
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeExtension (Base := Base) (Const := Const) C)) :
    ∃ Gamma : Ctx Base,
      ¬ CompletenessFrontier.SingletonStrengthConsequence
        (Base := Base)
        (Const := ParamConst (Base := Base) Const Gamma)
        (F.toParam Gamma) := by
  rcases hW with ⟨W⟩
  exact ⟨W.Gamma, W.not_singletonStrengthConsequence_toParam⟩

/-- Existence of a parameterized singleton world-model counterexample for the
parameterized frontier refutes native derivability of the original frontier. -/
theorem not_derivable_of_exists_paramSingletonCountermodel
    {F : CompletenessFrontier Const []}
    (_C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty (Σ Gamma : Ctx Base,
        CompletenessFrontier.SingletonWorldModelCounterexample
          (Base := Base)
          (Const := ParamConst (Base := Base) Const Gamma)
          (F.toParam Gamma))) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  rcases hW with ⟨⟨Gamma, Cwm⟩⟩
  exact CompletenessFrontier.not_derivable_of_mapped_singletonWorldModelCounterexample
    (Base := Base) (Const := Const)
    (Const' := ParamConst (Base := Base) Const Gamma)
    (CompletenessFrontier.paramEmbedding (Base := Base) (Const := Const) Gamma)
    Cwm

/-- Existence of a certified parameterized prime extension refutes native
derivability via its singleton world-model counterexample endpoint. -/
theorem not_derivable_via_paramSingletonCountermodel_of_exists_candidateParamPrimeExtension
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeExtension (Base := Base) (Const := Const) C)) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  C.not_derivable_of_exists_paramSingletonCountermodel
    (C.exists_paramSingletonCountermodel_of_exists_candidateParamPrimeExtension hW)

/-- Raw parameterized prime-extension data with fresh-constant implication
agreement can be consumed into the implication-style production target. -/
theorem exists_candidateParamPrimeImplicationExtension_of_exists_primeImplicationExtensionAgreement
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty
        (PrimeImplicationExtensionAgreement
          (Base := Base) (Const := Const) C)) :
    Nonempty
      (CandidateParamPrimeImplicationExtension (Base := Base) (Const := Const) C) := by
  rcases hW with ⟨W⟩
  exact ⟨{
    Gamma := W.Gamma
    carrier := W.carrier
    extension := W.extension
    implications := W.implications
    true_mem := W.true_mem
    false_not_mem := W.false_not_mem }⟩

/-- Existence of an implication-style parameterized prime extension produces
the existing closed-term-witness candidate package. -/
theorem exists_candidateParamPrimeExtension_of_exists_candidateParamPrimeImplicationExtension
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeImplicationExtension (Base := Base) (Const := Const) C)) :
    Nonempty
      (CandidateParamPrimeExtension (Base := Base) (Const := Const) C) := by
  rcases hW with ⟨W⟩
  exact ⟨W.toCandidateParamPrimeExtension⟩

/-- Existence of an implication-style parameterized prime extension produces a
parameterized singleton world-model counterexample. -/
theorem exists_paramSingletonCountermodel_of_exists_candidateParamPrimeImplicationExtension
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeImplicationExtension (Base := Base) (Const := Const) C)) :
    Nonempty (Σ Gamma : Ctx Base,
      CompletenessFrontier.SingletonWorldModelCounterexample
        (Base := Base)
        (Const := ParamConst (Base := Base) Const Gamma)
        (F.toParam Gamma)) := by
  rcases hW with ⟨W⟩
  exact ⟨⟨W.Gamma, W.toParamSingletonWorldModelCounterexample⟩⟩

/-- Existence of an implication-style parameterized prime extension refutes
native derivability through the singleton world-model endpoint. -/
theorem not_derivable_of_exists_candidateParamPrimeImplicationExtension
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeImplicationExtension (Base := Base) (Const := Const) C)) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  rcases hW with ⟨W⟩
  exact W.not_derivable_via_paramSingletonWorldModelCounterexample

/-- Raw parameterized prime-extension implication agreement refutes native
derivability through the implication-style candidate package. -/
theorem not_derivable_of_exists_primeImplicationExtensionAgreement
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hW :
      Nonempty
        (PrimeImplicationExtensionAgreement
          (Base := Base) (Const := Const) C)) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  C.not_derivable_of_exists_candidateParamPrimeImplicationExtension
    (C.exists_candidateParamPrimeImplicationExtension_of_exists_primeImplicationExtensionAgreement hW)

end CertifiedHeadPriorityCompletion

namespace CertifiedCountermodelCandidate

/-- Candidate-level alias for implication-style certified production-side
parameterized prime extensions. -/
abbrev CandidateParamPrimeImplicationExtension
    (C : CertifiedCountermodelCandidate Const []) :=
  CertifiedHeadPriorityCompletion.CandidateParamPrimeImplicationExtension
    (C := C.toCertifiedCompletion)

/-- Candidate-level alias for the raw implication-style prime-extension
agreement package. -/
abbrev PrimeImplicationExtensionAgreement
    (C : CertifiedCountermodelCandidate Const []) :=
  CertifiedHeadPriorityCompletion.PrimeImplicationExtensionAgreement
    (C := C.toCertifiedCompletion)

/-- Candidate-level existential singleton world-model endpoint for the
parameterized prime-extension route. -/
theorem exists_paramSingletonCountermodel_of_exists_candidateParamPrimeExtension
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty (CandidateParamPrimeExtension (Base := Base) (Const := Const) C)) :
    Nonempty (Σ Gamma : Ctx Base,
      CompletenessFrontier.SingletonWorldModelCounterexample
        (Base := Base)
        (Const := ParamConst (Base := Base) Const Gamma)
        (C.frontier.toParam Gamma)) := by
  rcases hW with ⟨W⟩
  exact ⟨⟨W.Gamma, W.toParamSingletonWorldModelCounterexample⟩⟩

/-- Candidate-level existential singleton-strength failure for the
parameterized prime-extension route. -/
theorem exists_not_singletonStrengthConsequence_toParam_of_exists_candidateParamPrimeExtension
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty (CandidateParamPrimeExtension (Base := Base) (Const := Const) C)) :
    ∃ Gamma : Ctx Base,
      ¬ CompletenessFrontier.SingletonStrengthConsequence
        (Base := Base)
        (Const := ParamConst (Base := Base) Const Gamma)
        (C.frontier.toParam Gamma) := by
  rcases hW with ⟨W⟩
  exact ⟨W.Gamma, W.not_singletonStrengthConsequence_toParam⟩

/-- Candidate-level singleton world-model pullback from a parameterized
countermodel to original-frontier non-derivability. -/
theorem not_derivable_of_exists_paramSingletonCountermodel
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty (Σ Gamma : Ctx Base,
        CompletenessFrontier.SingletonWorldModelCounterexample
          (Base := Base)
          (Const := ParamConst (Base := Base) Const Gamma)
          (C.frontier.toParam Gamma))) :
    ¬ Derivable (Base := Base) (Const := Const)
        C.frontier.antecedents C.frontier.succedent := by
  rcases hW with ⟨⟨Gamma, Cwm⟩⟩
  exact CompletenessFrontier.not_derivable_of_mapped_singletonWorldModelCounterexample
    (Base := Base) (Const := Const)
    (Const' := ParamConst (Base := Base) Const Gamma)
    (CompletenessFrontier.paramEmbedding (Base := Base) (Const := Const) Gamma)
    Cwm

/-- Candidate-level certified parameterized prime extensions refute native
derivability via the singleton world-model endpoint. -/
theorem not_derivable_via_paramSingletonCountermodel_of_exists_candidateParamPrimeExtension
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty (CandidateParamPrimeExtension (Base := Base) (Const := Const) C)) :
    ¬ Derivable (Base := Base) (Const := Const)
        C.frontier.antecedents C.frontier.succedent :=
  C.not_derivable_of_exists_paramSingletonCountermodel
    (C.exists_paramSingletonCountermodel_of_exists_candidateParamPrimeExtension hW)

/-- Candidate-level implication-style parameterized prime extensions produce
the existing closed-term-witness candidate package. -/
theorem exists_candidateParamPrimeExtension_of_exists_candidateParamPrimeImplicationExtension
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty
        (CandidateParamPrimeImplicationExtension
          (Base := Base) (Const := Const) C)) :
    Nonempty (CandidateParamPrimeExtension (Base := Base) (Const := Const) C) := by
  simpa [CertifiedCountermodelCandidate.CandidateParamPrimeImplicationExtension,
    CertifiedCountermodelCandidate.CandidateParamPrimeExtension] using
    (CertifiedHeadPriorityCompletion.exists_candidateParamPrimeExtension_of_exists_candidateParamPrimeImplicationExtension
      (Base := Base) (Const := Const) (C := C.toCertifiedCompletion) hW)

/-- Candidate-level implication-style parameterized prime extensions produce
parameterized singleton world-model counterexamples. -/
theorem exists_paramSingletonCountermodel_of_exists_candidateParamPrimeImplicationExtension
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty
        (CandidateParamPrimeImplicationExtension
          (Base := Base) (Const := Const) C)) :
    Nonempty (Σ Gamma : Ctx Base,
      CompletenessFrontier.SingletonWorldModelCounterexample
        (Base := Base)
        (Const := ParamConst (Base := Base) Const Gamma)
        (C.frontier.toParam Gamma)) :=
  CertifiedHeadPriorityCompletion.exists_paramSingletonCountermodel_of_exists_candidateParamPrimeImplicationExtension
    (Base := Base) (Const := Const) (C := C.toCertifiedCompletion) hW

/-- Candidate-level implication-style parameterized prime extensions refute
native derivability through the singleton world-model endpoint. -/
theorem not_derivable_of_exists_candidateParamPrimeImplicationExtension
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty
        (CandidateParamPrimeImplicationExtension
          (Base := Base) (Const := Const) C)) :
    ¬ Derivable (Base := Base) (Const := Const)
        C.frontier.antecedents C.frontier.succedent :=
  CertifiedHeadPriorityCompletion.not_derivable_of_exists_candidateParamPrimeImplicationExtension
    (Base := Base) (Const := Const) (C := C.toCertifiedCompletion) hW

/-- Candidate-level raw parameterized prime-extension implication agreement can
be consumed into the implication-style candidate package. -/
theorem exists_candidateParamPrimeImplicationExtension_of_exists_primeImplicationExtensionAgreement
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty
        (PrimeImplicationExtensionAgreement
          (Base := Base) (Const := Const) C)) :
    Nonempty
      (CandidateParamPrimeImplicationExtension (Base := Base) (Const := Const) C) := by
  simpa [CertifiedCountermodelCandidate.CandidateParamPrimeImplicationExtension,
    CertifiedCountermodelCandidate.PrimeImplicationExtensionAgreement,
    CertifiedCountermodelCandidate.toCertifiedCompletion] using
    (CertifiedHeadPriorityCompletion.exists_candidateParamPrimeImplicationExtension_of_exists_primeImplicationExtensionAgreement
      (Base := Base) (Const := Const) (C := C.toCertifiedCompletion) hW)

/-- Candidate-level raw parameterized prime-extension implication agreement
refutes native derivability through the singleton world-model endpoint. -/
theorem not_derivable_of_exists_primeImplicationExtensionAgreement
    (C : CertifiedCountermodelCandidate Const [])
    (hW :
      Nonempty
        (PrimeImplicationExtensionAgreement
          (Base := Base) (Const := Const) C)) :
    ¬ Derivable (Base := Base) (Const := Const)
        C.frontier.antecedents C.frontier.succedent :=
  C.not_derivable_of_exists_candidateParamPrimeImplicationExtension
    (C.exists_candidateParamPrimeImplicationExtension_of_exists_primeImplicationExtensionAgreement hW)

end CertifiedCountermodelCandidate

namespace SaturationSearchState.HeadPriorityCompletion

/-- Head-priority completions can expose the implication-style parameterized
prime-extension agreement directly from an original prime separating extension
plus fresh-constant implication data. -/
def toPrimeImplicationExtensionAgreementOfPrimeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hImp : ClosedTheorySet.ConstantHenkinImplicationData (Const := Const) U)
    (hTrue :
      ∀ {φ : ClosedFormula Const},
        (Sign.trueE, φ) ∈ C.state.hintikka.formulas → φ ∈ U)
    (hFalse :
      ∀ {φ : ClosedFormula Const},
        (Sign.falseE, φ) ∈ C.state.hintikka.formulas → φ ∉ U) :
    CertifiedHeadPriorityCompletion.PrimeImplicationExtensionAgreement
      (Base := Base)
      (Const := Const)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) where
  Gamma := []
  carrier := CompletenessFrontier.emptyParamTheorySet (Base := Base) (Const := Const) U
  extension :=
    CompletenessFrontier.toEmptyParamPrimeSeparatingExtension
      (Base := Base) (Const := Const) (F := F) hFU
  implications :=
    CompletenessFrontier.emptyParamTheorySet_constantHenkinImplicationData
      (Base := Base) (Const := Const) hImp
  true_mem := by
    intro φ hφ
    have hφ' : φ ∈ U := HintikkaSet.true_mem_close_of_true_mem
      (H := C.state.hintikka)
      (P := fun ψ : ClosedFormula Const => ψ ∈ U)
      (CompletenessFrontier.top_mem_of_primeSeparatingExtension
        (Base := Base) (Const := Const) (F := F) hFU)
      (fun {ψ} hψ => hTrue hψ)
      (by
        simpa [SaturationSearchState.HeadPriorityCompletion.toCertifiedOfPrimeSeparatingExtension,
          SaturationSearchState.HeadPriorityCompletion.toCertified,
          CertifiedHeadPriorityCompletion.state,
          CertifiedHeadPriorityCompletion.hintikka,
          CertifiedHeadPriorityCompletion.closedHintikka] using hφ)
    change
      Mettapedia.Logic.HOL.mapClosedFormula
        (CompletenessFrontier.emptyParamRetraction (Base := Base) (Const := Const))
        (Mettapedia.Logic.HOL.mapClosedFormula
          (CompletenessFrontier.paramEmbedding (Base := Base) (Const := Const) [])
          φ) ∈ U
    simpa [Mettapedia.Logic.HOL.mapClosedFormula,
      CompletenessFrontier.emptyParamRetraction,
      CompletenessFrontier.paramEmbedding] using hφ'
  false_not_mem := by
    intro φ hφ
    have hφ' : φ ∉ U := HintikkaSet.false_mem_close_of_false_mem
      (H := C.state.hintikka)
      (P := fun ψ : ClosedFormula Const => ψ ∉ U)
      (CompletenessFrontier.bot_not_mem_of_primeSeparatingExtension
        (Base := Base) (Const := Const) (F := F) hFU)
      (fun {ψ} hψ => hFalse hψ)
      (by
        simpa [SaturationSearchState.HeadPriorityCompletion.toCertifiedOfPrimeSeparatingExtension,
          SaturationSearchState.HeadPriorityCompletion.toCertified,
          CertifiedHeadPriorityCompletion.state,
          CertifiedHeadPriorityCompletion.hintikka,
          CertifiedHeadPriorityCompletion.closedHintikka] using hφ)
    change
      Mettapedia.Logic.HOL.mapClosedFormula
        (CompletenessFrontier.emptyParamRetraction (Base := Base) (Const := Const))
        (Mettapedia.Logic.HOL.mapClosedFormula
          (CompletenessFrontier.paramEmbedding (Base := Base) (Const := Const) [])
          φ) ∉ U
    simpa [Mettapedia.Logic.HOL.mapClosedFormula,
      CompletenessFrontier.emptyParamRetraction,
      CompletenessFrontier.paramEmbedding] using hφ'

/-- The same head-priority handoff as a packaged implication-style candidate. -/
def toCandidateParamPrimeImplicationExtensionOfPrimeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hImp : ClosedTheorySet.ConstantHenkinImplicationData (Const := Const) U)
    (hTrue :
      ∀ {φ : ClosedFormula Const},
        (Sign.trueE, φ) ∈ C.state.hintikka.formulas → φ ∈ U)
    (hFalse :
      ∀ {φ : ClosedFormula Const},
        (Sign.falseE, φ) ∈ C.state.hintikka.formulas → φ ∉ U) :
    CertifiedHeadPriorityCompletion.CandidateParamPrimeImplicationExtension
      (Base := Base)
      (Const := Const)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) where
  Gamma := []
  carrier := CompletenessFrontier.emptyParamTheorySet (Base := Base) (Const := Const) U
  extension :=
    CompletenessFrontier.toEmptyParamPrimeSeparatingExtension
      (Base := Base) (Const := Const) (F := F) hFU
  implications :=
    CompletenessFrontier.emptyParamTheorySet_constantHenkinImplicationData
      (Base := Base) (Const := Const) hImp
  true_mem :=
    (C.toPrimeImplicationExtensionAgreementOfPrimeSeparatingExtension
      (hCompat := hCompat) (hFU := hFU) (hImp := hImp)
      (hTrue := hTrue) (hFalse := hFalse)).true_mem
  false_not_mem :=
    (C.toPrimeImplicationExtensionAgreementOfPrimeSeparatingExtension
      (hCompat := hCompat) (hFU := hFU) (hImp := hImp)
      (hTrue := hTrue) (hFalse := hFalse)).false_not_mem

/-- Head-priority completions can consume the Henkin implication theory-set
containment obligation directly, instead of requiring callers to first package
it as `ConstantHenkinImplicationData`. -/
def toPrimeImplicationExtensionAgreementOfPrimeSeparatingExtensionContainedImplications
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hContains :
      ∀ {θ : ClosedFormula Const},
        θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := Base) (Const := Const) exConst allConst →
          θ ∈ U)
    (hTrue :
      ∀ {φ : ClosedFormula Const},
        (Sign.trueE, φ) ∈ C.state.hintikka.formulas → φ ∈ U)
    (hFalse :
      ∀ {φ : ClosedFormula Const},
        (Sign.falseE, φ) ∈ C.state.hintikka.formulas → φ ∉ U) :
    CertifiedHeadPriorityCompletion.PrimeImplicationExtensionAgreement
      (Base := Base)
      (Const := Const)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) :=
  C.toPrimeImplicationExtensionAgreementOfPrimeSeparatingExtension
    (hCompat := hCompat)
    (hFU := hFU)
    (hImp :=
      ClosedTheorySet.constantHenkinImplicationDataOfContainsTheorySet
        (Base := Base) (Const := Const) exConst allConst hContains)
    (hTrue := hTrue)
    (hFalse := hFalse)

/-- The same theory-set containment handoff as a packaged implication-style
candidate. -/
def toCandidateParamPrimeImplicationExtensionOfPrimeSeparatingExtensionContainedImplications
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hContains :
      ∀ {θ : ClosedFormula Const},
        θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := Base) (Const := Const) exConst allConst →
          θ ∈ U)
    (hTrue :
      ∀ {φ : ClosedFormula Const},
        (Sign.trueE, φ) ∈ C.state.hintikka.formulas → φ ∈ U)
    (hFalse :
      ∀ {φ : ClosedFormula Const},
        (Sign.falseE, φ) ∈ C.state.hintikka.formulas → φ ∉ U) :
    CertifiedHeadPriorityCompletion.CandidateParamPrimeImplicationExtension
      (Base := Base)
      (Const := Const)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) :=
  C.toCandidateParamPrimeImplicationExtensionOfPrimeSeparatingExtension
    (hCompat := hCompat)
    (hFU := hFU)
    (hImp :=
      ClosedTheorySet.constantHenkinImplicationDataOfContainsTheorySet
        (Base := Base) (Const := Const) exConst allConst hContains)
    (hTrue := hTrue)
    (hFalse := hFalse)

/-- Guided head-priority derivations can replace explicit staged-formula
agreement hypotheses for the implication-style handoff. -/
def toCandidateParamPrimeImplicationExtensionOfPrimeSeparatingExtensionOfGuidedByTheorySet
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hGuide :
      SaturationSearchState.HeadPrioritySearchDerivation.GuidedByTheorySet
        (Const := Const) U C.derivation)
    (hImp : ClosedTheorySet.ConstantHenkinImplicationData (Const := Const) U) :
    CertifiedHeadPriorityCompletion.CandidateParamPrimeImplicationExtension
      (Base := Base)
      (Const := Const)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) :=
  C.toCandidateParamPrimeImplicationExtensionOfPrimeSeparatingExtension
    (hCompat := hCompat)
    (hFU := hFU)
    (hImp := hImp)
    (hTrue := fun hφ =>
      SaturationSearchState.HeadPrioritySearchDerivation.true_mem_of_guidedByTheorySet
        (Const := Const) C.derivation hFU hGuide hφ)
    (hFalse := fun hφ =>
      SaturationSearchState.HeadPrioritySearchDerivation.false_mem_of_guidedByTheorySet
        (Const := Const) C.derivation hFU hGuide hφ)

/-- Guided head-priority derivations can also consume containment of the
generated Henkin implication theory-set directly. -/
def toCandidateParamPrimeImplicationExtensionOfPrimeSeparatingExtensionContainedImplicationsOfGuidedByTheorySet
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hGuide :
      SaturationSearchState.HeadPrioritySearchDerivation.GuidedByTheorySet
        (Const := Const) U C.derivation)
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hContains :
      ∀ {θ : ClosedFormula Const},
        θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := Base) (Const := Const) exConst allConst →
          θ ∈ U) :
    CertifiedHeadPriorityCompletion.CandidateParamPrimeImplicationExtension
      (Base := Base)
      (Const := Const)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) :=
  C.toCandidateParamPrimeImplicationExtensionOfPrimeSeparatingExtensionContainedImplications
    (hCompat := hCompat)
    (hFU := hFU)
    (exConst := exConst)
    (allConst := allConst)
    (hContains := hContains)
    (hTrue := fun hφ =>
      SaturationSearchState.HeadPrioritySearchDerivation.true_mem_of_guidedByTheorySet
        (Const := Const) C.derivation hFU hGuide hφ)
    (hFalse := fun hφ =>
      SaturationSearchState.HeadPrioritySearchDerivation.false_mem_of_guidedByTheorySet
        (Const := Const) C.derivation hFU hGuide hφ)

/-- A packaged prime Henkin-implication separating extension feeds the guided
head-priority singleton-world endpoint without manually unpacking the generated
implication theory-set containment. -/
def toCandidateParamPrimeImplicationExtensionOfPrimeHenkinImplicationSeparatingExtensionOfGuidedByTheorySet
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (E : CompletenessFrontier.PrimeHenkinImplicationSeparatingExtension
      (Base := Base) (Const := Const) F)
    (hGuide :
      SaturationSearchState.HeadPrioritySearchDerivation.GuidedByTheorySet
        (Const := Const) E.carrier C.derivation) :
    CertifiedHeadPriorityCompletion.CandidateParamPrimeImplicationExtension
      (Base := Base)
      (Const := Const)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat E.extension) :=
  C.toCandidateParamPrimeImplicationExtensionOfPrimeSeparatingExtensionContainedImplicationsOfGuidedByTheorySet
    (hCompat := hCompat)
    (hFU := E.extension)
    (hGuide := hGuide)
    (exConst := E.exConst)
    (allConst := E.allConst)
    (hContains := E.contains_implications)

/-- Guided head-priority derivations plus fresh-constant implications already
refute native derivability via the singleton world-model endpoint. -/
theorem not_derivable_of_primeSeparatingExtension_implications_guided
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hGuide :
      SaturationSearchState.HeadPrioritySearchDerivation.GuidedByTheorySet
        (Const := Const) U C.derivation)
    (hImp : ClosedTheorySet.ConstantHenkinImplicationData (Const := Const) U) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  let W :=
    C.toCandidateParamPrimeImplicationExtensionOfPrimeSeparatingExtensionOfGuidedByTheorySet
      (hCompat := hCompat) (hFU := hFU) (hGuide := hGuide) (hImp := hImp)
  W.not_derivable_via_paramSingletonWorldModelCounterexample

/-- Guided head-priority derivations plus containment of the generated Henkin
implication theory-set refute native derivability via the singleton
world-model endpoint. -/
theorem not_derivable_of_primeSeparatingExtension_containedImplications_guided
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hGuide :
      SaturationSearchState.HeadPrioritySearchDerivation.GuidedByTheorySet
        (Const := Const) U C.derivation)
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hContains :
      ∀ {θ : ClosedFormula Const},
        θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := Base) (Const := Const) exConst allConst →
          θ ∈ U) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  C.not_derivable_of_primeSeparatingExtension_implications_guided
    (hCompat := hCompat)
    (hFU := hFU)
    (hGuide := hGuide)
    (hImp :=
      ClosedTheorySet.constantHenkinImplicationDataOfContainsTheorySet
        (Base := Base) (Const := Const) exConst allConst hContains)

/-- A packaged prime Henkin-implication separating extension plus a guided
head-priority derivation refutes native derivability through the singleton
world-model endpoint. -/
theorem not_derivable_of_primeHenkinImplicationSeparatingExtension_guided
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (E : CompletenessFrontier.PrimeHenkinImplicationSeparatingExtension
      (Base := Base) (Const := Const) F)
    (hGuide :
      SaturationSearchState.HeadPrioritySearchDerivation.GuidedByTheorySet
        (Const := Const) E.carrier C.derivation) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  C.not_derivable_of_primeSeparatingExtension_containedImplications_guided
    (hCompat := hCompat)
    (hFU := E.extension)
    (hGuide := hGuide)
    (exConst := E.exConst)
    (allConst := E.allConst)
    (hContains := E.contains_implications)

end SaturationSearchState.HeadPriorityCompletion

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
