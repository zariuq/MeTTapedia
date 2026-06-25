import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ParametricHenkinWorldBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ParametricHenkinWorldBridgeRegression

open Mettapedia.Logic.HOL
open Mettapedia.PLN.WorldModel.PLNWorldModel
open CompletenessFrontier
open CertifiedHeadPriorityCompletion
open ClosedTermCanonicalWorldModel
open scoped ENNReal

inductive TestBase where
  | atom
deriving DecidableEq, Repr

inductive TestConst : Ty TestBase → Type where
  | a : TestConst (.base .atom)

def candidateParamPrimeImplicationExtension_constantWitnessData_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W :
      CandidateParamPrimeImplicationExtension
        (Base := TestBase) (Const := TestConst) C) :
    ClosedTheorySet.ConstantHenkinWitnessData
      (Const := ParamConst (Base := TestBase) TestConst W.Gamma)
      W.carrier :=
  W.constantHenkinWitnessData

def candidateParamPrimeImplicationExtension_henkinWitnessData_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W :
      CandidateParamPrimeImplicationExtension
        (Base := TestBase) (Const := TestConst) C) :
    ClosedTheorySet.HenkinWitnessData
      (Const := ParamConst (Base := TestBase) TestConst W.Gamma)
      W.carrier :=
  W.henkinWitnessData

def candidateParamPrimeImplicationExtension_toPrimeConstantHenkin_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W :
      CandidateParamPrimeImplicationExtension
        (Base := TestBase) (Const := TestConst) C) :
    PrimeConstantHenkinSeparatingExtension
      (Base := TestBase)
      (Const := ParamConst (Base := TestBase) TestConst W.Gamma)
      (F.toParam W.Gamma) :=
  W.toPrimeConstantHenkinSeparatingExtension

def candidateParamPrimeImplicationExtension_toCandidateParamPrime_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W :
      CandidateParamPrimeImplicationExtension
        (Base := TestBase) (Const := TestConst) C) :
    CandidateParamPrimeExtension (Base := TestBase) (Const := TestConst) C :=
  W.toCandidateParamPrimeExtension

def candidateParamPrimeImplicationExtension_paramSingletonCountermodel_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W :
      CandidateParamPrimeImplicationExtension
        (Base := TestBase) (Const := TestConst) C) :
    SingletonWorldModelCounterexample
      (Base := TestBase)
      (Const := ParamConst (Base := TestBase) TestConst W.Gamma)
      (F.toParam W.Gamma) :=
  W.toParamSingletonWorldModelCounterexample

theorem candidateParamPrimeImplicationExtension_not_singletonStrengthConsequence_toParam_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W :
      CandidateParamPrimeImplicationExtension
        (Base := TestBase) (Const := TestConst) C) :
    ¬ SingletonStrengthConsequence
      (Base := TestBase)
      (Const := ParamConst (Base := TestBase) TestConst W.Gamma)
      (F.toParam W.Gamma) :=
  W.not_singletonStrengthConsequence_toParam

theorem candidateParamPrimeImplicationExtension_not_derivable_via_paramSingleton_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W :
      CandidateParamPrimeImplicationExtension
        (Base := TestBase) (Const := TestConst) C) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  W.not_derivable_via_paramSingletonWorldModelCounterexample

def candidateParamPrimeExtension_henkinWitnessData_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W : CandidateParamPrimeExtension (Base := TestBase) (Const := TestConst) C) :
    ClosedTheorySet.HenkinWitnessData
      (Const := ParamConst (Base := TestBase) TestConst W.Gamma)
      W.carrier :=
  W.henkinWitnessData

def candidateParamPrimeExtension_primeHenkin_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W : CandidateParamPrimeExtension (Base := TestBase) (Const := TestConst) C) :
    PrimeHenkinSeparatingExtension
      (Base := TestBase)
      (Const := ParamConst (Base := TestBase) TestConst W.Gamma)
      (F.toParam W.Gamma) :=
  W.toPrimeHenkinSeparatingExtension

def candidateParamPrimeExtension_toParamWorld_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W : CandidateParamPrimeExtension (Base := TestBase) (Const := TestConst) C) :
    ClosedTheorySet.World (ParamConst (Base := TestBase) TestConst W.Gamma) :=
  W.toParamWorld

theorem candidateParamPrimeExtension_toParamWorld_carrier_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W : CandidateParamPrimeExtension (Base := TestBase) (Const := TestConst) C) :
    W.toParamWorld.carrier = W.carrier :=
  CandidateParamPrimeExtension.toParamWorld_carrier
    (Base := TestBase) (Const := TestConst) W

def candidateParamPrimeExtension_paramSingletonCountermodel_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W : CandidateParamPrimeExtension (Base := TestBase) (Const := TestConst) C) :
    SingletonWorldModelCounterexample
      (Base := TestBase)
      (Const := ParamConst (Base := TestBase) TestConst W.Gamma)
      (F.toParam W.Gamma) :=
  W.toParamSingletonWorldModelCounterexample

theorem candidateParamPrimeExtension_not_singletonStrengthConsequence_toParam_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W : CandidateParamPrimeExtension (Base := TestBase) (Const := TestConst) C) :
    ¬ SingletonStrengthConsequence
      (Base := TestBase)
      (Const := ParamConst (Base := TestBase) TestConst W.Gamma)
      (F.toParam W.Gamma) :=
  W.not_singletonStrengthConsequence_toParam

theorem mapped_singletonWorldModelCounterexample_not_derivable_canary
    {F : CompletenessFrontier TestConst []}
    {Gamma : Ctx TestBase}
    (Cwm :
      SingletonWorldModelCounterexample
        (Base := TestBase)
        (Const := ParamConst (Base := TestBase) TestConst Gamma)
        (F.toParam Gamma)) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  not_derivable_of_mapped_singletonWorldModelCounterexample
    (Base := TestBase) (Const := TestConst)
    (Const' := ParamConst (Base := TestBase) TestConst Gamma)
    (CompletenessFrontier.paramEmbedding (Base := TestBase) (Const := TestConst) Gamma)
    Cwm

theorem candidateParamPrimeExtension_not_derivable_via_paramSingleton_canary
    {F : CompletenessFrontier TestConst []}
    {C : CertifiedHeadPriorityCompletion TestConst [] F}
    (W : CandidateParamPrimeExtension (Base := TestBase) (Const := TestConst) C) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  W.not_derivable_via_paramSingletonWorldModelCounterexample

theorem certifiedCompletion_exists_paramSingletonCountermodel_canary
    {F : CompletenessFrontier TestConst []}
    (C : CertifiedHeadPriorityCompletion TestConst [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeExtension (Base := TestBase) (Const := TestConst) C)) :
    Nonempty (Σ Gamma : Ctx TestBase,
      SingletonWorldModelCounterexample
        (Base := TestBase)
        (Const := ParamConst (Base := TestBase) TestConst Gamma)
        (F.toParam Gamma)) :=
  CertifiedHeadPriorityCompletion.exists_paramSingletonCountermodel_of_exists_candidateParamPrimeExtension
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCompletion_exists_not_singletonStrengthConsequence_toParam_canary
    {F : CompletenessFrontier TestConst []}
    (C : CertifiedHeadPriorityCompletion TestConst [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeExtension (Base := TestBase) (Const := TestConst) C)) :
    ∃ Gamma : Ctx TestBase,
      ¬ SingletonStrengthConsequence
        (Base := TestBase)
        (Const := ParamConst (Base := TestBase) TestConst Gamma)
        (F.toParam Gamma) :=
  CertifiedHeadPriorityCompletion.exists_not_singletonStrengthConsequence_toParam_of_exists_candidateParamPrimeExtension
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCompletion_not_derivable_of_exists_paramSingletonCountermodel_canary
    {F : CompletenessFrontier TestConst []}
    (C : CertifiedHeadPriorityCompletion TestConst [] F)
    (hW :
      Nonempty (Σ Gamma : Ctx TestBase,
        SingletonWorldModelCounterexample
          (Base := TestBase)
          (Const := ParamConst (Base := TestBase) TestConst Gamma)
          (F.toParam Gamma))) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  CertifiedHeadPriorityCompletion.not_derivable_of_exists_paramSingletonCountermodel
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCompletion_not_derivable_via_paramSingleton_of_exists_candidateParamPrimeExtension_canary
    {F : CompletenessFrontier TestConst []}
    (C : CertifiedHeadPriorityCompletion TestConst [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeExtension (Base := TestBase) (Const := TestConst) C)) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  CertifiedHeadPriorityCompletion.not_derivable_via_paramSingletonCountermodel_of_exists_candidateParamPrimeExtension
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCompletion_exists_candidateParamPrime_of_exists_candidateParamPrimeImplication_canary
    {F : CompletenessFrontier TestConst []}
    (C : CertifiedHeadPriorityCompletion TestConst [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeImplicationExtension
          (Base := TestBase) (Const := TestConst) C)) :
    Nonempty (CandidateParamPrimeExtension (Base := TestBase) (Const := TestConst) C) :=
  CertifiedHeadPriorityCompletion.exists_candidateParamPrimeExtension_of_exists_candidateParamPrimeImplicationExtension
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCompletion_exists_paramSingleton_of_exists_candidateParamPrimeImplication_canary
    {F : CompletenessFrontier TestConst []}
    (C : CertifiedHeadPriorityCompletion TestConst [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeImplicationExtension
          (Base := TestBase) (Const := TestConst) C)) :
    Nonempty (Σ Gamma : Ctx TestBase,
      SingletonWorldModelCounterexample
        (Base := TestBase)
        (Const := ParamConst (Base := TestBase) TestConst Gamma)
        (F.toParam Gamma)) :=
  CertifiedHeadPriorityCompletion.exists_paramSingletonCountermodel_of_exists_candidateParamPrimeImplicationExtension
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCompletion_not_derivable_of_exists_candidateParamPrimeImplication_canary
    {F : CompletenessFrontier TestConst []}
    (C : CertifiedHeadPriorityCompletion TestConst [] F)
    (hW :
      Nonempty
        (CandidateParamPrimeImplicationExtension
          (Base := TestBase) (Const := TestConst) C)) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  CertifiedHeadPriorityCompletion.not_derivable_of_exists_candidateParamPrimeImplicationExtension
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCompletion_exists_candidateParamPrimeImplication_of_rawAgreement_canary
    {F : CompletenessFrontier TestConst []}
    (C : CertifiedHeadPriorityCompletion TestConst [] F)
    (hW :
      Nonempty
        (PrimeImplicationExtensionAgreement
          (Base := TestBase) (Const := TestConst) C)) :
    Nonempty
      (CandidateParamPrimeImplicationExtension
        (Base := TestBase) (Const := TestConst) C) :=
  CertifiedHeadPriorityCompletion.exists_candidateParamPrimeImplicationExtension_of_exists_primeImplicationExtensionAgreement
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCompletion_not_derivable_of_rawAgreement_canary
    {F : CompletenessFrontier TestConst []}
    (C : CertifiedHeadPriorityCompletion TestConst [] F)
    (hW :
      Nonempty
        (PrimeImplicationExtensionAgreement
          (Base := TestBase) (Const := TestConst) C)) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  CertifiedHeadPriorityCompletion.not_derivable_of_exists_primeImplicationExtensionAgreement
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCandidate_exists_paramSingletonCountermodel_canary
    (C : CertifiedCountermodelCandidate TestConst [])
    (hW :
      Nonempty
        (CertifiedCountermodelCandidate.CandidateParamPrimeExtension
          (Base := TestBase) (Const := TestConst) C)) :
    Nonempty (Σ Gamma : Ctx TestBase,
      SingletonWorldModelCounterexample
        (Base := TestBase)
        (Const := ParamConst (Base := TestBase) TestConst Gamma)
        (C.frontier.toParam Gamma)) :=
  CertifiedCountermodelCandidate.exists_paramSingletonCountermodel_of_exists_candidateParamPrimeExtension
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCandidate_exists_not_singletonStrengthConsequence_toParam_canary
    (C : CertifiedCountermodelCandidate TestConst [])
    (hW :
      Nonempty
        (CertifiedCountermodelCandidate.CandidateParamPrimeExtension
          (Base := TestBase) (Const := TestConst) C)) :
    ∃ Gamma : Ctx TestBase,
      ¬ SingletonStrengthConsequence
        (Base := TestBase)
        (Const := ParamConst (Base := TestBase) TestConst Gamma)
        (C.frontier.toParam Gamma) :=
  CertifiedCountermodelCandidate.exists_not_singletonStrengthConsequence_toParam_of_exists_candidateParamPrimeExtension
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCandidate_not_derivable_of_exists_paramSingletonCountermodel_canary
    (C : CertifiedCountermodelCandidate TestConst [])
    (hW :
      Nonempty (Σ Gamma : Ctx TestBase,
        SingletonWorldModelCounterexample
          (Base := TestBase)
          (Const := ParamConst (Base := TestBase) TestConst Gamma)
          (C.frontier.toParam Gamma))) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        C.frontier.antecedents C.frontier.succedent :=
  CertifiedCountermodelCandidate.not_derivable_of_exists_paramSingletonCountermodel
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCandidate_not_derivable_via_paramSingleton_of_exists_candidateParamPrimeExtension_canary
    (C : CertifiedCountermodelCandidate TestConst [])
    (hW :
      Nonempty
        (CertifiedCountermodelCandidate.CandidateParamPrimeExtension
          (Base := TestBase) (Const := TestConst) C)) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        C.frontier.antecedents C.frontier.succedent :=
  CertifiedCountermodelCandidate.not_derivable_via_paramSingletonCountermodel_of_exists_candidateParamPrimeExtension
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCandidate_exists_candidateParamPrime_of_exists_candidateParamPrimeImplication_canary
    (C : CertifiedCountermodelCandidate TestConst [])
    (hW :
      Nonempty
        (CertifiedCountermodelCandidate.CandidateParamPrimeImplicationExtension
          (Base := TestBase) (Const := TestConst) C)) :
    Nonempty
      (CertifiedCountermodelCandidate.CandidateParamPrimeExtension
        (Base := TestBase) (Const := TestConst) C) :=
  CertifiedCountermodelCandidate.exists_candidateParamPrimeExtension_of_exists_candidateParamPrimeImplicationExtension
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCandidate_exists_paramSingleton_of_exists_candidateParamPrimeImplication_canary
    (C : CertifiedCountermodelCandidate TestConst [])
    (hW :
      Nonempty
        (CertifiedCountermodelCandidate.CandidateParamPrimeImplicationExtension
          (Base := TestBase) (Const := TestConst) C)) :
    Nonempty (Σ Gamma : Ctx TestBase,
      SingletonWorldModelCounterexample
        (Base := TestBase)
        (Const := ParamConst (Base := TestBase) TestConst Gamma)
        (C.frontier.toParam Gamma)) :=
  CertifiedCountermodelCandidate.exists_paramSingletonCountermodel_of_exists_candidateParamPrimeImplicationExtension
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCandidate_not_derivable_of_exists_candidateParamPrimeImplication_canary
    (C : CertifiedCountermodelCandidate TestConst [])
    (hW :
      Nonempty
        (CertifiedCountermodelCandidate.CandidateParamPrimeImplicationExtension
          (Base := TestBase) (Const := TestConst) C)) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        C.frontier.antecedents C.frontier.succedent :=
  CertifiedCountermodelCandidate.not_derivable_of_exists_candidateParamPrimeImplicationExtension
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCandidate_exists_candidateParamPrimeImplication_of_rawAgreement_canary
    (C : CertifiedCountermodelCandidate TestConst [])
    (hW :
      Nonempty
        (CertifiedCountermodelCandidate.PrimeImplicationExtensionAgreement
          (Base := TestBase) (Const := TestConst) C)) :
    Nonempty
      (CertifiedCountermodelCandidate.CandidateParamPrimeImplicationExtension
        (Base := TestBase) (Const := TestConst) C) :=
  CertifiedCountermodelCandidate.exists_candidateParamPrimeImplicationExtension_of_exists_primeImplicationExtensionAgreement
    (Base := TestBase) (Const := TestConst) C hW

theorem certifiedCandidate_not_derivable_of_rawAgreement_canary
    (C : CertifiedCountermodelCandidate TestConst [])
    (hW :
      Nonempty
        (CertifiedCountermodelCandidate.PrimeImplicationExtensionAgreement
          (Base := TestBase) (Const := TestConst) C)) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        C.frontier.antecedents C.frontier.succedent :=
  CertifiedCountermodelCandidate.not_derivable_of_exists_primeImplicationExtensionAgreement
    (Base := TestBase) (Const := TestConst) C hW

def emptyParamTheorySet_constantHenkinImplicationData_canary
    {U : ClosedTheorySet TestConst}
    (hImp :
      ClosedTheorySet.ConstantHenkinImplicationData (Const := TestConst) U) :
    ClosedTheorySet.ConstantHenkinImplicationData
      (Const := ParamConst (Base := TestBase) TestConst [])
      (CompletenessFrontier.emptyParamTheorySet
        (Base := TestBase) (Const := TestConst) U) :=
  CompletenessFrontier.emptyParamTheorySet_constantHenkinImplicationData
    (Base := TestBase) (Const := TestConst) hImp

def headPriorityCompletion_primeImplicationAgreement_canary
    {F : CompletenessFrontier TestConst []}
    (C : SaturationSearchState.HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hImp :
      ClosedTheorySet.ConstantHenkinImplicationData (Const := TestConst) U)
    (hTrue :
      ∀ {φ : ClosedFormula TestConst},
        (Sign.trueE, φ) ∈ C.state.hintikka.formulas → φ ∈ U)
    (hFalse :
      ∀ {φ : ClosedFormula TestConst},
        (Sign.falseE, φ) ∈ C.state.hintikka.formulas → φ ∉ U) :
    CertifiedHeadPriorityCompletion.PrimeImplicationExtensionAgreement
      (Base := TestBase)
      (Const := TestConst)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) :=
  C.toPrimeImplicationExtensionAgreementOfPrimeSeparatingExtension
    (hCompat := hCompat) (hFU := hFU) (hImp := hImp)
    (hTrue := hTrue) (hFalse := hFalse)

def headPriorityCompletion_candidateParamPrimeImplication_canary
    {F : CompletenessFrontier TestConst []}
    (C : SaturationSearchState.HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hImp :
      ClosedTheorySet.ConstantHenkinImplicationData (Const := TestConst) U)
    (hTrue :
      ∀ {φ : ClosedFormula TestConst},
        (Sign.trueE, φ) ∈ C.state.hintikka.formulas → φ ∈ U)
    (hFalse :
      ∀ {φ : ClosedFormula TestConst},
        (Sign.falseE, φ) ∈ C.state.hintikka.formulas → φ ∉ U) :
    CandidateParamPrimeImplicationExtension
      (Base := TestBase)
      (Const := TestConst)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) :=
  C.toCandidateParamPrimeImplicationExtensionOfPrimeSeparatingExtension
    (hCompat := hCompat) (hFU := hFU) (hImp := hImp)
    (hTrue := hTrue) (hFalse := hFalse)

def headPriorityCompletion_primeImplicationAgreement_contained_canary
    {F : CompletenessFrontier TestConst []}
    (C : SaturationSearchState.HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hContains :
      ∀ {θ : ClosedFormula TestConst},
        θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst →
          θ ∈ U)
    (hTrue :
      ∀ {φ : ClosedFormula TestConst},
        (Sign.trueE, φ) ∈ C.state.hintikka.formulas → φ ∈ U)
    (hFalse :
      ∀ {φ : ClosedFormula TestConst},
        (Sign.falseE, φ) ∈ C.state.hintikka.formulas → φ ∉ U) :
    CertifiedHeadPriorityCompletion.PrimeImplicationExtensionAgreement
      (Base := TestBase)
      (Const := TestConst)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) :=
  C.toPrimeImplicationExtensionAgreementOfPrimeSeparatingExtensionContainedImplications
    (hCompat := hCompat) (hFU := hFU)
    (exConst := exConst) (allConst := allConst) (hContains := hContains)
    (hTrue := hTrue) (hFalse := hFalse)

def headPriorityCompletion_candidateParamPrimeImplication_contained_canary
    {F : CompletenessFrontier TestConst []}
    (C : SaturationSearchState.HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hContains :
      ∀ {θ : ClosedFormula TestConst},
        θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst →
          θ ∈ U)
    (hTrue :
      ∀ {φ : ClosedFormula TestConst},
        (Sign.trueE, φ) ∈ C.state.hintikka.formulas → φ ∈ U)
    (hFalse :
      ∀ {φ : ClosedFormula TestConst},
        (Sign.falseE, φ) ∈ C.state.hintikka.formulas → φ ∉ U) :
    CandidateParamPrimeImplicationExtension
      (Base := TestBase)
      (Const := TestConst)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) :=
  C.toCandidateParamPrimeImplicationExtensionOfPrimeSeparatingExtensionContainedImplications
    (hCompat := hCompat) (hFU := hFU)
    (exConst := exConst) (allConst := allConst) (hContains := hContains)
    (hTrue := hTrue) (hFalse := hFalse)

def headPriorityCompletion_candidateParamPrimeImplication_guided_canary
    {F : CompletenessFrontier TestConst []}
    (C : SaturationSearchState.HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hGuide :
      SaturationSearchState.HeadPrioritySearchDerivation.GuidedByTheorySet
        (Const := TestConst) U C.derivation)
    (hImp :
      ClosedTheorySet.ConstantHenkinImplicationData (Const := TestConst) U) :
    CandidateParamPrimeImplicationExtension
      (Base := TestBase)
      (Const := TestConst)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) :=
  C.toCandidateParamPrimeImplicationExtensionOfPrimeSeparatingExtensionOfGuidedByTheorySet
    (hCompat := hCompat) (hFU := hFU) (hGuide := hGuide) (hImp := hImp)

def headPriorityCompletion_candidateParamPrimeImplication_contained_guided_canary
    {F : CompletenessFrontier TestConst []}
    (C : SaturationSearchState.HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hGuide :
      SaturationSearchState.HeadPrioritySearchDerivation.GuidedByTheorySet
        (Const := TestConst) U C.derivation)
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hContains :
      ∀ {θ : ClosedFormula TestConst},
        θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst →
          θ ∈ U) :
    CandidateParamPrimeImplicationExtension
      (Base := TestBase)
      (Const := TestConst)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) :=
  C.toCandidateParamPrimeImplicationExtensionOfPrimeSeparatingExtensionContainedImplicationsOfGuidedByTheorySet
    (hCompat := hCompat) (hFU := hFU) (hGuide := hGuide)
    (exConst := exConst) (allConst := allConst) (hContains := hContains)

def headPriorityCompletion_candidateParamPrimeImplication_packaged_guided_canary
    {F : CompletenessFrontier TestConst []}
    (C : SaturationSearchState.HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (E : PrimeHenkinImplicationSeparatingExtension (Const := TestConst) F)
    (hGuide :
      SaturationSearchState.HeadPrioritySearchDerivation.GuidedByTheorySet
        (Const := TestConst) E.carrier C.derivation) :
    CandidateParamPrimeImplicationExtension
      (Base := TestBase)
      (Const := TestConst)
      (C.toCertifiedOfPrimeSeparatingExtension hCompat E.extension) :=
  C.toCandidateParamPrimeImplicationExtensionOfPrimeHenkinImplicationSeparatingExtensionOfGuidedByTheorySet
    (hCompat := hCompat) E hGuide

theorem headPriorityCompletion_not_derivable_implications_guided_canary
    {F : CompletenessFrontier TestConst []}
    (C : SaturationSearchState.HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hGuide :
      SaturationSearchState.HeadPrioritySearchDerivation.GuidedByTheorySet
        (Const := TestConst) U C.derivation)
    (hImp :
      ClosedTheorySet.ConstantHenkinImplicationData (Const := TestConst) U) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  C.not_derivable_of_primeSeparatingExtension_implications_guided
    (hCompat := hCompat) (hFU := hFU) (hGuide := hGuide) (hImp := hImp)

theorem headPriorityCompletion_not_derivable_containedImplications_guided_canary
    {F : CompletenessFrontier TestConst []}
    (C : SaturationSearchState.HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hGuide :
      SaturationSearchState.HeadPrioritySearchDerivation.GuidedByTheorySet
        (Const := TestConst) U C.derivation)
    (exConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (allConst : ∀ {σ : Ty TestBase}, Formula TestConst [σ] → TestConst σ)
    (hContains :
      ∀ {θ : ClosedFormula TestConst},
        θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := TestBase) (Const := TestConst) exConst allConst →
          θ ∈ U) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  C.not_derivable_of_primeSeparatingExtension_containedImplications_guided
    (hCompat := hCompat) (hFU := hFU) (hGuide := hGuide)
    (exConst := exConst) (allConst := allConst) (hContains := hContains)

theorem headPriorityCompletion_not_derivable_packaged_guided_canary
    {F : CompletenessFrontier TestConst []}
    (C : SaturationSearchState.HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (E : PrimeHenkinImplicationSeparatingExtension (Const := TestConst) F)
    (hGuide :
      SaturationSearchState.HeadPrioritySearchDerivation.GuidedByTheorySet
        (Const := TestConst) E.carrier C.derivation) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  C.not_derivable_of_primeHenkinImplicationSeparatingExtension_guided
    (hCompat := hCompat) E hGuide

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ParametricHenkinWorldBridgeRegression
