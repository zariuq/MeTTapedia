import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermWorldModelCountermodel

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermWorldModelCountermodelRegression

open Mettapedia.Logic.HOL
open Mettapedia.PLN.WorldModel.PLNWorldModel
open CompletenessFrontier
open ClosedTermCanonicalWorldModel
open scoped ENNReal

inductive TestBase where
  | atom
deriving DecidableEq, Repr

inductive TestConst : Ty TestBase → Type where
  | a : TestConst (.base .atom)

def singletonCountermodel_of_world_counterexample_canary
    {F : CompletenessFrontier TestConst []}
    {W : ClosedTheorySet.World TestConst}
    (hAnte : ∀ φ, φ ∈ F.antecedents → φ ∈ W.carrier)
    (hSucc : F.succedent ∉ W.carrier) :
    SingletonWorldModelCounterexample (Const := TestConst) F :=
  singletonWorldModelCounterexampleOfWorldCounterexample
    (Base := TestBase) (Const := TestConst) hAnte hSucc

theorem singletonCountermodel_antecedent_strength_canary
    {F : CompletenessFrontier TestConst []}
    (C : SingletonWorldModelCounterexample (Const := TestConst) F)
    {φ : ClosedFormula TestConst}
    (hφ : φ ∈ F.antecedents) :
    BinaryWorldModel.queryStrength
        (State := Multiset (ClosedTheorySet.World TestConst))
        (Query := CanonicalQuery TestConst)
        ({C.world} : Multiset (ClosedTheorySet.World TestConst)) φ = 1 :=
  C.antecedent_strength_one hφ

theorem singletonCountermodel_succedent_strength_canary
    {F : CompletenessFrontier TestConst []}
    (C : SingletonWorldModelCounterexample (Const := TestConst) F) :
    BinaryWorldModel.queryStrength
        (State := Multiset (ClosedTheorySet.World TestConst))
        (Query := CanonicalQuery TestConst)
        ({C.world} : Multiset (ClosedTheorySet.World TestConst)) F.succedent = 0 :=
  C.succedent_strength_zero

theorem singletonCountermodel_antecedent_mem_canary
    {F : CompletenessFrontier TestConst []}
    (C : SingletonWorldModelCounterexample (Const := TestConst) F)
    {φ : ClosedFormula TestConst}
    (hφ : φ ∈ F.antecedents) :
    φ ∈ C.world.carrier :=
  C.antecedent_mem hφ

theorem singletonCountermodel_succedent_not_mem_canary
    {F : CompletenessFrontier TestConst []}
    (C : SingletonWorldModelCounterexample (Const := TestConst) F) :
    F.succedent ∉ C.world.carrier :=
  C.succedent_not_mem

theorem singletonCountermodel_to_world_counterexample_canary
    {F : CompletenessFrontier TestConst []}
    (C : SingletonWorldModelCounterexample (Const := TestConst) F) :
    (∀ φ, φ ∈ F.antecedents → φ ∈ C.world.carrier) ∧
      F.succedent ∉ C.world.carrier :=
  C.to_world_counterexample

theorem singletonCountermodel_not_derivable_canary
    {F : CompletenessFrontier TestConst []}
    (C : SingletonWorldModelCounterexample (Const := TestConst) F) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  C.not_derivable

theorem not_derivable_of_singletonCountermodel_canary
    {F : CompletenessFrontier TestConst []}
    (C : SingletonWorldModelCounterexample (Const := TestConst) F) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  not_derivable_of_singletonWorldModelCounterexample
    (Base := TestBase) (Const := TestConst) C

def singletonCountermodel_of_quotientRealizationSemanticCounterexample_canary
    {F : CompletenessFrontier TestConst []}
    {M : HenkinModel TestBase TestConst}
    {W : ClosedTheorySet.World TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (hAnte : ∀ φ, φ ∈ F.antecedents → HenkinModel.models M φ)
    (hSucc : ¬ HenkinModel.models M F.succedent) :
    SingletonWorldModelCounterexample (Const := TestConst) F :=
  singletonWorldModelCounterexampleOfQuotientRealizationSemanticCounterexample
    (Base := TestBase) (Const := TestConst) R hAnte hSucc

theorem not_derivable_of_quotientRealizationSemanticCounterexample_canary
    {F : CompletenessFrontier TestConst []}
    {M : HenkinModel TestBase TestConst}
    {W : ClosedTheorySet.World TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (hAnte : ∀ φ, φ ∈ F.antecedents → HenkinModel.models M φ)
    (hSucc : ¬ HenkinModel.models M F.succedent) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  not_derivable_of_quotientRealizationSemanticCounterexample
    (Base := TestBase) (Const := TestConst) R hAnte hSucc

theorem singletonCountermodel_antecedent_models_of_quotientRealization_canary
    {F : CompletenessFrontier TestConst []}
    (C : SingletonWorldModelCounterexample (Const := TestConst) F)
    {M : HenkinModel TestBase TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M C.world.carrier)
    {φ : ClosedFormula TestConst}
    (hφ : φ ∈ F.antecedents) :
    HenkinModel.models M φ :=
  C.antecedent_models_of_quotientRealization R hφ

theorem singletonCountermodel_not_models_succedent_of_quotientRealization_canary
    {F : CompletenessFrontier TestConst []}
    (C : SingletonWorldModelCounterexample (Const := TestConst) F)
    {M : HenkinModel TestBase TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M C.world.carrier) :
    ¬ HenkinModel.models M F.succedent :=
  C.not_models_succedent_of_quotientRealization R

theorem singletonStrength_preservation_of_derivable_canary
    {F : CompletenessFrontier TestConst []}
    (hDer : Derivable (Base := TestBase) (Const := TestConst)
      F.antecedents F.succedent)
    (W : ClosedTheorySet.World TestConst)
    (hAnte :
      ∀ {φ : ClosedFormula TestConst}, φ ∈ F.antecedents →
        BinaryWorldModel.queryStrength
            (State := Multiset (ClosedTheorySet.World TestConst))
            (Query := CanonicalQuery TestConst)
            ({W} : Multiset (ClosedTheorySet.World TestConst)) φ = 1) :
    BinaryWorldModel.queryStrength
        (State := Multiset (ClosedTheorySet.World TestConst))
        (Query := CanonicalQuery TestConst)
        ({W} : Multiset (ClosedTheorySet.World TestConst)) F.succedent = 1 :=
  singletonStrength_preservation_of_derivable
    (Base := TestBase) (Const := TestConst) hDer W hAnte

theorem no_singletonCountermodel_of_derivable_canary
    {F : CompletenessFrontier TestConst []}
    (hDer : Derivable (Base := TestBase) (Const := TestConst)
      F.antecedents F.succedent) :
    ¬ Nonempty (SingletonWorldModelCounterexample (Const := TestConst) F) :=
  not_nonempty_singletonWorldModelCounterexample_of_derivable
    (Base := TestBase) (Const := TestConst) hDer

theorem singletonStrengthConsequence_of_derivable_canary
    {F : CompletenessFrontier TestConst []}
    (hDer : Derivable (Base := TestBase) (Const := TestConst)
      F.antecedents F.succedent) :
    SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F :=
  singletonStrengthConsequence_of_derivable
    (Base := TestBase) (Const := TestConst) hDer

theorem not_singletonStrengthConsequence_of_counterexample_canary
    {F : CompletenessFrontier TestConst []}
    (C : SingletonWorldModelCounterexample (Const := TestConst) F) :
    ¬ SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F :=
  not_singletonStrengthConsequence_of_counterexample
    (Base := TestBase) (Const := TestConst) C

theorem not_singletonStrengthConsequence_of_quotientRealizationSemanticCounterexample_canary
    {F : CompletenessFrontier TestConst []}
    {M : HenkinModel TestBase TestConst}
    {W : ClosedTheorySet.World TestConst}
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (hAnte : ∀ φ, φ ∈ F.antecedents → HenkinModel.models M φ)
    (hSucc : ¬ HenkinModel.models M F.succedent) :
    ¬ SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F :=
  not_singletonStrengthConsequence_of_quotientRealizationSemanticCounterexample
    (Base := TestBase) (Const := TestConst) R hAnte hSucc

theorem singletonStrengthConsequence_iff_no_counterexample_canary
    (F : CompletenessFrontier TestConst []) :
    SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F ↔
      ¬ Nonempty (SingletonWorldModelCounterexample (Const := TestConst) F) :=
  singletonStrengthConsequence_iff_no_counterexample
    (Base := TestBase) (Const := TestConst) F

theorem not_singletonStrengthConsequence_iff_counterexample_canary
    (F : CompletenessFrontier TestConst []) :
    ¬ SingletonStrengthConsequence (Base := TestBase) (Const := TestConst) F ↔
      Nonempty (SingletonWorldModelCounterexample (Const := TestConst) F) :=
  not_singletonStrengthConsequence_iff_counterexample
    (Base := TestBase) (Const := TestConst) F

def singletonCountermodel_of_primeSeparatingExtension_canary
    {F : CompletenessFrontier TestConst []}
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hExistsWitness :
      ∀ {σ : Ty TestBase} {φ : Formula TestConst [σ]},
        (.ex φ : ClosedFormula TestConst) ∈ U →
          ∃ t : ClosedTerm TestConst σ, instantiate (Base := TestBase) t φ ∈ U)
    (hAllCounterexample :
      ∀ {σ : Ty TestBase} {φ : Formula TestConst [σ]},
        (.all φ : ClosedFormula TestConst) ∉ U →
          ∃ t : ClosedTerm TestConst σ, instantiate (Base := TestBase) t φ ∉ U) :
    SingletonWorldModelCounterexample (Const := TestConst) F :=
  singletonWorldModelCounterexampleOfPrimeSeparatingExtension
    (Base := TestBase) (Const := TestConst)
    hFU hExistsWitness hAllCounterexample

theorem not_derivable_of_primeSeparatingExtension_with_witnesses_canary
    {F : CompletenessFrontier TestConst []}
    {U : ClosedTheorySet TestConst}
    (hFU : PrimeSeparatingExtension (Const := TestConst) F U)
    (hExistsWitness :
      ∀ {σ : Ty TestBase} {φ : Formula TestConst [σ]},
        (.ex φ : ClosedFormula TestConst) ∈ U →
          ∃ t : ClosedTerm TestConst σ, instantiate (Base := TestBase) t φ ∈ U)
    (hAllCounterexample :
      ∀ {σ : Ty TestBase} {φ : Formula TestConst [σ]},
        (.all φ : ClosedFormula TestConst) ∉ U →
          ∃ t : ClosedTerm TestConst σ, instantiate (Base := TestBase) t φ ∉ U) :
    ¬ Derivable (Base := TestBase) (Const := TestConst)
        F.antecedents F.succedent :=
  not_derivable_of_primeSeparatingExtension_with_witnesses
    (Base := TestBase) (Const := TestConst)
    hFU hExistsWitness hAllCounterexample

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermWorldModelCountermodelRegression
