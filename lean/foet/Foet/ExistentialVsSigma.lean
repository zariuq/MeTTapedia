import Foet.SumoEthicsSig

set_option autoImplicit false

namespace Foet

universe u

/-
Existential (`∃`) vs witness-carrying dependent sum (`Σ`) in “there exists a virtue …” translations.

This is the kernel of the “reify the existentially introduced virtue?” question.
In Lean, `∃ v, P v` lives in `Prop` (no computational content), while `Σ v, P v`
is a type whose inhabitants *include* a concrete witness `v`.
-/

def ExistsVirtueDesire {World : Type u} (sig : SumoEthicsSig World) (φ : Formula World) : Formula World :=
  fun w => ∃ v : sig.VirtueAttribute, sig.virtueDesireFormula v φ w

def SigmaVirtueDesire {World : Type u} (sig : SumoEthicsSig World) (φ : Formula World) (w : World) : Type u :=
  PSigma fun v : sig.VirtueAttribute => sig.virtueDesireFormula v φ w

theorem exists_to_nonempty_sigma {World : Type u} (sig : SumoEthicsSig World) (φ : Formula World) (w : World) :
    ExistsVirtueDesire sig φ w → Nonempty (SigmaVirtueDesire sig φ w) := by
  intro h
  rcases h with ⟨v, hv⟩
  exact ⟨⟨v, hv⟩⟩

theorem sigma_to_exists {World : Type u} (sig : SumoEthicsSig World) (φ : Formula World) (w : World) :
    SigmaVirtueDesire sig φ w → ExistsVirtueDesire sig φ w := by
  intro h
  exact ⟨h.1, h.2⟩

def witnessOfSigma {World : Type u} {sig : SumoEthicsSig World} {φ : Formula World} {w : World} :
    SigmaVirtueDesire sig φ w → sig.VirtueAttribute :=
  fun h => h.fst

namespace Example

inductive World : Type
  | w

def sig : SumoEthicsSig World :=
  { Agent := Unit
    Process := Unit
    ProcessClass := Unit
    ChoicePoint := Unit
    Situation := Unit
    SituationClass := Unit
    Value := Unit
    VirtueAttribute := Bool
    EthicalPhilosophy := Unit
    UtilityFormulaFn := Unit
    hasAgent := fun _ _ => fun _ => True
    situationFn := fun _ => ()
    part := fun _ _ => fun _ => True
    isInstance := fun _ _ => fun _ => True
    isProcessInstance := fun _ _ => fun _ => True
    element := fun _ _ => fun _ => True
    choicePointAgentFn := fun _ => ()
    choicePointSituationFn := fun _ => ()
    describesSituation := fun _ _ => fun _ => True
    situationFormulaFn := fun _ => ()
    hasAttribute := fun _ _ => fun _ => True
    desires := fun _ φ => φ
    prefers := fun _ _ _ => fun _ => True
    interferesWith := fun _ _ => fun _ => False
    holdsObligation := fun _ _ => fun _ => True
    holdsEthicalPhilosophy := fun _ _ => fun _ => True
    practicesEthicalPhilosophy := fun _ _ => fun _ => True
    realizesFormula := fun _ _ => fun _ => True
    capableInSituation := fun _ _ _ => fun _ => True
    holdsValue := fun _ _ => fun _ => True
    bestActionByUtilityInSituation := fun _ _ _ => fun _ => True
    relevantField := fun _ _ => fun _ => True
    relevantProcessClass := fun _ _ => fun _ => True
    similar := fun _ _ _ => fun _ => True }

def φ : Formula World :=
  fun _ => True

def w : World := .w

def sigmaWitnessTrue : SigmaVirtueDesire sig φ w :=
  ⟨true, by
    -- `virtueDesireFormula` reduces to a trivial proposition under our dummy signature.
    intro a ha
    trivial⟩

def sigmaWitnessFalse : SigmaVirtueDesire sig φ w :=
  ⟨false, by
    intro a ha
    trivial⟩

theorem sigmaWitnessesDistinct : sigmaWitnessTrue ≠ sigmaWitnessFalse := by
  intro hEq
  have : (true : Bool) = false :=
    congrArg PSigma.fst hEq
  cases this

end Example

end Foet
