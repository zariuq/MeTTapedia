import Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness
import Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness

/-!
# Infinitary WM Regression Fixtures (PredCode + FOL)

Concrete theorem-level fixtures exercising the new countable-connective wrappers:

- `iAnd → component` (elimination)
- `component → iOr` (introduction)

for both infinitary predicate-code and infinitary FOL WM layers.
-/

namespace Mettapedia.Logic.PLNWorldModelInfinitaryRegression

open LO
open LO.FirstOrder
open Mettapedia.Logic.PLNWorldModel

/-! ## Predicate-code fixtures -/

abbrev predCodeInfFalse :
    Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfQuery Bool :=
  .atom (.comp_not .trivial)

abbrev predCodeInfTrue :
    Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfQuery Bool :=
  .atom .trivial

def predCodeInfSeq :
    Nat → Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfQuery Bool
  | 0 => predCodeInfFalse
  | _ => predCodeInfTrue

def predCodeInfFixtureState :
    Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfState Bool :=
  ({⟨true⟩} : Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfState Bool) +
    ({⟨false⟩} : Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfState Bool)

/-- Predicate-code infinitary fixture: conjunction-elimination transport via wrapper API. -/
theorem predCodeInf_iAnd_component_fixture :
    BinaryWorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfState Bool)
        (Query := Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfQuery Bool)
        predCodeInfFixtureState (.iAnd predCodeInfSeq) ≤
      BinaryWorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfState Bool)
        (Query := Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfQuery Bool)
        predCodeInfFixtureState (predCodeInfSeq 0) := by
  exact
    (Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.wmConsequenceRule_of_pointwise
      (q₁ := .iAnd predCodeInfSeq) (q₂ := predCodeInfSeq 0)).sound
      (Mettapedia.Logic.PLNWorldModelPredCodeInfinitary.pointwise_iAnd_to_component
        (F := predCodeInfSeq) (n := 0))
      predCodeInfFixtureState

/-- Predicate-code infinitary fixture: disjunction-introduction transport via wrapper API. -/
theorem predCodeInf_component_iOr_fixture :
    BinaryWorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfState Bool)
        (Query := Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfQuery Bool)
        predCodeInfFixtureState (predCodeInfSeq 0) ≤
      BinaryWorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfState Bool)
        (Query := Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfQuery Bool)
        predCodeInfFixtureState (.iOr predCodeInfSeq) := by
  exact
    (Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.wmConsequenceRule_of_pointwise
      (q₁ := predCodeInfSeq 0) (q₂ := .iOr predCodeInfSeq)).sound
      (Mettapedia.Logic.PLNWorldModelPredCodeInfinitary.pointwise_component_to_iOr
        (F := predCodeInfSeq) (n := 0))
      predCodeInfFixtureState

/-! ## FOL fixtures -/

abbrev folInfTop {L : Language} :
    Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfQuery L :=
  .atom (⊤ : Sentence L)

abbrev folInfBottom {L : Language} :
    Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfQuery L :=
  .atom (⊥ : Sentence L)

def folInfSeq {L : Language} :
    Nat → Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfQuery L
  | 0 => folInfBottom
  | _ => folInfTop

/-- FOL infinitary singleton fixture: conjunction-elimination transport via wrapper API. -/
theorem folInf_iAnd_component_singleton_fixture
    {L : Language} (S : Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.PointedFOL L) :
    BinaryWorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)
        (Query := Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfQuery L)
        ({S} : Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)
        (.iAnd (folInfSeq (L := L))) ≤
      BinaryWorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)
        (Query := Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfQuery L)
        ({S} : Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)
        (folInfSeq (L := L) 0) := by
  exact
    (Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.wmConsequenceRule_of_pointwise
      (q₁ := .iAnd (folInfSeq (L := L))) (q₂ := folInfSeq (L := L) 0)).sound
      (Mettapedia.Logic.PLNWorldModelFOLInfinitary.pointwise_iAnd_to_component
        (F := folInfSeq (L := L)) (n := 0))
      ({S} : Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)

/-- FOL infinitary singleton fixture: disjunction-introduction transport via wrapper API. -/
theorem folInf_component_iOr_singleton_fixture
    {L : Language} (S : Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.PointedFOL L) :
    BinaryWorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)
        (Query := Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfQuery L)
        ({S} : Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)
        (folInfSeq (L := L) 0) ≤
      BinaryWorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)
        (Query := Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfQuery L)
        ({S} : Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)
        (.iOr (folInfSeq (L := L))) := by
  exact
    (Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.wmConsequenceRule_of_pointwise
      (q₁ := folInfSeq (L := L) 0) (q₂ := .iOr (folInfSeq (L := L)))).sound
      (Mettapedia.Logic.PLNWorldModelFOLInfinitary.pointwise_component_to_iOr
        (F := folInfSeq (L := L)) (n := 0))
      ({S} : Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)

end Mettapedia.Logic.PLNWorldModelInfinitaryRegression
