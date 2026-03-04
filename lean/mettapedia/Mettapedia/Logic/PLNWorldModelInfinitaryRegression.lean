import Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness
import Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness

/-!
# Infinitary WM Regression Fixtures (HOL + FOL)

Concrete theorem-level fixtures exercising the new countable-connective wrappers:

- `iAnd → component` (elimination)
- `component → iOr` (introduction)

for both infinitary HOL and infinitary FOL WM layers.
-/

namespace Mettapedia.Logic.PLNWorldModelInfinitaryRegression

open LO
open LO.FirstOrder
open Mettapedia.Logic.PLNWorldModel

/-! ## HOL fixtures -/

abbrev holInfFalse : Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfQuery Bool :=
  .atom (.comp_not .trivial)

abbrev holInfTrue : Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfQuery Bool :=
  .atom .trivial

def holInfSeq : Nat → Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfQuery Bool
  | 0 => holInfFalse
  | _ => holInfTrue

def holInfFixtureState :
    Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfState Bool :=
  ({⟨true⟩} : Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfState Bool) +
    ({⟨false⟩} : Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfState Bool)

/-- HOL infinitary fixture: conjunction-elimination transport via wrapper API. -/
theorem holInf_iAnd_component_fixture :
    WorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfState Bool)
        (Query := Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfQuery Bool)
        holInfFixtureState (.iAnd holInfSeq) ≤
      WorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfState Bool)
        (Query := Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfQuery Bool)
        holInfFixtureState (holInfSeq 0) := by
  exact
    (Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.wmConsequenceRule_of_pointwise
      (q₁ := .iAnd holInfSeq) (q₂ := holInfSeq 0)).sound
      (Mettapedia.Logic.PLNWorldModelHOLInfinitary.pointwise_iAnd_to_component
        (F := holInfSeq) (n := 0))
      holInfFixtureState

/-- HOL infinitary fixture: disjunction-introduction transport via wrapper API. -/
theorem holInf_component_iOr_fixture :
    WorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfState Bool)
        (Query := Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfQuery Bool)
        holInfFixtureState (holInfSeq 0) ≤
      WorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfState Bool)
        (Query := Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.HOLInfQuery Bool)
        holInfFixtureState (.iOr holInfSeq) := by
  exact
    (Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness.wmConsequenceRule_of_pointwise
      (q₁ := holInfSeq 0) (q₂ := .iOr holInfSeq)).sound
      (Mettapedia.Logic.PLNWorldModelHOLInfinitary.pointwise_component_to_iOr
        (F := holInfSeq) (n := 0))
      holInfFixtureState

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
    WorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)
        (Query := Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfQuery L)
        ({S} : Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)
        (.iAnd (folInfSeq (L := L))) ≤
      WorldModel.queryStrength
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
    WorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)
        (Query := Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfQuery L)
        ({S} : Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness.FOLInfState L)
        (folInfSeq (L := L) 0) ≤
      WorldModel.queryStrength
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

