import Mettapedia.Logic.PLNWorldModelCategoricalBridge
import Mettapedia.Logic.PLNWorldModelHOLCompleteness
import Mettapedia.Logic.PLNWorldModelFOLCompleteness

/-!
# Chapter-8 WM Categorical Regression Fixture

Concrete theorem-level regression fixture instantiating
`institution_beckChevalley_endpoint` on an identity pullback square.
-/

namespace Mettapedia.Logic.PLNWorldModelCategoricalRegression

open CategoryTheory
open LO
open LO.FirstOrder
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelInstitution
open Mettapedia.Logic.EvidenceClass

universe u v x

abbrev WMHyper (State : Type x) [EvidenceType State] :=
  Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine.{u, v, 0, x} State

variable {State : Type x} [EvidenceType State]

/-- Ch.8 concrete fixture: instantiate the unified categorical endpoint on the
identity square at one object. -/
theorem ch8_institution_beckChevalley_endpoint_id_fixture
    (H : WMHyper State)
    {X : H.Obj} (W : State) (φ : H.query X) :
    Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointStatement
      (H := H) (π₁ := 𝟙 X) (π₂ := 𝟙 X) (f := 𝟙 X) (g := 𝟙 X) W φ := by
  simpa using
    (Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine.institution_beckChevalley_endpoint
      (H := H) (P := X) (A := X) (B := X) (D := X)
      (π₁ := 𝟙 X) (π₂ := 𝟙 X) (f := 𝟙 X) (g := 𝟙 X)
      (hpb := CategoryTheory.IsPullback.id_horiz (f := (𝟙 X)))
      (W := W) (φ := φ))

abbrev holBoolFalseQuery :
    Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLQuery Bool := .comp_not .trivial
abbrev holBoolTrueQuery :
    Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLQuery Bool := .trivial

def holBoolFixtureState :
    Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLState Bool :=
  ({⟨true⟩} : Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLState Bool) +
    ({⟨false⟩} : Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLState Bool)

theorem holBoolFalse_to_true_pointwise :
    Mettapedia.Logic.PLNWorldModelHOLCompleteness.pointwiseImplies
      holBoolFalseQuery holBoolTrueQuery := by
  intro pw _h
  simp [Mettapedia.Logic.PLNWorldModelHOL.PointedHOL.satisfies,
    Mettapedia.Logic.HigherOrder.evalPred]

/-- Ch.8 concrete HOL fixture:
consume the categorical HOL wrapper endpoint on a fixed Bool state/query pair. -/
theorem ch8_hol_categorical_wrapper_bool_fixture
    (H : WMHyper (Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLState Bool))
    (hcat :
      Mettapedia.Logic.PLNWorldModelHOLCompleteness.WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (φc : H.query X) :
    WorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLState Bool)
        (Query := Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLQuery Bool)
        holBoolFixtureState holBoolFalseQuery ≤
      WorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLState Bool)
        (Query := Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLQuery Bool)
        holBoolFixtureState holBoolTrueQuery := by
  exact
    Mettapedia.Logic.PLNWorldModelHOLCompleteness.multiset_strength_le_of_pointwise_categorical
      (H := H) (_hcat := hcat) (X := X) (_φc := φc)
      (W := holBoolFixtureState) (q₁ := holBoolFalseQuery) (q₂ := holBoolTrueQuery)
      holBoolFalse_to_true_pointwise

/-- Ch.8 concrete FOL fixture:
`T ⊨ (φ ➝ ψ)` (here `⊥ ➝ ⊤` under empty theory) transported to a WM inequality
on a singleton FOL state via the categorical wrapper endpoint. -/
theorem ch8_fol_categorical_consequence_singleton_fixture
    {L : Language.{u}}
    (H : WMHyper (Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLState L))
    (hcat :
      Mettapedia.Logic.PLNWorldModelFOLCompleteness.WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (φc : H.query X)
    (S : Mettapedia.Logic.PLNWorldModelFOLCompleteness.PointedFOL L) :
    WorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLState L)
        (Query := Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLQuery L)
        ({S} : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLState L)
        (⊥ : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLQuery L) ≤
      WorldModel.queryStrength
        (State := Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLState L)
        (Query := Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLQuery L)
        ({S} : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLState L)
        (⊤ : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLQuery L) := by
  let T : Theory L := (∅ : Theory L)
  have hW :
      Mettapedia.Logic.PLNWorldModelFOLCompleteness.stateModelsTheory T
        ({S} : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLState L) := by
    intro S' hmem
    simp [T]
  have hcons :
      T ⊨ ((⊥ : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLQuery L) ➝
        (⊤ : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLQuery L)) := by
    intro S' hST
    simp
  exact
    Mettapedia.Logic.PLNWorldModelFOLCompleteness.multiset_strength_le_of_consequence_categorical
      (H := H) (_hcat := hcat) (X := X) (_φc := φc)
      (T := T)
      (W := ({S} : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLState L))
      (φ := (⊥ : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLQuery L))
      (ψ := (⊤ : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLQuery L))
      hW hcons

end Mettapedia.Logic.PLNWorldModelCategoricalRegression
