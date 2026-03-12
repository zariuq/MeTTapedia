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
open Mettapedia.Logic.HOL
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

abbrev HOLFixtureBase := PUnit
abbrev HOLFixtureConst (_ : Ty HOLFixtureBase) := PEmpty

def holFixtureModel :
    HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst :=
  HenkinModel.standard (Base := HOLFixtureBase) (Const := HOLFixtureConst)
    (Carrier := fun _ => PUnit)
    (constDen := by intro τ c; nomatch c)

abbrev holFalseQuery :
    Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLQuery
      (Base := HOLFixtureBase) HOLFixtureConst := .bot
abbrev holTrueQuery :
    Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLQuery
      (Base := HOLFixtureBase) HOLFixtureConst := .top

def holFixtureState :
    Multiset (HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst) :=
  ({holFixtureModel} :
      Multiset (HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst)) +
    ({holFixtureModel} :
      Multiset (HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst))

theorem holFalse_to_true_pointwise :
    ∀ M : HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst,
      Mettapedia.Logic.HOL.WorldModel.holSatisfies
        (Base := HOLFixtureBase) (Const := HOLFixtureConst) M holFalseQuery →
      Mettapedia.Logic.HOL.WorldModel.holSatisfies
        (Base := HOLFixtureBase) (Const := HOLFixtureConst) M holTrueQuery := by
  intro M hFalse
  exact False.elim ((HenkinModel.models_bot M) hFalse)

/-- Ch.8 concrete HOL fixture:
consume the categorical HOL wrapper endpoint on a fixed Bool state/query pair. -/
theorem ch8_hol_categorical_wrapper_bool_fixture
    (H : WMHyper
      (Multiset (HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst)))
    (hcat :
      Mettapedia.Logic.PLNWorldModelHOLCompleteness.WMCategoricalEndpointSurface
        (Base := HOLFixtureBase) (Const := HOLFixtureConst) (H := H))
    {X : H.Obj} (φc : H.query X) :
    WorldModel.queryStrength
        (State := Multiset (HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst))
        (Query := Mettapedia.Logic.HOL.WorldModel.HOLQuery HOLFixtureConst)
        holFixtureState holFalseQuery ≤
      WorldModel.queryStrength
        (State := Multiset (HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst))
        (Query := Mettapedia.Logic.HOL.WorldModel.HOLQuery HOLFixtureConst)
        holFixtureState holTrueQuery := by
  exact
    Mettapedia.Logic.HOL.WorldModelCompleteness.multiset_strength_le_of_pointwise_categorical
      (Base := HOLFixtureBase) (Const := HOLFixtureConst)
      (H := H) (_hcat := hcat) (X := X) (_φc := φc)
      (W := holFixtureState) (φ := holFalseQuery) (ψ := holTrueQuery)
      holFalse_to_true_pointwise

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

/-- Ch.8 concrete FOL fixture (proof-theoretic path):
consume `provable_imp_iff_singletonStrengthLEOnTheory` to obtain provability,
then build and execute a `wmConsequenceRuleOn_of_provable_imp` endpoint on a
singleton state. -/
theorem ch8_fol_provable_bridge_rule_singleton_fixture
    {L : Language.{u}}
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
  let φ : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLQuery L :=
    (⊥ : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLQuery L)
  let ψ : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLQuery L :=
    (⊤ : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLQuery L)
  have hpoint :
      Mettapedia.Logic.PLNWorldModelFOLCompleteness.pointwiseImpliesOnTheory
        T φ ψ := by
    intro S' _hT hφ
    exact (False.elim (by simpa [φ] using hφ))
  have hsing :
      Mettapedia.Logic.PLNWorldModelFOLCompleteness.singletonStrengthLEOnTheory
        T φ ψ :=
    (Mettapedia.Logic.PLNWorldModelFOLCompleteness.pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory
      (T := T) (φ := φ) (ψ := ψ)).1 hpoint
  have hprov : T ⊢ (φ ➝ ψ) :=
    (Mettapedia.Logic.PLNWorldModelFOLCompleteness.provable_imp_iff_singletonStrengthLEOnTheory
      (T := T) (φ := φ) (ψ := ψ)).2 hsing
  let rule :=
    Mettapedia.Logic.PLNWorldModelFOLCompleteness.wmConsequenceRuleOn_of_provable_imp
      (T := T) (φ := φ) (ψ := ψ) hprov
  have hside : rule.side ({S} : Mettapedia.Logic.PLNWorldModelFOLCompleteness.FOLState L) := by
    intro S' hmem
    simp [T]
  simpa [rule, T, φ, ψ] using
    (rule.sound hside)

end Mettapedia.Logic.PLNWorldModelCategoricalRegression
