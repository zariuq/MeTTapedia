import Mettapedia.Languages.GF.UGCommonViewCore

/-!
# Bridge Between Selected-Core and Common-View UG Cores

This file compares the two UG-core constructions.

The abstract theorem states that if a family-indexed selected signature and a
common-view universe cover each other on the nose, then they induce the same
quotient relation on abstract trees.

We then instantiate this for the real English/Czech shared views
(pattern/evidence/strength) extracted from `UGCommonViewCore.lean`.
-/

namespace Mettapedia.Languages.GF.UGCoreBridge

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.UGCoreSelected
open Mettapedia.Languages.GF.UGCoreFamily
open Mettapedia.Languages.GF.UGCommonViewCore
open Mettapedia.Languages.GF.WorldModelSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open scoped ENNReal

universe u v

/-- A comparison witness between a family-indexed selected core and a
common-view core. Every member-selected view comes from a common global view,
and every common global view comes from some member-selected view. -/
structure UGCoreBridgeWitness
    {ι : Type u} (fam : ι → UGSignature)
    (U : UGViewUniverse) (supports : ι → U.Label → Prop) where
  member_to_common : ∀ i (ℓi : (fam i).Label),
    ∃ ℓ, IsCommonView supports ℓ ∧
      ∃ e : (fam i).Obs ℓi ≃ U.Obs ℓ,
        ∀ t, e ((fam i).observe ℓi t) = U.observe ℓ t
  common_to_member : ∀ ℓ, IsCommonView supports ℓ →
    ∃ i, ∃ ℓi : (fam i).Label, ∃ e : U.Obs ℓ ≃ (fam i).Obs ℓi,
      ∀ t, e (U.observe ℓ t) = (fam i).observe ℓi t

theorem familyEq_implies_commonEq
    {ι : Type u} {fam : ι → UGSignature}
    {U : UGViewUniverse} {supports : ι → U.Label → Prop}
    (hBridge : UGCoreBridgeWitness fam U supports)
    {t₁ t₂ : AbstractNode} :
    UGFamilyCoreEq fam t₁ t₂ → UGCommonViewEq U supports t₁ t₂ := by
  intro hFam ℓ hCommon
  rcases hBridge.common_to_member ℓ hCommon with ⟨i, ℓi, e, hObs⟩
  apply e.injective
  rw [hObs t₁, hObs t₂]
  exact (hFam i) ℓi

theorem commonEq_implies_familyEq
    {ι : Type u} {fam : ι → UGSignature}
    {U : UGViewUniverse} {supports : ι → U.Label → Prop}
    (hBridge : UGCoreBridgeWitness fam U supports)
    {t₁ t₂ : AbstractNode} :
    UGCommonViewEq U supports t₁ t₂ → UGFamilyCoreEq fam t₁ t₂ := by
  intro hCommon i ℓi
  rcases hBridge.member_to_common i ℓi with ⟨ℓ, hIsCommon, e, hObs⟩
  apply e.injective
  rw [hObs t₁, hObs t₂]
  exact hCommon ℓ hIsCommon

theorem familyEq_iff_commonEq
    {ι : Type u} {fam : ι → UGSignature}
    {U : UGViewUniverse} {supports : ι → U.Label → Prop}
    (hBridge : UGCoreBridgeWitness fam U supports)
    {t₁ t₂ : AbstractNode} :
    UGFamilyCoreEq fam t₁ t₂ ↔ UGCommonViewEq U supports t₁ t₂ := by
  constructor
  · exact familyEq_implies_commonEq hBridge
  · exact commonEq_implies_familyEq hBridge

section EnglishCzechShared

variable {State : Type u} [EvidenceType State] [BinaryWorldModel State Pattern]

inductive EnglishCzechSharedLabel where
  | sharedPattern
  | evidence
  | strength
  deriving DecidableEq

/-- The genuinely shared selected views for the current English/Czech stack. -/
noncomputable def englishCzechSharedSelectedSignature (W : State) : UGSignature where
  Label := EnglishCzechSharedLabel
  Obs
    | .sharedPattern => Pattern
    | .evidence => BinaryEvidence
    | .strength => ℝ≥0∞
  observe
    | .sharedPattern => gfAbstractToPattern
    | .evidence => gfEvidenceDenote W
    | .strength => fun t => BinaryWorldModel.queryStrength W (gfAbstractToPattern t)

/-- Family of shared selected signatures: both English and Czech demand the same
shared invariant package. -/
noncomputable def englishCzechSharedFamily (W : State) :
    EnglishCzechMember → UGSignature :=
  fun _ => englishCzechSharedSelectedSignature W

private theorem sharedPattern_is_common (W : State) :
    IsCommonView (U := englishCzechViewUniverse W)
      englishCzechSupports EnglishCzechViewLabel.sharedPattern := by
  intro i
  cases i <;> simp [englishCzechSupports]

private theorem evidence_is_common (W : State) :
    IsCommonView (U := englishCzechViewUniverse W)
      englishCzechSupports EnglishCzechViewLabel.evidence := by
  intro i
  cases i <;> simp [englishCzechSupports]

private theorem strength_is_common (W : State) :
    IsCommonView (U := englishCzechViewUniverse W)
      englishCzechSupports EnglishCzechViewLabel.strength := by
  intro i
  cases i <;> simp [englishCzechSupports]

/-- The real English/Czech common-view universe and the selected shared-family
core coincide on the shared views pattern/evidence/strength. -/
noncomputable def englishCzechSharedBridge (W : State) :
    UGCoreBridgeWitness (englishCzechSharedFamily W)
      (englishCzechViewUniverse W) englishCzechSupports where
  member_to_common i ℓi := by
    cases i
    case english =>
      cases ℓi with
      | sharedPattern =>
          exact ⟨.sharedPattern, sharedPattern_is_common W, Equiv.refl _, by intro t; rfl⟩
      | evidence =>
          exact ⟨.evidence, evidence_is_common W, Equiv.refl _, by intro t; rfl⟩
      | strength =>
          exact ⟨.strength, strength_is_common W, Equiv.refl _, by intro t; rfl⟩
    case czech =>
      cases ℓi with
      | sharedPattern =>
          exact ⟨.sharedPattern, sharedPattern_is_common W, Equiv.refl _, by intro t; rfl⟩
      | evidence =>
          exact ⟨.evidence, evidence_is_common W, Equiv.refl _, by intro t; rfl⟩
      | strength =>
          exact ⟨.strength, strength_is_common W, Equiv.refl _, by intro t; rfl⟩
  common_to_member ℓ hCommon := by
    cases ℓ with
    | sharedPattern =>
        exact ⟨.english, .sharedPattern, Equiv.refl _, by intro t; rfl⟩
    | evidence =>
        exact ⟨.english, .evidence, Equiv.refl _, by intro t; rfl⟩
    | strength =>
        exact ⟨.english, .strength, Equiv.refl _, by intro t; rfl⟩
    | englishHouseSem =>
        have hFalse : False := by
          have := hCommon .czech
          simp [englishCzechSupports] at this
        exact False.elim hFalse
    | czechHouseSem =>
        have hFalse : False := by
          have := hCommon .english
          simp [englishCzechSupports] at this
        exact False.elim hFalse

theorem EnglishCzech_shared_selected_eq_commonView
    (W : State) {t₁ t₂ : AbstractNode} :
    UGFamilyCoreEq (englishCzechSharedFamily W) t₁ t₂ ↔
      UGCommonViewEq (englishCzechViewUniverse W) englishCzechSupports t₁ t₂ := by
  exact familyEq_iff_commonEq (englishCzechSharedBridge W)

/-- On the actual shared English/Czech profile, both the selected-core and the
common-view construction collapse to semantic-core equality. -/
theorem EnglishCzech_shared_selected_eq_semanticCore
    (W : State) {t₁ t₂ : AbstractNode} :
    UGFamilyCoreEq (englishCzechSharedFamily W) t₁ t₂ ↔
      UniversalGrammarCore.semanticCore.observe t₁ =
        UniversalGrammarCore.semanticCore.observe t₂ := by
  rw [EnglishCzech_shared_selected_eq_commonView,
    englishCzech_commonView_eq_semanticCore]

end EnglishCzechShared

end Mettapedia.Languages.GF.UGCoreBridge
