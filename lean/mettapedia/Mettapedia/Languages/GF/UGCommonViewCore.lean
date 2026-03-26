import Mettapedia.Languages.GF.UGCoreFamily
import Mettapedia.Languages.GF.OSLFBridge_handcrafted

/-!
# Common-View UG Core

This file formalizes the second UG-core construction:

- a global universe of possible views on abstract trees;
- each family member supports only some of those views;
- the **common-view core** retains only views supported by every member.

Unlike the family-indexed selected core, this construction becomes **coarser**
as the family grows, because the set of views common to all members shrinks.
-/

namespace Mettapedia.Languages.GF.UGCommonViewCore

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.HandCrafted.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.WorldModelSemantics
open Mettapedia.Languages.GF.UniversalGrammarCore
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open scoped ENNReal

universe u v

/-- A global universe of possible views on abstract trees. -/
structure UGViewUniverse where
  Label : Type
  Obs : Label → Type
  observe : (ℓ : Label) → AbstractNode → Obs ℓ

/-- A view is common to a family iff every family member supports it. -/
def IsCommonView {U : UGViewUniverse} {ι : Type u}
    (supports : ι → U.Label → Prop) (ℓ : U.Label) : Prop :=
  ∀ i, supports i ℓ

/-- Equality at the common-view core: trees agree on every view common to all
family members. -/
def UGCommonViewEq (U : UGViewUniverse) {ι : Type u}
    (supports : ι → U.Label → Prop) (t₁ t₂ : AbstractNode) : Prop :=
  ∀ ℓ, IsCommonView supports ℓ → U.observe ℓ t₁ = U.observe ℓ t₂

theorem UGCommonViewEq.refl (U : UGViewUniverse) {ι : Type u}
    (supports : ι → U.Label → Prop) (t : AbstractNode) :
    UGCommonViewEq U supports t t := by
  intro ℓ hCommon
  rfl

theorem UGCommonViewEq.symm (U : UGViewUniverse) {ι : Type u}
    (supports : ι → U.Label → Prop) {t₁ t₂ : AbstractNode} :
    UGCommonViewEq U supports t₁ t₂ → UGCommonViewEq U supports t₂ t₁ := by
  intro h ℓ hCommon
  exact (h ℓ hCommon).symm

theorem UGCommonViewEq.trans (U : UGViewUniverse) {ι : Type u}
    (supports : ι → U.Label → Prop) {t₁ t₂ t₃ : AbstractNode} :
    UGCommonViewEq U supports t₁ t₂ →
    UGCommonViewEq U supports t₂ t₃ →
    UGCommonViewEq U supports t₁ t₃ := by
  intro h12 h23 ℓ hCommon
  exact (h12 ℓ hCommon).trans (h23 ℓ hCommon)

/-- Setoid induced by the common-view core. -/
def ugCommonViewSetoid (U : UGViewUniverse) {ι : Type u}
    (supports : ι → U.Label → Prop) : Setoid AbstractNode where
  r := UGCommonViewEq U supports
  iseqv := by
    constructor
    · exact UGCommonViewEq.refl U supports
    · exact UGCommonViewEq.symm U supports
    · exact UGCommonViewEq.trans U supports

/-- The quotient by common-view equality supports every common view. -/
def UGViewUniverse.observeOnCommonCore (U : UGViewUniverse) {ι : Type u}
    (supports : ι → U.Label → Prop) (ℓ : U.Label)
    (hCommon : IsCommonView supports ℓ) :
    Quotient (ugCommonViewSetoid U supports) → U.Obs ℓ :=
  Quotient.lift (U.observe ℓ) (by
    intro x y hEq
    exact hEq ℓ hCommon)

theorem UGViewUniverse.observeOnCommonCore_mk (U : UGViewUniverse) {ι : Type u}
    (supports : ι → U.Label → Prop) (ℓ : U.Label)
    (hCommon : IsCommonView supports ℓ) (t : AbstractNode) :
    U.observeOnCommonCore supports ℓ hCommon
      (Quotient.mk (ugCommonViewSetoid U supports) t) = U.observe ℓ t := rfl

/-- An interface preserves the common-view core iff every common view can be
recovered from the interface observation. -/
structure CommonViewPreservingInterface (U : UGViewUniverse) {ι : Type u}
    (supports : ι → U.Label → Prop) (Obs : Type*) where
  observe : AbstractNode → Obs
  recover : ∀ ℓ, IsCommonView supports ℓ →
    ∃ decode : Obs → U.Obs ℓ, ∀ t, U.observe ℓ t = decode (observe t)

theorem CommonViewPreservingInterface.obsEq_implies_commonCoreEq
    {U : UGViewUniverse} {ι : Type u} {Obs : Type*}
    {supports : ι → U.Label → Prop}
    (I : CommonViewPreservingInterface U supports Obs)
    {t₁ t₂ : AbstractNode} :
    I.observe t₁ = I.observe t₂ → UGCommonViewEq U supports t₁ t₂ := by
  intro hObs ℓ hCommon
  rcases I.recover ℓ hCommon with ⟨decode, hdecode⟩
  rw [hdecode t₁, hdecode t₂, hObs]

/-- Weakest-core theorem for the common-view construction. -/
def CommonViewPreservingInterface.quotientMap
    {U : UGViewUniverse} {ι : Type u} {Obs : Type*}
    {supports : ι → U.Label → Prop}
    (I : CommonViewPreservingInterface U supports Obs) :
    Quotient (obsSetoid I.observe) → Quotient (ugCommonViewSetoid U supports) :=
  Quotient.lift
    (fun t => Quotient.mk (ugCommonViewSetoid U supports) t)
    (by
      intro t₁ t₂ hEq
      exact Quotient.sound (I.obsEq_implies_commonCoreEq hEq))

theorem CommonViewPreservingInterface.quotientMap_surjective
    {U : UGViewUniverse} {ι : Type u} {Obs : Type*}
    {supports : ι → U.Label → Prop}
    (I : CommonViewPreservingInterface U supports Obs) :
    Function.Surjective I.quotientMap := by
  intro q
  refine Quotient.inductionOn q ?_
  intro t
  exact ⟨Quotient.mk (obsSetoid I.observe) t, rfl⟩

theorem UGCommonViewEq_is_weakest
    (U : UGViewUniverse) {ι : Type u} (supports : ι → U.Label → Prop)
    {Obs : Type*}
    (I : CommonViewPreservingInterface U supports Obs) :
    ∃ π : Quotient (obsSetoid I.observe) → Quotient (ugCommonViewSetoid U supports),
      Function.Surjective π := by
  exact ⟨I.quotientMap, I.quotientMap_surjective⟩

/-! ## Family growth: larger families yield coarser common-view cores -/

/-- If `small` embeds into `large`, every view common to `large` is also common
to `small`. -/
theorem commonView_of_familyGrowth
    {U : UGViewUniverse} {α : Type u} {β : Type v}
    {supportsSmall : α → U.Label → Prop}
    {supportsLarge : β → U.Label → Prop}
    (embed : α → β)
    (hEmbed : ∀ a ℓ, supportsSmall a ℓ ↔ supportsLarge (embed a) ℓ) :
    ∀ ℓ, IsCommonView supportsLarge ℓ → IsCommonView supportsSmall ℓ := by
  intro ℓ hLarge a
  exact (hEmbed a ℓ).2 (hLarge (embed a))

/-- Equality at the smaller-family common-view core implies equality at the
larger-family common-view core. This is the formal ``coarser as family grows''
theorem. -/
theorem UGCommonViewEq.of_familyGrowth
    {U : UGViewUniverse} {α : Type u} {β : Type v}
    {supportsSmall : α → U.Label → Prop}
    {supportsLarge : β → U.Label → Prop}
    (embed : α → β)
    (hEmbed : ∀ a ℓ, supportsSmall a ℓ ↔ supportsLarge (embed a) ℓ)
    {t₁ t₂ : AbstractNode} :
    UGCommonViewEq U supportsSmall t₁ t₂ →
    UGCommonViewEq U supportsLarge t₁ t₂ := by
  intro hSmall ℓ hLarge
  exact hSmall ℓ (commonView_of_familyGrowth embed hEmbed ℓ hLarge)

/-- Canonical quotient map from the smaller-family common-view quotient to the
larger-family common-view quotient. -/
def quotientMap_of_familyGrowth
    {U : UGViewUniverse} {α : Type u} {β : Type v}
    {supportsSmall : α → U.Label → Prop}
    {supportsLarge : β → U.Label → Prop}
    (embed : α → β)
    (hEmbed : ∀ a ℓ, supportsSmall a ℓ ↔ supportsLarge (embed a) ℓ) :
    Quotient (ugCommonViewSetoid U supportsSmall) →
      Quotient (ugCommonViewSetoid U supportsLarge) :=
  Quotient.lift
    (fun t => Quotient.mk (ugCommonViewSetoid U supportsLarge) t)
    (by
      intro t₁ t₂ hEq
      exact Quotient.sound (UGCommonViewEq.of_familyGrowth embed hEmbed hEq))

theorem quotientMap_of_familyGrowth_surjective
    {U : UGViewUniverse} {α : Type u} {β : Type v}
    {supportsSmall : α → U.Label → Prop}
    {supportsLarge : β → U.Label → Prop}
    (embed : α → β)
    (hEmbed : ∀ a ℓ, supportsSmall a ℓ ↔ supportsLarge (embed a) ℓ) :
    Function.Surjective (quotientMap_of_familyGrowth embed hEmbed) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro t
  exact ⟨Quotient.mk (ugCommonViewSetoid U supportsSmall) t, rfl⟩

/-! ## Concrete English/Czech common-view support example -/

section EnglishCzechViews

variable {State : Type u} [EvidenceType State] [BinaryWorldModel State Pattern]

inductive EnglishCzechViewLabel where
  | sharedPattern
  | evidence
  | strength
  | englishHouseSem
  | czechHouseSem
  deriving DecidableEq

inductive EnglishCzechMember where
  | english
  | czech
  deriving DecidableEq

/-- Global view universe built from actual GF/WM artifacts:

- semantic core pattern view;
- world-model evidence;
- world-model strength;
- an English-specific OSLF witness view;
- a Czech-specific OSLF witness view.
-/
noncomputable def englishCzechViewUniverse (W : State) : UGViewUniverse where
  Label := EnglishCzechViewLabel
  Obs
    | .sharedPattern => Pattern
    | .evidence => BinaryEvidence
    | .strength => ℝ≥0∞
    | .englishHouseSem => Prop
    | .czechHouseSem => Prop
  observe
    | .sharedPattern => gfAbstractToPattern
    | .evidence => gfEvidenceDenote W
    | .strength => fun t => BinaryWorldModel.queryStrength W (gfAbstractToPattern t)
    | .englishHouseSem => fun t =>
        sem (langReduces englishGFLanguageDef) (gfAtomSem_isName "house")
          (.dia (.atom "is_house")) (gfAbstractToPattern t)
    | .czechHouseSem => fun t =>
        sem (langReduces czechGFLanguageDef) (gfAtomSem_isName "house")
          (.dia (.atom "is_house")) (gfAbstractToPattern t)

/-- Support profile for the singleton English family. Every view English can
interpret is common at this stage, including the English-only semantic view. -/
def englishSingletonSupports : Unit → EnglishCzechViewLabel → Prop
  | (), .sharedPattern => True
  | (), .evidence => True
  | (), .strength => True
  | (), .englishHouseSem => True
  | (), .czechHouseSem => False

/-- Support profile for the English+Czech family. Only the genuinely shared
views remain common across both members. -/
def englishCzechSupports : EnglishCzechMember → EnglishCzechViewLabel → Prop
  | .english, .sharedPattern => True
  | .english, .evidence => True
  | .english, .strength => True
  | .english, .englishHouseSem => True
  | .english, .czechHouseSem => False
  | .czech, .sharedPattern => True
  | .czech, .evidence => True
  | .czech, .strength => True
  | .czech, .englishHouseSem => False
  | .czech, .czechHouseSem => True

/-- The English-only semantic view is real: it distinguishes the same concrete
pair used in the family-indexed nontriviality witness. -/
theorem englishHouseSem_separates_useNHouse_bareHouse (W : State) :
    let U := englishCzechViewUniverse W
    U.observe .englishHouseSem Mettapedia.Languages.GF.UGCoreFamily.useNHouseTree ≠
      U.observe .englishHouseSem Mettapedia.Languages.GF.UGCoreFamily.bareHouseTree := by
  dsimp [englishCzechViewUniverse]
  intro hEq
  have hPos :
      sem (langReduces englishGFLanguageDef) (gfAtomSem_isName "house")
        (.dia (.atom "is_house"))
        (gfAbstractToPattern Mettapedia.Languages.GF.UGCoreFamily.useNHouseTree) :=
    Mettapedia.Languages.GF.UGCoreFamily.english_useNHouse_dia_is_house
  have hTransferred :
      sem (langReduces englishGFLanguageDef) (gfAtomSem_isName "house")
        (.dia (.atom "is_house"))
        (gfAbstractToPattern Mettapedia.Languages.GF.UGCoreFamily.bareHouseTree) := by
    rwa [hEq] at hPos
  exact Mettapedia.Languages.GF.UGCoreFamily.english_bareHouse_not_dia_is_house hTransferred

private theorem englishSingleton_sharedPattern_common (W : State) :
    IsCommonView (U := englishCzechViewUniverse W)
      englishSingletonSupports EnglishCzechViewLabel.sharedPattern := by
  intro i
  cases i
  simp [englishSingletonSupports]

private theorem englishCzech_sharedPattern_common (W : State) :
    IsCommonView (U := englishCzechViewUniverse W)
      englishCzechSupports EnglishCzechViewLabel.sharedPattern := by
  intro i
  cases i <;> simp [englishCzechSupports]

/-- In the singleton-English support profile, every common view already factors
through the shared semantic core because `.sharedPattern` is itself common. -/
theorem semanticCoreEq_implies_englishSingletonCommonViewEq
    (W : State) {t₁ t₂ : AbstractNode}
    (hCore : semanticCore.observe t₁ = semanticCore.observe t₂) :
    UGCommonViewEq (englishCzechViewUniverse W) englishSingletonSupports t₁ t₂ := by
  intro ℓ hCommon
  cases ℓ with
  | sharedPattern =>
      simpa [englishCzechViewUniverse, semanticCore] using hCore
  | evidence =>
      simpa [englishCzechViewUniverse] using
        (semanticCoreEq_implies_evidenceAgreement (State := State) hCore W)
  | strength =>
      simpa [englishCzechViewUniverse] using
        (semanticCoreEq_implies_strengthAgreement (State := State) hCore W)
  | englishHouseSem =>
      have hPat : gfAbstractToPattern t₁ = gfAbstractToPattern t₂ := by
        simpa [semanticCore] using hCore
      simpa [englishCzechViewUniverse] using
        congrArg
          (fun p =>
            sem (langReduces englishGFLanguageDef) (gfAtomSem_isName "house")
              (.dia (.atom "is_house")) p)
          hPat
  | czechHouseSem =>
      have hFalse : False := by
        have := hCommon ()
        simp [englishSingletonSupports] at this
      exact False.elim hFalse

/-- In the current English+Czech support profile, common-view equality is
already exactly semantic-core equality: the only common views are
pattern/evidence/strength, all of which factor through `gfAbstractToPattern`. -/
theorem semanticCoreEq_implies_englishCzechCommonViewEq
    (W : State) {t₁ t₂ : AbstractNode}
    (hCore : semanticCore.observe t₁ = semanticCore.observe t₂) :
    UGCommonViewEq (englishCzechViewUniverse W) englishCzechSupports t₁ t₂ := by
  intro ℓ hCommon
  cases ℓ with
  | sharedPattern =>
      simpa [englishCzechViewUniverse, semanticCore] using hCore
  | evidence =>
      simpa [englishCzechViewUniverse] using
        (semanticCoreEq_implies_evidenceAgreement (State := State) hCore W)
  | strength =>
      simpa [englishCzechViewUniverse] using
        (semanticCoreEq_implies_strengthAgreement (State := State) hCore W)
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

/-- The singleton-English common-view core is equivalent to semantic-core
equality. -/
theorem englishSingleton_commonView_eq_semanticCore
    (W : State) {t₁ t₂ : AbstractNode} :
    UGCommonViewEq (englishCzechViewUniverse W) englishSingletonSupports t₁ t₂ ↔
      semanticCore.observe t₁ = semanticCore.observe t₂ := by
  constructor
  · intro hCommon
    exact hCommon .sharedPattern (englishSingleton_sharedPattern_common W)
  · exact semanticCoreEq_implies_englishSingletonCommonViewEq W

/-- The current English+Czech common-view core is also equivalent to
semantic-core equality. This sharpens the earlier quotient-map result:
for the present view universe, adding Czech does not strictly coarsen the
common-view relation at all. -/
theorem englishCzech_commonView_eq_semanticCore
    (W : State) {t₁ t₂ : AbstractNode} :
    UGCommonViewEq (englishCzechViewUniverse W) englishCzechSupports t₁ t₂ ↔
      semanticCore.observe t₁ = semanticCore.observe t₂ := by
  constructor
  · intro hCommon
    exact hCommon .sharedPattern (englishCzech_sharedPattern_common W)
  · exact semanticCoreEq_implies_englishCzechCommonViewEq W

/-- Consequently, the English-only and English+Czech common-view relations are
extensionally identical for the current view universe. -/
theorem englishSingleton_commonView_eq_englishCzech_commonView
    (W : State) {t₁ t₂ : AbstractNode} :
    UGCommonViewEq (englishCzechViewUniverse W) englishSingletonSupports t₁ t₂ ↔
      UGCommonViewEq (englishCzechViewUniverse W) englishCzechSupports t₁ t₂ := by
  rw [englishSingleton_commonView_eq_semanticCore,
    englishCzech_commonView_eq_semanticCore]

/-- Adding Czech removes the English-only semantic view from the set of views
common to all family members, so the common-view quotient becomes coarser. -/
theorem EnglishCzech_commonView_core_coarsens
    (W : State) :
    ∃ π :
      Quotient (ugCommonViewSetoid (englishCzechViewUniverse W) englishSingletonSupports) →
        Quotient (ugCommonViewSetoid (englishCzechViewUniverse W) englishCzechSupports),
      Function.Surjective π := by
  let embed : Unit → EnglishCzechMember := fun _ => .english
  refine ⟨quotientMap_of_familyGrowth embed ?_, quotientMap_of_familyGrowth_surjective embed ?_⟩
  · intro a ℓ
    cases a
    cases ℓ <;> simp [embed, englishSingletonSupports, englishCzechSupports]
  · intro a ℓ
    cases a
    cases ℓ <;> simp [embed, englishSingletonSupports, englishCzechSupports]

end EnglishCzechViews

end Mettapedia.Languages.GF.UGCommonViewCore
