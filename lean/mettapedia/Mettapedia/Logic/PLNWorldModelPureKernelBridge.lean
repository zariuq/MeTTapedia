import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWorldModelCategoricalBridge
import Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
import Mettapedia.Languages.MeTTa.PureKernel.Inst0BridgeDerived
import Provenance.Util.ValueTypeString

/-!
# PureKernel -> WM Obligation Bridge (A/B/C Aligned)

This module provides an explicit interpretation interface from closed PureKernel
judgments into WM strength obligations, while keeping kernel/profile bridge
contracts explicit.

It does **not** alter PureKernel semantics; it only consumes already-proved
bridge theorems as inputs.

Layering:
- A: executable closed fragment (`PureOpStep`) in `CoreEmbedding`
- B: kernel theory reduction (`Red`)
- C: profile theory closure (`PureProfileTheoryStep`)

This file consumes the canonical A/B/C bridge surface from `CoreEmbedding` and
lands on the same WM obligation surface that the generic formula-side closure
modules package in:
- `OSLFNTTWMBridge`
- `OSLFNTTTheoryClosure`
- `OSLFNTTWMCanonicalClosure`

The two routes are intentionally parallel:
- this file is the PureKernel/DTT-specific producer of WM obligations
- the OSLF/NTT modules are the generic formula/evidence closure route
-/

namespace Mettapedia.Logic.PLNWorldModelPureKernelBridge

open CategoryTheory
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory
open Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped ENNReal

/-- Closed A -> C1 bridge alias from the canonical PureKernel A/B/C surface. -/
abbrev PureClosedOperationalBridge : Prop :=
  ∀ {t u : PureTm 0}, PureOpStep t u →
    PureProfileTheoryStep (quoteClosedTm t) (quoteClosedTm u)

/-- Closed A* -> C1* bridge alias from the canonical PureKernel A/B/C surface. -/
abbrev PureClosedOperationalBridgeStar : Prop :=
  ∀ {t u : PureTm 0}, PureOpStepStar t u →
    PureProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u)

/-- Closed B -> C1 bridge alias from the canonical PureKernel A/B/C surface. -/
abbrev PureClosedTheoryBridge : Prop :=
  ∀ {t u : PureTm 0}, Red t u →
    PureProfileTheoryStep (quoteClosedTm t) (quoteClosedTm u)

/-- Closed B* -> C1* bridge alias from the canonical PureKernel A/B/C surface. -/
abbrev PureClosedTheoryBridgeStar : Prop :=
  ∀ {t u : PureTm 0}, RedStar t u →
    PureProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u)

private theorem defaultBinderName_injective : Function.Injective defaultBinderName := by
  intro a b hab
  rw [← natStringValue_repr a, ← natStringValue_repr b]
  simpa [defaultBinderName, natStringValue] using congrArg natStringValue hab

private theorem defaultBinderName_quoteCompat0 :
    QuoteCompat defaultBinderName 0 emptyEnv :=
  quoteCompat_empty defaultBinderName defaultBinderName_injective 0

/-- Canonical theoremic A -> C1 bridge specialized to the default binder policy. -/
theorem pureClosedOperationalBridge_default :
    PureClosedOperationalBridge :=
  pureOpStep_sound_pureProfileTheoryStep_quoteClosed

/-- Canonical theoremic A* -> C1* bridge specialized to the default binder policy. -/
theorem pureClosedOperationalBridgeStar_default :
    PureClosedOperationalBridgeStar :=
  pureOpStepStar_sound_pureProfileTheoryStep_quoteClosed

/-- Canonical theoremic B -> C1 bridge specialized to the default binder policy. -/
theorem pureClosedTheoryBridge_default :
    PureClosedTheoryBridge :=
  pureTheoryStep_sound_pureProfileTheoryStep_quoteClosed
    inst0OpenBridgeCompat_defaultBinderName
    defaultBinderName_quoteCompat0

/-- Canonical theoremic B* -> C1* bridge specialized to the default binder policy. -/
theorem pureClosedTheoryBridgeStar_default :
    PureClosedTheoryBridgeStar :=
  pureTheoryStepStar_sound_pureProfileTheoryStepStar_quoteClosed
    inst0OpenBridgeCompat_defaultBinderName
    defaultBinderName_quoteCompat0

/-- Default-binder regression wrapper: one nested β binder still transports to C1. -/
theorem betaPi_bridge_regression_one_nestedLam :
    PureProfileTheoryStep
      (quoteClosedTm
        (.app (.lam (.lam (.var (Fin.succ (0 : Fin 1))))) .u0))
      (quoteClosedTm (.lam .u0)) :=
  betaPi_bridge_regression_one_nestedLam_assuming_inst0
    inst0OpenBridgeCompat_defaultBinderName
    defaultBinderName_quoteCompat0

/-- Default-binder regression wrapper: two nested β binders still transport to C1. -/
theorem betaPi_bridge_regression_two_nestedLam :
    PureProfileTheoryStep
      (quoteClosedTm
        (.app (.lam (.lam (.lam (.var (Fin.succ (Fin.succ (0 : Fin 1))))))) .u0))
      (quoteClosedTm (.lam (.lam .u0))) :=
  betaPi_bridge_regression_two_nestedLam_assuming_inst0
    inst0OpenBridgeCompat_defaultBinderName
    defaultBinderName_quoteCompat0

/-- Star bridge is derivable from the one-step bridge by closure induction. -/
theorem pureClosedTheoryBridge_to_star
    (hbridge : PureClosedTheoryBridge) :
    PureClosedTheoryBridgeStar := by
  intro t u hstar
  induction hstar with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih (hbridge hyz)

/-- Local WM strength obligation for a fixed state/query pair. -/
abbrev WMStrengthObligation
    (State Query : Type*) [EvidenceType State] [WorldModel State Query]
    (W : State) (q₁ q₂ : Query) : Prop :=
  WorldModel.queryStrength (State := State) (Query := Query) W q₁ ≤
    WorldModel.queryStrength (State := State) (Query := Query) W q₂

/-- Alias for the unified categorical endpoint surface used by WM wrappers. -/
abbrev WMCategoricalEndpointSurface
    {State : Type*} [EvidenceType State]
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State) : Prop :=
  Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointSurface (H := H)

/-- Explicit interpretation map from Pure/profile judgments into WM obligations.

`encode` maps quoted `Pattern` terms into WM queries.
`profileStep_sound` is the semantic contract: one C1 profile step transports to
the corresponding WM strength inequality under `side` conditions.
-/
structure PureJudgmentWMInterface
    (State Query : Type*) [EvidenceType State] [WorldModel State Query] where
  encode : Pattern → Query
  side : State → Prop := fun _ => True
  profileStep_sound :
    ∀ {W : State} {p q : Pattern},
      side W →
      PureProfileTheoryStep p q →
      WMStrengthObligation State Query W (encode p) (encode q)

namespace PureJudgmentWMInterface

variable {State Query : Type*}
variable [EvidenceType State] [WorldModel State Query]

/-- C1 star closure transports to WM inequalities by transitivity. -/
theorem profileStepStar_sound
    (I : PureJudgmentWMInterface State Query)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstar : PureProfileTheoryStepStar p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) := by
  induction hstar with
  | refl =>
      exact le_rfl
  | tail hxy hyz ih =>
      exact le_trans ih (I.profileStep_sound hW hyz)

end PureJudgmentWMInterface

variable {State Query : Type*}
variable [EvidenceType State] [WorldModel State Query]

/-- One-step closed PureKernel reduction transports to a WM strength obligation,
provided an explicit closed bridge theorem is supplied. -/
theorem pureTheoryStep_to_wmStrengthObligation
    (I : PureJudgmentWMInterface State Query)
    (hbridge : PureClosedTheoryBridge)
    {W : State} {t u : PureTm 0}
    (hW : I.side W)
    (hred : Red t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  I.profileStep_sound hW (hbridge hred)

/-- One-step closed PureKernel reduction transports to a WM strength obligation
through the canonical theoremic B -> C1 bridge. -/
theorem pureTheoryStep_to_wmStrengthObligation_default
    (I : PureJudgmentWMInterface State Query)
    {W : State} {t u : PureTm 0}
    (hW : I.side W)
    (hred : Red t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  pureTheoryStep_to_wmStrengthObligation I pureClosedTheoryBridge_default hW hred

/-- Categorical-aligned wrapper:
same Pure one-step WM obligation transport, with explicit endpoint-surface input. -/
theorem pureTheoryStep_to_wmStrengthObligation_categorical
    (I : PureJudgmentWMInterface State Query)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    (hbridge : PureClosedTheoryBridge)
    {W : State} {t u : PureTm 0}
    (hW : I.side W)
    (hred : Red t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  pureTheoryStep_to_wmStrengthObligation I hbridge hW hred

/-- Categorical-aligned default wrapper using the canonical theoremic B -> C1 bridge. -/
theorem pureTheoryStep_to_wmStrengthObligation_categorical_default
    (I : PureJudgmentWMInterface State Query)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    {W : State} {t u : PureTm 0}
    (hW : I.side W)
    (hred : Red t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  pureTheoryStep_to_wmStrengthObligation_categorical
    (I := I) (H := H) (_hcat := _hcat) (_φc := _φc)
    (hbridge := pureClosedTheoryBridge_default) (W := W) (hW := hW) hred

/-- Star closed PureKernel reduction transports to a WM strength obligation,
using the same one-step closed bridge via closure lifting. -/
theorem pureTheoryStepStar_to_wmStrengthObligation
    (I : PureJudgmentWMInterface State Query)
    (hbridge : PureClosedTheoryBridge)
    {W : State} {t u : PureTm 0}
    (hW : I.side W)
    (hred : RedStar t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) := by
  have hbridgeStar : PureClosedTheoryBridgeStar :=
    pureClosedTheoryBridge_to_star hbridge
  exact
    I.profileStepStar_sound hW (hbridgeStar hred)

/-- Star closed PureKernel reduction transports to a WM strength obligation
through the canonical theoremic B* -> C1* bridge. -/
theorem pureTheoryStepStar_to_wmStrengthObligation_default
    (I : PureJudgmentWMInterface State Query)
    {W : State} {t u : PureTm 0}
    (hW : I.side W)
    (hred : RedStar t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  pureTheoryStepStar_to_wmStrengthObligation I pureClosedTheoryBridge_default hW hred

/-- Categorical-aligned wrapper:
same Pure star WM obligation transport, with explicit endpoint-surface input. -/
theorem pureTheoryStepStar_to_wmStrengthObligation_categorical
    (I : PureJudgmentWMInterface State Query)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    (hbridge : PureClosedTheoryBridge)
    {W : State} {t u : PureTm 0}
    (hW : I.side W)
    (hred : RedStar t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  pureTheoryStepStar_to_wmStrengthObligation I hbridge hW hred

/-- Categorical-aligned default wrapper using the canonical theoremic B* -> C1* bridge. -/
theorem pureTheoryStepStar_to_wmStrengthObligation_categorical_default
    (I : PureJudgmentWMInterface State Query)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    {W : State} {t u : PureTm 0}
    (hW : I.side W)
    (hred : RedStar t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  pureTheoryStepStar_to_wmStrengthObligation_categorical
    (I := I) (H := H) (_hcat := _hcat) (_φc := _φc)
    (hbridge := pureClosedTheoryBridge_default) (W := W) (hW := hW) hred

/-- Package a closed PureKernel one-step as a state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_closed_pureTheoryStep
    (I : PureJudgmentWMInterface State Query)
    (hbridge : PureClosedTheoryBridge)
    {t u : PureTm 0}
    (hred : Red t u) :
    WMConsequenceRuleOn State Query where
  side := I.side
  premise := I.encode (quoteClosedTm t)
  conclusion := I.encode (quoteClosedTm u)
  sound := by
    intro W hW
    exact pureTheoryStep_to_wmStrengthObligation I hbridge hW hred

/-- Package a closed PureKernel one-step as a WM consequence rule using the
canonical theoremic B -> C1 bridge. -/
def wmConsequenceRuleOn_of_closed_pureTheoryStep_default
    (I : PureJudgmentWMInterface State Query)
    {t u : PureTm 0}
    (hred : Red t u) :
    WMConsequenceRuleOn State Query :=
  wmConsequenceRuleOn_of_closed_pureTheoryStep I pureClosedTheoryBridge_default hred

/-- Package a closed PureKernel star reduction as a state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_closed_pureTheoryStepStar
    (I : PureJudgmentWMInterface State Query)
    (hbridge : PureClosedTheoryBridge)
    {t u : PureTm 0}
    (hred : RedStar t u) :
    WMConsequenceRuleOn State Query where
  side := I.side
  premise := I.encode (quoteClosedTm t)
  conclusion := I.encode (quoteClosedTm u)
  sound := by
    intro W hW
    exact pureTheoryStepStar_to_wmStrengthObligation I hbridge hW hred

/-- Package a closed PureKernel star reduction as a WM consequence rule using
the canonical theoremic B* -> C1* bridge. -/
def wmConsequenceRuleOn_of_closed_pureTheoryStepStar_default
    (I : PureJudgmentWMInterface State Query)
    {t u : PureTm 0}
    (hred : RedStar t u) :
    WMConsequenceRuleOn State Query :=
  wmConsequenceRuleOn_of_closed_pureTheoryStepStar I pureClosedTheoryBridge_default hred

/-- Categorical-aligned packaging of a closed PureKernel one-step as a
state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_closed_pureTheoryStep_categorical
    (I : PureJudgmentWMInterface State Query)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    (hbridge : PureClosedTheoryBridge)
    {t u : PureTm 0}
    (hred : Red t u) :
    WMConsequenceRuleOn State Query where
  side := I.side
  premise := I.encode (quoteClosedTm t)
  conclusion := I.encode (quoteClosedTm u)
  sound := by
    intro W hW
    exact
      pureTheoryStep_to_wmStrengthObligation_categorical
        (I := I) (H := H) (_hcat := _hcat) (_φc := _φc)
        (hbridge := hbridge) (W := W) (hW := hW) hred

/-- Categorical-aligned packaging of a closed PureKernel star reduction as a
state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_closed_pureTheoryStepStar_categorical
    (I : PureJudgmentWMInterface State Query)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    (hbridge : PureClosedTheoryBridge)
    {t u : PureTm 0}
    (hred : RedStar t u) :
    WMConsequenceRuleOn State Query where
  side := I.side
  premise := I.encode (quoteClosedTm t)
  conclusion := I.encode (quoteClosedTm u)
  sound := by
    intro W hW
    exact
      pureTheoryStepStar_to_wmStrengthObligation_categorical
        (I := I) (H := H) (_hcat := _hcat) (_φc := _φc)
        (hbridge := hbridge) (W := W) (hW := hW) hred

/-! ## WM-side regression canaries (consume existing PureKernel regressions) -/

/-- Canary: the one-nested-binder beta transport theorem from `CoreEmbedding`
induces a concrete WM obligation witness under the interpretation interface. -/
theorem canary_betaPi_bridge_regression_one_nestedLam_wm
    (I : PureJudgmentWMInterface State Query)
    {W : State}
    (hW : I.side W) :
    ∃ p q : Pattern,
      PureProfileTheoryStep p q ∧
      WMStrengthObligation State Query W (I.encode p) (I.encode q) := by
  let hreg :=
    betaPi_bridge_regression_one_nestedLam
  have hregExists : ∃ p q : Pattern, PureProfileTheoryStep p q := by
    exact ⟨_, _, hreg⟩
  rcases hregExists with ⟨p, q, hstep⟩
  refine ⟨p, q, hstep, ?_⟩
  exact I.profileStep_sound hW hstep

/-- Canary: the two-nested-binder beta transport theorem from `CoreEmbedding`
induces a concrete WM obligation witness under the interpretation interface. -/
theorem canary_betaPi_bridge_regression_two_nestedLam_wm
    (I : PureJudgmentWMInterface State Query)
    {W : State}
    (hW : I.side W) :
    ∃ p q : Pattern,
      PureProfileTheoryStep p q ∧
      WMStrengthObligation State Query W (I.encode p) (I.encode q) := by
  let hreg :=
    betaPi_bridge_regression_two_nestedLam
  have hregExists : ∃ p q : Pattern, PureProfileTheoryStep p q := by
    exact ⟨_, _, hreg⟩
  rcases hregExists with ⟨p, q, hstep⟩
  refine ⟨p, q, hstep, ?_⟩
  exact I.profileStep_sound hW hstep

end Mettapedia.Logic.PLNWorldModelPureKernelBridge
