import Mettapedia.PLN.WorldModel.PLNWorldModelCalculus
import Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.CoreEmbedding
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.Inst0BridgeDerived
import Provenance.Util.ValueTypeString

/-!
# TwoSortPiSigmaId -> WM Obligation Bridge (A/B/C Aligned)

This module provides an explicit interpretation interface from closed TwoSortPiSigmaId
judgments into WM strength obligations, while keeping kernel/profile bridge
contracts explicit.

It does **not** alter TwoSortPiSigmaId semantics; it only consumes already-proved
bridge theorems as inputs.

Layering:
- A: executable closed fragment (`TwoSortOpStep`) in `CoreEmbedding`
- B: kernel theory reduction (`Red`)
- C: profile theory closure (`TwoSortProfileTheoryStep`)

This file consumes the canonical A/B/C bridge interface from `CoreEmbedding` and
lands on the same WM obligation interface that the generic formula-side closure
modules package in:
- `OSLFNTTWMBridge`
- `OSLFNTTTheoryClosure`
- `OSLFNTTWMCanonicalClosure`

The two routes are intentionally parallel:
- this file is the TwoSortPiSigmaId/DTT-specific producer of WM obligations
- the OSLF/NTT modules are the generic formula/evidence closure route
-/

namespace Mettapedia.PLN.Bridges.Languages.WorldModel.PLNWorldModelTwoSortBridge

open CategoryTheory
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.ProfileTheory
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.CoreEmbedding
open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped ENNReal

/-- Closed A -> C1 bridge alias from the canonical TwoSortPiSigmaId A/B/C interface. -/
abbrev TwoSortClosedOperationalBridge : Prop :=
  ∀ {t u : ScopedTerm 0}, TwoSortOpStep t u →
    TwoSortProfileTheoryStep (quoteClosedTm t) (quoteClosedTm u)

/-- Closed A* -> C1* bridge alias from the canonical TwoSortPiSigmaId A/B/C interface. -/
abbrev TwoSortClosedOperationalBridgeStar : Prop :=
  ∀ {t u : ScopedTerm 0}, TwoSortOpStepStar t u →
    TwoSortProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u)

/-- Closed B -> C1 bridge alias from the canonical TwoSortPiSigmaId A/B/C interface. -/
abbrev TwoSortClosedTheoryBridge : Prop :=
  ∀ {t u : ScopedTerm 0}, Red t u →
    TwoSortProfileTheoryStep (quoteClosedTm t) (quoteClosedTm u)

/-- Closed B* -> C1* bridge alias from the canonical TwoSortPiSigmaId A/B/C interface. -/
abbrev TwoSortClosedTheoryBridgeStar : Prop :=
  ∀ {t u : ScopedTerm 0}, RedStar t u →
    TwoSortProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u)

private theorem defaultBinderName_injective : Function.Injective defaultBinderName := by
  intro a b hab
  rw [← natStringValue_repr a, ← natStringValue_repr b]
  simpa [defaultBinderName, natStringValue, parseDigits, digitNat] using congrArg natStringValue hab

private theorem defaultBinderName_quoteCompat0 :
    QuoteCompat defaultBinderName 0 emptyEnv :=
  quoteCompat_empty defaultBinderName defaultBinderName_injective 0

/-- Canonical theoremic A -> C1 bridge specialized to the default binder policy. -/
theorem twoSortClosedOperationalBridge_default :
    TwoSortClosedOperationalBridge :=
  twoSortOpStep_sound_twoSortProfileTheoryStep_quoteClosed

/-- Canonical theoremic A* -> C1* bridge specialized to the default binder policy. -/
theorem twoSortClosedOperationalBridgeStar_default :
    TwoSortClosedOperationalBridgeStar :=
  twoSortOpStepStar_sound_twoSortProfileTheoryStep_quoteClosed

/-- Canonical theoremic B -> C1 bridge specialized to the default binder policy. -/
theorem twoSortClosedTheoryBridge_default :
    TwoSortClosedTheoryBridge :=
  twoSortTheoryStep_sound_twoSortProfileTheoryStep_quoteClosed
    inst0OpenBridgeCompat_defaultBinderName
    defaultBinderName_quoteCompat0

/-- Canonical theoremic B* -> C1* bridge specialized to the default binder policy. -/
theorem twoSortClosedTheoryBridgeStar_default :
    TwoSortClosedTheoryBridgeStar :=
  twoSortTheoryStepStar_sound_twoSortProfileTheoryStepStar_quoteClosed
    inst0OpenBridgeCompat_defaultBinderName
    defaultBinderName_quoteCompat0

/-- Default-binder regression wrapper: one nested β binder still transports to C1. -/
theorem betaPi_bridge_regression_one_nestedLam :
    TwoSortProfileTheoryStep
      (quoteClosedTm
        (.app (.lam (.lam (.var (Fin.succ (0 : Fin 1))))) .u0))
      (quoteClosedTm (.lam .u0)) :=
  betaPi_bridge_regression_one_nestedLam_assuming_inst0
    inst0OpenBridgeCompat_defaultBinderName
    defaultBinderName_quoteCompat0

/-- Default-binder regression wrapper: two nested β binders still transport to C1. -/
theorem betaPi_bridge_regression_two_nestedLam :
    TwoSortProfileTheoryStep
      (quoteClosedTm
        (.app (.lam (.lam (.lam (.var (Fin.succ (Fin.succ (0 : Fin 1))))))) .u0))
      (quoteClosedTm (.lam (.lam .u0))) :=
  betaPi_bridge_regression_two_nestedLam_assuming_inst0
    inst0OpenBridgeCompat_defaultBinderName
    defaultBinderName_quoteCompat0

/-- Star bridge is derivable from the one-step bridge by closure induction. -/
theorem twoSortClosedTheoryBridge_to_star
    (hbridge : TwoSortClosedTheoryBridge) :
    TwoSortClosedTheoryBridgeStar := by
  intro t u hstar
  induction hstar with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih (hbridge hyz)

/-- Local WM strength obligation for a fixed state/query pair. -/
abbrev WMStrengthObligation
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query]
    (W : State) (q₁ q₂ : Query) : Prop :=
  BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₁ ≤
    BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₂

/-- Alias for the unified categorical endpoint contract used by WM wrappers. -/
abbrev WMCategoricalEndpointContract
    {State : Type*} [EvidenceType State]
    (H : Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine.WMHyperdoctrine State) : Prop :=
  Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointContract (H := H)

/-- Explicit interpretation map from Pure/profile judgments into WM obligations.

`encode` maps quoted `Pattern` terms into WM queries.
`profileStep_sound` is the semantic contract: one C1 profile step transports to
the corresponding WM strength inequality under `side` conditions.
-/
structure TwoSortJudgmentWMInterface
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query] where
  encode : Pattern → Query
  side : State → Prop := fun _ => True
  profileStep_sound :
    ∀ {W : State} {p q : Pattern},
      side W →
      TwoSortProfileTheoryStep p q →
      WMStrengthObligation State Query W (encode p) (encode q)

namespace TwoSortJudgmentWMInterface

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- C1 star closure transports to WM inequalities by transitivity. -/
theorem profileStepStar_sound
    (I : TwoSortJudgmentWMInterface State Query)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstar : TwoSortProfileTheoryStepStar p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) := by
  induction hstar with
  | refl =>
      exact le_rfl
  | tail hxy hyz ih =>
      exact le_trans ih (I.profileStep_sound hW hyz)

end TwoSortJudgmentWMInterface

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- One-step closed TwoSortPiSigmaId reduction transports to a WM strength obligation,
provided an explicit closed bridge theorem is supplied. -/
theorem pureTheoryStep_to_wmStrengthObligation
    (I : TwoSortJudgmentWMInterface State Query)
    (hbridge : TwoSortClosedTheoryBridge)
    {W : State} {t u : ScopedTerm 0}
    (hW : I.side W)
    (hred : Red t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  I.profileStep_sound hW (hbridge hred)

/-- One-step closed TwoSortPiSigmaId reduction transports to a WM strength obligation
through the canonical theoremic B -> C1 bridge. -/
theorem twoSortTheoryStep_to_wmStrengthObligation_default
    (I : TwoSortJudgmentWMInterface State Query)
    {W : State} {t u : ScopedTerm 0}
    (hW : I.side W)
    (hred : Red t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  pureTheoryStep_to_wmStrengthObligation I twoSortClosedTheoryBridge_default hW hred

/-- Closed declaration-aware multi-step reduction on the strongest
assumption-free slice transports all the way to the WM-strength endpoint.

This is the canonical no-values declaration-side bridge for downstream WM
consumers: ordered checked specs, no declaration values, and the existing
quoted Pure-profile bridge. It intentionally stays off the value-bearing delta
frontier. -/
theorem checkedNoValuesDeclKernelStar_to_wmStrengthObligation_default
    (I : TwoSortJudgmentWMInterface State Query)
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    (hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {W : State} {t u : ScopedTerm 0}
    (hW : I.side W)
    (hred :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.RedStarDecl
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs) t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) := by
  have hprofile :
      TwoSortProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u) :=
    checkedNoValuesDeclKernel_star_sound_twoSortProfileTheoryStepStar_quoteClosed
      hSig hNone inst0OpenBridgeCompat_defaultBinderName defaultBinderName_quoteCompat0 hred
  exact I.profileStepStar_sound hW hprofile

/-- Packaged no-values declaration-side closed subject reduction plus the WM
endpoint obligation.

This is the strongest fully discharged declaration-aware endpoint theorem
available today without crossing into value-bearing delta reasoning. -/
theorem checkedNoValuesDeclKernelBoundary_closedSubjectReduction_and_wmBridge
    (I : TwoSortJudgmentWMInterface State Query)
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    {hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs}
    {hNone : ∀ s ∈ specs, s.value? = none}
    (hBoundary :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Assembly.CheckedNoValuesDeclKernelBoundary
        hSig hNone)
    {W : State} (hW : I.side W)
    {t u A : ScopedTerm 0}
    (ht :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.HasTypeDecl
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs) .nil t A)
    (hred :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.RedStarDecl
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs) t u) :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.HasTypeDecl
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs) .nil u A ∧
      WMStrengthObligation State Query W
        (I.encode (quoteClosedTm t))
        (I.encode (quoteClosedTm u)) := by
  exact
    ⟨ hBoundary.starSubjectReduction ht hred
    , checkedNoValuesDeclKernelStar_to_wmStrengthObligation_default
        I hSig hNone hW hred
    ⟩

/-- Closed declaration conversion on the strongest assumption-free slice yields
an explicit quoted common reduct that both endpoints strengthen to in the WM
interface.

This packages the no-values refinement into the same endpoint shape used by the
generic closed Pure bridge, while keeping the value-bearing delta case honest
and separate. -/
theorem checkedNoValuesDeclKernelBoundary_closedCommonReduct_wmBridge
    (I : TwoSortJudgmentWMInterface State Query)
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    {hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs}
    {hNone : ∀ s ∈ specs, s.value? = none}
    (hBoundary :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Assembly.CheckedNoValuesDeclKernelBoundary
        hSig hNone)
    {W : State} (hW : I.side W)
    {t u : ScopedTerm 0}
    (hconv :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.ConvDecl
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs) t u) :
    ∃ w : ScopedTerm 0,
      WMStrengthObligation State Query W
        (I.encode (quoteClosedTm t))
        (I.encode (quoteClosedTm w)) ∧
      WMStrengthObligation State Query W
        (I.encode (quoteClosedTm u))
        (I.encode (quoteClosedTm w)) := by
  rcases hBoundary.commonReduct hconv with ⟨w, htw, huw⟩
  exact
    ⟨ w
    , checkedNoValuesDeclKernelStar_to_wmStrengthObligation_default
        I hSig hNone hW htw
    , checkedNoValuesDeclKernelStar_to_wmStrengthObligation_default
        I hSig hNone hW huw
    ⟩

/-- Categorical-aligned wrapper:
same Pure one-step WM obligation transport, with explicit endpoint-interface input. -/
theorem pureTheoryStep_to_wmStrengthObligation_categorical
    (I : TwoSortJudgmentWMInterface State Query)
    (H : Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    (_hcat : WMCategoricalEndpointContract (H := H))
    {X : H.Obj} (_φc : H.query X)
    (hbridge : TwoSortClosedTheoryBridge)
    {W : State} {t u : ScopedTerm 0}
    (hW : I.side W)
    (hred : Red t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  pureTheoryStep_to_wmStrengthObligation I hbridge hW hred

/-- Categorical-aligned default wrapper using the canonical theoremic B -> C1 bridge. -/
theorem pureTheoryStep_to_wmStrengthObligation_categorical_default
    (I : TwoSortJudgmentWMInterface State Query)
    (H : Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    (_hcat : WMCategoricalEndpointContract (H := H))
    {X : H.Obj} (_φc : H.query X)
    {W : State} {t u : ScopedTerm 0}
    (hW : I.side W)
    (hred : Red t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  pureTheoryStep_to_wmStrengthObligation_categorical
    (I := I) (H := H) (_hcat := _hcat) (_φc := _φc)
    (hbridge := twoSortClosedTheoryBridge_default) (W := W) (hW := hW) hred

/-- Star closed TwoSortPiSigmaId reduction transports to a WM strength obligation,
using the same one-step closed bridge via closure lifting. -/
theorem pureTheoryStepStar_to_wmStrengthObligation
    (I : TwoSortJudgmentWMInterface State Query)
    (hbridge : TwoSortClosedTheoryBridge)
    {W : State} {t u : ScopedTerm 0}
    (hW : I.side W)
    (hred : RedStar t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) := by
  have hbridgeStar : TwoSortClosedTheoryBridgeStar :=
    twoSortClosedTheoryBridge_to_star hbridge
  exact
    I.profileStepStar_sound hW (hbridgeStar hred)

/-- Star closed TwoSortPiSigmaId reduction transports to a WM strength obligation
through the canonical theoremic B* -> C1* bridge. -/
theorem pureTheoryStepStar_to_wmStrengthObligation_default
    (I : TwoSortJudgmentWMInterface State Query)
    {W : State} {t u : ScopedTerm 0}
    (hW : I.side W)
    (hred : RedStar t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  pureTheoryStepStar_to_wmStrengthObligation I twoSortClosedTheoryBridge_default hW hred

/-- Categorical-aligned wrapper:
same Pure star WM obligation transport, with explicit endpoint-interface input. -/
theorem pureTheoryStepStar_to_wmStrengthObligation_categorical
    (I : TwoSortJudgmentWMInterface State Query)
    (H : Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    (_hcat : WMCategoricalEndpointContract (H := H))
    {X : H.Obj} (_φc : H.query X)
    (hbridge : TwoSortClosedTheoryBridge)
    {W : State} {t u : ScopedTerm 0}
    (hW : I.side W)
    (hred : RedStar t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  pureTheoryStepStar_to_wmStrengthObligation I hbridge hW hred

/-- Categorical-aligned default wrapper using the canonical theoremic B* -> C1* bridge. -/
theorem pureTheoryStepStar_to_wmStrengthObligation_categorical_default
    (I : TwoSortJudgmentWMInterface State Query)
    (H : Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    (_hcat : WMCategoricalEndpointContract (H := H))
    {X : H.Obj} (_φc : H.query X)
    {W : State} {t u : ScopedTerm 0}
    (hW : I.side W)
    (hred : RedStar t u) :
    WMStrengthObligation State Query W
      (I.encode (quoteClosedTm t))
      (I.encode (quoteClosedTm u)) :=
  pureTheoryStepStar_to_wmStrengthObligation_categorical
    (I := I) (H := H) (_hcat := _hcat) (_φc := _φc)
    (hbridge := twoSortClosedTheoryBridge_default) (W := W) (hW := hW) hred

/-- Package a closed TwoSortPiSigmaId one-step as a state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_closed_pureTheoryStep
    (I : TwoSortJudgmentWMInterface State Query)
    (hbridge : TwoSortClosedTheoryBridge)
    {t u : ScopedTerm 0}
    (hred : Red t u) :
    WMConsequenceRuleOn State Query where
  side := I.side
  premise := I.encode (quoteClosedTm t)
  conclusion := I.encode (quoteClosedTm u)
  sound := by
    intro W hW
    exact pureTheoryStep_to_wmStrengthObligation I hbridge hW hred

/-- Package a closed TwoSortPiSigmaId one-step as a WM consequence rule using the
canonical theoremic B -> C1 bridge. -/
def wmConsequenceRuleOn_of_closed_pureTheoryStep_default
    (I : TwoSortJudgmentWMInterface State Query)
    {t u : ScopedTerm 0}
    (hred : Red t u) :
    WMConsequenceRuleOn State Query :=
  wmConsequenceRuleOn_of_closed_pureTheoryStep I twoSortClosedTheoryBridge_default hred

/-- Package a closed TwoSortPiSigmaId star reduction as a state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_closed_pureTheoryStepStar
    (I : TwoSortJudgmentWMInterface State Query)
    (hbridge : TwoSortClosedTheoryBridge)
    {t u : ScopedTerm 0}
    (hred : RedStar t u) :
    WMConsequenceRuleOn State Query where
  side := I.side
  premise := I.encode (quoteClosedTm t)
  conclusion := I.encode (quoteClosedTm u)
  sound := by
    intro W hW
    exact pureTheoryStepStar_to_wmStrengthObligation I hbridge hW hred

/-- Package a closed TwoSortPiSigmaId star reduction as a WM consequence rule using
the canonical theoremic B* -> C1* bridge. -/
def wmConsequenceRuleOn_of_closed_pureTheoryStepStar_default
    (I : TwoSortJudgmentWMInterface State Query)
    {t u : ScopedTerm 0}
    (hred : RedStar t u) :
    WMConsequenceRuleOn State Query :=
  wmConsequenceRuleOn_of_closed_pureTheoryStepStar I twoSortClosedTheoryBridge_default hred

/-- Categorical-aligned packaging of a closed TwoSortPiSigmaId one-step as a
state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_closed_pureTheoryStep_categorical
    (I : TwoSortJudgmentWMInterface State Query)
    (H : Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    (_hcat : WMCategoricalEndpointContract (H := H))
    {X : H.Obj} (_φc : H.query X)
    (hbridge : TwoSortClosedTheoryBridge)
    {t u : ScopedTerm 0}
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

/-- Categorical-aligned packaging of a closed TwoSortPiSigmaId star reduction as a
state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_closed_pureTheoryStepStar_categorical
    (I : TwoSortJudgmentWMInterface State Query)
    (H : Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    (_hcat : WMCategoricalEndpointContract (H := H))
    {X : H.Obj} (_φc : H.query X)
    (hbridge : TwoSortClosedTheoryBridge)
    {t u : ScopedTerm 0}
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

/-! ## WM-side regression canaries (consume existing TwoSortPiSigmaId regressions) -/

/-- Canary: the one-nested-binder beta transport theorem from `CoreEmbedding`
induces a concrete WM obligation witness under the interpretation interface. -/
theorem canary_betaPi_bridge_regression_one_nestedLam_wm
    (I : TwoSortJudgmentWMInterface State Query)
    {W : State}
    (hW : I.side W) :
    ∃ p q : Pattern,
      TwoSortProfileTheoryStep p q ∧
      WMStrengthObligation State Query W (I.encode p) (I.encode q) := by
  let hreg :=
    betaPi_bridge_regression_one_nestedLam
  have hregExists : ∃ p q : Pattern, TwoSortProfileTheoryStep p q := by
    exact ⟨_, _, hreg⟩
  rcases hregExists with ⟨p, q, hstep⟩
  refine ⟨p, q, hstep, ?_⟩
  exact I.profileStep_sound hW hstep

/-- Canary: the two-nested-binder beta transport theorem from `CoreEmbedding`
induces a concrete WM obligation witness under the interpretation interface. -/
theorem canary_betaPi_bridge_regression_two_nestedLam_wm
    (I : TwoSortJudgmentWMInterface State Query)
    {W : State}
    (hW : I.side W) :
    ∃ p q : Pattern,
      TwoSortProfileTheoryStep p q ∧
      WMStrengthObligation State Query W (I.encode p) (I.encode q) := by
  let hreg :=
    betaPi_bridge_regression_two_nestedLam
  have hregExists : ∃ p q : Pattern, TwoSortProfileTheoryStep p q := by
    exact ⟨_, _, hreg⟩
  rcases hregExists with ⟨p, q, hstep⟩
  refine ⟨p, q, hstep, ?_⟩
  exact I.profileStep_sound hW hstep

end Mettapedia.PLN.Bridges.Languages.WorldModel.PLNWorldModelTwoSortBridge
