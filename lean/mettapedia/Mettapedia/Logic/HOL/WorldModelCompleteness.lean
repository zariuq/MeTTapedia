import Mettapedia.Logic.HOL.WorldModel
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWorldModelCategoricalBridge

/-!
# HOL WM Consequence-Closure Wrappers

This module exposes implication-consequence transfer wrappers from the real HOL
world-model instance to `WMConsequenceRule` / `WMConsequenceRuleOn`.

At this stage it is intentionally semantic and schema-level: it packages the
new Henkin-model HOL bridge, and it also provides proof-system-agnostic
templates parameterized by an external implication relation.
-/

namespace Mettapedia.Logic.HOL.WorldModelCompleteness

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.HOL.WorldModel
open Mettapedia.Logic.PLNWorldModelHyperdoctrine
open scoped ENNReal

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

abbrev HOLQuery (Const : Ty Base → Type v) := Mettapedia.Logic.HOL.WorldModel.HOLQuery Const
abbrev HOLState (Base : Type u) (Const : Ty Base → Type v) :=
  Multiset (HenkinModel.{u, v, w} Base Const)

/-- Alias for the unified categorical endpoint surface, specialized to HOL WM states. -/
abbrev WMCategoricalEndpointSurface
    (H : WMHyperdoctrine (HOLState Base Const)) : Prop :=
  Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointSurface (H := H)

theorem pointwiseImplies_iff_singletonStrengthLE (φ ψ : HOLQuery Const) :
    (∀ M : HenkinModel.{u, v, w} Base Const,
      holSatisfies (Base := Base) (Const := Const) M φ →
        holSatisfies (Base := Base) (Const := Const) M ψ) ↔
      (∀ M : HenkinModel.{u, v, w} Base Const,
        BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
            ({M} : HOLState Base Const) φ ≤
          BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
            ({M} : HOLState Base Const) ψ) := by
  simpa using
    (Mettapedia.Logic.HOL.WorldModel.pointwiseImplies_iff_singletonStrengthLE
      (Base := Base) (Const := Const) (φ := φ) (ψ := ψ))

/-- Naming alias for the same bridge with `singletonConsequence` terminology. -/
theorem pointwiseImplies_iff_singletonConsequence (φ ψ : HOLQuery Const) :
    (∀ M : HenkinModel.{u, v, w} Base Const,
      holSatisfies (Base := Base) (Const := Const) M φ →
        holSatisfies (Base := Base) (Const := Const) M ψ) ↔
      (∀ M : HenkinModel.{u, v, w} Base Const,
        BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
            ({M} : HOLState Base Const) φ ≤
          BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
            ({M} : HOLState Base Const) ψ) :=
  pointwiseImplies_iff_singletonStrengthLE (Base := Base) (Const := Const) (φ := φ) (ψ := ψ)

/-- Pointwise HOL equivalence is exactly HOL WM query equivalence. -/
theorem pointwiseIff_iff_queryEq (φ ψ : HOLQuery Const) :
    (∀ M : HenkinModel.{u, v, w} Base Const,
      holSatisfies (Base := Base) (Const := Const) M φ ↔
        holSatisfies (Base := Base) (Const := Const) M ψ) ↔
      WMQueryEq
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const) φ ψ := by
  constructor
  · intro hiff
    classical
    have hp :
        ∀ W : Multiset (HenkinModel.{u, v, w} Base Const),
          Multiset.countP (fun M : HenkinModel.{u, v, w} Base Const => holSatisfies M φ) W =
            Multiset.countP (fun M : HenkinModel.{u, v, w} Base Const => holSatisfies M ψ) W := by
      intro W
      exact Multiset.countP_congr rfl (by
        intro M _hM
        exact propext (hiff M))
    have hn :
        ∀ W : Multiset (HenkinModel.{u, v, w} Base Const),
          Multiset.countP (fun M : HenkinModel.{u, v, w} Base Const => ¬ holSatisfies M φ) W =
            Multiset.countP (fun M : HenkinModel.{u, v, w} Base Const => ¬ holSatisfies M ψ) W := by
      intro W
      exact Multiset.countP_congr rfl (by
        intro M _hM
        exact propext (not_congr (hiff M)))
    intro W
    ext <;> simp [BinaryWorldModel.evidence, holEvidence, hp W, hn W]
  · intro hEq M
    constructor
    · intro hφ
      have hStrength :=
        show BinaryWorldModel.queryStrength
                (State := Multiset (HenkinModel.{u, v, w} Base Const)) (Query := HOLQuery Const)
                ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ =
              BinaryWorldModel.queryStrength
                (State := Multiset (HenkinModel.{u, v, w} Base Const)) (Query := HOLQuery Const)
                ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) ψ by
          simpa [BinaryWorldModel.queryStrength] using
            congrArg BinaryEvidence.toStrength
              (hEq ({M} : Multiset (HenkinModel.{u, v, w} Base Const)))
      have hφ1 :
          BinaryWorldModel.queryStrength
              (State := Multiset (HenkinModel.{u, v, w} Base Const))
              (Query := HOLQuery Const)
              ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ = 1 :=
        (singleton_adequacy_strength_one (Base := Base) (Const := Const) M φ).mp hφ
      have hψ1 :
          BinaryWorldModel.queryStrength
              (State := Multiset (HenkinModel.{u, v, w} Base Const))
              (Query := HOLQuery Const)
              ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) ψ = 1 := by
        calc
          BinaryWorldModel.queryStrength
              (State := Multiset (HenkinModel.{u, v, w} Base Const))
              (Query := HOLQuery Const)
              ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) ψ
              =
            BinaryWorldModel.queryStrength
              (State := Multiset (HenkinModel.{u, v, w} Base Const))
              (Query := HOLQuery Const)
              ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ := hStrength.symm
          _ = 1 := hφ1
      exact (singleton_adequacy_strength_one (Base := Base) (Const := Const) M ψ).mpr hψ1
    · intro hψ
      have hStrength :=
        show BinaryWorldModel.queryStrength
                (State := Multiset (HenkinModel.{u, v, w} Base Const)) (Query := HOLQuery Const)
                ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ =
              BinaryWorldModel.queryStrength
                (State := Multiset (HenkinModel.{u, v, w} Base Const)) (Query := HOLQuery Const)
                ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) ψ by
          simpa [BinaryWorldModel.queryStrength] using
            congrArg BinaryEvidence.toStrength
              (hEq ({M} : Multiset (HenkinModel.{u, v, w} Base Const)))
      have hψ1 :
          BinaryWorldModel.queryStrength
              (State := Multiset (HenkinModel.{u, v, w} Base Const))
              (Query := HOLQuery Const)
              ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) ψ = 1 :=
        (singleton_adequacy_strength_one (Base := Base) (Const := Const) M ψ).mp hψ
      have hφ1 :
          BinaryWorldModel.queryStrength
              (State := Multiset (HenkinModel.{u, v, w} Base Const))
              (Query := HOLQuery Const)
              ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ = 1 := by
        calc
          BinaryWorldModel.queryStrength
              (State := Multiset (HenkinModel.{u, v, w} Base Const))
              (Query := HOLQuery Const)
              ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ
              =
            BinaryWorldModel.queryStrength
              (State := Multiset (HenkinModel.{u, v, w} Base Const))
              (Query := HOLQuery Const)
              ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) ψ := hStrength
          _ = 1 := hψ1
      exact (singleton_adequacy_strength_one (Base := Base) (Const := Const) M φ).mpr hφ1

/-- Pointwise HOL implication lifts to a multiset WM strength inequality. -/
theorem multiset_strength_le_of_pointwise
    (W : Multiset (HenkinModel.{u, v, w} Base Const)) (φ ψ : HOLQuery Const)
    (himp : ∀ M : HenkinModel.{u, v, w} Base Const,
      holSatisfies (Base := Base) (Const := Const) M φ →
        holSatisfies (Base := Base) (Const := Const) M ψ) :
    BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ ≤
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W ψ := by
  exact
    Mettapedia.Logic.HOL.WorldModel.queryStrength_le_of_pointwise.{u, v, w}
      (Base := Base) (Const := Const) (W := W) (φ := φ) (ψ := ψ) himp

/-- Naming alias: transfer from pointwise implication to multiset consequence. -/
theorem multiset_consequence_of_pointwise
    (W : Multiset (HenkinModel.{u, v, w} Base Const)) (φ ψ : HOLQuery Const)
    (himp : ∀ M : HenkinModel.{u, v, w} Base Const,
      holSatisfies (Base := Base) (Const := Const) M φ →
        holSatisfies (Base := Base) (Const := Const) M ψ) :
    BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ ≤
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W ψ :=
  multiset_strength_le_of_pointwise (Base := Base) (Const := Const) (W := W) (φ := φ) (ψ := ψ) himp

/-- Categorical-aligned HOL implication closure wrapper. -/
theorem multiset_strength_le_of_pointwise_categorical
    (H : WMHyperdoctrine (HOLState Base Const))
    (_hcat : WMCategoricalEndpointSurface (Base := Base) (Const := Const) (H := H))
    {X : H.Obj} (_φc : H.query X)
    (W : Multiset (HenkinModel.{u, v, w} Base Const)) (φ ψ : HOLQuery Const)
    (himp : ∀ M : HenkinModel.{u, v, w} Base Const,
      holSatisfies (Base := Base) (Const := Const) M φ →
        holSatisfies (Base := Base) (Const := Const) M ψ) :
    BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ ≤
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W ψ :=
  multiset_strength_le_of_pointwise (Base := Base) (Const := Const) (W := W) (φ := φ) (ψ := ψ) himp

/-- Singleton-strength consequence lifts to multiset WM strength inequality. -/
theorem multiset_strength_le_of_singletonStrengthLE
    (W : Multiset (HenkinModel.{u, v, w} Base Const)) (φ ψ : HOLQuery Const)
    (hsing : ∀ M : HenkinModel.{u, v, w} Base Const,
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
          ({M} : HOLState Base Const) φ ≤
        BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
          ({M} : HOLState Base Const) ψ) :
    BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ ≤
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W ψ := by
  exact
    Mettapedia.Logic.HOL.WorldModel.multiset_strength_le_of_singletonStrengthLE.{u, v, w}
      (Base := Base) (Const := Const) (W := W) (φ := φ) (ψ := ψ) hsing

/-- Naming alias: transfer from singleton consequence to multiset consequence. -/
theorem multiset_consequence_of_singletonConsequence
    (W : Multiset (HenkinModel.{u, v, w} Base Const)) (φ ψ : HOLQuery Const)
    (hsing : ∀ M : HenkinModel.{u, v, w} Base Const,
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
          ({M} : HOLState Base Const) φ ≤
        BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
          ({M} : HOLState Base Const) ψ) :
    BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ ≤
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W ψ :=
  multiset_strength_le_of_singletonStrengthLE
    (Base := Base) (Const := Const) (W := W) (φ := φ) (ψ := ψ) hsing

/-- Proof-system-agnostic bridge schema:
if an external implication relation is sound and complete for pointwise HOL
implication, then it is equivalent to singleton HOL WM consequence. -/
theorem externalImplication_iff_singletonConsequence_of_sound_complete
    (ProvImp : HOLQuery Const → HOLQuery Const → Prop)
    (hSound :
      ∀ {φ ψ}, ProvImp φ ψ →
        ∀ M : HenkinModel.{u, v, w} Base Const,
          holSatisfies (Base := Base) (Const := Const) M φ →
            holSatisfies (Base := Base) (Const := Const) M ψ)
    (hComplete :
      ∀ {φ ψ},
        (∀ M : HenkinModel.{u, v, w} Base Const,
          holSatisfies (Base := Base) (Const := Const) M φ →
            holSatisfies (Base := Base) (Const := Const) M ψ) → ProvImp φ ψ)
    (φ ψ : HOLQuery Const) :
    ProvImp φ ψ ↔
      (∀ M : HenkinModel.{u, v, w} Base Const,
        BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
            ({M} : HOLState Base Const) φ ≤
          BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
            ({M} : HOLState Base Const) ψ) := by
  constructor
  · intro hprov
    exact (pointwiseImplies_iff_singletonConsequence
      (Base := Base) (Const := Const) (φ := φ) (ψ := ψ)).1 (hSound hprov)
  · intro hsing
    exact hComplete ((pointwiseImplies_iff_singletonConsequence
      (Base := Base) (Const := Const) (φ := φ) (ψ := ψ)).2 hsing)

/-- Proof-system-agnostic soundness transfer from an external implication relation. -/
theorem multiset_consequence_of_externalImplication_sound
    (ProvImp : HOLQuery Const → HOLQuery Const → Prop)
    (hSound :
      ∀ {φ ψ}, ProvImp φ ψ →
        ∀ M : HenkinModel.{u, v, w} Base Const,
          holSatisfies (Base := Base) (Const := Const) M φ →
            holSatisfies (Base := Base) (Const := Const) M ψ)
    (W : Multiset (HenkinModel.{u, v, w} Base Const)) (φ ψ : HOLQuery Const)
    (hprov : ProvImp φ ψ) :
    BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ ≤
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W ψ :=
  multiset_consequence_of_pointwise
    (Base := Base) (Const := Const) (W := W) (φ := φ) (ψ := ψ) (hSound hprov)

/-- Categorical-aligned HOL singleton-strength closure wrapper. -/
theorem multiset_strength_le_of_singletonStrengthLE_categorical
    (H : WMHyperdoctrine (HOLState Base Const))
    (_hcat : WMCategoricalEndpointSurface (Base := Base) (Const := Const) (H := H))
    {X : H.Obj} (_φc : H.query X)
    (W : Multiset (HenkinModel.{u, v, w} Base Const)) (φ ψ : HOLQuery Const)
    (hsing : ∀ M : HenkinModel.{u, v, w} Base Const,
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
          ({M} : HOLState Base Const) φ ≤
        BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
          ({M} : HOLState Base Const) ψ) :
    BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W φ ≤
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const) W ψ :=
  multiset_strength_le_of_singletonStrengthLE
    (Base := Base) (Const := Const) (W := W) (φ := φ) (ψ := ψ) hsing

/-- Implication-closure wrapper: package pointwise HOL implication as a global
side `WMConsequenceRule`. -/
def wmConsequenceRule_of_pointwise (φ ψ : HOLQuery Const) :
    WMConsequenceRule (HOLState Base Const) (HOLQuery Const) where
  side := ∀ M : HenkinModel.{u, v, w} Base Const,
    holSatisfies (Base := Base) (Const := Const) M φ →
      holSatisfies (Base := Base) (Const := Const) M ψ
  premise := φ
  conclusion := ψ
  sound := by
    intro hSide W
    exact multiset_strength_le_of_pointwise
      (Base := Base) (Const := Const) (W := W) (φ := φ) (ψ := ψ) hSide

/-- Implication-closure wrapper from singleton-strength side conditions. -/
def wmConsequenceRule_of_singletonStrengthLE (φ ψ : HOLQuery Const) :
    WMConsequenceRule (HOLState Base Const) (HOLQuery Const) where
  side := ∀ M : HenkinModel.{u, v, w} Base Const,
    BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
        ({M} : HOLState Base Const) φ ≤
      BinaryWorldModel.queryStrength (State := HOLState Base Const) (Query := HOLQuery Const)
        ({M} : HOLState Base Const) ψ
  premise := φ
  conclusion := ψ
  sound := by
    intro hSide W
    exact multiset_strength_le_of_singletonStrengthLE
      (Base := Base) (Const := Const) (W := W) (φ := φ) (ψ := ψ) hSide

/-- State-indexed wrapper promoted from the global implication-closure rule. -/
def wmConsequenceRuleOn_of_pointwise (φ ψ : HOLQuery Const) :
    WMConsequenceRuleOn (HOLState Base Const) (HOLQuery Const) :=
  WMConsequenceRuleOn.ofGlobal
    (wmConsequenceRule_of_pointwise.{u, v, w}
      (Base := Base) (Const := Const) (φ := φ) (ψ := ψ))

/-- Categorical-aligned state-indexed wrapper from HOL pointwise implication. -/
def wmConsequenceRuleOn_of_pointwise_categorical
    (H : WMHyperdoctrine (HOLState Base Const))
    (_hcat : WMCategoricalEndpointSurface (Base := Base) (Const := Const) (H := H))
    {X : H.Obj} (_φc : H.query X)
    (φ ψ : HOLQuery Const) :
    WMConsequenceRuleOn (HOLState Base Const) (HOLQuery Const) :=
  WMConsequenceRuleOn.ofGlobal
    (wmConsequenceRule_of_pointwise.{u, v, w}
      (Base := Base) (Const := Const) (φ := φ) (ψ := ψ))

/-- State-indexed wrapper promoted from singleton-strength side conditions. -/
def wmConsequenceRuleOn_of_singletonStrengthLE (φ ψ : HOLQuery Const) :
    WMConsequenceRuleOn (HOLState Base Const) (HOLQuery Const) :=
  WMConsequenceRuleOn.ofGlobal
    (wmConsequenceRule_of_singletonStrengthLE.{u, v, w}
      (Base := Base) (Const := Const) (φ := φ) (ψ := ψ))

/-- Categorical-aligned state-indexed wrapper from HOL singleton-strength side conditions. -/
def wmConsequenceRuleOn_of_singletonStrengthLE_categorical
    (H : WMHyperdoctrine (HOLState Base Const))
    (_hcat : WMCategoricalEndpointSurface (Base := Base) (Const := Const) (H := H))
    {X : H.Obj} (_φc : H.query X)
    (φ ψ : HOLQuery Const) :
    WMConsequenceRuleOn (HOLState Base Const) (HOLQuery Const) :=
  WMConsequenceRuleOn.ofGlobal
    (wmConsequenceRule_of_singletonStrengthLE.{u, v, w}
      (Base := Base) (Const := Const) (φ := φ) (ψ := ψ))

end Mettapedia.Logic.HOL.WorldModelCompleteness
