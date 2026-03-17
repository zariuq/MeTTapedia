import Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
import Mettapedia.Logic.PLNWorldModelFOL

/-!
# WM Calculus ↔ FOL Semantics OSLF Bridge

This module connects the OSLF LanguageDef modal operators (◇, □, ◇ ⊣ □) to the
concrete `BinaryWorldModel (Multiset (PointedFOL L)) (FOLQuery L)` instance from
first-order Tarskian semantics.

## Architecture — Valuation Fibers

A `FOLValuation L` assigns concrete mathematical meaning (pointed FOL structures
+ first-order sentences) to the abstract string names in `WMTerm`. This makes
the FOL BinaryWorldModel instance a *fiber* over the generic WM calculus LanguageDef.

The bridge proves:
- **BinaryEvidence-add correspondence**: the LanguageDef reduction
  `Extract(Revise(W₁,W₂), q) → Combine(Extract(W₁,q), Extract(W₂,q))`
  is the syntactic shadow of `folEvidence (W₁+W₂) φ = folEvidence W₁ φ + folEvidence W₂ φ`.
- **Diamond interpretation**: ◇(isCombined) at decomposable terms means evidence
  can be decomposed into per-source Tarskian satisfaction counts.
- **Singleton adequacy**: sentence truth ↔ strength = 1 lifts through
  the valuation.
- **BinaryEvidence barbs**: non-zero evidence from satisfying structures.
- **Satisfiability as evidence**: any satisfying structure yields non-zero evidence.
- **Validity as maximal strength**: all structures satisfying → strength = 1.
- **Model-theoretic consequence**: FOL semantic consequence ↔ WM strength ordering.
- **Galois corollary**: forward evidence reachability ↔ backward model-theoretic safety.

## References

- `WMCalculusOSLFBridge.lean` — generic bridge (WMTermEncodes, isCombined, diamond theorems)
- `PLNWorldModelFOL.lean` — `BinaryWorldModel (Multiset (PointedFOL L)) (FOLQuery L)`
- `TypeSynthesis.lean` — `langDiamond`, `langBox`, `langGalois`, `langOSLF`
-/

namespace Mettapedia.OSLF.Framework.WMCalculusFOLBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.PLNWMHypercubeBasis
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelFOL
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open LO LO.FirstOrder
open scoped ENNReal

universe u

/-! ## Section 1: FOL Valuation

A valuation assigns concrete FOL-semantic objects to the abstract
string names used in WMTerm patterns. -/

/-- A valuation mapping WMTerm names to concrete FOL-semantic objects. -/
structure FOLValuation (L : Language.{u}) where
  /-- Maps state names to multisets of pointed FOL structures. -/
  stateVal : String → Multiset (PointedFOL L)
  /-- Maps query names to first-order sentences. -/
  queryVal : String → FOLQuery L

/-! ## Section 2: BinaryEvidence-Add Correspondence

The core bridge theorem: the LanguageDef reduction and the mathematical identity
are the same fact expressed in two formalisms. -/

/-- The syntactic evidence-add reduction and the semantic evidence additivity
    are corresponding facts: one is a LanguageDef rewrite step, the other is
    the `folEvidence_add` theorem.  Both express that evidence
    extraction distributes over state composition. -/
theorem fol_evidence_add_correspondence {L : Language.{u}}
    (v : WMExtVertex) (val : FOLValuation L) (s₁ s₂ q : String) :
    -- Syntactic side: the LanguageDef reduction fires
    langReduces (wmExtVertexLanguageDef v)
      (pExtract (pRevise (.fvar s₁) (.fvar s₂)) (.fvar q))
      (pCombine (pExtract (.fvar s₁) (.fvar q)) (pExtract (.fvar s₂) (.fvar q))) ∧
    -- Semantic side: evidence additivity holds on the valued FOL states
    folEvidence (val.stateVal s₁ + val.stateVal s₂) (val.queryVal q) =
      folEvidence (val.stateVal s₁) (val.queryVal q) +
        folEvidence (val.stateVal s₂) (val.queryVal q) :=
  ⟨wmLangReduces_evidenceAdd v (.fvar s₁) (.fvar s₂) (.fvar q),
   folEvidence_add (val.stateVal s₁) (val.stateVal s₂) (val.queryVal q)⟩

/-- Full-vertex version of evidence-add correspondence. -/
theorem fol_evidence_add_correspondence_full {L : Language.{u}}
    (v : WMFullVertex) (val : FOLValuation L) (s₁ s₂ q : String) :
    langReduces (wmFullVertexLanguageDef v)
      (pExtract (pRevise (.fvar s₁) (.fvar s₂)) (.fvar q))
      (pCombine (pExtract (.fvar s₁) (.fvar q)) (pExtract (.fvar s₂) (.fvar q))) ∧
    folEvidence (val.stateVal s₁ + val.stateVal s₂) (val.queryVal q) =
      folEvidence (val.stateVal s₁) (val.queryVal q) +
        folEvidence (val.stateVal s₂) (val.queryVal q) :=
  ⟨wmFullLangReduces_evidenceAdd v (.fvar s₁) (.fvar s₂) (.fvar q),
   folEvidence_add (val.stateVal s₁) (val.stateVal s₂) (val.queryVal q)⟩

/-! ## Section 3: Diamond Interpretation

◇(isCombined) at a decomposable term means evidence can be decomposed
into per-source Tarskian satisfaction counts. -/

/-- Diamond(isCombined) at an encoded decomposable FOL state has
    a concrete semantic interpretation: there exist two evidence components,
    one from each sub-state, whose sum equals the combined evidence. -/
theorem fol_diamond_evidence_decomposition {L : Language.{u}}
    (v : WMExtVertex) (val : FOLValuation L) (s₁ s₂ q : String) :
    -- Syntactic: ◇(isCombined) holds at the decomposable pattern
    langDiamond (wmExtVertexLanguageDef v) isCombined
      (pExtract (pRevise (.fvar s₁) (.fvar s₂)) (.fvar q)) ∧
    -- Semantic: evidence decomposes into per-source components
    ∃ e₁ e₂ : BinaryEvidence,
      e₁ = folEvidence (val.stateVal s₁) (val.queryVal q) ∧
      e₂ = folEvidence (val.stateVal s₂) (val.queryVal q) ∧
      folEvidence (val.stateVal s₁ + val.stateVal s₂) (val.queryVal q) = e₁ + e₂ :=
  ⟨diamond_isCombined_at_decomposable v (.fvar s₁) (.fvar s₂) (.fvar q),
   ⟨folEvidence (val.stateVal s₁) (val.queryVal q),
    folEvidence (val.stateVal s₂) (val.queryVal q),
    rfl, rfl,
    folEvidence_add (val.stateVal s₁) (val.stateVal s₂) (val.queryVal q)⟩⟩

/-- Revision commutativity: the syntactic diamond for commutativity corresponds
    to the semantic fact that multiset addition is commutative. -/
theorem fol_diamond_revision_comm {L : Language.{u}}
    (v : WMExtVertex) (val : FOLValuation L) (s₁ s₂ : String) :
    langDiamond (wmExtVertexLanguageDef v) isRevision
      (pRevise (.fvar s₁) (.fvar s₂)) ∧
    val.stateVal s₁ + val.stateVal s₂ = val.stateVal s₂ + val.stateVal s₁ :=
  ⟨diamond_isCommuted v (.fvar s₁) (.fvar s₂),
   Multiset.add_comm (val.stateVal s₁) (val.stateVal s₂)⟩

/-! ## Section 4: Singleton Adequacy Lift

First-order sentence truth ↔ strength = 1 lifts through the valuation. -/

/-- Singleton adequacy: a pointed FOL structure satisfies a sentence
    iff the WM query strength at the singleton state equals 1, lifted through
    the valuation. -/
theorem fol_singleton_adequacy_lift {L : Language.{u}}
    (val : FOLValuation L) (S : PointedFOL L) (φ : FOLQuery L)
    (s : String) (hs : val.stateVal s = {S}) :
    folSatisfies S φ ↔
      BinaryWorldModel.queryStrength
        (State := Multiset (PointedFOL L)) (Query := FOLQuery L)
        (val.stateVal s) φ = 1 := by
  rw [hs]
  exact singleton_adequacy_strength_one S φ

/-! ## Section 5: BinaryEvidence Barb (Process-Algebraic Observable)

A revised FOL state exhibits an evidence barb when the combined
evidence is non-zero — the topological observable. -/

/-- A revised FOL state exhibits an evidence barb when the combined
    extraction is non-zero. Under the valuation, this means the per-source
    FOL structures yield non-trivial evidence for the query. -/
theorem fol_revised_barb (v : WMExtVertex) (s₁ s₂ q : String)
    (hne : ¬ isZeroEvidence
      (pCombine (pExtract (.fvar s₁) (.fvar q))
                (pExtract (.fvar s₂) (.fvar q)))) :
    wmHasEvidenceBarb (wmExtVertexLanguageDef v)
      (pRevise (.fvar s₁) (.fvar s₂)) (.fvar q) :=
  wmRevisedState_evidenceBarb v (.fvar s₁) (.fvar s₂) (.fvar q) hne

/-! ## Section 6: Satisfying Structure → Non-Zero BinaryEvidence

If any pointed FOL structure in the multiset satisfies the query,
the evidence is non-zero. -/

/-- If a pointed FOL structure in the multiset satisfies the query sentence,
    the positive evidence count is at least 1. -/
theorem fol_nonzero_evidence_of_satisfying_model {L : Language.{u}}
    (W : Multiset (PointedFOL L)) (φ : FOLQuery L)
    (S : PointedFOL L) (hmem : S ∈ W) (hsat : folSatisfies S φ) :
    (folEvidence W φ).pos ≥ 1 := by
  classical
  simp only [folEvidence]
  have hpos : 0 < Multiset.countP (fun S => folSatisfies S φ) W :=
    Multiset.countP_pos.mpr ⟨S, hmem, hsat⟩
  exact_mod_cast hpos

/-- Valued version: if the valuation maps a state name to a multiset containing
    a structure satisfying the query, then evidence is non-zero. -/
theorem fol_nonzero_evidence_of_satisfying_model_val {L : Language.{u}}
    (val : FOLValuation L) (s : String) (φ : FOLQuery L)
    (S : PointedFOL L) (hmem : S ∈ val.stateVal s) (hsat : folSatisfies S φ) :
    (folEvidence (val.stateVal s) φ).pos ≥ 1 :=
  fol_nonzero_evidence_of_satisfying_model (val.stateVal s) φ S hmem hsat

/-! ## Section 7: Consequence Lifting Through OSLF

Pointwise semantic implication between FOL sentences lifts to WM strength
ordering on multiset states. -/

/-- Pointwise FOL semantic implication lifts to WM strength ordering:
    if every pointed structure satisfying φ also satisfies ψ, then the WM query
    strength of φ is at most that of ψ at any multiset state. -/
theorem fol_consequence_lifts {L : Language.{u}}
    (φ ψ : FOLQuery L)
    (himp : ∀ S : PointedFOL L, folSatisfies S φ → folSatisfies S ψ)
    (W : Multiset (PointedFOL L)) :
    BinaryWorldModel.queryStrength
      (State := Multiset (PointedFOL L)) (Query := FOLQuery L) W φ ≤
    BinaryWorldModel.queryStrength
      (State := Multiset (PointedFOL L)) (Query := FOLQuery L) W ψ :=
  queryStrength_le_of_pointwise W φ ψ himp

/-! ## Section 8: Galois Corollary with FOL Reading

The Galois connection ◇ ⊣ □ instantiated with evidence-theoretic meaning:
"forward evidence reachability" is adjoint to "backward model-theoretic safety." -/

/-- The ◇ ⊣ □ Galois connection at any WM vertex gives, when read through
    the FOL fiber:
    - Forward (◇): "evidence can be decomposed into per-source satisfaction counts"
    - Backward (□): "all predecessors of a combined evidence form satisfy the safety property"

    The adjunction says these are equivalent perspectives on the same evidence-theoretic
    structure. -/
theorem fol_galois_evidence_safety
    (v : WMExtVertex) (ψ : Pattern → Prop) :
    (∀ p, langDiamond (wmExtVertexLanguageDef v) isCombined p → ψ p) ↔
    (∀ p, isCombined p → langBox (wmExtVertexLanguageDef v) ψ p) :=
  wmCalc_decomposability_safety v ψ

/-- Full-vertex Galois corollary. -/
theorem fol_galois_evidence_safety_full
    (v : WMFullVertex) (ψ : Pattern → Prop) :
    (∀ p, langDiamond (wmFullVertexLanguageDef v) isCombined p → ψ p) ↔
    (∀ p, isCombined p → langBox (wmFullVertexLanguageDef v) ψ p) :=
  wmFullCalc_decomposability_safety v ψ

/-! ## Section 9: FOL-Specific — Validity as Maximal Strength

When all structures in the state satisfy the query, strength is maximal. -/

/-- FOL validity (all structures satisfy) yields maximal evidence strength.
    This follows from the singleton adequacy theorem: if every structure
    satisfies φ, then at every singleton the strength is 1, so the multiset
    average is also 1. -/
theorem fol_strength_one_of_validity {L : Language.{u}}
    (W : Multiset (PointedFOL L)) (φ : FOLQuery L)
    (hvalid : ∀ S ∈ W, folSatisfies S φ)
    (hne : W ≠ 0) :
    BinaryWorldModel.queryStrength
      (State := Multiset (PointedFOL L)) (Query := FOLQuery L) W φ = 1 := by
  classical
  -- All structures satisfy φ, so countP = card and strength = card/card = 1
  have hcount : Multiset.countP (fun S => folSatisfies S φ) W = W.card :=
    Multiset.countP_eq_card.mpr (fun S hS => hvalid S hS)
  have hcardPos : 0 < W.card := Multiset.card_pos.mpr hne
  -- Direct computation via the consequence lifting infrastructure
  -- φ implies itself, so strength is maximal when all models satisfy
  have himp : ∀ S : PointedFOL L, folSatisfies S φ → folSatisfies S φ := fun _ h => h
  -- We need: strength = countP_sat / (countP_sat + countP_neg) = card / card = 1
  -- when all satisfy, countP_neg = 0 and countP_sat = card
  have hcountNeg : Multiset.countP (fun S => ¬folSatisfies S φ) W = 0 := by
    apply Multiset.countP_eq_zero.mpr
    intro S hS habs
    exact habs (hvalid S hS)
  change BinaryEvidence.toStrength (folEvidence W φ) = 1
  simp only [BinaryEvidence.toStrength, folEvidence, hcount, hcountNeg]
  have hne0 : (W.card : ℝ≥0∞) ≠ 0 := by positivity
  simp [BinaryEvidence.total, hne0]
  exact ENNReal.div_self hne0 (ENNReal.natCast_ne_top W.card)

/-! ## Section 10: FOL Model-Theoretic Consequence Bridge

FOL model-theoretic consequence corresponds to WM strength ordering,
which is the semantic content of the OSLF Galois connection's forward direction. -/

/-- FOL model-theoretic consequence (all models of φ satisfy ψ)
    corresponds to WM strength ordering, which is the semantic content
    of the OSLF Galois connection's forward direction. -/
theorem fol_model_theoretic_consequence_is_strength_le {L : Language.{u}}
    (φ ψ : FOLQuery L)
    (hcons : ∀ S : PointedFOL L, folSatisfies S φ → folSatisfies S ψ)
    (W : Multiset (PointedFOL L)) :
    BinaryWorldModel.queryStrength
      (State := Multiset (PointedFOL L)) (Query := FOLQuery L) W φ ≤
    BinaryWorldModel.queryStrength
      (State := Multiset (PointedFOL L)) (Query := FOLQuery L) W ψ :=
  queryStrength_le_of_pointwise W φ ψ hcons

/-- The converse: if singleton-strength is monotone, then model-theoretic
    consequence holds — the FOL bridge is fully faithful at singletons. -/
theorem fol_strength_le_implies_model_theoretic_consequence {L : Language.{u}}
    (φ ψ : FOLQuery L)
    (hle : singletonStrengthLE φ ψ) :
    ∀ S : PointedFOL L, folSatisfies S φ → folSatisfies S ψ :=
  (pointwiseImplies_iff_singletonStrengthLE φ ψ).mpr hle

end Mettapedia.OSLF.Framework.WMCalculusFOLBridge
