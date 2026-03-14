import Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
import Mettapedia.Logic.PLNWorldModelNeighborhood

/-!
# WM Calculus ↔ Neighborhood Semantics OSLF Bridge

This module connects the OSLF LanguageDef modal operators (◇, □, ◇ ⊣ □) to the
concrete `WorldModel (Multiset PointedNeighborhood) ModalQuery` instance from
neighborhood semantics.

## Architecture — Valuation Fibers

A `NeighborhoodValuation` assigns concrete mathematical meaning (pointed
neighborhood models + modal formulas) to the abstract string names in `WMTerm`.
This makes the neighborhood WorldModel instance a *fiber* over the generic
WM calculus LanguageDef.

The bridge proves:
- **Evidence-add correspondence**: the LanguageDef reduction
  `Extract(Revise(W₁,W₂), q) → Combine(Extract(W₁,q), Extract(W₂,q))`
  is the syntactic shadow of `neighborhoodEvidence (W₁+W₂) φ = neighborhoodEvidence W₁ φ + neighborhoodEvidence W₂ φ`.
- **Diamond interpretation**: ◇(isCombined) at decomposable terms means evidence
  can be decomposed into per-source neighborhood satisfaction counts.
- **Singleton adequacy**: pointed-model satisfaction ↔ strength = 1 lifts through
  the valuation.
- **Evidence barbs**: non-zero evidence from satisfying models.
- **Galois corollary**: forward evidence reachability ↔ backward model-theoretic safety.

## References

- `WMCalculusOSLFBridge.lean` — generic bridge (WMTermEncodes, isCombined, diamond theorems)
- `PLNWorldModelNeighborhood.lean` — `WorldModel (Multiset PointedNeighborhood) ModalQuery`
- `TypeSynthesis.lean` — `langDiamond`, `langBox`, `langGalois`
-/

namespace Mettapedia.OSLF.Framework.WMCalculusNeighborhoodBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.PLNWMHypercubeBasis
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelNeighborhood
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

/-! ## Section 1: Neighborhood Valuation

A valuation assigns concrete neighborhood-semantic objects to the abstract
string names used in WMTerm patterns. -/

/-- A valuation mapping WMTerm names to concrete neighborhood-semantic objects. -/
structure NeighborhoodValuation where
  /-- Maps state names to multisets of pointed neighborhood models. -/
  stateVal : String → Multiset PointedNeighborhood
  /-- Maps query names to modal formulas. -/
  queryVal : String → ModalQuery

/-! ## Section 2: Evidence-Add Correspondence

The core bridge theorem: the LanguageDef reduction and the mathematical identity
are the same fact expressed in two formalisms. -/

/-- The syntactic evidence-add reduction and the semantic evidence additivity
    are corresponding facts: one is a LanguageDef rewrite step, the other is
    the `neighborhoodEvidence_add` theorem.  Both express that evidence
    extraction distributes over state composition. -/
theorem neighborhood_evidence_add_correspondence
    (v : WMExtVertex) (val : NeighborhoodValuation) (s₁ s₂ q : String) :
    -- Syntactic side: the LanguageDef reduction fires
    langReduces (wmExtVertexLanguageDef v)
      (pExtract (pRevise (.fvar s₁) (.fvar s₂)) (.fvar q))
      (pCombine (pExtract (.fvar s₁) (.fvar q)) (pExtract (.fvar s₂) (.fvar q))) ∧
    -- Semantic side: evidence additivity holds on the valued neighborhood states
    neighborhoodEvidence (val.stateVal s₁ + val.stateVal s₂) (val.queryVal q) =
      neighborhoodEvidence (val.stateVal s₁) (val.queryVal q) +
        neighborhoodEvidence (val.stateVal s₂) (val.queryVal q) :=
  ⟨wmLangReduces_evidenceAdd v (.fvar s₁) (.fvar s₂) (.fvar q),
   neighborhoodEvidence_add (val.stateVal s₁) (val.stateVal s₂) (val.queryVal q)⟩

/-- Full-vertex version of evidence-add correspondence. -/
theorem neighborhood_evidence_add_correspondence_full
    (v : WMFullVertex) (val : NeighborhoodValuation) (s₁ s₂ q : String) :
    langReduces (wmFullVertexLanguageDef v)
      (pExtract (pRevise (.fvar s₁) (.fvar s₂)) (.fvar q))
      (pCombine (pExtract (.fvar s₁) (.fvar q)) (pExtract (.fvar s₂) (.fvar q))) ∧
    neighborhoodEvidence (val.stateVal s₁ + val.stateVal s₂) (val.queryVal q) =
      neighborhoodEvidence (val.stateVal s₁) (val.queryVal q) +
        neighborhoodEvidence (val.stateVal s₂) (val.queryVal q) :=
  ⟨wmFullLangReduces_evidenceAdd v (.fvar s₁) (.fvar s₂) (.fvar q),
   neighborhoodEvidence_add (val.stateVal s₁) (val.stateVal s₂) (val.queryVal q)⟩

/-! ## Section 3: Diamond Interpretation

◇(isCombined) at a decomposable term means evidence can be decomposed
into per-source neighborhood satisfaction counts. -/

/-- Diamond(isCombined) at an encoded decomposable neighborhood state has
    a concrete semantic interpretation: there exist two evidence components,
    one from each sub-state, whose sum equals the combined evidence. -/
theorem neighborhood_diamond_evidence_decomposition
    (v : WMExtVertex) (val : NeighborhoodValuation) (s₁ s₂ q : String) :
    -- Syntactic: ◇(isCombined) holds at the decomposable pattern
    langDiamond (wmExtVertexLanguageDef v) isCombined
      (pExtract (pRevise (.fvar s₁) (.fvar s₂)) (.fvar q)) ∧
    -- Semantic: evidence decomposes into per-source components
    ∃ e₁ e₂ : Evidence,
      e₁ = neighborhoodEvidence (val.stateVal s₁) (val.queryVal q) ∧
      e₂ = neighborhoodEvidence (val.stateVal s₂) (val.queryVal q) ∧
      neighborhoodEvidence (val.stateVal s₁ + val.stateVal s₂) (val.queryVal q) = e₁ + e₂ :=
  ⟨diamond_isCombined_at_decomposable v (.fvar s₁) (.fvar s₂) (.fvar q),
   ⟨neighborhoodEvidence (val.stateVal s₁) (val.queryVal q),
    neighborhoodEvidence (val.stateVal s₂) (val.queryVal q),
    rfl, rfl,
    neighborhoodEvidence_add (val.stateVal s₁) (val.stateVal s₂) (val.queryVal q)⟩⟩

/-- Revision commutativity: the syntactic diamond for commutativity corresponds
    to the semantic fact that multiset addition is commutative. -/
theorem neighborhood_diamond_revision_comm
    (v : WMExtVertex) (val : NeighborhoodValuation) (s₁ s₂ : String) :
    langDiamond (wmExtVertexLanguageDef v) isRevision
      (pRevise (.fvar s₁) (.fvar s₂)) ∧
    val.stateVal s₁ + val.stateVal s₂ = val.stateVal s₂ + val.stateVal s₁ :=
  ⟨diamond_isCommuted v (.fvar s₁) (.fvar s₂),
   Multiset.add_comm (val.stateVal s₁) (val.stateVal s₂)⟩

/-! ## Section 4: Singleton Adequacy Lift

Pointed-model satisfaction ↔ strength = 1 lifts through the valuation. -/

/-- Singleton adequacy: a pointed neighborhood model satisfies a modal formula
    iff the WM query strength at the singleton state equals 1, lifted through
    the valuation. -/
theorem neighborhood_singleton_adequacy_lift
    (val : NeighborhoodValuation) (pn : PointedNeighborhood) (φ : ModalQuery)
    (s : String) (hs : val.stateVal s = {pn}) :
    pn.satisfies φ ↔
      WorldModel.queryStrength
        (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (val.stateVal s) φ = 1 := by
  rw [hs]
  exact singleton_adequacy_strength_one pn φ

/-! ## Section 5: Evidence Barb (Process-Algebraic Observable)

A revised neighborhood state exhibits an evidence barb when the combined
evidence is non-zero — the topological observable. -/

/-- A revised neighborhood state exhibits an evidence barb when the combined
    extraction is non-zero. Under the valuation, this means the per-source
    neighborhood models yield non-trivial evidence for the query. -/
theorem neighborhood_revised_barb (v : WMExtVertex) (s₁ s₂ q : String)
    (hne : ¬ isZeroEvidence
      (pCombine (pExtract (.fvar s₁) (.fvar q))
                (pExtract (.fvar s₂) (.fvar q)))) :
    wmHasEvidenceBarb (wmExtVertexLanguageDef v)
      (pRevise (.fvar s₁) (.fvar s₂)) (.fvar q) :=
  wmRevisedState_evidenceBarb v (.fvar s₁) (.fvar s₂) (.fvar q) hne

/-! ## Section 6: Satisfying Model → Non-Zero Evidence

If any pointed neighborhood model in the multiset satisfies the query,
the evidence is non-zero. -/

/-- If a pointed neighborhood model in the multiset satisfies the query,
    the positive evidence count is at least 1. -/
theorem neighborhood_nonzero_evidence_of_satisfying_model
    (W : Multiset PointedNeighborhood) (φ : ModalQuery)
    (pn : PointedNeighborhood) (hmem : pn ∈ W) (hsat : pn.satisfies φ) :
    (neighborhoodEvidence W φ).pos ≥ 1 := by
  classical
  simp only [neighborhoodEvidence]
  have hpos : 0 < Multiset.countP (fun pn => pn.satisfies φ) W :=
    Multiset.countP_pos.mpr ⟨pn, hmem, hsat⟩
  exact_mod_cast hpos

/-- Valued version: if the valuation maps a state name to a multiset containing
    a model satisfying the query, then evidence is non-zero. -/
theorem neighborhood_nonzero_evidence_of_satisfying_model_val
    (val : NeighborhoodValuation) (s : String) (φ : ModalQuery)
    (pn : PointedNeighborhood) (hmem : pn ∈ val.stateVal s) (hsat : pn.satisfies φ) :
    (neighborhoodEvidence (val.stateVal s) φ).pos ≥ 1 :=
  neighborhood_nonzero_evidence_of_satisfying_model (val.stateVal s) φ pn hmem hsat

/-! ## Section 7: Consequence Lifting Through OSLF

Pointwise semantic implication between modal formulas lifts to WM strength
ordering on multiset states. -/

/-- Pointwise neighborhood semantic implication lifts to WM strength ordering:
    if every pointed model satisfying φ also satisfies ψ, then the WM query
    strength of φ is at most that of ψ at any multiset state. -/
theorem neighborhood_consequence_lifts
    (φ ψ : ModalQuery)
    (himp : ∀ pn : PointedNeighborhood, pn.satisfies φ → pn.satisfies ψ)
    (W : Multiset PointedNeighborhood) :
    WorldModel.queryStrength
      (State := Multiset PointedNeighborhood) (Query := ModalQuery) W φ ≤
    WorldModel.queryStrength
      (State := Multiset PointedNeighborhood) (Query := ModalQuery) W ψ :=
  queryStrength_le_of_pointwise W φ ψ himp

/-! ## Section 8: Galois Corollary with Neighborhood Reading

The Galois connection ◇ ⊣ □ instantiated with evidence-theoretic meaning:
"forward evidence reachability" is adjoint to "backward model-theoretic safety." -/

/-- The ◇ ⊣ □ Galois connection at any WM vertex gives, when read through
    the neighborhood fiber:
    - Forward (◇): "evidence can be decomposed into per-source satisfaction counts"
    - Backward (□): "all predecessors of a combined evidence form satisfy the safety property"

    The adjunction says these are equivalent perspectives on the same evidence-theoretic
    structure. -/
theorem neighborhood_galois_evidence_safety
    (v : WMExtVertex) (ψ : Pattern → Prop) :
    (∀ p, langDiamond (wmExtVertexLanguageDef v) isCombined p → ψ p) ↔
    (∀ p, isCombined p → langBox (wmExtVertexLanguageDef v) ψ p) :=
  wmCalc_decomposability_safety v ψ

/-- Full-vertex Galois corollary. -/
theorem neighborhood_galois_evidence_safety_full
    (v : WMFullVertex) (ψ : Pattern → Prop) :
    (∀ p, langDiamond (wmFullVertexLanguageDef v) isCombined p → ψ p) ↔
    (∀ p, isCombined p → langBox (wmFullVertexLanguageDef v) ψ p) :=
  wmFullCalc_decomposability_safety v ψ

end Mettapedia.OSLF.Framework.WMCalculusNeighborhoodBridge
