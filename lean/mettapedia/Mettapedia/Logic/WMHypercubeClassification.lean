import KnuthSkilling.Core.Hypercube
import Mettapedia.Logic.PLNWorldModelGeneric
import Mettapedia.Logic.WorldModelOverlap

/-!
# WM Regime Classification via the KS Probability Hypercube

Each world-model regime corresponds to a specific vertex in the
Knuth-Skilling probability hypercube (logic axis × representation axis).

## The Classification

| WM Regime | Logic Axis | Representation Axis | Hypercube Vertex |
|-----------|-----------|---------------------|-----------------|
| Additive (main) | Boolean | Point | Classical Bayesian |
| Overlap-aware | Boolean | Bounds | Imprecise Probability |
| Evidence-tracking | Heyting | 2D bounds | PLN Evidence |
| Trust-gated | Heyting | Point | Heyting Point KS |

## Why This Matters

The WM regimes are NOT arbitrary design choices. Each regime is determined
by two independent structural decisions:
1. Does your event algebra satisfy excluded middle? (Boolean vs Heyting)
2. Do you track evidence per-channel or summarize to a point? (Bounds vs Point)

The KS formalism then constrains what kinds of additive and representation
surfaces fit those choices. The WM calculus instantiates each vertex.

## References

- KS Hypercube: `KnuthSkilling/Core/Hypercube.lean` (13 theorems, 0 sorry)
- WM regimes: `PLNWorldModelGeneric.lean` (additive) + `WorldModelOverlap.lean` (overlap)
- WM-PLN book, Ch 4 (Evidence Carriers), Ch 18 (Future: Probability Hypercube)

0 sorry.
-/

namespace Mettapedia.Logic.WMHypercubeClassification

open KnuthSkilling.Hypercube
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric

/-! ## 1. WM Regimes as named structures

Each regime is characterized by its algebraic properties. -/

/-- The four WM regimes from the book, corresponding to hypercube vertices. -/
inductive WMRegime
  | additive          -- Ch 4: additive revision, extract_add
  | overlapAware      -- Ch 4 §non-additive: overlap correction needed
  | evidenceTracking  -- Ch 5: 2D evidence carriers (n⁺, n⁻)
  | trustGated        -- Ch 15: revision depends on source authority
  deriving DecidableEq, BEq, Repr

/-! ## 2. Classification: each regime → hypercube vertex -/

/-- Map each WM regime to its KS probability hypercube vertex. -/
def regimeVertex : WMRegime → HypercubeVertex
  | .additive         => classicalProbability      -- Boolean + Point
  | .overlapAware     => impreciseProbability      -- Boolean + Bounds
  | .evidenceTracking => plnEvidence               -- Heyting + 2D
  | .trustGated       => heytingPointKS            -- Heyting + Point

/-! ## 3. Classification theorems -/

/-- The additive WM regime lives at the classical Bayesian vertex:
    Boolean logic (excluded middle holds) + point-valued probabilities. -/
theorem additive_is_classical :
    regimeVertex .additive = classicalProbability := rfl

/-- The overlap-aware regime lives at the imprecise probability vertex:
    Boolean logic + interval/bounds-valued (because overlap creates uncertainty). -/
theorem overlap_is_imprecise :
    regimeVertex .overlapAware = impreciseProbability := rfl

/-- The evidence-tracking regime lives at the PLN evidence vertex:
    Heyting logic (no excluded middle — incomparable evidence states exist) +
    2D bounds (positive/negative evidence tracked separately). -/
theorem evidence_is_pln :
    regimeVertex .evidenceTracking = plnEvidence := rfl

/-- The trust-gated regime lives at the Heyting point vertex:
    Heyting logic (source authority breaks Boolean symmetry) +
    point-valued (single authority score, not interval). -/
theorem trustgated_is_heyting_point :
    regimeVertex .trustGated = heytingPointKS := rfl

/-! ## 4. Structural properties of the classification -/

/-- The classification is injective: distinct regimes → distinct vertices. -/
theorem classification_injective :
    Function.Injective regimeVertex := by
  intro a b hab
  cases a <;> cases b <;> simp [regimeVertex, classicalProbability, impreciseProbability,
    plnEvidence, heytingPointKS, HypercubeVertex.mk.injEq] at hab <;> rfl

/-- The classification covers all four vertices of the 2×2 hypercube. -/
theorem classification_surjective_on_2x2 :
    ∀ v : HypercubeVertex,
    v = classicalProbability ∨ v = impreciseProbability ∨
    v = plnEvidence ∨ v = heytingPointKS →
    ∃ r, regimeVertex r = v := by
  intro v hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact ⟨.additive, rfl⟩
  · exact ⟨.overlapAware, rfl⟩
  · exact ⟨.evidenceTracking, rfl⟩
  · exact ⟨.trustGated, rfl⟩

/-! ## 5. Logic axis determines complement behavior

The logic axis controls whether evidence has "slack" (Heyting excluded-middle gap)
or is "tight" (Boolean complement equality). This is the GATE between the
additive powerhouse and the evidence-tracking regime. -/

/-- Additive and overlap regimes use Boolean logic (complement equality). -/
theorem additive_boolean : (regimeVertex .additive).logic = .boolean := rfl
theorem overlap_boolean : (regimeVertex .overlapAware).logic = .boolean := rfl

/-- Evidence and trust-gated regimes use Heyting logic (complement inequality). -/
theorem evidence_heyting : (regimeVertex .evidenceTracking).logic = .heyting := rfl
theorem trustgated_heyting : (regimeVertex .trustGated).logic = .heyting := rfl

/-! ## 6. Representation axis determines evidence dimensionality -/

/-- Additive and trust-gated use point representation (scalar summary). -/
theorem additive_point : (regimeVertex .additive).representation = .point := rfl
theorem trustgated_point : (regimeVertex .trustGated).representation = .point := rfl

/-- Overlap and evidence-tracking use bounds/2D representation. -/
theorem overlap_bounds : (regimeVertex .overlapAware).representation = .bounds := rfl
theorem evidence_bounds : (regimeVertex .evidenceTracking).representation = .bounds := rfl

/-! ## 7. Summary -/

/-- The complete hypercube classification in one theorem. -/
theorem hypercube_classification_summary :
    regimeVertex .additive = ⟨.boolean, .point⟩ ∧
    regimeVertex .overlapAware = ⟨.boolean, .bounds⟩ ∧
    regimeVertex .evidenceTracking = ⟨.heyting, .bounds⟩ ∧
    regimeVertex .trustGated = ⟨.heyting, .point⟩ := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Mettapedia.Logic.WMHypercubeClassification
