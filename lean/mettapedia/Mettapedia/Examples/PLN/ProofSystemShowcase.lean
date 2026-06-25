import Mettapedia.PLN.Evidence.EvidenceProofSystem
import Mettapedia.PLN.Evidence.KSEvidenceMeasureBridge
import Mettapedia.PLN.WorldModel.WMHypercubeClassification
import Mettapedia.PLN.Bridges.ProbabilityTheory.ModalProbabilityBridge
import Mettapedia.PLN.Bridges.GSLT.WeightMapBridge
import Mettapedia.PLN.WorldModel.WMCalculusSoundness
import Mettapedia.PLN.Evidence.ComplexEvidenceCarrier
import Mettapedia.PLN.WorldModel.UniversalEnsembleWM
import Mettapedia.PLN.Evidence.SourceReliability
import Mettapedia.Examples.PLN.ClassicExamples

/-!
# PLN as a Proof System — Showcase

READ THIS FILE. It is the single entry point for the entire formalization.

## Executive Summary

1. The WM-PLN evidence algebra IS a classical proof system: revision = cut,
   extraction = evaluation, forgetting = weakening, commutativity = exchange.
   All four structural rules of sequent calculus are closed Lean theorems.

2. The probability hypercube classifies 4 WM regimes at 4 probability vertices.
   The ℂ carrier sits at the quantum vertex (no lattice → amplitude inference).
   KS-style additive structure provides the foundation; bridge files then
   connect evidence summaries and measure-theoretic readings.

3. Implementations of the WM calculus prove `CalculusSound` to get ALL algebraic
   properties for free — the certification path for any backend.

## Files

| File                          | Theorems | What it proves                         |
|-------------------------------|----------|----------------------------------------|
| `EvidenceProofSystem`         |       10 | Curry-Howard: 4 structural rules       |
| `KSEvidenceMeasureBridge`     |        8 | KS → evidence → measure triangle       |
| `WMHypercubeClassification`   |       10 | 4 regimes → 4 vertices (injective)     |
| `ModalProbabilityBridge`      |       14 | 13-axis classification + quantum       |
| `GSLT/WeightMapBridge`        |        6 | GSLT weight map = WM extract           |
| `WMCalculusSoundness`         |        5 | Sound calculi inherit all properties    |
| `ComplexEvidenceCarrier`      |        8 | ℂ carrier: quantum vertex              |
| `UniversalEnsembleWM`         |        5 | Universality: existence + uniqueness    |
| `SourceReliability`           |        8 | Dawid-Skene reliability layer           |
| `PLNClassicExamples`          |       15 | Deduction, raven induction, forgetting  |

## References

- Stay, Meredith, Wells, "Generating Hypercubes of Type Systems" (2026)
- Meredith, "Computation, Causality, and Consciousness" (2026)
- Knuth & Skilling, "Foundations of Inference" (2012)
- Howard, "The Formulae-as-Types Notion of Construction" (1980)
- WM-PLN book, Ch 7 (Natively Typed World Models)
-/

namespace Mettapedia.Examples.PLN.ProofSystemShowcase

/-! ## 1. Curry-Howard Correspondence for Evidence

Revision = cut rule. Extraction = evaluation. Forgetting = weakening.
Commutativity = exchange. Self-revision = contraction.

All four structural rules of classical sequent calculus are proven. -/

#check @Mettapedia.PLN.Evidence.EvidenceProofSystem.structural_rules_summary
  -- cut ∧ weakening ∧ exchange ∧ contraction

/-! ## 2. KS Foundation

The evidence algebra satisfies the additive/monotone structure used here.
Θ = `.ess` (total evidence count) is the additive statistic proved in the bridge.
The measure bridge factors through Θ via Dirac weighting.
σ-additivity requires countable additivity — finitely additive measures
do NOT extend (proven by counterexample from the KS formalization). -/

#check @Mettapedia.PLN.Evidence.KSEvidenceMeasureBridge.Θ_additive
  -- Θ(e₁+e₂) = Θ(e₁) + Θ(e₂)
#check @Mettapedia.PLN.Evidence.KSEvidenceMeasureBridge.triangle_summary
  -- KS → evidence → measure triangle
#check @Mettapedia.PLN.Evidence.KSEvidenceMeasureBridge.sigma_additivity_boundary
  -- ¬IsSigmaAdditive for diffuse finitely-additive measures

/-! ## 3. Hypercube Classification

4 WM regimes (additive, overlapAware, evidenceTracking, trustGated)
map injectively to 4 vertices in a 2-axis (logic × representation)
hypercube, and to 4 vertices in the full 13-axis probability hypercube.
The ℂ carrier sits OUTSIDE all 4: orthomodular, no lattice → quantum. -/

#check @Mettapedia.PLN.WorldModel.WMHypercubeClassification.hypercube_classification_summary
  -- 4 regimes → 4 vertices, all commutative & probabilistic
#check @Mettapedia.PLN.Bridges.ProbabilityTheory.ModalProbabilityBridge.full_classification_injective
  -- wmToProbVertex is injective on 13 axes
#check @Mettapedia.PLN.Bridges.ProbabilityTheory.ModalProbabilityBridge.quantum_not_classical
  -- ℂ carrier ≠ classical vertex (orthomodular ≠ boolean)

/-! ## 4. GSLT Weight Map = WM Extract

The GSLT's weight map on rewrite states IS the WM's extract function.
weight_add = extract_add. The bridge is definitional. -/

#check @Mettapedia.PLN.Bridges.GSLT.WeightMapBridge.weight_satisfies_extract_add
  -- ea.weight (s₁+s₂) q = ea.weight s₁ q + ea.weight s₂ q
#check @Mettapedia.PLN.Bridges.GSLT.WeightMapBridge.full_picture_summary
  -- classification + weakness ordering

/-! ## 5. Calculus Soundness

Define `WMCalculus` (the operational rules: revise, extract, forget).
Prove `CalculusSound` (the calculus agrees with the model). Get ALL
algebraic properties (extract_add, sequential composition, zero
preservation) for free. -/

#check @Mettapedia.PLN.WorldModel.WMCalculusSoundness.soundness_guarantees
  -- extraction ∧ revision ∧ extract_add — all transfer from soundness

/-! ## 6. Universality and Breadth

Every typed observation space generates a UNIQUE additive world model
(existence + uniqueness). The ℂ carrier gives amplitude inference.
Source reliability (Dawid-Skene) layers on top without breaking algebra. -/

#check @Mettapedia.PLN.WorldModel.UniversalEnsembleWM.universalEnsembleTheorem
  -- existence + uniqueness of the additive extension
#check @Mettapedia.PLN.Evidence.ComplexEvidenceCarrier.complex_carrier_summary
  -- tensor + commutativity + Born probability
#check @Mettapedia.PLN.Evidence.SourceReliability.reliability_summary
  -- perfect preserves, inverted zeroes, empirical > text

/-! ## 7. Empirical Validation

Deduction-revision (A→B, B→D with stamp disjointness),
raven induction (two ravens, forgetting preserves disjoint source),
and frame/relevance (Sam the raven, Pingu the penguin) — all
kernel-checked with `decide`. -/

#check @ClassicExamples.dr_stamps_disjoint
  -- deduction-revision stamp disjointness
#check @ClassicExamples.ri_forget_rv2_preserves_rv1
  -- raven induction: forgetting rv2 preserves rv1
#check @ClassicExamples.fr_sam_pingu_disjoint
  -- frame/relevance: Sam and Pingu are disjoint sources

/-! ## 8. What This Means

PLN is a classical proof system with:
- KS foundations (uniqueness of evidence representation)
- Hypercube classification (4 regimes at 4 probability vertices)
- GSLT connection (weight map = extract, forward transport)
- Calculus soundness (prove CalculusSound, get all properties for free)
- Universality (every typed observation space → unique world model)
- Quantum extension (ℂ carrier at the orthomodular vertex)

The theorem surfaces above are closed and avoid native-decision shortcuts or
extra axioms beyond the accepted Lean footprint. -/

end Mettapedia.Examples.PLN.ProofSystemShowcase
