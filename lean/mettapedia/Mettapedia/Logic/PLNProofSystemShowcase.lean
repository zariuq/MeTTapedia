import Mettapedia.Logic.EvidenceProofSystem
import Mettapedia.Logic.KSEvidenceMeasureBridge
import Mettapedia.Logic.WMHypercubeClassification
import Mettapedia.Logic.ModalProbabilityBridge
import Mettapedia.Logic.GSLTWeightMapBridge
import Mettapedia.Logic.RuntimeSoundnessBridge
import Mettapedia.Logic.ComplexEvidenceCarrier
import Mettapedia.Logic.UniversalEnsembleWM
import Mettapedia.Logic.SourceReliability
import Mettapedia.Logic.PLNClassicExamples

/-!
# PLN as a Proof System — Showcase

READ THIS FILE. It is the single entry point for the entire formalization.

## Executive Summary

1. The WM-PLN evidence algebra IS a classical proof system: revision = cut,
   extraction = evaluation, forgetting = weakening, commutativity = exchange.
   All four structural rules of sequent calculus are proven (0 sorry).

2. The probability hypercube classifies 4 WM regimes at 4 probability vertices.
   The ℂ carrier sits at the quantum vertex (no lattice → amplitude inference).
   KS axioms provide the foundation; the representation theorem gives uniqueness.

3. Runtime implementations prove `RuntimeSound` to get ALL algebraic properties
   for free — the certification path for mettail-c and mettail-rust.

## Files (0 sorry across all)

| File                          | Theorems | What it proves                         |
|-------------------------------|----------|----------------------------------------|
| `EvidenceProofSystem`         |       10 | Curry-Howard: 4 structural rules       |
| `KSEvidenceMeasureBridge`     |        8 | KS → evidence → measure triangle       |
| `WMHypercubeClassification`   |       10 | 4 regimes → 4 vertices (injective)     |
| `ModalProbabilityBridge`      |       14 | 13-axis classification + quantum       |
| `GSLTWeightMapBridge`         |        6 | GSLT weight map = WM extract           |
| `RuntimeSoundnessBridge`      |        5 | Sound runtimes inherit all properties   |
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

namespace Mettapedia.Logic.PLNProofSystemShowcase

/-! ## 1. Curry-Howard Correspondence for Evidence

Revision = cut rule. Extraction = evaluation. Forgetting = weakening.
Commutativity = exchange. Self-revision = contraction.

All four structural rules of classical sequent calculus are proven. -/

#check @EvidenceProofSystem.structural_rules_summary
  -- cut ∧ weakening ∧ exchange ∧ contraction

/-! ## 2. KS Foundation

The evidence algebra IS a Knuth-Skilling ordered semigroup.
Θ = `.ess` (total evidence count) is the additive representation.
The measure bridge factors through Θ via Dirac weighting.
σ-additivity requires countable additivity — finitely additive measures
do NOT extend (proven by counterexample from the KS formalization). -/

#check @KSEvidenceMeasureBridge.Θ_additive
  -- Θ(e₁+e₂) = Θ(e₁) + Θ(e₂)
#check @KSEvidenceMeasureBridge.triangle_summary
  -- KS → evidence → measure triangle
#check @KSEvidenceMeasureBridge.sigma_additivity_boundary
  -- ¬IsSigmaAdditive for diffuse finitely-additive measures

/-! ## 3. Hypercube Classification

4 WM regimes (additive, overlapAware, evidenceTracking, trustGated)
map injectively to 4 vertices in a 2-axis (logic × representation)
hypercube, and to 4 vertices in the full 13-axis probability hypercube.
The ℂ carrier sits OUTSIDE all 4: orthomodular, no lattice → quantum. -/

#check @WMHypercubeClassification.hypercube_classification_summary
  -- 4 regimes → 4 vertices, all commutative & probabilistic
#check @ModalProbabilityBridge.full_classification_injective
  -- wmToProbVertex is injective on 13 axes
#check @ModalProbabilityBridge.quantum_not_classical
  -- ℂ carrier ≠ classical vertex (orthomodular ≠ boolean)

/-! ## 4. GSLT Weight Map = WM Extract

The GSLT's weight map on rewrite states IS the WM's extract function.
weight_add = extract_add. The bridge is definitional. -/

#check @GSLTWeightMapBridge.weight_satisfies_extract_add
  -- ea.weight (s₁+s₂) q = ea.weight s₁ q + ea.weight s₂ q
#check @GSLTWeightMapBridge.full_picture_summary
  -- classification + weakness ordering

/-! ## 5. Runtime Certification

Define `EvidenceRuntime`. Prove `RuntimeSound`. Get ALL algebraic
properties (extract_add, sequential composition, zero preservation)
for free. This is the certification path for mettail-c and mettail-rust. -/

#check @RuntimeSoundnessBridge.soundness_guarantees
  -- extraction ∧ revision ∧ extract_add — all transfer from soundness

/-! ## 6. Universality and Breadth

Every typed observation space generates a UNIQUE additive world model
(existence + uniqueness). The ℂ carrier gives amplitude inference.
Source reliability (Dawid-Skene) layers on top without breaking algebra. -/

#check @UniversalEnsembleWM.universalEnsembleTheorem
  -- existence + uniqueness of the additive extension
#check @ComplexEvidenceCarrier.complex_carrier_summary
  -- tensor + commutativity + Born probability
#check @SourceReliability.reliability_summary
  -- perfect preserves, inverted zeroes, empirical > text

/-! ## 7. Empirical Validation

Deduction-revision (A→B, B→D with stamp disjointness),
raven induction (two ravens, forgetting preserves disjoint source),
and frame/relevance (Sam the raven, Pingu the penguin) — all
kernel-checked with `decide`. -/

#check @PLNClassicExamples.dr_stamps_disjoint
  -- deduction-revision stamp disjointness
#check @PLNClassicExamples.ri_forget_rv2_preserves_rv1
  -- raven induction: forgetting rv2 preserves rv1
#check @PLNClassicExamples.fr_sam_pingu_disjoint
  -- frame/relevance: Sam and Pingu are disjoint sources

/-! ## 8. What This Means

PLN is a classical proof system with:
- KS foundations (uniqueness of evidence representation)
- Hypercube classification (4 regimes at 4 probability vertices)
- GSLT connection (weight map = extract, forward transport)
- Certifiable runtime implementations (prove RuntimeSound, get all properties)
- Universality (every typed observation space → unique world model)
- Quantum extension (ℂ carrier at the orthomodular vertex)

All theorems above: 0 sorry, 0 native_decide, 0 axiom beyond Lean's core. -/

end Mettapedia.Logic.PLNProofSystemShowcase
