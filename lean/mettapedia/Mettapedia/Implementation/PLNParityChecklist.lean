import Mettapedia.Implementation.MettaVerification
import Mettapedia.Logic.NARSMettaTruthFunctions
import Mettapedia.Logic.PLN_KS_Bridge
import Mettapedia.Logic.PLNDerivedFromEvidence
import Mettapedia.Logic.PLNFrechetBounds
import Mettapedia.Logic.PLNInferenceRules
import Mettapedia.Logic.PeTTaLibPLNTruthFunctions
import Mettapedia.Logic.WMPLNJustifiedTruthFunctions
import Mettapedia.Logic.WMPLNDistributionalTruthFunctions
import Mettapedia.Logic.WMPLNDistributionalExamples
import Mettapedia.Logic.PeTTaLibPLNFormalAnalysis

/-!
# PLN Parity Checklist (MeTTa / PLN Book / Lean)

This file is an index for aligning three layers:

1. **MeTTa implementation** (e.g. `DeductionFormula.metta`)
2. **Textbook/PLN-book formulas** (Goertzel et al.)
3. **Lean formalization** (this repository)

It is intentionally *not* a prose paper section (no `.md`), just a compiler-checked map of names.

## Core: Deduction + Consistency

- Deduction strength formula (PLN book; MeTTa `DeductionFormula.metta`)
  - Lean spec (numeric): `Mettapedia.Logic.PLNDeduction.simpleDeductionStrengthFormula`
  - Lean derivation (probability + independence): `Mettapedia.Logic.PLN.pln_deduction_from_total_probability_ctx`
  - MeTTa parity proof: `Mettapedia.Implementation.MettaVerification.metta_deduction_correct`

- Fréchet / consistency bounds (MeTTa "smallest/largest intersection" helpers)
  - Lean bounds and equivalence: `Mettapedia.Logic.PLNFrechetBounds.frechet_bounds_iff_consistency`
  - MeTTa inner-expression check: `Mettapedia.Implementation.MettaVerification.smallest_intersection_correct`

## BinaryEvidence Semantics (Quantale/Heyting layer)

- BinaryEvidence carrier and operations: `Mettapedia.Logic.EvidenceQuantale`
  - `BinaryEvidence` (counts `(nPlus, nMinus)`), `toStrength`, `toConfidence`
  - revision-style aggregation lemma: `Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength_hplus`
  - polarity-swap negation rule: `Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength_flip`
    (defined in `Mettapedia.Logic.PLNDerivedFromEvidence`)

- KS vs BinaryEvidence (totality gate, “no faithful point semantics”)
  - `Mettapedia.Logic.PLN_KS_Bridge.evidence_no_point_representation`

## Additional PLN book-style rules (partial coverage)

- Similarity / inheritance conversions: `Mettapedia.Logic.PLNInferenceRules`
  - `twoInh2Sim`, `inh2sim`, `sim2inh`, `transitiveSimilarity`

- Modus ponens family: `Mettapedia.Logic.PLNInferenceRules`
  - `modusPonens`, `modusTollens`, `symmetricModusPonens`

## MeTTa Libraries: Truth-Function Coverage

### PeTTa PLN (`hyperon/PeTTa/lib/lib_pln.metta`)

Preferred discussion surface:

- transparent mirror: `Mettapedia.Logic.PeTTaLibPLNTruthFunctions`
- justified WM theory: `Mettapedia.Logic.WMPLNJustifiedTruthFunctions`
- formal comparison: `Mettapedia.Logic.PeTTaLibPLNFormalAnalysis`

Rule-status dashboard:

| Family | Current public Lean surface | Status |
|--------|-----------------------------|--------|
| Revision | `truthRevision` | exact WM-backed |
| Induction | `truthInduction` | exact WM-backed |
| Abduction | `truthAbduction` | exact WM-backed |
| Negation | `truthNegation` | exact WM-backed |
| Deduction | `truthDeductionConservative` | conservative scalar |
| Modus Ponens | `truthModusPonensConservative` | conservative scalar |
| Symmetric Modus Ponens | `truthSymmetricModusPonensConservative` | conservative scalar |
| Predictive Implication | `truthPredictiveImplicationConservative` | constructive WM addition |
| Conjunction (conditional regime) | `truthConjunctionConditionalConservative` | exact strength + conservative confidence |
| Conjunction (independent regime) | `truthConjunctionIndependentEvidenceStyle` | evidence-style weight-space regime |
| Conjunction (hypergeometric regime) | `truthConjunctionHypergeometric` | finite-population modal regime |
| Mirror-only heuristic extras | `truthInversion`, `truthEquivalenceToImplication`, `truthTransitiveSimilarity`, `truthEvaluationImplication` | compare in `PeTTaLibPLNFormalAnalysis` |

Selected WM-backed additions not present in the current PeTTa library:

- `truthPredictiveImplicationConservative`
  - conservative scalar lifting of the Chapter-14 predictive-implication lane
  - analysis hooks:
    `PeTTaLibPLNFormalAnalysis.predictiveImplication_conf_le_inputs`
- `truthConjunctionConditionalConservative`
  - exact conditional-conjunction strength surface plus conservative confidence
  - WM lift:
    `WMPLNJustifiedTruthFunctions.truthConjunctionConditional_strength_lifts_to_wm`
  - analysis hooks:
    `PeTTaLibPLNFormalAnalysis.conjunctionConditional_strength_lifts_to_wm`,
    `PeTTaLibPLNFormalAnalysis.conjunctionConditional_conf_le_inputs`
- `truthConjunctionIndependentEvidenceStyle`
  - explicit independent / weight-space conjunction regime
- `truthConjunctionHypergeometric`
  - explicit finite-population hypergeometric regime

- Confidence↔weight helpers:
  - `PeTTaLibPLNTruthFunctions.c2w`, `PeTTaLibPLNTruthFunctions.w2c`
- Core truth functions:
  - `Truth_Deduction` → `PeTTaLibPLNTruthFunctions.truthDeduction`
  - `Truth_Induction` → `PeTTaLibPLNTruthFunctions.truthInduction`
  - `Truth_Abduction` → `PeTTaLibPLNTruthFunctions.truthAbduction`
  - `Truth_ModusPonens` → `PeTTaLibPLNTruthFunctions.truthModusPonens`
  - `Truth_SymmetricModusPonens` → `PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens`
  - `Truth_Revision` → `PeTTaLibPLNTruthFunctions.truthRevision`
  - `Truth_Negation` → `PeTTaLibPLNTruthFunctions.truthNegation`
- Additional (WIP/heuristic in OpenCog / PeTTa):
  - `Truth_inversion` → `PeTTaLibPLNTruthFunctions.truthInversion`
  - `Truth_equivalenceToImplication` → `PeTTaLibPLNTruthFunctions.truthEquivalenceToImplication`
  - `Truth_transitiveSimilarity` → `PeTTaLibPLNTruthFunctions.truthTransitiveSimilarity`
  - `Truth_evaluationImplication` → `PeTTaLibPLNTruthFunctions.truthEvaluationImplication`

### PeTTa NARS (`hyperon/PeTTa/lib/lib_nars.metta`)

Lean mirror: `Mettapedia.Logic.NARSMettaTruthFunctions`

- Confidence↔weight helpers:
  - `c2w`, `w2c`
- Core syllogisms:
  - `Truth_Deduction` → `NARSMettaTruthFunctions.truthDeduction`
  - `Truth_Induction` → `NARSMettaTruthFunctions.truthInduction`
  - `Truth_Abduction` → `NARSMettaTruthFunctions.truthAbduction`
  - `Truth_Exemplification` → `NARSMettaTruthFunctions.truthExemplification`
- Other NARS truth functions:
  - `Truth_Revision` → `NARSMettaTruthFunctions.truthRevision`
  - `Truth_Negation` → `NARSMettaTruthFunctions.truthNegation`
  - `Truth_Intersection` / `Truth_Union` / `Truth_Comparison` / `Truth_Analogy` / …
    → corresponding defs in `NARSMettaTruthFunctions`

## TODO (next derivation targets)

- Derive *all* truth-value rules in `lib_pln` from the same semantic base:
  - start from `BinaryEvidence` + a semantics map (and explicit independence assumptions),
  - keep `[0,1]` strength/confidence as a lossy *view*, not the foundational carrier.

- NARS parity:
  - `Mettapedia.Logic.NARSMettaTruthFunctions` mirrors `lib_nars.metta` formulas.
  - `Mettapedia.Logic.PLN` also contains a *paper-focused* PLN↔NARS power comparison
    (arXiv:2412.19524) in `PLNDerivation.lean`; it is intentionally separate from the PeTTa mirror.

## Distribution-backed WM surfaces

Primary Lean entry point:

- `Mettapedia.Logic.WMPLNDistributionalTruthFunctions`

Distributional dashboard:

| Regime | Current public Lean surface | Status |
|--------|-----------------------------|--------|
| Dirichlet over worlds (prop STV) | `truthDirichletOverWorldsPropSTV` | exact view wrapper |
| Dirichlet over worlds (prop WTV) | `truthDirichletOverWorldsPropWTV` | exact view wrapper |
| Dirichlet over worlds (prop ITV) | `truthDirichletOverWorldsPropITVBayesExact95` | exact interval wrapper |
| Dirichlet over worlds (link STV) | `truthDirichletOverWorldsLinkSTV` | exact view wrapper |
| Dirichlet over worlds (link WTV) | `truthDirichletOverWorldsLinkWTV` | exact view wrapper |
| Dirichlet over worlds (link ITV) | `truthDirichletOverWorldsLinkITVBayesExact95` | exact interval wrapper |
| Markov-Dirichlet transition (STV) | `truthMarkovDirichletTransitionSTV` | exact query view |
| Markov-Dirichlet transition (WTV) | `truthMarkovDirichletTransitionWTV` | exact query view |
| Markov-Dirichlet transition (Walley ITV) | `truthMarkovDirichletTransitionITVWalley` | exact interval view |
| Markov-Dirichlet predictive chain mass | `truthMarkovDirichletPredictiveChainMass` | exact process-level predictive mass |
| Hypergeometric conjunction (modal TV) | `truthConjunctionHypergeometricModal` | exact modal point view |
| Hypergeometric conjunction (support ITV) | `truthConjunctionHypergeometricInterval` | exact support interval view |
| Hypergeometric conjunction (CDF ITV, 95%) | `truthConjunctionHypergeometricCDFInterval95` | exact equal-tailed CDF interval view |

Worked examples:

- `Mettapedia.Logic.WMPLNDistributionalExamples`
  - Dirichlet-over-worlds one-atom example:
    `binaryCoin_propEvidence`, `binaryCoin_propSTV_strength`,
    `binaryCoin_propSTV_confidence`
  - Markov one-step transition example:
    `oneStep01_transitionEvidence`, `oneStep01_walley_lower`,
    `oneStep01_walley_upper`, `oneStep01_walley_credibility`
  - Hypergeometric finite-population example:
    `hypergeometric_10_8_7_modal_strength`,
    `hypergeometric_10_8_7_interval_lower`,
    `hypergeometric_10_8_7_interval_upper`
  - Hypergeometric 95% CDF example:
    `hypergeometric_20_10_10_cdf95_credibility`,
    `hypergeometric_20_10_10_cdf95_width_nonneg`,
    `hypergeometric_20_10_10_cdf95_bounds_in_unit`
-/

namespace Mettapedia.Implementation.PLNParityChecklist
end Mettapedia.Implementation.PLNParityChecklist
