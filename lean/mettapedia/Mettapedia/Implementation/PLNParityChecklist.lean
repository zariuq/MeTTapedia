import Mettapedia.Implementation.MettaVerification
import Mettapedia.Logic.NARSMettaTruthFunctions
import Mettapedia.Logic.PLN_KS_Bridge
import Mettapedia.Logic.PLNDerivedFromEvidence
import Mettapedia.Logic.PLNFrechetBounds
import Mettapedia.Logic.PLNInferenceRules
import Mettapedia.Logic.PLNMettaTruthFunctions

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

## Evidence Semantics (Quantale/Heyting layer)

- Evidence carrier and operations: `Mettapedia.Logic.PLNEvidence`
  - `Evidence` (counts `(nPlus, nMinus)`), `toStrength`, `toConfidence`
  - revision-style aggregation lemma: `Mettapedia.Logic.PLNEvidence.Evidence.toStrength_hplus`
  - polarity-swap negation rule: `Mettapedia.Logic.PLNEvidence.Evidence.toStrength_flip`
    (defined in `Mettapedia.Logic.PLNDerivedFromEvidence`)

- KS vs Evidence (totality gate, “no faithful point semantics”)
  - `Mettapedia.Logic.PLN_KS_Bridge.evidence_no_point_representation`

## Additional PLN book-style rules (partial coverage)

- Similarity / inheritance conversions: `Mettapedia.Logic.PLNInferenceRules`
  - `twoInh2Sim`, `inh2sim`, `sim2inh`, `transitiveSimilarity`

- Modus ponens family: `Mettapedia.Logic.PLNInferenceRules`
  - `modusPonens`, `modusTollens`, `symmetricModusPonens`

## MeTTa Libraries: Truth-Function Coverage

### PeTTa PLN (`hyperon/PeTTa/lib/lib_pln.metta`)

Lean mirror: `Mettapedia.Logic.PLNMettaTruthFunctions`

- Confidence↔weight helpers:
  - `c2w`, `w2c`
- Core truth functions:
  - `Truth_Deduction` → `PLNMettaTruthFunctions.truthDeduction`
  - `Truth_Induction` → `PLNMettaTruthFunctions.truthInduction`
  - `Truth_Abduction` → `PLNMettaTruthFunctions.truthAbduction`
  - `Truth_ModusPonens` → `PLNMettaTruthFunctions.truthModusPonens`
  - `Truth_SymmetricModusPonens` → `PLNMettaTruthFunctions.truthSymmetricModusPonens`
  - `Truth_Revision` → `PLNMettaTruthFunctions.truthRevision`
  - `Truth_Negation` → `PLNMettaTruthFunctions.truthNegation`
- Additional (WIP/heuristic in OpenCog / PeTTa):
  - `Truth_inversion` → `PLNMettaTruthFunctions.truthInversion`
  - `Truth_equivalenceToImplication` → `PLNMettaTruthFunctions.truthEquivalenceToImplication`
  - `Truth_transitiveSimilarity` → `PLNMettaTruthFunctions.truthTransitiveSimilarity`
  - `Truth_evaluationImplication` → `PLNMettaTruthFunctions.truthEvaluationImplication`

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
  - start from `Evidence` + a semantics map (and explicit independence assumptions),
  - keep `[0,1]` strength/confidence as a lossy *view*, not the foundational carrier.

- NARS parity:
  - `Mettapedia.Logic.NARSMettaTruthFunctions` mirrors `lib_nars.metta` formulas.
  - `Mettapedia.Logic.PLN` also contains a *paper-focused* PLN↔NARS power comparison
    (arXiv:2412.19524) in `PLNDerivation.lean`; it is intentionally separate from the PeTTa mirror.
-/

namespace Mettapedia.Implementation.PLNParityChecklist
end Mettapedia.Implementation.PLNParityChecklist
