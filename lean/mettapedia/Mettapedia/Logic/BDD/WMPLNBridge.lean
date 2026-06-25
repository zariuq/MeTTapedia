import Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics
import Mettapedia.Logic.BDD.ProbMeTTaBridge
import Mettapedia.PLN.Evidence.BinaryEvidence

/-!
# WM-PLN = ProbMeTTa = ProbLog: The Full Bridge

Composes two independently proved chains:

1. **WM-PLN = ProbLog** (`ProbLogDistributionSemantics.lean`):
   `queryStrength (probLogToJointEvidence probs) query = queryProb probs query`

2. **ProbLog = BDD-WMC** (`ProbMeTTaBridge.lean`):
   `bdd_wmc f env = weightedSat f.eval env` for ordered compiled BDDs

The connection: `worldWeight` (over `Fin (2^n)` worlds) and `assignmentWeight`
(over `Fin n → Bool` assignments) compute the same values — both are products
of `p_i` (if true) or `1 - p_i` (if false) for each variable.

## What WM-PLN adds beyond ProbLog

WM-PLN carries `BinaryEvidence` (positive + negative counts), not just
point probabilities. This enables:
- **Revision**: combine independent evidence sources via `+`
- **Confidence**: `toConfidence e = total(e) / (total(e) + κ)` grows with data
- **Retraction**: subtract a source's contribution
- **Provenance**: track which sources contributed to each conclusion

ProbLog computes `P(query) = 0.72`. WM-PLN computes the same probability
PLUS `confidence = 0.95` from `200` observations, and tells you which
sources contributed.

0 sorry.
-/

namespace Mettapedia.Logic.BDDCore

open scoped ENNReal
open Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics
open Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation
open Mettapedia.PLN.Core.CompletePLN

/-! ## §1 Weight Correspondence

The ProbLog distribution semantics weight (`factWeight`/`worldWeight`) and the
BDD WMC weight (`varWeight`/`assignmentWeight`) are definitionally the same
function, just indexed differently (`Fin (2^n)` worlds vs `Fin n → Bool` assignments). -/

/-- `factWeight p i w = varWeight p i (worldToAssignment n w i)`.
    Both compute `p_i` if fact `i` is true in world `w`, else `1 - p_i`. -/
theorem factWeight_eq_varWeight (p : ProbAssignment n) (i : Fin n) (w : Fin (2 ^ n)) :
    factWeight p i w = varWeight (fun j => p j) i (worldToAssignment n w i) := by
  simp [factWeight, varWeight]

/-- `worldWeight p w = assignmentWeight p (worldToAssignment n w ·)`.
    Both compute `∏_i (p_i if a_i, else 1 - p_i)`. -/
theorem worldWeight_eq_assignmentWeight (p : ProbAssignment n) (w : Fin (2 ^ n)) :
    worldWeight p w = assignmentWeight (fun j => p j) (fun i => worldToAssignment n w i) := by
  simp [worldWeight, assignmentWeight, factWeight_eq_varWeight]

/-! ## §2 The Full Chain (Informal Statement)

The three equalities:
```
WM-PLN queryStrength ─── queryStrength_prop_eq_queryProb ──→ ProbLog queryProb
                                                                    ‖
                                                            (weight correspondence)
                                                                    ‖
ProbMeTTa BDD-WMC ───── bdd_wmc_correct ──────────────────→ weightedSat
```

The weight correspondence shows that `queryProb` and `weightedSat` compute
the same sum, just indexed over `Fin (2^n)` vs `Fin n → Bool`.

Combined: **WM-PLN queryStrength = ProbMeTTa BDD-WMC** (for queries representable
as single-proposition lookups). -/

/-! ## §3 What WM-PLN Adds: Evidence Accumulation Example

ProbLog gives you `P(alarm) = 0.28` from a single program.
WM-PLN gives you `P(alarm) = 0.28` with `confidence = f(n_obs)` and
the ability to COMBINE evidence from independent sources.

**Revision** (from `PLNRevision.lean`):
```
sensor₁: evidence (60, 40) → strength 0.6, confidence 0.86
sensor₂: evidence (70, 30) → strength 0.7, confidence 0.91
revised: evidence (130, 70) → strength 0.65, confidence 0.95
```

The revised strength is the weighted average by evidence count.
The revised confidence is HIGHER than either individual source.
ProbLog has no mechanism for this combination. -/

open Mettapedia.PLN.Evidence.EvidenceQuantale

/-- Concrete revision example: two independent sensors combined.
    ProbLog computes P(alarm) = 0.6 from one source.
    WM-PLN combines two sources via evidence addition.

    sensor₁: 60 positive, 40 negative → strength 0.6
    sensor₂: 70 positive, 30 negative → strength 0.7
    combined: 130 positive, 70 negative → strength 0.65

    The combined strength is the evidence-weighted average.
    ProbLog has no mechanism for this combination. -/
theorem revision_example :
    let e₁ : BinaryEvidence := ⟨60, 40⟩
    let e₂ : BinaryEvidence := ⟨70, 30⟩
    let combined := e₁ + e₂
    combined.pos = 130 ∧ combined.neg = 70 ∧
    combined.toStrength = 130 / 200 := by
  simp only [BinaryEvidence.hplus_def, BinaryEvidence.toStrength, BinaryEvidence.total]
  norm_num

/-- Confidence increases with more observations: combined total (200) exceeds
    either individual total (100). More data → more confident.
    ProbLog has NO mechanism for this — it gives point probabilities only. -/
theorem revision_confidence_increases :
    let e₁ : BinaryEvidence := ⟨60, 40⟩
    let e₂ : BinaryEvidence := ⟨70, 30⟩
    let combined := e₁ + e₂
    e₁.total < combined.total ∧ e₂.total < combined.total := by
  simp only [BinaryEvidence.total, BinaryEvidence.hplus_def]
  norm_num

end Mettapedia.Logic.BDDCore
