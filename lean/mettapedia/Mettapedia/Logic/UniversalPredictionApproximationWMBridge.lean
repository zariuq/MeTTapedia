import Mettapedia.Logic.UniversalPredictionApproximation
import Mettapedia.Logic.BinaryEvidence

/-!
# Anytime Universal-Mixture Approximation → WM Strength Bridge

This file turns finite-prefix universal-mixture approximations into
**WM-style query scores** by packaging each approximate probability mass as
`BinaryEvidence`.

The first bridge is intentionally simple:
- query = a binary-string prefix event `x`
- score = `BinaryEvidence.toStrength` of the approximant evidence

This gives a clean theorem spine:
- the WM-style score equals the approximate mixture mass exactly,
- the score is monotone in the approximation budget `n`,
- and it is bounded above by the full universal-mixture score.

This is the first theorem-level handle on *incremental Solomonoff
approximation feeding WM semantics*.
-/

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical
open scoped BigOperators

open Mettapedia.Logic.EvidenceQuantale

/-- WM-style evidence view of a finite universal-mixture approximant.
The evidence is chosen so that `toStrength` recovers the approximate mass. -/
noncomputable def approxEvidence
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (n : ℕ) (x : BinString) : BinaryEvidence :=
  { pos := (xiApproxSemimeasure ν w hw n) x
    neg := (1 : ENNReal) - (xiApproxSemimeasure ν w hw n) x }

/-- The corresponding WM-style strength score. -/
noncomputable def approxQueryStrength
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (n : ℕ) (x : BinString) : ENNReal :=
  BinaryEvidence.toStrength (approxEvidence ν w hw n x)

theorem approxQueryStrength_eq_mass
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (n : ℕ) (x : BinString) :
    approxQueryStrength ν w hw n x = (xiApproxSemimeasure ν w hw n) x := by
  unfold approxQueryStrength approxEvidence
  have hx : (xiApproxSemimeasure ν w hw n) x ≤ 1 :=
    semimeasure_le_one (xiApproxSemimeasure ν w hw n) x
  simpa using
    (BinaryEvidence.toStrength_of_scaled
      ((xiApproxSemimeasure ν w hw n) x) 1 hx one_ne_zero ENNReal.one_ne_top)

/-- The limiting WM-style score for the full universal mixture. -/
noncomputable def fullQueryStrength
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (x : BinString) : ENNReal :=
  BinaryEvidence.toStrength
    { pos := (xiSemimeasure ν w hw) x
      neg := (1 : ENNReal) - (xiSemimeasure ν w hw) x }

theorem fullQueryStrength_eq_mass
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (x : BinString) :
    fullQueryStrength ν w hw x = (xiSemimeasure ν w hw) x := by
  unfold fullQueryStrength
  have hx : (xiSemimeasure ν w hw) x ≤ 1 := semimeasure_le_one (xiSemimeasure ν w hw) x
  simpa using
    (BinaryEvidence.toStrength_of_scaled
      ((xiSemimeasure ν w hw) x) 1 hx one_ne_zero ENNReal.one_ne_top)

theorem approxQueryStrength_mono
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1)
    {n m : ℕ} (hnm : n ≤ m) (x : BinString) :
    approxQueryStrength ν w hw n x ≤ approxQueryStrength ν w hw m x := by
  rw [approxQueryStrength_eq_mass, approxQueryStrength_eq_mass]
  exact xiApproxSemimeasure_mono ν w hw hnm x

theorem approxQueryStrength_le_full
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (n : ℕ) (x : BinString) :
    approxQueryStrength ν w hw n x ≤ fullQueryStrength ν w hw x := by
  rw [approxQueryStrength_eq_mass, fullQueryStrength_eq_mass]
  exact xiApproxSemimeasure_le_full ν w hw n x

/-- Specialized WM-style score for the canonical geometric universal mixture. -/
noncomputable def geomApproxQueryStrength
    (ν : ℕ → Semimeasure) (n : ℕ) (x : BinString) : ENNReal :=
  approxQueryStrength ν geometricWeight tsum_geometricWeight_le_one n x

/-- Full geometric-mixture WM-style score. -/
noncomputable def geomFullQueryStrength
    (ν : ℕ → Semimeasure) (x : BinString) : ENNReal :=
  fullQueryStrength ν geometricWeight tsum_geometricWeight_le_one x

theorem geomApproxQueryStrength_eq_mass
    (ν : ℕ → Semimeasure) (n : ℕ) (x : BinString) :
    geomApproxQueryStrength ν n x = (xiGeomApproxSemimeasure ν n) x := by
  exact approxQueryStrength_eq_mass ν geometricWeight tsum_geometricWeight_le_one n x

theorem geomFullQueryStrength_eq_mass
    (ν : ℕ → Semimeasure) (x : BinString) :
    geomFullQueryStrength ν x = (xiGeomSemimeasure ν) x := by
  exact fullQueryStrength_eq_mass ν geometricWeight tsum_geometricWeight_le_one x

theorem geomApproxQueryStrength_mono
    (ν : ℕ → Semimeasure) {n m : ℕ} (hnm : n ≤ m) (x : BinString) :
    geomApproxQueryStrength ν n x ≤ geomApproxQueryStrength ν m x := by
  exact approxQueryStrength_mono ν geometricWeight tsum_geometricWeight_le_one hnm x

theorem geomApproxQueryStrength_le_full
    (ν : ℕ → Semimeasure) (n : ℕ) (x : BinString) :
    geomApproxQueryStrength ν n x ≤ geomFullQueryStrength ν x := by
  exact approxQueryStrength_le_full ν geometricWeight tsum_geometricWeight_le_one n x

end Mettapedia.Logic.UniversalPrediction
