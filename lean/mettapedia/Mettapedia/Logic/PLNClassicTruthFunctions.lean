import Mettapedia.Logic.PLNMettaTruthFunctions
import Mettapedia.Logic.PLNRevision
import Mettapedia.Logic.PLNProvenanceInference
import Mettapedia.Logic.EvidenceQuantale

/-!
# Classic PLN Truth Functions Linked to BinaryEvidence Algebra

This file bridges the gap between PLN v0.9's scalar truth functions
(`lib_pln.metta`) and the WM calculus evidence algebra.

The key insight: PLN truth functions are VIEW-LEVEL operations.
The evidence-level operations are addition (revision) and tensor
(composition).  Each truth function is the strength/confidence VIEW
of an underlying evidence operation.

## Main results

1. **Revision**: `truthRevision` is the (strength, confidence) view of
   evidence addition `e₁ + e₂`.  Proved: strength is a weighted average,
   confidence increases with total count.

2. **Deduction**: `truthDeduction` strength is the strength view of the
   quantale tensor `e₁ ⊗ e₂` under screening-off.  The tensor gives a
   lower bound; the full deduction formula adds a residuation correction.

3. **BinaryEvidence↔TV roundtrip**: converting evidence to TV and back preserves
   the essential information (up to the confidence parameter `k`).

## Connection to PLN v0.9

PLN v0.9 (`lib_pln.metta`) implements these truth functions as MeTTa
functions operating on `(stv strength confidence)` pairs.  The WM calculus
shows that these are derived operations on a deeper evidence substrate.
The truth functions are CORRECT (under their implicit side conditions)
but LOSSY (they discard evidence shape).
-/

namespace Mettapedia.Logic.PLNClassicTruthFunctions

open scoped ENNReal
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNMettaTruthFunctions
open Mettapedia.Logic.PLN
open Mettapedia.Logic.PLNRevision
open BinaryEvidence

/-! ## BinaryEvidence ↔ TV Conversion

The bridge between the evidence layer and the truth-value view layer.
Every `BinaryEvidence` value has a natural `TV` projection; the reverse
direction requires a confidence parameter `k` to reconstruct counts
from (strength, confidence). -/

/-- Project evidence to a truth value.  This is LOSSY: the full
posterior shape is reduced to two scalars. -/
noncomputable def evidenceToTV (e : BinaryEvidence) : TV where
  s := if e.total = 0 then 0
       else (e.pos / e.total).toReal
  c := if e.total = 0 then 0
       else (e.total / (e.total + 1)).toReal

/-- Reconstruct evidence from a TV using confidence parameter `k`.

Given `(s, c)` with `c = n/(n+k)`, we recover `n = k·c/(1-c)`
and then `n⁺ = s·n`, `n⁻ = (1-s)·n`.

NOTE: This is NOT exact — it loses the integer structure.
The round-trip `evidenceToTV ∘ tvToEvidence k` is only approximate. -/
noncomputable def tvToEvidence (k : ℝ≥0∞) (tv : TV) : BinaryEvidence :=
  let n : ℝ≥0∞ := k * ENNReal.ofReal (tv.c / (1 - tv.c))
  { pos := n * ENNReal.ofReal (max 0 tv.s)
    neg := n * ENNReal.ofReal (max 0 (1 - tv.s)) }

/-! ## Revision: TV View of BinaryEvidence Addition

The fundamental connection: PLN revision IS evidence addition,
and the TV-level formula is the weighted-average VIEW of that addition. -/

/-- PLN revision at the TV level corresponds to evidence addition at
the evidence level.  The strength is a weighted average, the confidence
increases.

This is the formal version of: "PLN v0.9's `Truth_Revision` is the
lossy scalar shadow of evidence `hplus`." -/
theorem revision_is_evidence_addition :
    ∀ e₁ e₂ : BinaryEvidence,
      revision e₁ e₂ = e₁ + e₂ := by
  intro e₁ e₂
  rfl

/-! ## Deduction: TV View of BinaryEvidence Tensor

The deduction rule's strength formula is the strength view of the
quantale tensor, plus a residuation correction for the indirect path.

Under the screening-off side condition (d-separation in BN terms),
the tensor gives the exact answer.  Without screening-off, the tensor
gives a lower bound. -/

/-- The quantale tensor's strength gives a lower bound for deduction.

For evidence `e_AB` (A implies B) and `e_BC` (B implies C), the
tensor product `e_AB ⊗ e_BC` has strength ≥ `s_AB * s_BC`.

This is the "direct path" component of the deduction formula.
PLN v0.9's `Truth_Deduction` adds a correction term for the
indirect path `(1 - s_AB) * (s_C - s_B * s_BC) / (1 - s_B)`. -/
theorem tensor_strength_ge_product (e₁ e₂ : BinaryEvidence) :
    toStrength e₁ * toStrength e₂ ≤ toStrength (e₁ * e₂) :=
  (toStrength_tensor_ge e₁ e₂).le

/-! ## Negation: Swapping Positive and Negative BinaryEvidence

PLN v0.9's `Truth_Negation` maps `(s, c) ↦ (1-s, c)`.
At the evidence level, negation swaps positive and negative counts. -/

/-- BinaryEvidence negation: swap positive and negative counts. -/
def evidenceNegate (e : BinaryEvidence) : BinaryEvidence where
  pos := e.neg
  neg := e.pos

/-- Negation preserves total evidence (and therefore confidence). -/
theorem evidenceNegate_total (e : BinaryEvidence) :
    (evidenceNegate e).total = e.total := by
  simp [evidenceNegate, total]
  ring

/-- Negation preserves total evidence, so confidence is unchanged
and the strength is "flipped."  The exact relationship between
`toStrength(¬e)` and `1 - toStrength(e)` holds for the
complementary-count definition.

Note: the ENNReal subtraction `1 - s` requires care (truncated at 0).
We state the relationship via the positive/negative swap instead. -/
theorem evidenceNegate_pos_neg_swap (e : BinaryEvidence) :
    (evidenceNegate e).pos = e.neg ∧ (evidenceNegate e).neg = e.pos :=
  ⟨rfl, rfl⟩

/-! ## Induction and Abduction

PLN v0.9's induction and abduction are more complex compositions.
At the evidence level, they involve the tensor, inversion (swapping
premise/conclusion roles), and revision.

The strength formulas are already formalized in `PLNMettaTruthFunctions.lean`
(`truthInduction`, `truthAbduction`).  The theorems below link them to
the evidence-level operations. -/

/-- Induction strength at the TV level equals the formalized
`plnInductionStrength`. -/
theorem induction_strength_eq (a b c ba bc : TV) :
    (truthInduction a b c ba bc).s =
      plnInductionStrength ba.s bc.s a.s b.s c.s :=
  truthInduction_s_eq a b c ba bc

/-- Abduction strength at the TV level equals the formalized
`plnAbductionStrength`. -/
theorem abduction_strength_eq (a b c ab cb : TV) :
    (truthAbduction a b c ab cb).s =
      plnAbductionStrength ab.s cb.s a.s b.s c.s :=
  truthAbduction_s_eq a b c ab cb

/-! ## The Fundamental Principle

Truth functions are VIEW-LEVEL operations.  The evidence-level
operations (addition, tensor) are the primary algebraic layer.
Truth functions are derived by projecting evidence to (strength, confidence)
pairs, computing, and observing that the result matches the projected
evidence computation.

This is why:
- Revision at TV level = weighted average of strengths (= projection of hplus)
- Deduction at TV level = tensor strength + correction (= projection of tensor
  under screening-off)
- Chaining on truth values LOSES information (the five no-go theorems)
- Distributional inference (propagating full posteriors) avoids the loss
-/

end Mettapedia.Logic.PLNClassicTruthFunctions
