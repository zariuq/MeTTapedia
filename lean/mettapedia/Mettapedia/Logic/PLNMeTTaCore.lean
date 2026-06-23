import Mettapedia.Logic.EvidenceSTVBridge
import Mettapedia.Logic.PLNDeduction
import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.PLNInferenceCalculus
import Mettapedia.Logic.PLNInferenceRules
import Mettapedia.Logic.PLNLinkCalculusSoundness
import Mettapedia.Logic.PLNTruthTower
import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Mettapedia.Languages.MeTTa.OSLFCore.Atomspace
import Mettapedia.Languages.MeTTa.OSLFCore.MinimalOps

/-!
# PLN-MeTTaCore Bridge

This module bridges the gap between:
1. **PLN formulas** (proved correct in PLNDerivation.lean)
2. **MeTTaCore evaluation** (formalized interpreter semantics)

## The Verification Goal

We want to prove:
> When MeTTaCore evaluates PLN inference rules, the results are
> mathematically correct according to probability theory.

This gives us an end-to-end verification:
```
Probability Axioms
      ↓ (PLNDerivation.lean)
PLN Formulas (proved correct)
      ↓ (this file)
MeTTaCore Evaluation (proved to match formulas)
      ↓
Correct PLN Inference
```

## Design Decision: Unified Formula

Both `deductionFormulaSTV` (PLNDeduction.lean) and `plnDeductionStrength` (PLNDerivation.lean)
compute the same formula. The only difference is:
- `deductionFormulaSTV` wraps result in `clamp01` for defensive programming
- `plnDeductionStrength` returns raw result (bounds proved separately)

We prove these are equivalent under valid inputs, giving a single source of truth.

## References

- EvidenceSTVBridge.lean: canonical STV view
- PLNDeduction.lean: deduction formula with clamp01
- PLNDerivation.lean: Raw formula + measure-theoretic correctness proofs
- MeTTaCore: Evaluation semantics
- lib_pln.metta: MeTTa PLN implementation
-/

namespace Mettapedia.Logic.PLNMeTTaCore

open Mettapedia.Logic.PLNDeduction
open Mettapedia.Logic.PLN
open Mettapedia.Logic.PLNInferenceRules
open Mettapedia.Logic.PLNConfidenceWeight.EvidenceWeightCoordinate
open Mettapedia.Languages.MeTTa.OSLFCore

/-- Canonical STV view for this bridge module. -/
abbrev STV := Mettapedia.Logic.EvidenceSTVBridge.DeductionSTV

/-! ## Count-backed STV views -/

/-- The MeTTa-facing PLN odds coordinate, with unit prior weight. -/
noncomputable abbrev semanticPLNOddsCoordinate :
    Mettapedia.Logic.PLNConfidenceWeight.EvidenceWeightCoordinate :=
  plnOddsCoordinate 1 (by norm_num)

/-- Convert positive finite binary evidence counts to the MeTTa-facing STV view.

The input counts are the load-bearing state; the displayed confidence is only
the PLN odds coordinate for the total evidence weight. -/
noncomputable def semanticPLNCountSTV
    (e : Mettapedia.Logic.PLNTruthTower.BinaryCounts)
    (hTotal : e.total ≠ 0) : STV where
  strength := e.strength
  confidence := semanticPLNOddsCoordinate.encode e.total
  strength_nonneg :=
    (e.strength_mem_unit_of_total_ne_zero hTotal).1
  strength_le_one :=
    (e.strength_mem_unit_of_total_ne_zero hTotal).2
  confidence_nonneg := by
    exact (plnOddsCoordinate_encode_in_Ico 1 (by norm_num) e.total_nonneg).1
  confidence_le_one := by
    exact le_of_lt
      (plnOddsCoordinate_encode_in_Ico 1 (by norm_num) e.total_nonneg).2

/-- Decoding the PLN odds confidence display recovers the evidence weight. -/
private theorem c2w_semanticPLNOddsCoordinate_encode
    {w : ℝ} (hw : 0 ≤ w) :
    Mettapedia.Logic.PLNInferenceCalculus.c2w
        (semanticPLNOddsCoordinate.encode w) = w := by
  unfold semanticPLNOddsCoordinate
  unfold Mettapedia.Logic.PLNInferenceCalculus.c2w plnOddsCoordinate
  have hden_pos : 0 < w + 1 := by linarith
  have hlt : w / (w + 1) < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  simp [hlt]
  field_simp [ne_of_gt hden_pos]
  ring

/-- Encoding evidence weight as PLN odds is the same display as
`PLNInferenceCalculus.w2c` at prior weight one. -/
private theorem w2c_eq_semanticPLNOddsCoordinate_encode {w : ℝ} :
    Mettapedia.Logic.PLNInferenceCalculus.w2c w =
      semanticPLNOddsCoordinate.encode w :=
  rfl

/-! ## Unified PLN Deduction Formula

We establish that `deductionFormulaSTV` and `plnDeductionStrength` compute
the same value under valid inputs. This is the key unification. -/

/-- The raw PLN deduction formula (without clamp01).
    This is the canonical formula that both implementations compute. -/
noncomputable def plnDeductionRaw (s_PQ s_QR s_Q s_R : ℝ) : ℝ :=
  s_PQ * s_QR + (1 - s_PQ) * (s_R - s_Q * s_QR) / (1 - s_Q)

/-- `plnDeductionRaw` equals `plnDeductionStrength` by definition -/
theorem plnDeductionRaw_eq_plnDeductionStrength (s_PQ s_QR s_Q s_R : ℝ) :
    plnDeductionRaw s_PQ s_QR s_Q s_R = plnDeductionStrength s_PQ s_QR s_Q s_R := rfl

/-- **Unification Theorem**: Under valid inputs, `deductionFormulaSTV.strength`
    equals `plnDeductionStrength` (and hence `plnDeductionRaw`).

    The key insight: when consistency holds and Q is not near 1, the formula
    produces a value in [0,1], so clamp01 is the identity function. -/
theorem unified_deduction_formula
    (tvP tvQ tvR tvPQ tvQR : STV)
    (h_consistency : conditionalProbabilityConsistency tvP.strength tvQ.strength tvPQ.strength ∧
                     conditionalProbabilityConsistency tvQ.strength tvR.strength tvQR.strength)
    (h_q_not_near_1 : tvQ.strength ≤ 0.9999)
    (h_in_range : let raw := plnDeductionRaw tvPQ.strength tvQR.strength tvQ.strength tvR.strength
                  0 ≤ raw ∧ raw ≤ 1) :
    (deductionFormulaSTV tvP tvQ tvR tvPQ tvQR).strength =
    plnDeductionStrength tvPQ.strength tvQR.strength tvQ.strength tvR.strength := by
  unfold deductionFormulaSTV plnDeductionStrength plnDeductionRaw at *
  simp only [h_consistency, ↓reduceIte, not_lt.mpr h_q_not_near_1, not_true_eq_false, and_self]
  rw [clamp01_of_mem_unit (Set.mem_Icc.mpr h_in_range)]

/-! ## STV as MeTTaCore Semantic Values

Instead of encoding STVs as atoms (which has precision issues), we work at
the semantic level. MeTTaCore evaluation of PLN is modeled as operating
directly on STVs. -/

/-- Semantic PLN deduction: operates directly on STVs.
    This is what MeTTaCore evaluation *means* when it evaluates Truth_Deduction. -/
noncomputable def semanticPLNDeduction (tvP tvQ tvR tvPQ tvQR : STV) : STV :=
  deductionFormulaSTV tvP tvQ tvR tvPQ tvQR

/-- **Semantic Soundness**: Semantic PLN deduction computes the mathematically
    correct formula from probability theory.

    This is the core correctness theorem for MeTTaCore PLN. -/
theorem semantic_pln_deduction_correct
    (tvP tvQ tvR tvPQ tvQR : STV)
    (h_consistency : conditionalProbabilityConsistency tvP.strength tvQ.strength tvPQ.strength ∧
                     conditionalProbabilityConsistency tvQ.strength tvR.strength tvQR.strength)
    (h_q_not_near_1 : tvQ.strength ≤ 0.9999)
    (h_in_range : let raw := plnDeductionRaw tvPQ.strength tvQR.strength tvQ.strength tvR.strength
                  0 ≤ raw ∧ raw ≤ 1) :
    (semanticPLNDeduction tvP tvQ tvR tvPQ tvQR).strength =
    plnDeductionStrength tvPQ.strength tvQR.strength tvQ.strength tvR.strength := by
  exact unified_deduction_formula tvP tvQ tvR tvPQ tvQR h_consistency h_q_not_near_1 h_in_range

/-! ## Bounds from Consistency

We can derive the `h_in_range` condition from the consistency conditions
using theorems from PLNDerivation.lean. -/

/-- Helper: Extract positivity from consistency condition -/
lemma consistency_implies_q_pos (h : conditionalProbabilityConsistency pA pQ s) : 0 < pA := h.1

/-- Under valid probability inputs, the PLN formula is bounded.
    This uses `pln_deduction_bounded` from PLNDerivation.lean. -/
theorem pln_formula_in_range
    (_tvP tvQ tvR tvPQ tvQR : STV)
    (h_q_pos : 0 < tvQ.strength)
    (h_q_lt1 : tvQ.strength < 1)
    (h_constraint_upper : tvR.strength - tvQ.strength * tvQR.strength ≤ 1 - tvQ.strength)
    (h_constraint_lower : tvQ.strength * tvQR.strength ≤ tvR.strength) :
    let raw := plnDeductionRaw tvPQ.strength tvQR.strength tvQ.strength tvR.strength
    0 ≤ raw ∧ raw ≤ 1 := by
  constructor
  · -- Non-negativity from pln_deduction_nonneg
    exact pln_deduction_nonneg tvPQ.strength tvQR.strength tvQ.strength tvR.strength
      ⟨tvPQ.strength_nonneg, tvPQ.strength_le_one⟩
      tvQR.strength_nonneg
      ⟨h_q_pos, h_q_lt1⟩
      h_constraint_lower
  · -- Upper bound from pln_deduction_bounded
    exact pln_deduction_bounded tvPQ.strength tvQR.strength tvQ.strength tvR.strength
      ⟨tvPQ.strength_nonneg, tvPQ.strength_le_one⟩
      ⟨tvQR.strength_nonneg, tvQR.strength_le_one⟩
      ⟨h_q_pos, h_q_lt1⟩
      ⟨tvR.strength_nonneg, tvR.strength_le_one⟩
      h_constraint_upper

/-- **Formula Soundness Theorem**: under valid PLN inputs, MeTTaCore semantic
    deduction computes the canonical raw PLN deduction formula.

    This combines:
    1. unified_deduction_formula (clamp01 is identity)
    2. pln_formula_in_range (formula is in [0,1]).

    The measure-context theorem `semantic_pln_deduction_measure_sound` below is
    the one that additionally consumes `pln_deduction_from_total_probability_ctx`
    and reaches `P(C|A)`. -/
theorem complete_pln_soundness
    (tvP tvQ tvR tvPQ tvQR : STV)
    (h_consistency : conditionalProbabilityConsistency tvP.strength tvQ.strength tvPQ.strength ∧
                     conditionalProbabilityConsistency tvQ.strength tvR.strength tvQR.strength)
    (h_q_pos : 0 < tvQ.strength)
    (h_q_not_near_1 : tvQ.strength ≤ 0.9999)
    (h_constraint_upper : tvR.strength - tvQ.strength * tvQR.strength ≤ 1 - tvQ.strength)
    (h_constraint_lower : tvQ.strength * tvQR.strength ≤ tvR.strength) :
    (semanticPLNDeduction tvP tvQ tvR tvPQ tvQR).strength =
    plnDeductionStrength tvPQ.strength tvQR.strength tvQ.strength tvR.strength := by
  have h_q_lt1 : tvQ.strength < 1 := by linarith
  apply semantic_pln_deduction_correct
  · exact h_consistency
  · exact h_q_not_near_1
  · exact pln_formula_in_range tvP tvQ tvR tvPQ tvQR h_q_pos h_q_lt1
      h_constraint_upper h_constraint_lower

/-! ### Measure-context soundness for semantic deduction

The theorem above reaches the raw PLN formula. The next theorem consumes the
measure-theoretic derivation theorem, so the MeTTa-facing semantic deduction
surface reaches the actual conditional probability under the explicit PLN
deduction context.
-/

/-- **Measure Soundness for Semantic Deduction**: if the supplied STVs are the
term/link probabilities of a probability space satisfying the PLN deduction
independence context, semantic PLN deduction computes the true conditional
probability `P(C | A)`.

This is the non-tautological end-to-end deduction bridge:
`semanticPLNDeduction` -> guarded STV formula -> `plnDeductionStrength` ->
measure-theoretic total probability under the explicit context. -/
theorem semantic_pln_deduction_measure_sound
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {A B C : Set Ω}
    (ctx : PLNDeductionMeasureContext (μ := μ) (A := A) (B := B) (C := C))
    (tvP tvQ tvR tvPQ tvQR : STV)
    (h_consistency :
      conditionalProbabilityConsistency tvP.strength tvQ.strength tvPQ.strength ∧
        conditionalProbabilityConsistency tvQ.strength tvR.strength tvQR.strength)
    (h_q_not_near_1 : tvQ.strength ≤ 0.9999)
    (_hP : tvP.strength = μ.real A)
    (hQ : tvQ.strength = μ.real B)
    (hR : tvR.strength = μ.real C)
    (hPQ : tvPQ.strength = μ.real (B ∩ A) / μ.real A)
    (hQR : tvQR.strength = μ.real (C ∩ B) / μ.real B) :
    (semanticPLNDeduction tvP tvQ tvR tvPQ tvQR).strength =
      μ.real (C ∩ A) / μ.real A := by
  have hctx :=
    (pln_deduction_from_total_probability_ctx (μ := μ) (A := A) (B := B) (C := C) ctx)
  have hraw :
      plnDeductionStrength tvPQ.strength tvQR.strength tvQ.strength tvR.strength =
        μ.real (C ∩ A) / μ.real A := by
    have hQR' : μ.real (C ∩ B) / tvQ.strength = tvQR.strength := by
      simpa [hQ] using hQR.symm
    have h :
        μ.real (C ∩ A) / μ.real A =
          plnDeductionStrength tvPQ.strength tvQR.strength tvQ.strength tvR.strength := by
      simpa [← hPQ, hQR', ← hQ, ← hR] using hctx
    exact h.symm
  have hraw_expr :
      tvPQ.strength * tvQR.strength +
          (1 - tvPQ.strength) *
            (tvR.strength - tvQ.strength * tvQR.strength) / (1 - tvQ.strength) =
        μ.real (C ∩ A) / μ.real A := by
    simpa [plnDeductionStrength] using hraw
  have hmem :
      μ.real (C ∩ A) / μ.real A ∈ Set.Icc (0 : ℝ) 1 :=
    Mettapedia.Logic.PLNLinkCalculus.Soundness.condProb_mem_unit
      (μ := μ) (A := A) (C := C) ctx.hA_pos
  unfold semanticPLNDeduction deductionFormulaSTV
  simp only [h_consistency]
  have hq : ¬ tvQ.strength > 0.9999 := not_lt.mpr h_q_not_near_1
  simp only [hq, ↓reduceIte]
  rw [hraw_expr]
  exact clamp01_of_mem_unit hmem

/-! ## PLN Induction

Induction: given B→A and B→C, infer A→C.
Uses Bayes inversion to get A→B, then deduction. -/

/-- The raw PLN induction formula (from PLNDerivation.lean) -/
noncomputable def plnInductionRaw (s_BA s_BC s_A s_B s_C : ℝ) : ℝ :=
  plnInductionStrength s_BA s_BC s_A s_B s_C

/-- `plnInductionRaw` equals `plnInductionStrength` by definition -/
theorem plnInductionRaw_eq_plnInductionStrength (s_BA s_BC s_A s_B s_C : ℝ) :
    plnInductionRaw s_BA s_BC s_A s_B s_C = plnInductionStrength s_BA s_BC s_A s_B s_C := rfl

/-- Semantic PLN induction: operates directly on STVs.
    This is what MeTTaCore evaluation *means* when it evaluates Truth_Induction.

    Parameters: tvA, tvB, tvC are term truth values; tvBA is B→A, tvBC is B→C. -/
noncomputable def semanticPLNInduction (tvA tvB tvC tvBA tvBC : STV) : STV :=
  let s := plnInductionStrength tvBA.strength tvBC.strength tvA.strength tvB.strength tvC.strength
  let c := min tvBA.confidence tvBC.confidence
  ⟨clamp01 s, clamp01 c, clamp01_nonneg s, clamp01_le_one s, clamp01_nonneg c, clamp01_le_one c⟩

/-- **Induction Soundness**: Under valid inputs, computes the probability formula. -/
theorem semantic_pln_induction_correct
    (tvA tvB tvC tvBA tvBC : STV)
    (h_bounds : plnInductionStrength tvBA.strength tvBC.strength tvA.strength tvB.strength tvC.strength ≤ 1)
    (h_nonneg : 0 ≤ plnInductionStrength tvBA.strength tvBC.strength tvA.strength tvB.strength tvC.strength) :
    (semanticPLNInduction tvA tvB tvC tvBA tvBC).strength =
    plnInductionStrength tvBA.strength tvBC.strength tvA.strength tvB.strength tvC.strength := by
  unfold semanticPLNInduction
  simp only
  rw [clamp01_of_mem_unit (Set.mem_Icc.mpr ⟨h_nonneg, h_bounds⟩)]

/-- **Measure Soundness for Semantic Induction / SourceRule**: if `tvBA`
represents `P(A | B)` and `tvBC` represents `P(C | B)` in a probability space
satisfying the explicit PLN deduction context, semantic PLN induction computes
the true conditional probability `P(C | A)`.

The proof reuses the weight-first link-calculus source-rule soundness theorem;
the STV-to-WTV conversion is only an internal bridge and does not introduce a
second semantics. -/
theorem semantic_pln_induction_measure_sound
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {A B C : Set Ω}
    (ctx : PLNDeductionMeasureContext (μ := μ) (A := A) (B := B) (C := C))
    (tvA tvB tvC tvBA tvBC : STV)
    (hA : tvA.strength = μ.real A)
    (hB : tvB.strength = μ.real B)
    (hC : tvC.strength = μ.real C)
    (hBA : tvBA.strength = μ.real (A ∩ B) / μ.real B)
    (hBC : tvBC.strength = μ.real (C ∩ B) / μ.real B) :
    (semanticPLNInduction tvA tvB tvC tvBA tvBC).strength =
      μ.real (C ∩ A) / μ.real A := by
  let wA := Mettapedia.Logic.PLNWeightTV.WTV.ofCTV tvA
  let wB := Mettapedia.Logic.PLNWeightTV.WTV.ofCTV tvB
  let wC := Mettapedia.Logic.PLNWeightTV.WTV.ofCTV tvC
  let wBA := Mettapedia.Logic.PLNWeightTV.WTV.ofCTV tvBA
  let wBC := Mettapedia.Logic.PLNWeightTV.WTV.ofCTV tvBC
  have hs :=
    Mettapedia.Logic.PLNLinkCalculus.Soundness.truth_sourceRule_sound
      (μ := μ) (interp := id) (A := A) (B := B) (C := C)
      (tA := wA) (tB := wB) (tC := wC) (tBA := wBA) (tBC := wBC)
      ctx
      (by
        simpa [Mettapedia.Logic.PLNLinkCalculus.Soundness.holdsTerm,
          Mettapedia.Logic.PLNWeightTV.WTV.ofCTV, wA] using hA)
      (by
        simpa [Mettapedia.Logic.PLNLinkCalculus.Soundness.holdsTerm,
          Mettapedia.Logic.PLNWeightTV.WTV.ofCTV, wB] using hB)
      (by
        simpa [Mettapedia.Logic.PLNLinkCalculus.Soundness.holdsTerm,
          Mettapedia.Logic.PLNWeightTV.WTV.ofCTV, wC] using hC)
      (by
        simpa [Mettapedia.Logic.PLNLinkCalculus.Soundness.holdsLink,
          Mettapedia.Logic.PLNWeightTV.WTV.ofCTV, wBA] using hBA)
      (by
        simpa [Mettapedia.Logic.PLNLinkCalculus.Soundness.holdsLink,
          Mettapedia.Logic.PLNWeightTV.WTV.ofCTV, wBC] using hBC)
  have hsource :
      (Mettapedia.Logic.PLNLinkCalculus.Truth.sourceRule wA wB wC wBA wBC).strength =
        μ.real (C ∩ A) / μ.real A := by
    simpa [Mettapedia.Logic.PLNLinkCalculus.Soundness.holdsLink] using hs
  calc
    (semanticPLNInduction tvA tvB tvC tvBA tvBC).strength
        = (Mettapedia.Logic.PLNLinkCalculus.Truth.sourceRule wA wB wC wBA wBC).strength := by
            simp [semanticPLNInduction, Mettapedia.Logic.PLNLinkCalculus.Truth.sourceRule,
              Mettapedia.Logic.PLNWeightTV.WTV.ofCTV, wA, wB, wC, wBA, wBC,
              plnSourceRuleStrength, plnInductionStrength]
    _ = μ.real (C ∩ A) / μ.real A := hsource

/-! ## PLN Abduction

Abduction: given A→B and C→B, infer A→C.
Uses Bayes inversion on the second to get B→C, then deduction. -/

/-- The raw PLN abduction formula (from PLNDerivation.lean) -/
noncomputable def plnAbductionRaw (s_AB s_CB s_A s_B s_C : ℝ) : ℝ :=
  plnAbductionStrength s_AB s_CB s_A s_B s_C

/-- `plnAbductionRaw` equals `plnAbductionStrength` by definition -/
theorem plnAbductionRaw_eq_plnAbductionStrength (s_AB s_CB s_A s_B s_C : ℝ) :
    plnAbductionRaw s_AB s_CB s_A s_B s_C = plnAbductionStrength s_AB s_CB s_A s_B s_C := rfl

/-- Semantic PLN abduction: operates directly on STVs.
    This is what MeTTaCore evaluation *means* when it evaluates Truth_Abduction.

    Parameters: tvA, tvB, tvC are term truth values; tvAB is A→B, tvCB is C→B. -/
noncomputable def semanticPLNAbduction (tvA tvB tvC tvAB tvCB : STV) : STV :=
  let s := plnAbductionStrength tvAB.strength tvCB.strength tvA.strength tvB.strength tvC.strength
  let c := min tvAB.confidence tvCB.confidence
  ⟨clamp01 s, clamp01 c, clamp01_nonneg s, clamp01_le_one s, clamp01_nonneg c, clamp01_le_one c⟩

/-- **Abduction Soundness**: Under valid inputs, computes the probability formula. -/
theorem semantic_pln_abduction_correct
    (tvA tvB tvC tvAB tvCB : STV)
    (h_bounds : plnAbductionStrength tvAB.strength tvCB.strength tvA.strength tvB.strength tvC.strength ≤ 1)
    (h_nonneg : 0 ≤ plnAbductionStrength tvAB.strength tvCB.strength tvA.strength tvB.strength tvC.strength) :
    (semanticPLNAbduction tvA tvB tvC tvAB tvCB).strength =
    plnAbductionStrength tvAB.strength tvCB.strength tvA.strength tvB.strength tvC.strength := by
  unfold semanticPLNAbduction
  simp only
  rw [clamp01_of_mem_unit (Set.mem_Icc.mpr ⟨h_nonneg, h_bounds⟩)]

/-- **Measure Soundness for Semantic Abduction / SinkRule**: if `tvAB`
represents `P(B | A)` and `tvCB` represents `P(B | C)` in a probability space
satisfying the explicit PLN deduction context, semantic PLN abduction computes
the true conditional probability `P(C | A)`.

As for induction, this reuses the weight-first link-calculus sink-rule
soundness theorem and keeps the STV-to-WTV conversion internal. -/
theorem semantic_pln_abduction_measure_sound
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {A B C : Set Ω}
    (ctx : PLNDeductionMeasureContext (μ := μ) (A := A) (B := B) (C := C))
    (tvA tvB tvC tvAB tvCB : STV)
    (hA : tvA.strength = μ.real A)
    (hB : tvB.strength = μ.real B)
    (hC : tvC.strength = μ.real C)
    (hAB : tvAB.strength = μ.real (B ∩ A) / μ.real A)
    (hCB : tvCB.strength = μ.real (B ∩ C) / μ.real C) :
    (semanticPLNAbduction tvA tvB tvC tvAB tvCB).strength =
      μ.real (C ∩ A) / μ.real A := by
  let wA := Mettapedia.Logic.PLNWeightTV.WTV.ofCTV tvA
  let wB := Mettapedia.Logic.PLNWeightTV.WTV.ofCTV tvB
  let wC := Mettapedia.Logic.PLNWeightTV.WTV.ofCTV tvC
  let wAB := Mettapedia.Logic.PLNWeightTV.WTV.ofCTV tvAB
  let wCB := Mettapedia.Logic.PLNWeightTV.WTV.ofCTV tvCB
  have hs :=
    Mettapedia.Logic.PLNLinkCalculus.Soundness.truth_sinkRule_sound
      (μ := μ) (interp := id) (A := A) (B := B) (C := C)
      (tA := wA) (tB := wB) (tC := wC) (tAB := wAB) (tCB := wCB)
      ctx
      (by
        simpa [Mettapedia.Logic.PLNLinkCalculus.Soundness.holdsTerm,
          Mettapedia.Logic.PLNWeightTV.WTV.ofCTV, wA] using hA)
      (by
        simpa [Mettapedia.Logic.PLNLinkCalculus.Soundness.holdsTerm,
          Mettapedia.Logic.PLNWeightTV.WTV.ofCTV, wB] using hB)
      (by
        simpa [Mettapedia.Logic.PLNLinkCalculus.Soundness.holdsTerm,
          Mettapedia.Logic.PLNWeightTV.WTV.ofCTV, wC] using hC)
      (by
        simpa [Mettapedia.Logic.PLNLinkCalculus.Soundness.holdsLink,
          Mettapedia.Logic.PLNWeightTV.WTV.ofCTV, wAB] using hAB)
      (by
        simpa [Mettapedia.Logic.PLNLinkCalculus.Soundness.holdsLink,
          Mettapedia.Logic.PLNWeightTV.WTV.ofCTV, wCB] using hCB)
  have hsink :
      (Mettapedia.Logic.PLNLinkCalculus.Truth.sinkRule wA wB wC wAB wCB).strength =
        μ.real (C ∩ A) / μ.real A := by
    simpa [Mettapedia.Logic.PLNLinkCalculus.Soundness.holdsLink] using hs
  calc
    (semanticPLNAbduction tvA tvB tvC tvAB tvCB).strength
        = (Mettapedia.Logic.PLNLinkCalculus.Truth.sinkRule wA wB wC wAB wCB).strength := by
            simp [semanticPLNAbduction, Mettapedia.Logic.PLNLinkCalculus.Truth.sinkRule,
              Mettapedia.Logic.PLNWeightTV.WTV.ofCTV, wB, wC, wAB, wCB,
              plnAbductionStrength]
    _ = μ.real (C ∩ A) / μ.real A := hsink

/-! ## PLN Negation

Negation: ¬A has strength 1 - s_A, confidence unchanged. -/

/-- Semantic PLN negation: computes 1 - strength. -/
noncomputable def semanticPLNNegation (tv : STV) : STV :=
  ⟨1 - tv.strength, tv.confidence,
   by linarith [tv.strength_nonneg, tv.strength_le_one],
   by linarith [tv.strength_nonneg],
   tv.confidence_nonneg, tv.confidence_le_one⟩

/-- **Negation Soundness**: trivially correct by definition. -/
theorem negation_sound (tv : STV) :
    (semanticPLNNegation tv).strength = 1 - tv.strength := rfl

/-! ## PLN Revision

Revision combines independent evidence sources by adding the latent evidence
weights decoded from their confidence coordinates.  This delegates to the
canonical `PLNInferenceCalculus.revisionTV` rule, so the MeTTaCore operational
surface remains a view of the shared evidence-addition semantics rather than a
parallel heuristic. -/

/-- Semantic PLN Revision: combines two truth values via weighted averaging.

    The formula (from lib_pln.metta):
    - w1 = c1 / (1 - c1), w2 = c2 / (1 - c2)  (confidence to weight)
    - s_combined = (w1 * s1 + w2 * s2) / (w1 + w2)
    - c_combined = (w1 + w2) / (w1 + w2 + 1)

    This is the same evidence-weight formula used by
    `PLNInferenceCalculus.revisionTV`. -/
noncomputable def semanticPLNRevision (tv1 tv2 : STV) : STV :=
  Mettapedia.Logic.PLNInferenceCalculus.revisionTV tv1 tv2

/-- **Revision computes weighted average of strengths by decoded evidence
weights, not by raw displayed confidences.** -/
theorem revision_weighted_average (tv1 tv2 : STV)
    (h_w_pos :
      Mettapedia.Logic.PLNInferenceCalculus.c2w tv1.confidence +
        Mettapedia.Logic.PLNInferenceCalculus.c2w tv2.confidence ≠ 0) :
    (semanticPLNRevision tv1 tv2).strength =
    clamp01
      ((Mettapedia.Logic.PLNInferenceCalculus.c2w tv1.confidence * tv1.strength +
          Mettapedia.Logic.PLNInferenceCalculus.c2w tv2.confidence * tv2.strength) /
        (Mettapedia.Logic.PLNInferenceCalculus.c2w tv1.confidence +
          Mettapedia.Logic.PLNInferenceCalculus.c2w tv2.confidence)) := by
  exact Mettapedia.Logic.PLNInferenceCalculus.revision_weighted_average
    tv1 tv2 h_w_pos

/-- **Revision confidence is the display of the added evidence weights.** -/
theorem revision_confidence_formula (tv1 tv2 : STV) :
    (semanticPLNRevision tv1 tv2).confidence =
      Mettapedia.Logic.PLNInferenceCalculus.w2c
        (Mettapedia.Logic.PLNInferenceCalculus.c2w tv1.confidence +
          Mettapedia.Logic.PLNInferenceCalculus.c2w tv2.confidence) := by
  exact Mettapedia.Logic.PLNInferenceCalculus.revision_confidence_formula
    tv1 tv2

/-- Operational Revision on count-backed STVs is exactly finite evidence-count
addition, displayed through the same PLN odds confidence coordinate.

This is the MeTTa-facing Bayesian/de-Finetti seal: `Truth_Revision` is not a
raw-confidence heuristic, but the STV display of adding positive and negative
evidence counts. -/
theorem semanticPLNRevision_countSTV_eq_added_count_view
    (e₁ e₂ : Mettapedia.Logic.PLNTruthTower.BinaryCounts)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0)
    (hSum : e₁.total + e₂.total ≠ 0) :
    let tv₁ := semanticPLNCountSTV e₁ h₁
    let tv₂ := semanticPLNCountSTV e₂ h₂
    (semanticPLNRevision tv₁ tv₂).strength = (e₁.add e₂).strength ∧
      (semanticPLNRevision tv₁ tv₂).confidence =
        semanticPLNOddsCoordinate.encode (e₁.add e₂).total := by
  dsimp
  have hw₁ :
      Mettapedia.Logic.PLNInferenceCalculus.c2w
          (semanticPLNCountSTV e₁ h₁).confidence = e₁.total := by
    exact c2w_semanticPLNOddsCoordinate_encode e₁.total_nonneg
  have hw₂ :
      Mettapedia.Logic.PLNInferenceCalculus.c2w
          (semanticPLNCountSTV e₂ h₂).confidence = e₂.total := by
    exact c2w_semanticPLNOddsCoordinate_encode e₂.total_nonneg
  have hWeightSum :
      Mettapedia.Logic.PLNInferenceCalculus.c2w
          (semanticPLNCountSTV e₁ h₁).confidence +
        Mettapedia.Logic.PLNInferenceCalculus.c2w
          (semanticPLNCountSTV e₂ h₂).confidence ≠ 0 := by
    simpa [hw₁, hw₂] using hSum
  have hAddTotal : (e₁.add e₂).total ≠ 0 := by
    rw [Mettapedia.Logic.PLNTruthTower.BinaryCounts.add_total]
    exact hSum
  constructor
  · rw [revision_weighted_average (semanticPLNCountSTV e₁ h₁)
      (semanticPLNCountSTV e₂ h₂) hWeightSum]
    rw [hw₁, hw₂]
    simp only [semanticPLNCountSTV]
    have hMix :=
      Mettapedia.Logic.PLNTruthTower.BinaryCounts.add_strength_eq_weighted_mixture
        e₁ e₂ h₁ h₂ hSum
    have hSame :
        ((e₁.total * e₁.strength + e₂.total * e₂.strength) /
            (e₁.total + e₂.total)) =
          (e₁.add e₂).strength := by
      rw [hMix]
      ring
    rw [hSame]
    exact clamp01_of_mem_unit
      ((e₁.add e₂).strength_mem_unit_of_total_ne_zero hAddTotal)
  · rw [revision_confidence_formula]
    rw [hw₁, hw₂]
    rw [w2c_eq_semanticPLNOddsCoordinate_encode]
    change semanticPLNOddsCoordinate.encode (e₁.total + e₂.total) =
      semanticPLNOddsCoordinate.encode (e₁.add e₂).total
    rw [Mettapedia.Logic.PLNTruthTower.BinaryCounts.add_total]

/-! ## PLN Modus Ponens

Modus Ponens: A, A→B ⊢ B. Uses background probability c. -/

/-- Semantic PLN Modus Ponens.
    Formula: s_B = s_AB · s_A + c · (1 - s_A)
    where c is the background probability (default 0.02 in lib_pln.metta). -/
noncomputable def semanticPLNModusPonens (tvA tvAB : STV) (c : ℝ := 0.02) : STV :=
  let s := modusPonens tvAB.strength tvA.strength c
  let conf := tvA.confidence * tvAB.confidence
  ⟨clamp01 s, clamp01 conf, clamp01_nonneg s, clamp01_le_one s, clamp01_nonneg conf, clamp01_le_one conf⟩

/-- **Modus Ponens Soundness**: Under valid inputs, computes the correct formula. -/
theorem modus_ponens_sound (tvA tvAB : STV) (c : ℝ) (hc : 0 ≤ c ∧ c ≤ 1) :
    (semanticPLNModusPonens tvA tvAB c).strength =
    modusPonens tvAB.strength tvA.strength c := by
  unfold semanticPLNModusPonens
  simp only
  have h_unit := modusPonens_mem_unit tvAB.strength tvA.strength c
    ⟨tvAB.strength_nonneg, tvAB.strength_le_one⟩
    ⟨tvA.strength_nonneg, tvA.strength_le_one⟩
    hc
  rw [clamp01_of_mem_unit h_unit]

/-! ## PLN Transitive Similarity

Transitive Similarity: A~B, B~C ⊢ A~C. -/

/-- Semantic PLN Transitive Similarity. -/
noncomputable def semanticPLNTransitiveSim (tvA tvB tvC tvAB tvBC : STV) : STV :=
  let s := transitiveSimilarity tvAB.strength tvBC.strength tvA.strength tvB.strength tvC.strength
  let c := min tvAB.confidence tvBC.confidence
  ⟨clamp01 s, clamp01 c, clamp01_nonneg s, clamp01_le_one s, clamp01_nonneg c, clamp01_le_one c⟩

/-- **Transitive Similarity Soundness**: Under valid inputs, computes the correct formula. -/
theorem transitive_sim_sound (tvA tvB tvC tvAB tvBC : STV)
    (h_unit : transitiveSimilarity tvAB.strength tvBC.strength tvA.strength tvB.strength tvC.strength ∈ Set.Icc (0 : ℝ) 1) :
    (semanticPLNTransitiveSim tvA tvB tvC tvAB tvBC).strength =
    transitiveSimilarity tvAB.strength tvBC.strength tvA.strength tvB.strength tvC.strength := by
  unfold semanticPLNTransitiveSim
  simp only
  rw [clamp01_of_mem_unit h_unit]

/-! ## Inference Chain Soundness -/

/-- A PLN inference chain is a sequence of rule applications -/
inductive PLNInferenceStep where
  | deduction : STV → STV → STV → STV → STV → PLNInferenceStep
  | induction : STV → STV → STV → STV → STV → PLNInferenceStep
  | abduction : STV → STV → STV → STV → STV → PLNInferenceStep
  | revision : STV → STV → PLNInferenceStep
  | modusPonens : STV → STV → PLNInferenceStep
  | negation : STV → PLNInferenceStep
  | transitiveSim : STV → STV → STV → STV → STV → PLNInferenceStep

/-- Execute a single PLN inference step -/
noncomputable def executeStep : PLNInferenceStep → STV
  | .deduction p q r pq qr => semanticPLNDeduction p q r pq qr
  | .induction a b c ba bc => semanticPLNInduction a b c ba bc
  | .abduction a b c ab cb => semanticPLNAbduction a b c ab cb
  | .revision tv1 tv2 => semanticPLNRevision tv1 tv2
  | .modusPonens a ab => semanticPLNModusPonens a ab
  | .negation tv => semanticPLNNegation tv
  | .transitiveSim a b c ab bc => semanticPLNTransitiveSim a b c ab bc

/-- Execute a chain of PLN inference steps -/
noncomputable def executeChain : List PLNInferenceStep → STV → STV
  | [], acc => acc
  | step :: rest, _ => executeChain rest (executeStep step)

/-- **Chain Soundness**: Each step in an inference chain preserves STV bounds.

    Since STVs have built-in proof obligations, this is automatic. -/
theorem pln_chain_preserves_bounds (steps : List PLNInferenceStep) (init : STV) :
    let result := executeChain steps init
    0 ≤ result.strength ∧ result.strength ≤ 1 ∧
    0 ≤ result.confidence ∧ result.confidence ≤ 1 :=
  ⟨(executeChain steps init).strength_nonneg,
   (executeChain steps init).strength_le_one,
   (executeChain steps init).confidence_nonneg,
   (executeChain steps init).confidence_le_one⟩

/-! ## Atom-Level Operations (for completeness)

These definitions show how STVs would be encoded as MeTTaCore atoms.
The semantic soundness theorems above establish correctness at the
semantic level, which the atom encoding preserves. -/

/-- Convert STV to a MeTTaCore Atom: `(stv s c)`
    Note: This uses integer encoding which has precision limitations. -/
noncomputable def stvToAtom (stv : STV) : Atom :=
  .expression [.symbol "stv",
               .grounded (.int (Int.floor (stv.strength * 10000))),
               .grounded (.int (Int.floor (stv.confidence * 10000)))]

/-- The deduction rule pattern for matching -/
def deductionPattern : Atom :=
  .expression [.symbol "Truth_Deduction",
               .var "tvP", .var "tvQ", .var "tvR", .var "tvPQ", .var "tvQR"]

/-- Empty atomspace witness used by the atom-level deduction examples. -/
def plnDeductionSpace : Atomspace := Atomspace.empty

/-! ## Unit Tests -/

section Tests

-- Test unified formula definitions
example : plnDeductionRaw 0.8 0.7 0.5 0.6 = plnDeductionStrength 0.8 0.7 0.5 0.6 := rfl
example : plnInductionRaw 0.8 0.7 0.5 0.5 0.6 = plnInductionStrength 0.8 0.7 0.5 0.5 0.6 := rfl
example : plnAbductionRaw 0.8 0.7 0.5 0.5 0.6 = plnAbductionStrength 0.8 0.7 0.5 0.5 0.6 := rfl

-- Test deduction pattern structure
example : deductionPattern =
          .expression [.symbol "Truth_Deduction",
                       .var "tvP", .var "tvQ", .var "tvR", .var "tvPQ", .var "tvQR"] := rfl

-- Negation soundness (by definition)
example : (semanticPLNNegation ⟨0.8, 0.9, by norm_num, by norm_num, by norm_num, by norm_num⟩).strength = 1 - 0.8 :=
  negation_sound _

-- Modus ponens formula test
example : modusPonens 0.8 0.7 0.02 = 0.8 * 0.7 + 0.02 * (1 - 0.7) := rfl

-- Chain preserves bounds follows from STV structure (automatic)

end Tests

/-! ## Summary

This module provides a semantic bridge between MeTTaCore evaluation and PLN.
For deduction, induction/source, and abduction/sink, the bridge now reaches both
the raw formula and explicit measure-context theorems. For the other rules, the
statements below are still formula-level bridges unless a separate
measure/context theorem is cited.

### Key Results (All Proved, 0 Sorries)

**Deduction:**
- `unified_deduction_formula`: `deductionFormulaSTV` = `plnDeductionStrength` under valid inputs
- `complete_pln_soundness`: formula-level semantic deduction bridge
- `semantic_pln_deduction_measure_sound`: measure-context theorem reaching `P(C|A)`

**Induction:**
- `semantic_pln_induction_correct`: Induction computes `plnInductionStrength`
- `semantic_pln_induction_measure_sound`: measure-context theorem reaching `P(C|A)`

**Abduction:**
- `semantic_pln_abduction_correct`: Abduction computes `plnAbductionStrength`
- `semantic_pln_abduction_measure_sound`: measure-context theorem reaching `P(C|A)`

**Revision:**
- `revision_weighted_average`: Revision computes weighted average by decoded
  evidence weights

**Modus Ponens:**
- `modus_ponens_sound`: MP computes `modusPonens` formula

**Negation:**
- `negation_sound`: Negation computes `1 - strength`

**Transitive Similarity:**
- `transitive_sim_sound`: Trans-sim computes `transitiveSimilarity`

**Chains:**
- `pln_chain_preserves_bounds`: Inference chains preserve STV bounds

### Coverage Summary

| Rule | Formula Source | Soundness Theorem |
|------|---------------|-------------------|
| Deduction | PLNDerivation | ✅ `semantic_pln_deduction_measure_sound` for the explicit measure context |
| Induction | PLNDerivation + LinkCalculusSoundness | ✅ `semantic_pln_induction_measure_sound` for the explicit measure context |
| Abduction | PLNDerivation + LinkCalculusSoundness | ✅ `semantic_pln_abduction_measure_sound` for the explicit measure context |
| Revision | PLNRevision | ✅ revision_weighted_average |
| Modus Ponens | PLNInferenceRules | ✅ modus_ponens_sound |
| Negation | trivial | ✅ negation_sound |
| Transitive Sim | PLNInferenceRules | ✅ transitive_sim_sound |

### Design Decisions

1. **Semantic Level**: We work with STVs directly, not atom encodings
   - Atom encoding has precision issues (Real → Int → Real)
   - Semantic correctness is what matters mathematically

2. **Unified Formula**: Both `deductionFormulaSTV` and `plnDeductionStrength` compute
   the same underlying formula. The `clamp01` wrapper is defensive programming that
   is provably the identity under valid inputs.

3. **Composable Proofs**: The deduction soundness proof composes:
   - PLNDerivation.lean: formula = conditional probability under the explicit context
   - PLNInferenceRules.lean: Extended rule formulas
   - This file: MeTTaCore deduction evaluation uses those formulas
   - Result: semantic deduction = correct conditional probability when the
     measure context and STV/source hypotheses are supplied

### Connection to Probability Theory

The complete verification chain is:
```
Probability Axioms (Kolmogorov)
      ↓ pln_deduction_from_total_probability (PLNDerivation.lean)
plnDeductionStrength = P(C|A) under independence
      ↓ unified_deduction_formula (this file)
deductionFormulaSTV.strength = plnDeductionStrength
      ↓ semanticPLNDeduction
MeTTaCore PLN evaluation = correct conditional probability
```

The same pattern applies to Induction and Abduction (via Bayes + Deduction),
and to other rules via their respective formula derivations.
-/

/-! ## Phase 4: Tests and Meta-Theorems -/

section Tests

/-! ### Bounds Preservation Meta-Theorem

All PLN inference rules preserve STV bounds. This is automatic from the STV
structure - the type itself carries the proofs. -/

/-- All PLN inference rules preserve bounds: output is always a valid STV.
    This is the key safety property for compositional inference. -/
theorem all_rules_preserve_bounds (step : PLNInferenceStep) :
    let r := executeStep step
    0 ≤ r.strength ∧ r.strength ≤ 1 ∧ 0 ≤ r.confidence ∧ r.confidence ≤ 1 :=
  ⟨(executeStep step).strength_nonneg,
   (executeStep step).strength_le_one,
   (executeStep step).confidence_nonneg,
   (executeStep step).confidence_le_one⟩

/-! ### Triad Uniformity

Under uniform priors (all base rates equal), Deduction, Induction, and Abduction
compute the same formula. This is proven in PLNDerivation.pln_triad_uniform. -/

/-- Under uniform priors, the triad computes the same formula.
    This explains why PLN's three core rules are deeply connected. -/
theorem triad_uniform_equivalence (s₁ s₂ s : ℝ) (hs : s ≠ 0) (hs1 : s < 1) :
    plnDeductionStrength s₁ s₂ s s =
      s₁ * s₂ + (1 - s₁) * s * (1 - s₂) / (1 - s) ∧
    plnInductionStrength s₁ s₂ s s s =
      s₁ * s₂ + (1 - s₁) * s * (1 - s₂) / (1 - s) ∧
    plnAbductionStrength s₁ s₂ s s s =
      s₁ * s₂ + (1 - s₁) * s * (1 - s₂) / (1 - s) :=
  pln_triad_uniform s₁ s₂ s hs hs1

/-! ### Concrete Examples (Sanity Checks) -/

/-- Negation inverts strength: s' = 1 - s. -/
example : (semanticPLNNegation ⟨0.8, 0.9, by norm_num, by norm_num, by norm_num, by norm_num⟩).strength = 0.2 := by
  simp only [semanticPLNNegation]
  norm_num

/-- Negation preserves confidence. -/
example : (semanticPLNNegation ⟨0.8, 0.9, by norm_num, by norm_num, by norm_num, by norm_num⟩).confidence = 0.9 := by
  simp only [semanticPLNNegation]

/-- Revision canary matching the CeTTa `Truth_Revision` half/half witness:
two equal one-unit evidence views revise to strength `1/2` and confidence
`2/3`. -/
theorem semanticPLNRevision_half_half_canary :
    let tv : STV := ⟨0.5, 0.5, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (semanticPLNRevision tv tv).strength = 0.5 ∧
      (semanticPLNRevision tv tv).confidence = (2 / 3 : ℝ) := by
  norm_num [
    semanticPLNRevision,
    Mettapedia.Logic.PLNInferenceCalculus.revisionTV,
    Mettapedia.Logic.PLNInferenceCalculus.c2w,
    Mettapedia.Logic.PLNInferenceCalculus.w2c,
    clamp01]

/-- Revision canary matching the CeTTa asymmetric witness:
`(0.2,0.5)` revised with `(0.8,0.75)` has strength `13/20` and confidence
`4/5`, because the decoded evidence weights are `1` and `3`. -/
theorem semanticPLNRevision_asymmetric_canary :
    let tv1 : STV := ⟨0.2, 0.5, by norm_num, by norm_num, by norm_num, by norm_num⟩
    let tv2 : STV := ⟨0.8, 0.75, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (semanticPLNRevision tv1 tv2).strength = (13 / 20 : ℝ) ∧
      (semanticPLNRevision tv1 tv2).confidence = (4 / 5 : ℝ) := by
  norm_num [
    semanticPLNRevision,
    Mettapedia.Logic.PLNInferenceCalculus.revisionTV,
    Mettapedia.Logic.PLNInferenceCalculus.c2w,
    Mettapedia.Logic.PLNInferenceCalculus.w2c,
    clamp01]

/-- Formula definitions are aliases (definitional equality). -/
example : plnDeductionRaw 0.8 0.7 0.5 0.6 = plnDeductionStrength 0.8 0.7 0.5 0.6 := rfl
example : plnInductionRaw 0.8 0.7 0.5 0.5 0.6 = plnInductionStrength 0.8 0.7 0.5 0.5 0.6 := rfl
example : plnAbductionRaw 0.8 0.7 0.5 0.5 0.6 = plnAbductionStrength 0.8 0.7 0.5 0.5 0.6 := rfl

end Tests

end Mettapedia.Logic.PLNMeTTaCore
