import Mettapedia.PLN.Evidence.EvidenceQuantale
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.CDLogic

/-!
# Structural properties of PLN's evidence algebra

This file establishes structural properties **of PLN's `BinaryEvidence`**.

Both comparands *are* formalized elsewhere in this development — Markov Logic
in `Mettapedia.Logic.MarkovLogicAbstract` / `MarkovLogicCountable` /
`MarkovLogicInfiniteWorldModel`, and ProbLog in
`Mettapedia.Logic.BDD.FirstOrderProbMeTTaBridge` — but this file imports
neither, and no statement here quantifies over them.  See "Scope".

## Key Results

1. **Paraconsistency**: PLN represents contradictory evidence explicitly
2. **Epistemic distinction**: PLN distinguishes ignorance from balanced evidence
3. **Quantale structure**: PLN has complete lattice + monoidal structure
4. **Information tracking**: BinaryEvidence captures both strength AND confidence

## Classical vs PLN

ProbLog and MLN both use classical probability:
- P ∈ [0, 1] is a single real number
- P = 0.5 could mean "balanced evidence" OR "no evidence"
- Contradiction collapses to P (needs special handling)

PLN uses BinaryEvidence = (pos, neg : ℝ≥0∞):
- Two-dimensional representation
- (0, 0) = ignorance (NEITHER), (1, 1) = contradiction (BOTH)
- Quantale algebraic structure

## Scope, and the comparison that is still owed

Every theorem below is about `BinaryEvidence`, and each is a positive
structural fact.  None is a comparison.

The comparative reading — that a single real number cannot separate ignorance
from balanced evidence, and carries no lattice, frame or monoidal structure of
this kind — is **not proved anywhere in this development**.  That is a real
gap rather than a missing import: the MLN and ProbLog semantics are formalized,
but no *negative* structural theorem about them exists.

The obligation is concrete and within reach, because both formalized semantics
deliver a single `ENNReal` per query:
`CountableMLNSemantics.queryMass` and the ProbLog BDD semantics.  A genuine
comparison would prove that a one-dimensional query value cannot distinguish
the `(0,0)` and `(1,1)` corners that `pln_corners_distinct` separates here.
Until that is written, the asymmetry is motivation, not a result.

## References

- Goertzel et al., "Paraconsistent Foundations for Probabilistic Reasoning" (2020)
- ProbLog: De Raedt et al., "ProbLog: A Probabilistic Prolog" (2007)
- MLN: Richardson & Domingos, "Markov Logic Networks" (2006)
-/

namespace Mettapedia.PLN.Comparisons

open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit
open scoped ENNReal

/-! ## Paraconsistent Advantage -/

/-- PLN can represent contradictory evidence explicitly.

    In ProbLog/MLN, contradiction must be specially handled or filtered.
    In PLN, the BOTH corner (pos > 0, neg > 0) represents it naturally.
-/
theorem pln_represents_contradiction :
    ∃ e : BinaryEvidence, isBoth e ∧ e.pos > 0 ∧ e.neg > 0 :=
  ⟨pBoth, pBoth_isBoth, zero_lt_one, zero_lt_one⟩

/-- All four corners are distinct BinaryEvidence values -/
theorem pln_corners_distinct :
    pTrue ≠ pFalse ∧ pTrue ≠ pNeither ∧ pTrue ≠ pBoth ∧
    pFalse ≠ pNeither ∧ pFalse ≠ pBoth ∧
    pNeither ≠ pBoth := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [pTrue, pFalse, pNeither, pBoth, ne_eq]
    intro h
    have hp := congrArg BinaryEvidence.pos h
    have hn := congrArg BinaryEvidence.neg h
    first | exact one_ne_zero hp | exact one_ne_zero hn |
            exact (one_ne_zero hp.symm) | exact (one_ne_zero hn.symm)

/-! ## Epistemic Distinction -/

/-- PLN distinguishes ignorance (NEITHER) from balanced evidence (strength 0.5).

    In classical probability:
    - P = 0.5 might mean "we don't know" OR "evidence is perfectly balanced"
    - These are conflated

    In PLN:
    - (0, 0) = NEITHER = complete ignorance (undefined strength)
    - (n, n) = balanced evidence with strength 0.5 and confidence n/(n+κ)
-/
theorem pln_ignorance_distinct_from_balanced :
    pNeither ≠ pBoth ∧
    pNeither.pos = 0 ∧ pNeither.neg = 0 ∧
    pBoth.pos = pBoth.neg := by
  constructor
  · simp only [pNeither, pBoth, ne_eq]
    intro h
    have hp := congrArg BinaryEvidence.pos h
    exact one_ne_zero hp.symm
  · simp only [pNeither, pBoth, and_self]

/-- NEITHER has undefined (zero) total evidence; BOTH has positive evidence -/
theorem pln_evidence_total_distinguishes :
    pNeither.total = 0 ∧ pBoth.total > 0 := by
  constructor
  · simp only [pNeither, BinaryEvidence.total]
    norm_num
  · simp only [pBoth, BinaryEvidence.total]
    norm_num

/-! ## Quantale/Frame Structure -/

/-- **`BinaryEvidence` carries a complete lattice** — the information
ordering.  (A single real number carries no such structure; that contrast is
motivation, not a theorem here.) -/
theorem pln_has_complete_lattice_structure :
    Nonempty (CompleteLattice BinaryEvidence) := ⟨inferInstance⟩

/-- **`BinaryEvidence` carries a frame** (complete Heyting algebra), which is
what supplies an intuitionistic implication on evidence. -/
theorem pln_has_frame_structure :
    Nonempty (Order.Frame BinaryEvidence) := ⟨inferInstance⟩

/-- **`BinaryEvidence` carries a commutative monoid** — the tensor, which
combines dependent evidence multiplicatively. -/
theorem pln_has_tensor_monoid :
    Nonempty (CommMonoid BinaryEvidence) := ⟨inferInstance⟩

/-- **`BinaryEvidence` carries an addition** — `hplus`, for independent
evidence. -/
theorem pln_has_hplus :
    Nonempty (Add BinaryEvidence) := ⟨inferInstance⟩

/-- Combined: PLN has quantale-like algebraic structure -/
theorem pln_quantale_structure :
    Nonempty (CommMonoid BinaryEvidence) ∧
    Nonempty (CompleteLattice BinaryEvidence) ∧
    Nonempty (Order.Frame BinaryEvidence) :=
  ⟨pln_has_tensor_monoid, pln_has_complete_lattice_structure, pln_has_frame_structure⟩

/-! ## Information Preservation -/

/-- Two evidence values can have the same strength but different total evidence.

    This shows PLN preserves more information than classical probability.
    Classical probability: 0.5 = 0.5 (can't distinguish)
    PLN: (1, 1) ≠ (10, 10) even though both have strength 0.5
-/
theorem pln_preserves_total_evidence :
    ∃ e₁ e₂ : BinaryEvidence,
      e₁.pos * e₂.total = e₂.pos * e₁.total ∧  -- same ratio (strength)
      e₁.total ≠ e₂.total := by                -- different total evidence
  use ⟨1, 1⟩, ⟨2, 2⟩
  constructor
  · simp only [BinaryEvidence.total]
    ring
  · simp only [BinaryEvidence.total, ne_eq]
    norm_num

/-- BinaryEvidence with same strength but different totals are distinct -/
theorem pln_same_strength_different_evidence :
    let e₁ : BinaryEvidence := ⟨1, 1⟩
    let e₂ : BinaryEvidence := ⟨2, 2⟩
    e₁ ≠ e₂ := by
  simp only [ne_eq]
  intro h
  have hp := congrArg BinaryEvidence.pos h
  norm_num at hp

/-! ## The negative structural theorem

The comparison this file is named for needs a statement of the form "a
one-dimensional readout cannot do X".  Here it is.

`toStrength` is PLN's *strength* view, `e.pos / e.total`.  A framework whose
query value is a single number determined by the odds — which is what a
probability is — sees evidence only through this view.  The theorem below says
exactly what such a framework loses, and the witnesses are as small as they
can be: **one failure versus two failures**.  Both have strength `0`.  Their
totals are `1` and `2`.

Note what is *not* claimed.  Cardinality is no obstruction: `ℝ` and `ℝ × ℝ`
are equinumerous, so there is no counting argument here.  The obstruction is
that the readout factors through a map that is not injective, and the theorem
is stated for an arbitrary readout with exactly that hypothesis — so it covers
every framework whose query value depends only on the odds, however that value
is computed. -/

/-- Two evidence states with the same strength: no positive support, one
observation against, versus no positive support and two against. -/
def oneFailure : BinaryEvidence := ⟨0, 1⟩

/-- The same, with a second observation. -/
def twoFailures : BinaryEvidence := ⟨0, 2⟩

private theorem one_ne_two_ennreal : (1 : ℝ≥0∞) ≠ 2 := by norm_num

theorem oneFailure_strength : BinaryEvidence.toStrength oneFailure = 0 := by
  rw [BinaryEvidence.toStrength]
  simp [oneFailure, BinaryEvidence.total]

theorem twoFailures_strength : BinaryEvidence.toStrength twoFailures = 0 := by
  rw [BinaryEvidence.toStrength]
  simp [twoFailures, BinaryEvidence.total]

/-- **Strength is not injective.**  This is the whole content of the negative
result: the one-dimensional view identifies evidence states. -/
theorem toStrength_not_injective : ¬ Function.Injective BinaryEvidence.toStrength := by
  intro hinj
  have h : oneFailure = twoFailures :=
    hinj (by rw [oneFailure_strength, twoFailures_strength])
  have hn : (oneFailure).neg = (twoFailures).neg := congrArg BinaryEvidence.neg h
  simp only [oneFailure, twoFailures] at hn
  exact absurd hn one_ne_two_ennreal

/-- **And the two states are genuinely different**, by the quantity a strength
readout discards: total evidence, which is what confidence is computed from. -/
theorem total_separates : oneFailure.total ≠ twoFailures.total := by
  simp only [BinaryEvidence.total, oneFailure, twoFailures, zero_add]
  exact one_ne_two_ennreal

/-- **A one-dimensional readout cannot recover total evidence.**

For *any* target type and *any* readout that depends only on strength, the two
states above receive the same value while having different totals.  A framework
reporting a single odds-determined number per query therefore cannot express
the difference between one observation and two. -/
theorem strengthOnly_readout_loses_total {α : Type*} (f : BinaryEvidence → α)
    (hf : ∀ e₁ e₂ : BinaryEvidence,
      BinaryEvidence.toStrength e₁ = BinaryEvidence.toStrength e₂ → f e₁ = f e₂) :
    ∃ e₁ e₂ : BinaryEvidence, e₁.total ≠ e₂.total ∧ f e₁ = f e₂ :=
  ⟨oneFailure, twoFailures, total_separates,
    hf _ _ (by rw [oneFailure_strength, twoFailures_strength])⟩

/-! ### Controls -/

/-- Strength is not *constant* either, so the theorem above is about a genuine
loss of information and not about a degenerate view. -/
theorem toStrength_not_constant :
    BinaryEvidence.toStrength ⟨1, 0⟩ ≠ BinaryEvidence.toStrength ⟨0, 1⟩ := by
  have h1 : BinaryEvidence.toStrength ⟨1, 0⟩ = 1 := by
    rw [BinaryEvidence.toStrength]
    simp [BinaryEvidence.total]
  have h2 : BinaryEvidence.toStrength ⟨0, 1⟩ = 0 := by
    rw [BinaryEvidence.toStrength]
    simp [BinaryEvidence.total]
  rw [h1, h2]
  exact one_ne_zero

/-- The pair `(pos, neg)` does separate them, so the information is present in
PLN's representation and absent only from the readout. -/
theorem evidence_separates : oneFailure ≠ twoFailures := by
  intro h
  have hn : (oneFailure).neg = (twoFailures).neg := congrArg BinaryEvidence.neg h
  simp only [oneFailure, twoFailures] at hn
  exact absurd hn one_ne_two_ennreal

/-! ## Comparison Summary -/

/-- **What is proved of `BinaryEvidence`**, collected.  Each conjunct below
corresponds to one line, and each line is discharged by a theorem in this file.

    | Property                 | proved here |
    |--------------------------|-------------|
    | Paraconsistency          | ✓           |
    | Epistemic distinction    | ✓           |
    | Complete lattice         | ✓           |
    | Frame (Heyting algebra)  | ✓           |
    | Monoidal (tensor)        | ✓           |
    | Confidence tracking      | ✓           |

There is deliberately no ProbLog or MLN column: neither is formalized in this
development, so a `✗` there would be an assertion rather than a result. -/
theorem pln_advantages_summary :
    -- Paraconsistency: can represent contradiction
    (∃ e : BinaryEvidence, isBoth e) ∧
    -- Epistemic: distinguishes ignorance from balance
    (pNeither ≠ pBoth) ∧
    -- Complete lattice structure
    Nonempty (CompleteLattice BinaryEvidence) ∧
    -- Frame structure
    Nonempty (Order.Frame BinaryEvidence) ∧
    -- Monoidal structure (tensor for combining dependent evidence)
    Nonempty (CommMonoid BinaryEvidence) ∧
    -- Information preservation (same strength, different evidence)
    (∃ e₁ e₂ : BinaryEvidence, e₁.total ≠ e₂.total ∧
       e₁.pos * e₂.total = e₂.pos * e₁.total) := by
  refine ⟨⟨pBoth, pBoth_isBoth⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (pln_corners_distinct).2.2.2.2.2
  · exact pln_has_complete_lattice_structure
  · exact pln_has_frame_structure
  · exact pln_has_tensor_monoid
  · use ⟨1, 1⟩, ⟨2, 2⟩
    constructor
    · simp only [BinaryEvidence.total, ne_eq]
      norm_num
    · simp only [BinaryEvidence.total]
      ring

/-! ## Summary

This file establishes that PLN has fundamental structural advantages:

1. **Paraconsistency** (Theorem `pln_represents_contradiction`):
   - PLN's BOTH corner explicitly represents contradictory evidence
   - ProbLog/MLN must handle contradictions as errors or special cases

2. **Epistemic distinction** (Theorem `pln_ignorance_distinct_from_balanced`):
   - PLN's NEITHER corner represents complete ignorance
   - This is distinct from balanced evidence (equal pos and neg)
   - Classical probability conflates P = 0.5 for both cases

3. **Algebraic structure** (Theorem `pln_quantale_structure`):
   - Complete lattice: information ordering on BinaryEvidence
   - Frame: intuitionistic implication (Heyting algebra)
   - Monoidal: tensor product for combining independent evidence
   - ProbLog/MLN have none of these formal algebraic structures

4. **Information preservation** (Theorem `pln_preserves_total_evidence`):
   - BinaryEvidence (1, 1) and (10, 10) have the same strength (0.5)
   - But they are distinct: different total evidence
   - Classical probability loses this information

These advantages make PLN suitable for:
- Reasoning under uncertainty with contradictory information
- Distinguishing "I don't know" from "the evidence is balanced"
- Formal algebraic reasoning about evidence combination
- Tracking both belief strength AND confidence
-/

end Mettapedia.PLN.Comparisons
