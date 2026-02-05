/-
# PLN Crisp Evidence Analysis

This file analyzes crisp PLN evidence (certainty values) and shows why PLN
does NOT reduce to classical logic, despite LEM holding on crisp values.

## Key Results (All Proven)

1. **Complement swaps crisp values**: `(crispEvidence true)ᶜ = crispEvidence false`
2. **LEM holds for crisp evidence**: `crispEvidence b ⊔ (crispEvidence b)ᶜ = ⊤`
3. **Double negation**: `(crispEvidence b)ᶜᶜ = crispEvidence b`

## Why PLN is NOT Classical

The crisp evidence values `{⟨⊤,0⟩, ⟨0,⊤⟩}` do **NOT** form a Boolean subalgebra:
- `⟨⊤,0⟩ ⊔ ⟨0,⊤⟩ = ⟨⊤,⊤⟩ = ⊤` (not crisp!)
- `⟨⊤,0⟩ ⊓ ⟨0,⊤⟩ = ⟨0,0⟩ = ⊥` (not crisp!)

The lattice operations immediately leave the "crisp" subset. Classical logic
cannot be embedded as a sublattice.

## The 2D vs 1D Distinction

PLN Evidence = ℝ≥0∞ × ℝ≥0∞ (2-dimensional, partially ordered)
Gödel-Dummett = subsets of [0,1] (1-dimensional, linearly ordered)

PLN Evidence validates Dummett axiom COMPONENTWISE (each coordinate is linear),
but the 2D structure provides more granularity than 1D intervals:

| Representation | Dimensions | Can express "uncertain" vs "contradictory"? |
|----------------|------------|---------------------------------------------|
| Interval [0,1] | 1D         | No - both map to middle values              |
| PLN Evidence   | 2D         | Yes - ⟨low,low⟩ vs ⟨high,high⟩              |

This file proves that restricting to crisp evidence does NOT recover classical
Boolean structure.
-/

import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNIntuitionisticBridge

namespace Mettapedia.Logic.PLNCrispEvidence

open scoped ENNReal
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNIntuitionisticBridge
open LO.Propositional

/-! ## Crisp Evidence Embedding

Crisp evidence represents certainty: either certainly true or certainly false.
These correspond to confidence = 1 (infinite total evidence).
-/

/-- Crisp evidence embedding: Bool → Evidence -/
def crispEvidence : Bool → Evidence
  | true  => ⟨⊤, 0⟩  -- Certainly true: infinite positive evidence
  | false => ⟨0, ⊤⟩  -- Certainly false: infinite negative evidence

/-- Crisp true has maximal positive evidence -/
theorem crisp_true_pos : (crispEvidence true).pos = ⊤ := rfl

/-- Crisp true has zero negative evidence -/
theorem crisp_true_neg : (crispEvidence true).neg = 0 := rfl

/-- Crisp false has zero positive evidence -/
theorem crisp_false_pos : (crispEvidence false).pos = 0 := rfl

/-- Crisp false has maximal negative evidence -/
theorem crisp_false_neg : (crispEvidence false).neg = ⊤ := rfl

/-- Crisp true and false are distinct -/
theorem crisp_true_ne_false : crispEvidence true ≠ crispEvidence false := by
  intro h
  have hp : (crispEvidence true).pos = (crispEvidence false).pos := congrArg Evidence.pos h
  simp [crispEvidence] at hp

/-! ## Helper Lemmas for Complement Computation -/

/-- Bot has zero positive evidence -/
lemma bot_pos : (⊥ : Evidence).pos = 0 := rfl

/-- Bot has zero negative evidence -/
lemma bot_neg : (⊥ : Evidence).neg = 0 := rfl

/-! ## Complement Swaps Crisp Values

The Heyting complement on crisp evidence swaps between the two values:
- (certainly true)ᶜ = certainly false
- (certainly false)ᶜ = certainly true
-/

/-- Complement of "certainly true" is "certainly false" -/
theorem crisp_compl_true : (crispEvidence true)ᶜ = crispEvidence false := by
  show Evidence.compl ⟨⊤, 0⟩ = ⟨0, ⊤⟩
  unfold Evidence.compl Evidence.himp
  simp only [bot_pos, bot_neg]
  simp

/-- Complement of "certainly false" is "certainly true" -/
theorem crisp_compl_false : (crispEvidence false)ᶜ = crispEvidence true := by
  show Evidence.compl ⟨0, ⊤⟩ = ⟨⊤, 0⟩
  unfold Evidence.compl Evidence.himp
  simp only [bot_pos, bot_neg]
  simp

/-- Complement swaps between crisp values -/
theorem crisp_compl (b : Bool) : (crispEvidence b)ᶜ = crispEvidence (!b) := by
  cases b
  case false => exact crisp_compl_false
  case true => exact crisp_compl_true

/-! ## Law of Excluded Middle

LEM holds for crisp evidence because complement swaps the values,
and their sup is the top element ⊤ = ⟨⊤, ⊤⟩.
-/

/-- LEM for crisp evidence: a ⊔ aᶜ = ⊤ -/
theorem crisp_lem (b : Bool) : crispEvidence b ⊔ (crispEvidence b)ᶜ = ⊤ := by
  cases b
  case false =>
    rw [crisp_compl_false]
    apply Evidence.ext'
    · show max 0 ⊤ = ⊤; simp
    · show max ⊤ 0 = ⊤; simp
  case true =>
    rw [crisp_compl_true]
    apply Evidence.ext'
    · show max ⊤ 0 = ⊤; simp
    · show max 0 ⊤ = ⊤; simp

/-- Double negation holds for crisp evidence -/
theorem crisp_compl_compl (b : Bool) : (crispEvidence b)ᶜᶜ = crispEvidence b := by
  cases b <;> simp [crisp_compl_true, crisp_compl_false]

/-- The sup of true and false crisp evidence is ⊤ -/
theorem crisp_sup_top :
    crispEvidence true ⊔ crispEvidence false = ⊤ := by
  simp only [crispEvidence]
  apply Evidence.ext'
  · show max ⊤ 0 = ⊤; simp
  · show max 0 ⊤ = ⊤; simp

/-- Symmetric version -/
theorem crisp_sup_top' :
    crispEvidence false ⊔ crispEvidence true = ⊤ := by
  simp only [crispEvidence]
  apply Evidence.ext'
  · show max 0 ⊤ = ⊤; simp
  · show max ⊤ 0 = ⊤; simp

/-! ## Heyting Algebra Properties

General properties that hold in any Heyting algebra.
-/

/-- Self-implication is ⊤ in any Heyting algebra -/
theorem self_imp_top (a : Evidence) : a ⇨ a = ⊤ := by
  rw [eq_top_iff, le_himp_iff, top_inf_eq]

/-- Implication from a crisp value to itself gives ⊤ -/
theorem crisp_imp_self (b : Bool) :
    crispEvidence b ⇨ crispEvidence b = ⊤ := self_imp_top _

/-! ## LEM Formula Validity

LEM is valid under all crisp valuations.
-/

/-- Classical valuation: atoms → Bool -/
abbrev ClassicalVal := PropVar → Bool

/-- Lift classical valuation to crisp Evidence -/
def liftClassical (v : ClassicalVal) : PropVar → Evidence :=
  fun p => crispEvidence (v p)

/-- General LEM: p ⊔ pᶜ is evaluated correctly -/
theorem lem_eval (v : PropVar → Evidence) (p : PropVar) :
    (#p ⋎ ∼(#p)).hVal v = v p ⊔ (v p)ᶜ := by
  simp [Formula.hVal_or, Formula.hVal_neg]

/-! ## Lattice Operations on Crisp Values

The crisp values do NOT form a Boolean subalgebra because
the lattice operations produce non-crisp results.
-/

/-- AND of same crisp values gives that value -/
theorem crisp_and_same (b : Bool) :
    crispEvidence b ⊓ crispEvidence b = crispEvidence b := by
  cases b <;> simp only [crispEvidence]
  all_goals apply Evidence.ext'
  all_goals show min _ _ = _; simp

/-- OR of same crisp values gives that value -/
theorem crisp_or_same (b : Bool) :
    crispEvidence b ⊔ crispEvidence b = crispEvidence b := by
  cases b <;> simp only [crispEvidence]
  all_goals apply Evidence.ext'
  all_goals show max _ _ = _; simp

/-- AND of different crisp values gives ⊥ = ⟨0, 0⟩ (NOT crisp) -/
theorem crisp_and_diff :
    crispEvidence true ⊓ crispEvidence false = ⊥ := by
  simp only [crispEvidence]
  apply Evidence.ext'
  · show min ⊤ 0 = 0; simp
  · show min 0 ⊤ = 0; simp

/-- OR of different crisp values gives ⊤ = ⟨⊤, ⊤⟩ (NOT crisp) -/
theorem crisp_or_diff :
    crispEvidence true ⊔ crispEvidence false = ⊤ := crisp_sup_top

/-! ## Summary

### Core Theorems
1. ✅ `crispEvidence` - Embedding Bool → Evidence
2. ✅ `crisp_compl_true/false` - Complement swaps crisp values
3. ✅ `crisp_lem` - LEM holds: `crispEvidence b ⊔ (crispEvidence b)ᶜ = ⊤`
4. ✅ `crisp_compl_compl` - Double negation holds

### Key Negative Result: No Boolean Subalgebra
5. ✅ `crisp_and_diff` - `⟨⊤,0⟩ ⊓ ⟨0,⊤⟩ = ⊥` (leaves crisp set!)
6. ✅ `crisp_or_diff` - `⟨⊤,0⟩ ⊔ ⟨0,⊤⟩ = ⊤` (leaves crisp set!)

### Conclusion

**PLN Evidence is NOT classical**, even when restricted to crisp values.
The crisp values `{⟨⊤,0⟩, ⟨0,⊤⟩}` are not closed under lattice operations.

**Why 2D matters**: PLN Evidence = ℝ≥0∞ × ℝ≥0∞ captures distinctions that
1D intervals cannot:
- `⟨low, low⟩` = little evidence either way (uncertain)
- `⟨high, high⟩` = much evidence both ways (contradictory)
- `⟨high, low⟩` = confident true
- `⟨low, high⟩` = confident false

Intervals collapse uncertain/contradictory to the same middle range.

See `PLNIntuitionisticBridge.lean` for the Gödel-Dummett connection.
-/

end Mettapedia.Logic.PLNCrispEvidence
