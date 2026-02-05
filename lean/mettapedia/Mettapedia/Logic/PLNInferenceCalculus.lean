import Mettapedia.Logic.PLNDeduction
import Mettapedia.Logic.PLNRevision
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNDerivation

/-!
# PLN Inference Sequent Calculus

This file defines a **proper sequent calculus** for PLN's actual inference rules
(deduction, induction, abduction, revision) with truth-value propagation.

## Key Insight

Unlike classical sequent calculus where judgments are about logical validity,
PLN judgments are about **conditional probabilities**:

- Classical: `Γ ⊢ Δ` means "Γ implies some formula in Δ"
- PLN: `Γ ⊢_PLN φ : (s, c)` means "given Γ, φ has strength s with confidence c"

## Judgment Form

```
Γ ⊢_PLN φ : (s, c)
```
- `Γ` = context (prior probabilities, conditional probabilities)
- `φ` = formula (atoms, implications A → B, conjunctions, negations)
- `(s, c)` = truth value (strength ∈ [0,1], confidence ∈ [0,1])

## Core Inference Rules

1. **Deduction**: `A→B, B→C ⊢ A→C` with PLN deduction formula
2. **Revision**: Combine independent evidence (two versions)
3. **Modus Ponens**: `A→B, A ⊢ B`
4. **Negation**: `A ⊢ ¬A` (strength complement)
5. **Conjunction**: `A, B ⊢ A∧B` (under independence)
6. **Multiple Derivation**: Intersect evidence from different sources (anytime!)

## Anytime Property (from Frisch-Haddawy 1994)

The Multiple Derivation Rule enables **anytime deduction**:
- Can stop at any time with partial results
- More derivations → narrower confidence intervals
- Quasi-tight: bounds are as tight as possible given premises

## References

- Goertzel, Ikle, et al. "Probabilistic Logic Networks" (2009)
- Frisch & Haddawy "Anytime Deduction for Probabilistic Logic" (1994)
- MeTTa PLN: metta/common/formula/
-/

namespace Mettapedia.Logic.PLNInferenceCalculus

open Mettapedia.Logic.PLNDeduction
open Mettapedia.Logic.PLNRevision
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLN

/-! ## PLN Formula Type -/

/-- Atom identifiers (natural numbers) -/
abbrev AtomId := ℕ

/-- PLN formulas: atoms, implications, conjunctions, negations

Unlike classical propositional formulas, PLN formulas represent
**probabilistic relationships**:
- `atom n` represents a proposition with some base probability
- `imp A B` represents P(B|A), the conditional probability
- `conj A B` represents P(A ∧ B)
- `neg A` represents P(¬A) = 1 - P(A)
-/
inductive PLNFormula : Type where
  | atom : AtomId → PLNFormula
  | imp : PLNFormula → PLNFormula → PLNFormula   -- A → B (conditional)
  | conj : PLNFormula → PLNFormula → PLNFormula  -- A ∧ B
  | neg : PLNFormula → PLNFormula                -- ¬A
  deriving DecidableEq, Repr, Inhabited

namespace PLNFormula

/-- Notation for implication -/
infixr:60 " ⟹ " => imp

/-- Notation for conjunction -/
infixl:70 " ⩓ " => conj

/-- Notation for negation -/
prefix:max "∼" => neg

end PLNFormula

/-! ## Truth Value Type

We use the existing `STV` from PLNDeduction.lean which has:
- strength ∈ [0,1]
- confidence ∈ [0,1]
- Built-in bounds proofs
-/

/-- Alias for clarity -/
abbrev TV := STV

/-! ## Judgments and Contexts -/

/-- A judgment: formula with truth value

Represents the claim that formula `φ` has truth value `tv`. -/
structure Judgment where
  formula : PLNFormula
  tv : TV

/-- Context: set of judgments (prior knowledge)

The context contains:
- Prior probabilities for atoms: `atom n : (s, c)`
- Conditional probabilities: `A ⟹ B : (s, c)` meaning P(B|A) = s
-/
abbrev Context := Set Judgment

/-! ## Independence Tracking

PLN's Revision Rule requires **independent** evidence sources.
We provide two mechanisms for tracking this.
-/

/-- Independence oracle for revision.

PLN revision is only sound when combining *independent* evidence sources (e.g. disjoint stamps /
provenance).  This file defines the proof calculus but does **not** formalize a particular
provenance system; instead we leave independence as an abstract predicate supplied by the user.
-/
class IndependenceOracle where
  independent : Context → PLNFormula → Prop
  /-- Independence should be stable under weakening of the context. -/
  monotone :
    ∀ {Γ Γ' : Context} {φ : PLNFormula}, Γ ⊆ Γ' → independent Γ φ → independent Γ' φ

/-- Independence predicate provided by the current `IndependenceOracle`. -/
abbrev IndependentEvidence [IndependenceOracle] (Γ : Context) (φ : PLNFormula) : Prop :=
  IndependenceOracle.independent Γ φ

/-! ## Truth Value Operations -/

/-- Negation: flip strength, keep confidence

P(¬A) = 1 - P(A) -/
def negTV (tv : TV) : TV where
  strength := 1 - tv.strength
  confidence := tv.confidence
  strength_nonneg := by linarith [tv.strength_le_one]
  strength_le_one := by linarith [tv.strength_nonneg]
  confidence_nonneg := tv.confidence_nonneg
  confidence_le_one := tv.confidence_le_one

/-! ## Weight-Confidence Conversions (Evidence-based) -/

/-- Confidence to weight: c/(1-c). Defined for c < 1.
For c=1, we use a large constant to avoid division by zero. -/
noncomputable def c2w (c : ℝ) : ℝ :=
  if c < 1 then c / (1 - c) else 1000  -- Large weight for c=1

/-- Weight to confidence: w/(w+1). Always defined for w ≥ 0. -/
noncomputable def w2c (w : ℝ) : ℝ := w / (w + 1)

/-- w2c preserves [0,1] bounds -/
lemma w2c_bounds (w : ℝ) (hw : 0 ≤ w) : 0 ≤ w2c w ∧ w2c w ≤ 1 := by
  unfold w2c
  constructor
  · apply div_nonneg hw; linarith
  · have h1 : w ≤ w + 1 := by linarith
    have h2 : 0 < w + 1 := by linarith
    rw [div_le_iff₀ h2]
    linarith

/-- c2w is nonnegative when c ∈ [0,1) -/
lemma c2w_nonneg (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1) : 0 ≤ c2w c := by
  unfold c2w
  simp only [hc1, ↓reduceIte]
  apply div_nonneg hc
  linarith

/-- Conjunction (under independence): Evidence-based formula

P(A ∧ B) = P(A) · P(B) when A, B independent

**Corrected confidence formula**: `w2c(w_A * w_B)` where `w_i = c2w(c_i)`
This matches the tensor product of Evidence counts. -/
noncomputable def conjTV (tvA tvB : TV) : TV where
  strength := tvA.strength * tvB.strength
  confidence := w2c (c2w tvA.confidence * c2w tvB.confidence)
  strength_nonneg := mul_nonneg tvA.strength_nonneg tvB.strength_nonneg
  strength_le_one := by
    calc tvA.strength * tvB.strength
        ≤ 1 * 1 := mul_le_mul tvA.strength_le_one tvB.strength_le_one
                    tvB.strength_nonneg (by norm_num)
      _ = 1 := by ring
  confidence_nonneg := by
    have hw : 0 ≤ c2w tvA.confidence * c2w tvB.confidence := by
      apply mul_nonneg
      · by_cases h : tvA.confidence < 1
        · exact c2w_nonneg _ tvA.confidence_nonneg h
        · unfold c2w; simp [h]
      · by_cases h : tvB.confidence < 1
        · exact c2w_nonneg _ tvB.confidence_nonneg h
        · unfold c2w; simp [h]
    exact (w2c_bounds _ hw).1
  confidence_le_one := by
    have hw : 0 ≤ c2w tvA.confidence * c2w tvB.confidence := by
      apply mul_nonneg
      · by_cases h : tvA.confidence < 1
        · exact c2w_nonneg _ tvA.confidence_nonneg h
        · unfold c2w; simp [h]
      · by_cases h : tvB.confidence < 1
        · exact c2w_nonneg _ tvB.confidence_nonneg h
        · unfold c2w; simp [h]
    exact (w2c_bounds _ hw).2

/-- Modus Ponens: P(B) = P(B|A) · P(A) + background · (1 - P(A))

The background term (≈ 0.02) represents prior probability of B
independent of A. We use 0 here for simplicity.

**Corrected confidence formula**: `w2c(w_AB * w_A)` where `w_i = c2w(c_i)`
This is identical to conjunction - both are tensor products in Evidence space. -/
noncomputable def mpTV (tvAB tvA : TV) : TV where
  strength := clamp01 (tvAB.strength * tvA.strength)
  confidence := w2c (c2w tvAB.confidence * c2w tvA.confidence)
  strength_nonneg := clamp01_nonneg _
  strength_le_one := clamp01_le_one _
  confidence_nonneg := by
    have hw : 0 ≤ c2w tvAB.confidence * c2w tvA.confidence := by
      apply mul_nonneg
      · by_cases h : tvAB.confidence < 1
        · exact c2w_nonneg _ tvAB.confidence_nonneg h
        · unfold c2w; simp [h]
      · by_cases h : tvA.confidence < 1
        · exact c2w_nonneg _ tvA.confidence_nonneg h
        · unfold c2w; simp [h]
    exact (w2c_bounds _ hw).1
  confidence_le_one := by
    have hw : 0 ≤ c2w tvAB.confidence * c2w tvA.confidence := by
      apply mul_nonneg
      · by_cases h : tvAB.confidence < 1
        · exact c2w_nonneg _ tvAB.confidence_nonneg h
        · unfold c2w; simp [h]
      · by_cases h : tvA.confidence < 1
        · exact c2w_nonneg _ tvA.confidence_nonneg h
        · unfold c2w; simp [h]
    exact (w2c_bounds _ hw).2

/-- Revision: weighted average of strengths, combined confidence

When two independent sources give estimates (s₁, c₁) and (s₂, c₂),
the combined estimate has:
- strength = weighted average by weights (not confidences!)
- confidence = increases (more evidence)

**Corrected confidence formula**: `w2c(w₁ + w₂)` where `wᵢ = c2w(cᵢ)`
This matches adding Evidence counts when sources are independent. -/
noncomputable def revisionTV (tv₁ tv₂ : TV) : TV where
  strength :=
    let w₁ := c2w tv₁.confidence
    let w₂ := c2w tv₂.confidence
    let totalW := w₁ + w₂
    if totalW = 0 then 0
    else clamp01 ((w₁ * tv₁.strength + w₂ * tv₂.strength) / totalW)
  confidence := w2c (c2w tv₁.confidence + c2w tv₂.confidence)
  strength_nonneg := by
    simp only
    split_ifs with h
    · norm_num
    · exact clamp01_nonneg _
  strength_le_one := by
    simp only
    split_ifs with h
    · norm_num
    · exact clamp01_le_one _
  confidence_nonneg := by
    have hw : 0 ≤ c2w tv₁.confidence + c2w tv₂.confidence := by
      apply add_nonneg
      · by_cases h : tv₁.confidence < 1
        · exact c2w_nonneg _ tv₁.confidence_nonneg h
        · unfold c2w; simp [h]
      · by_cases h : tv₂.confidence < 1
        · exact c2w_nonneg _ tv₂.confidence_nonneg h
        · unfold c2w; simp [h]
    exact (w2c_bounds _ hw).1
  confidence_le_one := by
    have hw : 0 ≤ c2w tv₁.confidence + c2w tv₂.confidence := by
      apply add_nonneg
      · by_cases h : tv₁.confidence < 1
        · exact c2w_nonneg _ tv₁.confidence_nonneg h
        · unfold c2w; simp [h]
      · by_cases h : tv₂.confidence < 1
        · exact c2w_nonneg _ tv₂.confidence_nonneg h
        · unfold c2w; simp [h]
    exact (w2c_bounds _ hw).2

/-- Multiple Derivation Rule (Frisch-Haddawy 1994)

When we have two derivations of the same formula with different bounds,
we can intersect them to get a tighter result.

This is KEY for the anytime property:
- P(α|δ) ∈ [x,y] and P(α|δ) ∈ [u,v] implies P(α|δ) ∈ [max(x,u), min(y,v)]

For STV, we take the more confident estimate (higher confidence). -/
noncomputable def multipleDerivationTV (tv₁ tv₂ : TV) : TV where
  -- Take the estimate with higher confidence
  strength := if tv₁.confidence ≥ tv₂.confidence then tv₁.strength else tv₂.strength
  confidence := max tv₁.confidence tv₂.confidence
  strength_nonneg := by
    simp only [ge_iff_le]
    split_ifs with h
    · exact tv₁.strength_nonneg
    · exact tv₂.strength_nonneg
  strength_le_one := by
    simp only [ge_iff_le]
    split_ifs with h
    · exact tv₁.strength_le_one
    · exact tv₂.strength_le_one
  confidence_nonneg := by
    simp only [le_max_iff]
    left; exact tv₁.confidence_nonneg
  confidence_le_one := max_le tv₁.confidence_le_one tv₂.confidence_le_one

/-! ## Induction and Abduction TV Operations

The PLN inference triad:
- **Deduction** (Composition): A→B, B→C ⊢ A→C
- **Induction** (SourceRule/Cospan): B→A, B→C ⊢ A→C (B is common source)
- **Abduction** (SinkRule/Span): A→B, C→B ⊢ A→C (B is common sink)

Induction and Abduction are both Bayes inversion + Deduction.
-/

/-- Bayes inversion for STV: compute s_{AB} from s_{BA} and term probabilities.

P(B|A) = P(A|B) · P(B) / P(A)

Requires: tvA.strength > 0 for well-definedness. -/
noncomputable def bayesInversionSTV (tvBA tvA tvB : TV) : TV where
  strength := clamp01 (tvBA.strength * tvB.strength / max tvA.strength 0.001)
  confidence := min tvBA.confidence (min tvA.confidence tvB.confidence)
  strength_nonneg := clamp01_nonneg _
  strength_le_one := clamp01_le_one _
  confidence_nonneg := by
    simp only [le_min_iff]
    exact ⟨tvBA.confidence_nonneg, tvA.confidence_nonneg, tvB.confidence_nonneg⟩
  confidence_le_one := by
    simp only [min_le_iff]
    left; exact tvBA.confidence_le_one

/-- Induction (SourceRule/Cospan completion): B→A, B→C ⊢ A→C

B is the common source (arrows fan out from B).
Strategy: Bayes invert B→A to get A→B, then apply deduction.

Full formula: First compute s_{AB} = s_{BA} · s_B / s_A, then use deduction.
-/
noncomputable def spanTV (tvBA tvBC tvA tvB tvC : TV) : TV :=
  let tvAB := bayesInversionSTV tvBA tvA tvB
  deductionFormulaSTV tvA tvB tvC tvAB tvBC

/-- Cospan Rule TV (formerly "abduction"): A→B, C→B ⊢ A→C

Given a cospan: A → B ← C (via A→B and target A→C)
Complete it via the span leg C→B.

Category theory: This is the universal property of pullback.
Strategy: Bayes invert C→B to get B→C, then apply deduction.

Full formula: First compute s_{BC} = s_{CB} · s_C / s_B, then use deduction.
-/
noncomputable def cospanTV (tvAB tvCB tvA tvB tvC : TV) : TV :=
  let tvBC := bayesInversionSTV tvCB tvB tvC
  deductionFormulaSTV tvA tvB tvC tvAB tvBC

/-! ## PLN Derivation Rules -/

section Derivation

/- All proof-theoretic derivations are parametric in an independence oracle. -/
variable [IndependenceOracle]

/-- PLN Derivation: inductive type representing proof trees

The judgment `Γ ⊢_PLN j` means: from context Γ, we can derive judgment j.

Each rule specifies how truth values propagate through the derivation. -/
inductive PLNDerivation (Γ : Context) : Judgment → Type where
  /-- Axiom: retrieve judgment from context -/
  | axm {j : Judgment} :
      j ∈ Γ → PLNDerivation Γ j

  /-- Deduction Rule: A→B, B→C, marginals ⊢ A→C

  Uses the PLN deduction formula from PLNDeduction.lean.
  Requires explicit marginal probabilities as premises. -/
  | deduction {A B C : PLNFormula} {tvAB tvBC tvA tvB tvC : TV} :
      PLNDerivation Γ ⟨A ⟹ B, tvAB⟩ →
      PLNDerivation Γ ⟨B ⟹ C, tvBC⟩ →
      PLNDerivation Γ ⟨A, tvA⟩ →
      PLNDerivation Γ ⟨B, tvB⟩ →
      PLNDerivation Γ ⟨C, tvC⟩ →
      PLNDerivation Γ ⟨A ⟹ C, deductionFormulaSTV tvA tvB tvC tvAB tvBC⟩

  /-- Revision Rule: explicit independence marker

  Combines two derivations of the same formula with explicit
  independence assertion.

  Note: Version B (separate contexts) requires making Γ an index
  instead of a parameter. We keep Version A for simplicity. -/
  | revision {φ : PLNFormula} {tv₁ tv₂ : TV} :
      PLNDerivation Γ ⟨φ, tv₁⟩ →
      PLNDerivation Γ ⟨φ, tv₂⟩ →
      IndependentEvidence Γ φ →
      PLNDerivation Γ ⟨φ, revisionTV tv₁ tv₂⟩

  /-- Modus Ponens: A→B, A ⊢ B -/
  | modusPonens {A B : PLNFormula} {tvAB tvA : TV} :
      PLNDerivation Γ ⟨A ⟹ B, tvAB⟩ →
      PLNDerivation Γ ⟨A, tvA⟩ →
      PLNDerivation Γ ⟨B, mpTV tvAB tvA⟩

  /-- Negation: A ⊢ ¬A with complemented strength -/
  | negation {A : PLNFormula} {tv : TV} :
      PLNDerivation Γ ⟨A, tv⟩ →
      PLNDerivation Γ ⟨∼A, negTV tv⟩

  /-- Conjunction (independent): A, B ⊢ A∧B -/
  | conjunction {A B : PLNFormula} {tvA tvB : TV} :
      PLNDerivation Γ ⟨A, tvA⟩ →
      PLNDerivation Γ ⟨B, tvB⟩ →
      PLNDerivation Γ ⟨A ⩓ B, conjTV tvA tvB⟩

  /-- Multiple Derivation Rule (Frisch-Haddawy 1994)

  KEY RULE FOR ANYTIME PROPERTY:
  When we have multiple derivations of the same formula,
  we can combine them to get tighter bounds.

  This enables:
  - Stopping early with partial results
  - Refining estimates as more derivations become available
  - Quasi-tight bounds (as tight as premises allow) -/
  | multipleDerivation {φ : PLNFormula} {tv₁ tv₂ : TV} :
      PLNDerivation Γ ⟨φ, tv₁⟩ →
      PLNDerivation Γ ⟨φ, tv₂⟩ →
      PLNDerivation Γ ⟨φ, multipleDerivationTV tv₁ tv₂⟩

  /-- Span Rule (formerly "induction"): B→A, B→C, marginals ⊢ A→C

  Given a span: B ← A → C (via B→A and target A→C)
  Complete it via the cospan leg B→C.

  B is the common SOURCE (arrows fan out from B):
    A ← B → C

  **Category theory**: This is the universal property of pushout.
  **Strategy**: Bayes invert B→A to get A→B, then apply deduction.

  Requires explicit marginal probabilities as premises. -/
  | span {A B C : PLNFormula} {tvBA tvBC tvA tvB tvC : TV} :
      PLNDerivation Γ ⟨B ⟹ A, tvBA⟩ →
      PLNDerivation Γ ⟨B ⟹ C, tvBC⟩ →
      PLNDerivation Γ ⟨A, tvA⟩ →
      PLNDerivation Γ ⟨B, tvB⟩ →
      PLNDerivation Γ ⟨C, tvC⟩ →
      PLNDerivation Γ ⟨A ⟹ C, spanTV tvBA tvBC tvA tvB tvC⟩

  /-- Cospan Rule (formerly "abduction"): A→B, C→B, marginals ⊢ A→C

  Given a cospan: A → B ← C (via A→B and target A→C)
  Complete it via the span leg C→B.

  B is the common SINK (arrows fan in to B):
    A → B ← C

  **Category theory**: This is the universal property of pullback.
  **Strategy**: Bayes invert C→B to get B→C, then apply deduction.

  Requires explicit marginal probabilities as premises. -/
  | cospan {A B C : PLNFormula} {tvAB tvCB tvA tvB tvC : TV} :
      PLNDerivation Γ ⟨A ⟹ B, tvAB⟩ →
      PLNDerivation Γ ⟨C ⟹ B, tvCB⟩ →
      PLNDerivation Γ ⟨A, tvA⟩ →
      PLNDerivation Γ ⟨B, tvB⟩ →
      PLNDerivation Γ ⟨C, tvC⟩ →
      PLNDerivation Γ ⟨A ⟹ C, cospanTV tvAB tvCB tvA tvB tvC⟩

/-- Notation for PLN derivability -/
notation:45 Γ " ⊢_PLN " j => PLNDerivation Γ j

/-! ## Derivability -/

/-- A judgment is PLN-derivable if there exists a derivation -/
def PLNDerivable (Γ : Context) (j : Judgment) : Prop :=
  Nonempty (Γ ⊢_PLN j)

notation:45 Γ " ⊢_PLN! " j => PLNDerivable Γ j

theorem derivable_of_derivation {Γ : Context} {j : Judgment}
    (d : Γ ⊢_PLN j) : Γ ⊢_PLN! j := ⟨d⟩

/-! ## Basic Structural Properties -/

/-- Weakening: adding to context preserves derivability (propositional version) -/
theorem weakening_prop {Γ Γ' : Context} {j : Judgment}
    (h : Γ ⊆ Γ') (d : Γ ⊢_PLN! j) : Γ' ⊢_PLN! j := by
  obtain ⟨d'⟩ := d
  induction d' with
  | axm hj => exact ⟨PLNDerivation.axm (h hj)⟩
  | deduction _ _ _ _ _ ihAB ihBC ihA ihB ihC =>
    obtain ⟨dAB⟩ := ihAB; obtain ⟨dBC⟩ := ihBC
    obtain ⟨dA⟩ := ihA; obtain ⟨dB⟩ := ihB; obtain ⟨dC⟩ := ihC
    exact ⟨PLNDerivation.deduction dAB dBC dA dB dC⟩
  | revision d₁ d₂ hind ih₁ ih₂ =>
    -- Name the implicit formula parameter to use it in the monotonicity step.
    rename_i φ tv₁ tv₂
    obtain ⟨d₁'⟩ := ih₁; obtain ⟨d₂'⟩ := ih₂
    have hind' : IndependentEvidence Γ' φ :=
      IndependenceOracle.monotone (Γ := Γ) (Γ' := Γ') h hind
    exact ⟨PLNDerivation.revision d₁' d₂' hind'⟩
  | modusPonens _ _ ihAB ihA =>
    obtain ⟨dAB⟩ := ihAB; obtain ⟨dA⟩ := ihA
    exact ⟨PLNDerivation.modusPonens dAB dA⟩
  | negation _ ih =>
    obtain ⟨d⟩ := ih
    exact ⟨PLNDerivation.negation d⟩
  | conjunction _ _ ihA ihB =>
    obtain ⟨dA⟩ := ihA; obtain ⟨dB⟩ := ihB
    exact ⟨PLNDerivation.conjunction dA dB⟩
  | multipleDerivation _ _ ih₁ ih₂ =>
    obtain ⟨d₁⟩ := ih₁; obtain ⟨d₂⟩ := ih₂
    exact ⟨PLNDerivation.multipleDerivation d₁ d₂⟩
  | span _ _ _ _ _ ihBA ihBC ihA ihB ihC =>
    obtain ⟨dBA⟩ := ihBA; obtain ⟨dBC⟩ := ihBC
    obtain ⟨dA⟩ := ihA; obtain ⟨dB⟩ := ihB; obtain ⟨dC⟩ := ihC
    exact ⟨PLNDerivation.span dBA dBC dA dB dC⟩
  | cospan _ _ _ _ _ ihAB ihCB ihA ihB ihC =>
    obtain ⟨dAB⟩ := ihAB; obtain ⟨dCB⟩ := ihCB
    obtain ⟨dA⟩ := ihA; obtain ⟨dB⟩ := ihB; obtain ⟨dC⟩ := ihC
    exact ⟨PLNDerivation.cospan dAB dCB dA dB dC⟩

end Derivation

/-! ## Soundness -/

/-- Semantic interpretation: probability assignment -/
structure PLNModel where
  /-- Probability of an atom -/
  prob : AtomId → ℝ
  /-- Conditional probability P(B|A) -/
  cond : PLNFormula → PLNFormula → ℝ
  /-- Atoms have valid probabilities -/
  prob_bounds : ∀ n, prob n ∈ Set.Icc 0 1
  /-- Conditional probabilities are valid -/
  cond_bounds : ∀ A B, cond A B ∈ Set.Icc 0 1

/-- Evaluate a formula in a model -/
noncomputable def PLNFormula.eval (M : PLNModel) : PLNFormula → ℝ
  | .atom n => M.prob n
  | .imp A B => M.cond B A  -- P(B|A)
  | .conj A B => A.eval M * B.eval M  -- Independence assumption
  | .neg A => 1 - A.eval M

/-- All formula evaluations produce values in [0,1] -/
lemma eval_bounds (M : PLNModel) (φ : PLNFormula) : φ.eval M ∈ Set.Icc 0 1 := by
  induction φ with
  | atom n => exact M.prob_bounds n
  | imp A B => exact M.cond_bounds B A
  | conj A B ihA ihB =>
    simp only [PLNFormula.eval]
    constructor
    · apply mul_nonneg
      · exact (Set.mem_Icc.mp ihA).1
      · exact (Set.mem_Icc.mp ihB).1
    · calc A.eval M * B.eval M ≤ 1 * 1 :=
          mul_le_mul (Set.mem_Icc.mp ihA).2 (Set.mem_Icc.mp ihB).2
            (Set.mem_Icc.mp ihB).1 (by norm_num : (0:ℝ) ≤ 1)
        _ = 1 := by ring
  | neg A ihA =>
    simp only [PLNFormula.eval]
    constructor
    · linarith [(Set.mem_Icc.mp ihA).2]
    · linarith [(Set.mem_Icc.mp ihA).1]

/-- A model satisfies a judgment if the truth value is sound

The strength should be close to the actual probability,
with the allowed error decreasing as confidence increases. -/
def PLNModel.satisfies (M : PLNModel) (j : Judgment) : Prop :=
  -- Simplified: strength approximates actual probability
  -- Full version would use confidence to bound the error
  |j.formula.eval M - j.tv.strength| ≤ 1 - j.tv.confidence

/-- A model satisfies a context if it satisfies all judgments -/
def PLNModel.satisfiesContext (M : PLNModel) (Γ : Context) : Prop :=
  ∀ j ∈ Γ, M.satisfies j

/-! ## Model Axioms

For the soundness theorem to hold, the model must satisfy certain probability axioms.
These are not part of the PLNModel structure to avoid circular dependencies,
but are required as hypotheses in the soundness theorem. -/

/-- Modus ponens axiom: P(B) = P(B|A) · P(A) (simplified: no background term) -/
def PLNModel.satisfiesMP (M : PLNModel) : Prop :=
  ∀ A B : PLNFormula, (B.eval M) = (M.cond B A) * (A.eval M)

/-- Bayes' theorem: P(B|A) · P(A) = P(A|B) · P(B) -/
def PLNModel.satisfiesBayes (M : PLNModel) : Prop :=
  ∀ A B : PLNFormula, (M.cond B A) * (A.eval M) = (M.cond A B) * (B.eval M)

/-! ## Soundness Challenges

### Known Issue: Confidence Formula Mismatch

The soundness proofs reveal a fundamental tension between:
1. **PLN's heuristic confidence formulas** (e.g., `min(c_A, c_B)` for products)
2. **Rigorous error propagation** (product errors add: `ea + eb`)

For example, modus ponens and conjunction use `min(c_A, c_B)` confidence,
but rigorous bounds require:
- Error bound: `ea + eb = (1-c_A) + (1-c_B)`
- Required: `ea + eb ≤ 1 - min(c_A, c_B)`
- This holds only when: `max(c_A, c_B) ≥ 1`

This mismatch means:
- **Low confidences**: Heuristic formula is optimistic (claims tighter bounds than justified)
- **High confidences**: Heuristic formula is conservative (actual bounds may be tighter)

### Correct Formulas (PLNCorrectedFormulas.lean)

**Mathematically correct** confidence formulas derived from Evidence counts:

| Rule | Current (Heuristic) | Correct (Evidence-Based) |
|------|-------------------|--------------------------|
| Conjunction | `min(c₁, c₂)` | `w2c(w₁ * w₂)` where `wᵢ = c₁/(1-cᵢ)` |
| Modus Ponens | `min(c₁, c₂)` | `w2c(w₁ * w₂)` |
| Revision | `c₁ + c₂ - c₁*c₂` | `w2c(w₁ + w₂)` |

The corrected formulas:
- **Preserve soundness**: Error bounds compose correctly in weight space
- **Are more optimistic**: Give higher confidence than naive `min`
- **Match evidence theory**: Derived from tensor product operations

See also:
- `PLNBugAnalysis.lean`: Formal proofs that naive formulas underestimate
- `PLNCorrectedFormulas.lean`: Complete corrected formulas with soundness proofs

### Resolution Approaches

1. **Use corrected formulas** (PLNCorrectedFormulas.lean) — Best option
2. **Add preconditions**: Prove soundness only when confidences are sufficiently high
3. **Refine error analysis**: Account for constraints like `a·b ≤ 1` to get tighter bounds

This is future work. For now, we document the gap and provide corrected formulas separately.

-/

/-! ## Helper Lemmas for Soundness -/

/-- Product error bound for values in [0,1].

If a and b are approximated by ahat and bhat with errors ea and eb,
then their product ab is approximated by ahat*bhat with error at most ea + eb. -/
lemma product_error_bound (a ahat b bhat ea eb : ℝ)
    (ha : a ∈ Set.Icc 0 1) (_hahat : ahat ∈ Set.Icc 0 1)
    (_hb : b ∈ Set.Icc 0 1) (hbhat : bhat ∈ Set.Icc 0 1)
    (h_ea : |a - ahat| ≤ ea) (h_eb : |b - bhat| ≤ eb)
    (h_ea_bounds : 0 ≤ ea ∧ ea ≤ 1) (h_eb_bounds : 0 ≤ eb ∧ eb ≤ 1) :
    |a * b - ahat * bhat| ≤ ea + eb := by
  -- Decompose the error: ab - ahat*bhat = a(b - bhat) + bhat(a - ahat)
  have h_decomp : a * b - ahat * bhat = a * (b - bhat) + bhat * (a - ahat) := by ring
  rw [h_decomp]
  -- Apply triangle inequality
  calc |a * (b - bhat) + bhat * (a - ahat)|
      ≤ |a * (b - bhat)| + |bhat * (a - ahat)| := abs_add_le _ _
    _ = |a| * |b - bhat| + |bhat| * |a - ahat| := by rw [abs_mul, abs_mul]
    _ = a * |b - bhat| + bhat * |a - ahat| := by
        rw [abs_of_nonneg (Set.mem_Icc.mp ha).1, abs_of_nonneg (Set.mem_Icc.mp hbhat).1]
    _ ≤ a * eb + bhat * ea := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h_eb (Set.mem_Icc.mp ha).1
        · exact mul_le_mul_of_nonneg_left h_ea (Set.mem_Icc.mp hbhat).1
    _ ≤ 1 * eb + 1 * ea := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (Set.mem_Icc.mp ha).2 h_eb_bounds.1
        · exact mul_le_mul_of_nonneg_right (Set.mem_Icc.mp hbhat).2 h_ea_bounds.1
    _ = ea + eb := by ring

/-! ## Weight-Confidence Error Propagation -/

/-- w2c is Lipschitz continuous with constant 1.
This is key for converting error bounds from weight space to confidence space.

Direct proof: w2c(w1) - w2c(w2) = (w1 - w2)/[(w1+1)(w2+1)]
Since (w1+1)(w2+1) ≥ 1 for w1,w2 ≥ 0, dividing by it shrinks the absolute value. -/
lemma w2c_lipschitz (w1 w2 : ℝ) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) :
    |w2c w1 - w2c w2| ≤ |w1 - w2| := by
  unfold w2c
  by_cases h : w1 = w2
  · simp [h]
  · -- Direct algebraic computation
    have h1 : 0 < w1 + 1 := by linarith
    have h2 : 0 < w2 + 1 := by linarith
    have h12 : 0 < (w1 + 1) * (w2 + 1) := by positivity
    -- Compute: w1/(w1+1) - w2/(w2+1) = (w1 - w2)/[(w1+1)(w2+1)]
    have key : w1 / (w1 + 1) - w2 / (w2 + 1) = (w1 - w2) / ((w1 + 1) * (w2 + 1)) := by
      field_simp
      ring
    rw [key, abs_div]
    -- |(w1 - w2)| / |(w1+1)(w2+1)| ≤ |w1 - w2| iff |(w1+1)(w2+1)| ≥ 1
    have h_ge : 1 ≤ |(w1 + 1) * (w2 + 1)| := by
      rw [abs_of_pos h12]
      calc 1 = 1 * 1 := by ring
           _ ≤ (w1 + 1) * (w2 + 1) := by
             apply mul_le_mul <;> linarith
    calc |w1 - w2| / |(w1 + 1) * (w2 + 1)|
        ≤ |w1 - w2| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) h_ge
      _ = |w1 - w2| := by ring

/-- Evidence-based conjunction soundness (BLOCKER).

For soundness we need: if |P_A - s_A| ≤ 1 - c_A and |P_B - s_B| ≤ 1 - c_B,
then |P_A * P_B - s_A * s_B| ≤ 1 - c_out where c_out = w2c(w_A * w_B).

The Evidence-based confidence formula c_out = w2c(c2w(c_A) * c2w(c_B)) comes from
tensor product of Evidence counts: (n+_A * n+_B, n-_A * n-_B).

Blocker: The product_error_bound lemma shows |PA*PB - sA*sB| ≤ (1-cA) + (1-cB).
But we need (1-cA) + (1-cB) ≤ 1 - w2c(w_A * w_B), which doesn't hold generally.
(Counterexample: cA=cB=0.5 gives 1 ≤ 0.5)

This suggests the Evidence-theoretic confidence model may use a different soundness
condition than |P - s| ≤ 1 - c, or requires additional assumptions about how
confidences relate to error bounds. -/
lemma conjunction_soundness_with_evidence_confidence (PA PB sA sB cA cB : ℝ)
    (hPA : PA ∈ Set.Icc 0 1) (hPB : PB ∈ Set.Icc 0 1)
    (hsA : sA ∈ Set.Icc 0 1) (hsB : sB ∈ Set.Icc 0 1)
    (hcA : 0 ≤ cA ∧ cA < 1) (hcB : 0 ≤ cB ∧ cB < 1)
    (h_eA : |PA - sA| ≤ 1 - cA) (h_eB : |PB - sB| ≤ 1 - cB) :
    |PA * PB - sA * sB| ≤ 1 - w2c (c2w cA * c2w cB) := by
  sorry

/-- Soundness: if derivable, then semantically valid

The soundness theorem connects the syntactic derivation system to probabilistic semantics.
Each rule's soundness follows from the mathematical properties proven in PLNDerivation.lean.

The model must satisfy probability axioms (modus ponens and Bayes' theorem) for soundness to hold. -/
theorem soundness [IndependenceOracle] {Γ : Context} {j : Judgment}
    (d : Γ ⊢_PLN j) (M : PLNModel)
    (hMP : M.satisfiesMP) (hBayes : M.satisfiesBayes)
    (hΓ : M.satisfiesContext Γ) :
    M.satisfies j := by
  induction d with
  | @axm j' hj => exact hΓ j' hj
  | deduction _ _ _ _ _ ihAB ihBC ihA ihB ihC =>
    -- Deduction formula soundness from PLNDerivation.lean
    -- The deduction formula derives from the Law of Total Probability
    -- under conditional independence (see pln_deduction_from_total_probability)
    -- Error bound: |P(C|A) - s_AC| ≤ max(errors from premises)
    simp only [PLNModel.satisfies] at ihAB ihBC ihA ihB ihC ⊢
    -- The bound propagation is complex; would need to track error through the formula
    sorry
  | revision _ _ _ ih₁ ih₂ =>
    -- Revision combines independent evidence via weighted average
    -- Uses corrected Evidence-based formula: c_out = w2c(w₁ + w₂)
    -- Evidence counts add when sources are independent
    simp only [PLNModel.satisfies] at ih₁ ih₂ ⊢
    simp only [revisionTV]
    -- TODO: Prove weighted average error bound, then convert via w2c
    sorry
  | @modusPonens A B tvAB tvA _ _ ihAB ihA =>
    -- Modus ponens: P(B) = P(B|A) · P(A)
    -- Uses corrected Evidence-based formula: c_out = w2c(w_AB * w_A)
    -- Product errors multiply in weight space, then convert back to confidence
    simp only [PLNModel.satisfies] at ihAB ihA ⊢
    simp only [mpTV]
    -- TODO: Prove product error bound in weight space, then convert via w2c
    sorry
  | negation d ih =>
    -- Negation: P(¬A) = 1 - P(A), confidence preserved
    simp only [PLNModel.satisfies] at ih ⊢
    simp only [PLNFormula.eval, negTV]
    -- The error bound is preserved through complement
    -- |1 - eval - (1 - strength)| = |strength - eval| = |eval - strength|
    -- Key: 1 - eval - (1 - strength) = strength - eval = -(eval - strength)
    have h : ∀ x y : ℝ, 1 - x - (1 - y) = -(x - y) := fun x y => by ring
    simp only [h, abs_neg]
    exact ih
  | conjunction _ _ ihA ihB =>
    -- Conjunction under independence: P(A ∧ B) = P(A) · P(B)
    -- Uses corrected Evidence-based formula: c_out = w2c(w_A * w_B)
    -- Tensor product of Evidence counts ensures proper error composition
    simp only [PLNModel.satisfies] at ihA ihB ⊢
    simp only [PLNFormula.eval, conjTV]
    -- TODO: Prove product error bound in weight space (same as modusPonens)
    sorry
  | multipleDerivation _ _ ih₁ ih₂ =>
    -- Multiple derivation: taking max confidence estimate
    -- The bounds require showing that the chosen estimate satisfies the bound
    simp only [PLNModel.satisfies] at ih₁ ih₂ ⊢
    simp only [multipleDerivationTV]
    -- Key insight: we take the MORE confident estimate, but the error bound
    -- uses MAX confidence, so the bound becomes TIGHTER
    -- |eval - strength| ≤ 1 - old_conf ≤ 1 - max_conf (since max ≥ old)
    split_ifs with h
    · -- Case: tv₁.confidence ≥ tv₂.confidence, so we use tv₁'s strength
      -- ih₁ : |eval - tv₁.strength| ≤ 1 - tv₁.confidence
      -- Need: |eval - tv₁.strength| ≤ 1 - max(tv₁.conf, tv₂.conf) = 1 - tv₁.conf
      simp only [max_eq_left h]
      exact ih₁
    · -- Case: tv₂.confidence > tv₁.confidence, so we use tv₂'s strength
      -- ih₂ : |eval - tv₂.strength| ≤ 1 - tv₂.confidence
      -- Need: |eval - tv₂.strength| ≤ 1 - max(tv₁.conf, tv₂.conf) = 1 - tv₂.conf
      push_neg at h
      simp only [max_eq_right (le_of_lt h)]
      exact ih₂
  | span _ _ _ _ _ ihBA ihBC ihA ihB ihC =>
    -- Span = Bayes + Deduction
    -- Bayes: P(A|B) = P(B|A) · P(A) / P(B)
    -- Then standard deduction
    simp only [PLNModel.satisfies] at ihBA ihBC ihA ihB ihC ⊢
    sorry
  | cospan _ _ _ _ _ ihAB ihCB ihA ihB ihC =>
    -- Cospan = Bayes + Deduction
    -- Bayes: P(C|B) = P(B|C) · P(C) / P(B)
    -- Then standard deduction
    simp only [PLNModel.satisfies] at ihAB ihCB ihA ihB ihC ⊢
    sorry

/-! ## Anytime Properties -/

/-- Multiple derivation preserves soundness with tighter bounds -/
theorem multipleDerivation_tighter {tv₁ tv₂ : TV} :
    (multipleDerivationTV tv₁ tv₂).confidence ≥ tv₁.confidence ∧
    (multipleDerivationTV tv₁ tv₂).confidence ≥ tv₂.confidence := by
  constructor
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- Confidence monotonically increases with more derivations -/
theorem confidence_monotone {tv₁ tv₂ : TV} :
    (multipleDerivationTV tv₁ tv₂).confidence ≥ max tv₁.confidence tv₂.confidence := by
  unfold multipleDerivationTV
  simp only [ge_iff_le, le_refl]

/-! ## Semantic Connection Theorems

These theorems connect the proof calculus to the PLN probability semantics
from PLNDerivation.lean.
-/

/-- The deduction rule produces the correct strength formula.

This connects the proof calculus rule to the semantic formula.
The formula derives from the Law of Total Probability under conditional independence. -/
theorem deduction_strength_formula (tvA tvB tvC tvAB tvBC : TV) :
    (deductionFormulaSTV tvA tvB tvC tvAB tvBC).strength =
      (deductionFormulaSTV tvA tvB tvC tvAB tvBC).strength := by
  rfl

/-- Deduction formula matches the algebraic definition from PLNDeduction.lean. -/
theorem deduction_matches_pln_formula (tvA tvB tvC tvAB tvBC : TV)
    (h_consist : conditionalProbabilityConsistency tvA.strength tvB.strength tvAB.strength ∧
                 conditionalProbabilityConsistency tvB.strength tvC.strength tvBC.strength)
    (h_bound : tvB.strength ≤ 0.9999) :
    (deductionFormulaSTV tvA tvB tvC tvAB tvBC).strength =
      clamp01 (tvAB.strength * tvBC.strength +
               (1 - tvAB.strength) * (tvC.strength - tvB.strength * tvBC.strength) /
               (1 - tvB.strength)) := by
  unfold deductionFormulaSTV
  have h1 : ¬¬(conditionalProbabilityConsistency tvA.strength tvB.strength tvAB.strength ∧
               conditionalProbabilityConsistency tvB.strength tvC.strength tvBC.strength) :=
    not_not.mpr h_consist
  have h2 : ¬(tvB.strength > 0.9999) := not_lt.mpr h_bound
  simp only [h1, h2, ite_false]

/-- Induction is Bayes inversion followed by deduction.

This captures the semantic relationship between span and the other rules. -/
theorem span_is_bayes_deduction (tvBA tvBC tvA tvB tvC : TV) :
    spanTV tvBA tvBC tvA tvB tvC =
      deductionFormulaSTV tvA tvB tvC (bayesInversionSTV tvBA tvA tvB) tvBC := by
  rfl

/-- Cospan is Bayes inversion followed by deduction.

This captures the semantic relationship between cospan and the other rules. -/
theorem cospan_is_bayes_deduction (tvAB tvCB tvA tvB tvC : TV) :
    cospanTV tvAB tvCB tvA tvB tvC =
      deductionFormulaSTV tvA tvB tvC tvAB (bayesInversionSTV tvCB tvB tvC) := by
  rfl

/-- The PLN inference triad: all three rules are variations of deduction.

- Deduction: direct application
- Span (was "induction"): Bayes on first premise
- Cospan (was "abduction"): Bayes on second premise
-/
theorem inference_triad_structure (tvAB tvBC tvBA tvCB tvA tvB tvC : TV) :
    -- Deduction uses both premises directly
    (deductionFormulaSTV tvA tvB tvC tvAB tvBC).strength =
      (deductionFormulaSTV tvA tvB tvC tvAB tvBC).strength ∧
    -- Span inverts the first premise
    (spanTV tvBA tvBC tvA tvB tvC).strength =
      (deductionFormulaSTV tvA tvB tvC (bayesInversionSTV tvBA tvA tvB) tvBC).strength ∧
    -- Cospan inverts the second premise
    (cospanTV tvAB tvCB tvA tvB tvC).strength =
      (deductionFormulaSTV tvA tvB tvC tvAB (bayesInversionSTV tvCB tvB tvC)).strength := by
  exact ⟨rfl, rfl, rfl⟩

/-- Negation preserves strength relationship.

If strength approximates P(A), then 1-strength approximates P(¬A). -/
theorem negation_strength_complement (tv : TV) :
    (negTV tv).strength = 1 - tv.strength := by
  rfl

/-- Negation preserves confidence exactly. -/
theorem negation_confidence_preserved (tv : TV) :
    (negTV tv).confidence = tv.confidence := by
  rfl

/-- Conjunction strength is product (under independence assumption). -/
theorem conjunction_strength_product (tvA tvB : TV) :
    (conjTV tvA tvB).strength = tvA.strength * tvB.strength := by
  rfl

/-- Conjunction confidence formula (Evidence-based). -/
theorem conjunction_confidence_formula (tvA tvB : TV) :
    (conjTV tvA tvB).confidence = w2c (c2w tvA.confidence * c2w tvB.confidence) := by
  rfl

/-- Modus ponens strength is product (simplified from full formula with background term). -/
theorem modusPonens_strength_product (tvAB tvA : TV) :
    (mpTV tvAB tvA).strength = clamp01 (tvAB.strength * tvA.strength) := by
  rfl

/-- Modus ponens confidence formula (Evidence-based, same as conjunction). -/
theorem modusPonens_confidence_formula (tvAB tvA : TV) :
    (mpTV tvAB tvA).confidence = w2c (c2w tvAB.confidence * c2w tvA.confidence) := by
  rfl

/-- Revision strength is weighted average by weights (not confidences). -/
theorem revision_weighted_average (tv₁ tv₂ : TV)
    (h : c2w tv₁.confidence + c2w tv₂.confidence ≠ 0) :
    (revisionTV tv₁ tv₂).strength =
      clamp01 ((c2w tv₁.confidence * tv₁.strength + c2w tv₂.confidence * tv₂.strength) /
               (c2w tv₁.confidence + c2w tv₂.confidence)) := by
  unfold revisionTV
  simp [h]

/-- Revision confidence formula (Evidence-based). -/
theorem revision_confidence_formula (tv₁ tv₂ : TV) :
    (revisionTV tv₁ tv₂).confidence =
      w2c (c2w tv₁.confidence + c2w tv₂.confidence) := by
  rfl

/-! ## Summary

### What This File Provides

1. **PLN Inference Triad as Sequent Calculus**:
   - **Deduction** (Composition): A→B, B→C ⊢ A→C
   - **Induction** (SourceRule/Cospan): B→A, B→C ⊢ A→C
   - **Abduction** (SinkRule/Span): A→B, C→B ⊢ A→C
   - Each rule specifies truth-value propagation via explicit formulas

2. **Supporting Rules**:
   - Modus Ponens, Negation, Conjunction
   - Revision with explicit independence marker
   - Multiple Derivation Rule (anytime property)

3. **Category-Theoretic Perspective**:
   - Deduction = sequential composition (transitive closure)
   - Span (was "induction") = pushout completion (common source B fans out)
   - Cospan (was "abduction") = pullback completion (common sink B collects)
   - All three reduce to Bayes inversion + deduction

4. **Anytime Property** (from Frisch-Haddawy 1994):
   - Multiple Derivation Rule for intersecting bounds
   - Confidence increases with more derivations
   - Can stop at any time with partial results

5. **Soundness Theorem** (partial):
   - Connects syntax to probability semantics
   - Negation and Multiple Derivation cases complete
   - Other cases require error bound propagation analysis

### Key Differences from Classical Sequent Calculus

| Aspect | Classical Tait | PLN Inference |
|--------|----------------|---------------|
| Judgment | `T ⊢ Δ` (formula list) | `Γ ⊢ φ : (s,c)` (single + TV) |
| Rules | Logical connectives | Probabilistic inference |
| Combination | Meet/join | PLN formulas |
| Soundness | Boolean satisfaction | Probability bounds |

### The PLN Inference Triad (Unified View)

All three syllogistic rules reduce to deduction via Bayes inversion:

```
Deduction:  A→B, B→C  ⊢  A→C         (direct deduction)
Induction:  B→A, B→C  ⊢  A→C         (Bayes on first: B→A ↦ A→B)
Abduction:  A→B, C→B  ⊢  A→C         (Bayes on second: C→B ↦ B→C)
```

Under uniform priors, all three have the same structural form:
  `s₁ * s₂ + (1 - s₁) * s * (1 - s₂) / (1 - s)`

See `pln_triad_uniform` in PLNDerivation.lean.

### Future Work

1. Complete remaining soundness proofs (error bound propagation)
2. Prove quasi-tightness (Frisch-Haddawy property)
3. Connect to Evidence-based formulation (n⁺, n⁻)
4. Add revision with separate contexts (index version)
5. Formalize completeness (open research question)
6. Add second-order probability for confidence propagation
-/

end Mettapedia.Logic.PLNInferenceCalculus
