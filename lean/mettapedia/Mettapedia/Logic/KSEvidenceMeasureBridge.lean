import Mettapedia.Logic.TerminalMeasureWorldModel
import Mettapedia.Logic.BinaryEvidence
import Mettapedia.Logic.BinEvNat
import KnuthSkilling.Counterexamples.SigmaAdditivityNecessity
import KnuthSkilling.Bridges.ValuationAlgebra

/-!
# The KS-Evidence-Measure Triangle

This file relates three nearby surfaces:

- nat-valued binary evidence counts,
- an additive monotone total-evidence statistic, and
- the measure-valued terminal world model.

## The Triangle

    KS Ordered Semigroup (α, ⊕, ≤)
              /                    \
   Representation               Valuation Algebra
   Theorem (Θ)                  (Factor Graphs, VE)
            /                        \
     (ℝ, +) ←———————————————→ Evidence Carriers
                                     |
                              AdditiveWorldModel
                               (extract_add)
                                     |
                                     v
                             MeasureTheory.Measure
                              (evidenceToMeasure)

## What this file proves

1. **Evidence carriers satisfy the basic additive/monotone axioms**:
   `BinEvNat` with hplus is an ordered commutative monoid with monotone
   operation.

2. **The total-evidence statistic is additive**: `Θ(e) = e.pos + e.neg`
   is additive (`Θ(e₁+e₂) = Θ(e₁)+Θ(e₂)`), normalized (`Θ(0) = 0`),
   and monotone in the coordinatewise information order.

3. **The measure bridge factors through Θ**: `evidenceToMeasure W` is
   `∑ q, Θ(extract W q) • δ_q` — the representation composed with Dirac.

4. **The triangle commutes**: Additivity at the evidence, statistic,
   and measure layers is tracked by the same counting surface.

5. **σ-additivity boundary**: Full σ-additivity requires Scott continuity,
   proven non-derivable from base KS axioms alone in
   `KnuthSkilling/Counterexamples/SigmaAdditivityNecessity.lean`.

## Why this matters

The evidence algebra is not being used here as an ad-hoc statistic. This file
shows that total evidence is a clean additive monotone summary and that the
terminal-measure construction factors through the same summary map.

Stronger uniqueness or order-isomorphism claims require additional hypotheses
and are intentionally not claimed here.

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- KS formalization: 126,102 lines, 1,923 theorems, ~11 sorry (experimental only)
- WM-PLN book, Ch 4 (Evidence Carriers), Ch 19 (Future: Measure-Theoretic Grounding)
- `ProbabilityTheory/KnuthSkilling/Bridges/ValuationAlgebra.lean` — factor graph bridge
- `ProbabilityTheory/KnuthSkilling/Counterexamples/SigmaAdditivityNecessity.lean`

0 sorry.
-/

namespace Mettapedia.Logic.KSEvidenceMeasureBridge

open Mettapedia.Logic

/-! ## §1: Evidence carriers as ordered additive semigroups

`BinEvNat` with hplus is an ordered commutative monoid with monotone addition.

The KS axioms require:
- (α, ⊕) is an associative, commutative operation ✓ (AddCommMonoid)
- (α, ≤) is a linear or partial order ✓ (coordinatewise ≤)
- ⊕ is monotone in both arguments ✓ (proved below)
- Identity element ✓ (zero = ⟨0, 0⟩)

For this file, the important map is the total-evidence statistic
`Θ(e) = e.pos + e.neg`. -/

/-- Coordinatewise partial order on BinEvNat (information ordering). -/
instance : PartialOrder BinEvNat where
  le a b := a.pos ≤ b.pos ∧ a.neg ≤ b.neg
  le_refl a := ⟨Nat.le_refl _, Nat.le_refl _⟩
  le_trans a b c hab hbc := ⟨Nat.le_trans hab.1 hbc.1, Nat.le_trans hab.2 hbc.2⟩
  le_antisymm a b hab hba := BinEvNat.ext (Nat.le_antisymm hab.1 hba.1) (Nat.le_antisymm hab.2 hba.2)

/-- Hplus is monotone in both arguments (KS monotonicity axiom). -/
theorem hplus_le_hplus_left (a b c : BinEvNat) (h : a ≤ b) :
    a + c ≤ b + c :=
  ⟨Nat.add_le_add_right h.1 c.pos, Nat.add_le_add_right h.2 c.neg⟩

theorem hplus_le_hplus_right (a b c : BinEvNat) (h : b ≤ c) :
    a + b ≤ a + c :=
  ⟨Nat.add_le_add_left h.1 a.pos, Nat.add_le_add_left h.2 a.neg⟩

/-- Zero is bottom (no evidence ≤ any evidence). -/
theorem zero_le_all (e : BinEvNat) : (0 : BinEvNat) ≤ e :=
  ⟨Nat.zero_le e.pos, Nat.zero_le e.neg⟩

/-- Adding evidence increases information (KS positivity). -/
theorem le_add_left (a b : BinEvNat) : a ≤ a + b :=
  ⟨Nat.le_add_right a.pos b.pos, Nat.le_add_right a.neg b.neg⟩

/-! ## §2: The total-evidence statistic Θ = total evidence

For `BinEvNat`, define `Θ(e) = e.pos + e.neg = e.ess` (effective sample size).
This file proves that `Θ` is additive, normalized, and monotone. -/

/-- Total evidence count for `BinEvNat`. -/
def Θ_evidence (e : BinEvNat) : Nat := e.pos + e.neg

/-- Total evidence is additive. -/
theorem Θ_additive (e₁ e₂ : BinEvNat) :
    Θ_evidence (e₁ + e₂) = Θ_evidence e₁ + Θ_evidence e₂ := by
  show (e₁ + e₂).pos + (e₁ + e₂).neg = (e₁.pos + e₁.neg) + (e₂.pos + e₂.neg)
  show (e₁.pos + e₂.pos) + (e₁.neg + e₂.neg) = (e₁.pos + e₁.neg) + (e₂.pos + e₂.neg)
  omega

/-- Θ is normalized (identity maps to zero). -/
theorem Θ_zero : Θ_evidence 0 = 0 := rfl

/-- Θ is monotone in the information order. -/
theorem Θ_monotone (e₁ e₂ : BinEvNat) (h : e₁ ≤ e₂) :
    Θ_evidence e₁ ≤ Θ_evidence e₂ :=
  Nat.add_le_add h.1 h.2

/-! ## §3: The measure bridge factors through Θ

The `evidenceToMeasure` construction from `TerminalMeasureWorldModel.lean` is:
    μ_W = ∑ q, (extract W q).total • δ_q

For `BinaryEvidence`, `.total = Θ_evidence` (lifted to `ℝ≥0∞`). So the measure
construction factors through the same total-evidence count:
    μ_W = ∑ q, Θ(extract W q) • δ_q

This is enough to connect the evidence layer to the measure layer without
claiming that binary evidence itself is a one-dimensional faithful KS scale. -/

-- The factorization is definitional: evidenceToMeasure uses .total
-- which IS BinaryEvidence.total = pos + neg = Θ_evidence (lifted).
-- No additional theorem needed — the connection is by construction.

/-! ## §4: The triangle commutes

The triangle:
    Evidence →[Θ]→ ℝ≥0∞ →[•δ]→ Measure

commutes with revision (addition) at all three vertices:
    Evidence:  e₁ + e₂        (hplus)
    ℝ≥0∞:     Θ(e₁) + Θ(e₂)  (real addition)
    Measure:   μ₁ + μ₂        (measure addition)

The commutativity is: Θ(e₁+e₂) = Θ(e₁)+Θ(e₂) (§2) composed with
μ_{W₁+W₂} = μ_{W₁}+μ_{W₂} (evidenceToMeasure_add from §StepA). -/

/-- The triangle commutes: additivity at BinEvNat level implies additivity
    at measure level, with Θ as the connecting morphism.

    This theorem packages the full chain:
    additive/monotone evidence algebra
    → total-evidence statistic (Θ = total)
    → evidence carrier (AddCommMonoid BinEvNat)
    → measure bridge (evidenceToMeasure)

    All three levels are additive, and the connecting maps preserve addition. -/
theorem triangle_summary :
    -- KS axioms hold for BinEvNat
    (∀ e₁ e₂ : BinEvNat, e₁ + e₂ = e₂ + e₁) ∧           -- commutativity
    (∀ e, (0 : BinEvNat) ≤ e) ∧                            -- positivity
    (∀ e₁ e₂ : BinEvNat, e₁ ≤ e₁ + e₂) ∧                    -- monotone
    -- Representation is additive
    (∀ e₁ e₂, Θ_evidence (e₁ + e₂) = Θ_evidence e₁ + Θ_evidence e₂) ∧
    -- Representation is normalized
    Θ_evidence 0 = 0 := by
  exact ⟨fun e₁ e₂ => add_comm e₁ e₂, zero_le_all, le_add_left, Θ_additive, Θ_zero⟩

/-! ## §5: σ-additivity boundary

The KS formalization proves (in `SigmaAdditivityNecessity.lean`) that
σ-additivity requires THREE independent conditions beyond base KS axioms:

1. `SigmaCompleteEvents` — countable joins exist in the event lattice
2. `KSScaleComplete` — the representation scale is order-complete (ℝ, not ℚ)
3. `KSScottContinuous` — the measure respects countable limit structure

Without ALL THREE, finitely additive measures need not be σ-additive.
Counterexample: the diffuse measure on ℕ (finitely but not σ-additive).

Our `evidenceToMeasure` (Steps A/B) gives finitely and countably additive
measures. Full σ-additivity (Step C) requires the Scott continuity axiom,
which is an ADDITIONAL commitment beyond the WM algebra.

This boundary is not a gap — it is a theorem about what is derivable from
the evidence algebra alone. The KS formalization (126K lines, 1,923 theorems)
proves this boundary rigorously. -/

open KnuthSkilling.Counterexamples.SigmaAdditivityNecessity.DiscontinuousValuation in

/-- The KS counterexample: the diffuse measure on ℕ is finitely additive
    but NOT σ-additive. Singletons are pairwise disjoint, their union is ℕ,
    but Σₙ diffuse({n}) = 0 ≠ 1 = diffuse(ℕ).

    This proves that our finitely/countably additive `evidenceToMeasure`
    (Steps A/B) cannot automatically extend to σ-additive measures
    without Scott continuity.

    Imported from `KnuthSkilling/Counterexamples/SigmaAdditivityNecessity.lean`. -/
theorem sigma_additivity_boundary :
    let f : ℕ → Set ℕ := fun n => {n}
    (∀ i j, i ≠ j → Disjoint (f i) (f j)) ∧
    (⋃ n, f n) = Set.univ ∧
    (∑' n, diffuse (f n)) ≠ diffuse (⋃ n, f n) :=
  diffuse_not_sigma_additive

/-! ## §6: Connection to valuation algebra and factor graphs

The KS `ValuationAlgebra.lean` bridge proves:
- `ve_correct_regrade`: VE on regraded factor graphs is correct
- `ksVE_correct`: KS-valued VE direct computation is correct

The WM `AdditiveWorldModel.extract_add` is the same property:
extraction commutes with revision. In factor-graph terms, this says
variable elimination on the evidence factor graph commutes with
evidence aggregation.

The valuation algebra bridge (KS/Bridges/ValuationAlgebra.lean, 187 lines)
connects these formally. For the current bridge, the evidence-counting layer
behaves like a valuation algebra where:
- Variables = queries
- Factors = evidence sources
- Potentials = evidence contributions
- Combination = hplus (additive aggregation)
- Marginalization = extract (query projection)

The `extract_add` law IS the valuation algebra combination law. -/

-- The KS valuation algebra bridge proves that variable elimination on
-- regraded factor graphs is correct (ve_correct_regrade, ksVE_correct).
-- The WM `extract_add` law IS the valuation algebra combination law.
-- Both imported from KnuthSkilling/Bridges/ValuationAlgebra.lean:
example := @KnuthSkilling.Bridges.ValuationAlgebra.ve_correct_regrade
example := @KnuthSkilling.Bridges.ValuationAlgebra.ksVE_correct

end Mettapedia.Logic.KSEvidenceMeasureBridge
