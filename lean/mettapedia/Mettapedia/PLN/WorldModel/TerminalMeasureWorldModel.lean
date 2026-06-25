import Mettapedia.PLN.Evidence.BinaryEvidence
import Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Terminal Measure-Valued World Model (Step A: Finite Query Spaces)

Every additive world model over a finite query space induces a discrete
measure. This is the first concrete bridge between the WM algebra and
`MeasureTheory.Measure` — the Tier 3 research frontier.

## Construction

For finite `Query` with `BinaryEvidence` carrier:

    μ_W = ∑ q : Query, (extract W q).total • Measure.dirac q

The terminal property: `μ_{W₁ + W₂} = μ_{W₁} + μ_{W₂}` — the measure
construction is an additive monoid homomorphism from states to measures.

## Why "terminal"

The measure-valued WM is the universal completion: every concrete carrier
(binary, Dirichlet, NormalGamma) embeds into measures via its `.total`
function. The evidence profile `Query → Ev` maps to a measure on `Query`
weighted by total evidence at each query point. The additive extraction
law ensures this respects revision.

## Scope

Step A: finite query spaces (discrete measures via Finset.sum + Dirac). DONE.
Step B: countable queries via Measure.sum + Dirac. DONE.
Step C (future): measurable queries via σ-algebras.

## References

- Kolmogorov foundation: discrete measures on finite sets
- Giry monad: `MeasureTheory.Measure` as the probability monad
- WM-PLN book, Ch 19 (Future Directions), §Measure-Theoretic Grounding
-/

namespace Mettapedia.PLN.WorldModel.TerminalMeasureWorldModel

open scoped ENNReal MeasureTheory
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric

/-! ## Step A: Finite query spaces -/

section FiniteQuery

variable {State Query : Type*}
variable [EvidenceType State] [AdditiveWorldModel State Query BinaryEvidence]
variable [Fintype Query] [MeasurableSpace Query] [MeasurableSingletonClass Query]

/-! ## 1. Evidence-to-measure construction -/

/-- Convert a world-model state to a discrete measure on the query space.
    Each query point `q` is weighted by the total evidence `(extract W q).total`. -/
noncomputable def evidenceToMeasure (W : State) : MeasureTheory.Measure Query :=
  ∑ q : Query,
    (AdditiveWorldModel.extract (Ev := BinaryEvidence) W q).total •
    MeasureTheory.Measure.dirac q

/-! ## 2. Terminal property: measure addition = state revision -/

/-- Helper: total evidence is additive. -/
private theorem total_add (e₁ e₂ : BinaryEvidence) :
    (e₁ + e₂).total = e₁.total + e₂.total := by
  show (BinaryEvidence.hplus e₁ e₂).pos + (BinaryEvidence.hplus e₁ e₂).neg =
    (e₁.pos + e₁.neg) + (e₂.pos + e₂.neg)
  simp [BinaryEvidence.hplus]; ring

omit [MeasurableSingletonClass Query] in
/-- The terminal WM property: the evidence-to-measure construction is additive.
    Revising states and then measuring equals measuring and then adding measures.
    This is the key theorem connecting the WM algebra to measure theory. -/
theorem evidenceToMeasure_add (W₁ W₂ : State) :
    evidenceToMeasure (W₁ + W₂) =
    (evidenceToMeasure W₁ : MeasureTheory.Measure Query) + evidenceToMeasure W₂ := by
  unfold evidenceToMeasure
  conv_lhs => arg 2; ext q; rw [AdditiveWorldModel.extract_add (Ev := BinaryEvidence), total_add, add_smul]
  rw [← Finset.sum_add_distrib]

end FiniteQuery

/-! ## Step B: Countable query spaces

For countable (or arbitrary) query spaces, replace `Finset.sum` with
`Measure.sum` — a countable sum of weighted Dirac measures.
No `Fintype` constraint needed. -/

section CountableQuery

variable {State Query : Type*}
variable [EvidenceType State] [AdditiveWorldModel State Query BinaryEvidence]
variable [MeasurableSpace Query] [MeasurableSingletonClass Query]

/-- Evidence-to-measure for arbitrary query spaces via `Measure.sum`.
    Each query point `q` contributes `total(extract W q) • δ_q`. -/
noncomputable def evidenceToMeasureCountable (W : State) : MeasureTheory.Measure Query :=
  MeasureTheory.Measure.sum fun q =>
    (AdditiveWorldModel.extract (Ev := BinaryEvidence) W q).total •
    MeasureTheory.Measure.dirac q

omit [MeasurableSingletonClass Query] in
/-- The terminal property for countable queries: measure construction is additive. -/
theorem evidenceToMeasureCountable_add (W₁ W₂ : State) :
    evidenceToMeasureCountable (W₁ + W₂) =
    (evidenceToMeasureCountable W₁ : MeasureTheory.Measure Query) +
    evidenceToMeasureCountable W₂ := by
  simp only [evidenceToMeasureCountable]
  rw [MeasureTheory.Measure.sum_add_sum]
  congr 1; ext q
  rw [AdditiveWorldModel.extract_add (Ev := BinaryEvidence), total_add, add_smul]

omit [MeasurableSingletonClass Query] in
/-- Bridge: on finite query spaces, the countable variant equals the finite one. -/
theorem evidenceToMeasureCountable_eq_finite [Fintype Query] (W : State) :
    evidenceToMeasureCountable W =
    (evidenceToMeasure W : MeasureTheory.Measure Query) := by
  simp only [evidenceToMeasureCountable, evidenceToMeasure,
    MeasureTheory.Measure.sum_fintype]

end CountableQuery

end Mettapedia.PLN.WorldModel.TerminalMeasureWorldModel
