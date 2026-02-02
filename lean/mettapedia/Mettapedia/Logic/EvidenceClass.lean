import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs

open scoped ENNReal NNReal

/-!
# Abstract Evidence Type Classes

This file defines the abstract interfaces for PLN evidence types across domains.

## Key Insight (Modal Evidence Theory)

The PLN quantale structure is on **EVIDENCE**, not on truth values.
The strength formula is a **VIEW** (interpretation) that requires context.

This separates:
- **Evidence** = observations (DATA) - forms a monoid under hplus
- **Context** = hyperparameters (INTERPRETATION) - specifies how to interpret

## Main Definitions

- `EvidenceType` : Evidence forms a commutative monoid under hplus
- `InterpretableEvidence` : Context-dependent interpretation (strength, mean, etc.)
- `MetaLearnable` : Support for learning context from meta-evidence

## Philosophical Foundation

The binary case (pos, neg) appears "self-contained" because it implicitly uses
the **improper prior** (α₀=β₀=0). Making this explicit:
- `strength_improper(e) = e.pos / (e.pos + e.neg)`           -- implicit α₀=β₀=0
- `strength(ctx, e) = (ctx.α₀ + e.pos) / (ctx.α₀ + ctx.β₀ + e.pos + e.neg)`

The continuous case (n, Σx, Σx²) makes the context dependence obvious.

## References

- Williams & Stay, "Native Type Theory" - types as comprehension subobjects
- Meredith & Stay, "Operational Semantics in Logical Form" - modal types as rely-guarantee
- Goertzel et al., "Probabilistic Logic Networks" - PLN foundations
-/

namespace Mettapedia.Logic.EvidenceClass

/-! ## Abstract Evidence Type Class

Evidence forms a commutative monoid under `hplus` (parallel aggregation).
This captures the PLN revision rule: independent evidence combines additively.
-/

/-- Evidence aggregates independently of interpretation context.
    This is the monoid structure underlying PLN revision. -/
class EvidenceType (Ev : Type*) extends AddCommMonoid Ev

/-- Evidence with sequential composition (tensor product).
    This captures evidence flow through deduction chains: A → B → C

    Note: The full quantale law (tensor_distrib_sup) requires SupSet on Ev,
    which we don't require here. Specific evidence types can prove this
    when they have the additional structure. -/
class SequentialEvidence (Ev : Type*) extends EvidenceType Ev, CommMonoid Ev

/-! ## Context-Dependent Interpretation

Different domains have different interpretation functions:
- Binary: strength = (α₀ + pos) / (α₀ + β₀ + pos + neg)
- Continuous: mean = (κ₀·μ₀ + Σx) / (κ₀ + n)
-/

/-- Context-dependent evidence interpretation.
    The interpretation function (strength, mean, etc.) requires a context. -/
class InterpretableEvidence (Ctx : Type*) (Ev : Type*) (Val : outParam Type*) where
  /-- The interpretation function: context + evidence → value -/
  interpret : Ctx → Ev → Val

/-- Notation for interpretation: ctx ⊢ e ↦ v means "under context ctx, evidence e interprets to v" -/
notation:50 ctx " ⊢ " e " ↦ " v => InterpretableEvidence.interpret ctx e = v

/-! ## Meta-Evidence for Hyperparameter Learning

For AGI applications, hyperparameters themselves need to be learned.
This requires evidence about evidence (meta-level).
-/

/-- Meta-learnable context: contexts can be updated from meta-evidence.
    This enables learning priors from prediction accuracy. -/
class MetaLearnable (Ctx : Type*) (Meta : Type*) where
  /-- Update context based on meta-evidence -/
  updateContext : Ctx → Meta → Ctx
  /-- Meta-evidence also aggregates (meta-level hplus) -/
  metaHplus : Meta → Meta → Meta

/-! ## Domain-Specific Contexts

These are the concrete context types for each domain.
-/

/-- Binary context: Beta distribution prior parameters -/
structure BinaryContext where
  /-- Prior positive pseudo-count (α₀ in Beta(α₀, β₀)) -/
  α₀ : ℝ≥0∞
  /-- Prior negative pseudo-count (β₀ in Beta(α₀, β₀)) -/
  β₀ : ℝ≥0∞
  deriving Inhabited

namespace BinaryContext

/-- The improper prior (α₀ = β₀ = 0): maximum entropy, no prior information.
    This is what standard PLN uses implicitly. -/
def improper : BinaryContext := ⟨0, 0⟩

/-- The Jeffreys prior (α₀ = β₀ = 0.5): the "reference prior" for binomial. -/
def jeffreys : BinaryContext := ⟨0.5, 0.5⟩

/-- The Bayes-Laplace prior (α₀ = β₀ = 1): uniform prior on [0,1]. -/
def uniform : BinaryContext := ⟨1, 1⟩

/-- The Haldane prior (α₀ = β₀ = 0): same as improper, historical name. -/
def haldane : BinaryContext := improper

end BinaryContext

/-- Continuous context: Normal-Gamma prior parameters -/
structure ContinuousContext where
  /-- Prior mean -/
  μ₀ : ℝ
  /-- Prior precision multiplier (pseudo-observations for mean) -/
  κ₀ : ℝ≥0
  /-- Gamma shape parameter -/
  α₀ : ℝ≥0
  /-- Gamma rate parameter -/
  β₀ : ℝ≥0

instance : Inhabited ContinuousContext := ⟨⟨0, 1, 1, 1⟩⟩

namespace ContinuousContext

/-- Weakly informative prior: centered at 0, low confidence -/
noncomputable def weaklyInformative : ContinuousContext := ⟨0, 0.01, 1, 1⟩

/-- Non-informative limit: κ₀ → 0 gives maximum entropy for mean -/
noncomputable def nonInformative : ContinuousContext := ⟨0, 0, 0.001, 0.001⟩

end ContinuousContext

/-- Categorical context: Dirichlet prior parameters -/
structure CategoricalContext (k : ℕ) where
  /-- Prior concentration parameters (α₁, ..., αₖ) -/
  priors : Fin k → ℝ≥0

namespace CategoricalContext

/-- Symmetric Dirichlet with concentration α for each category -/
def symmetric (k : ℕ) (α : ℝ≥0) : CategoricalContext k := ⟨fun _ => α⟩

/-- Uniform prior: α = 1 for each category -/
def uniform (k : ℕ) : CategoricalContext k := symmetric k 1

/-- Jeffreys prior for categorical: α = 1/2 for each category (standard choice) -/
noncomputable def jeffreys (k : ℕ) : CategoricalContext k := symmetric k (1 / 2)

end CategoricalContext

/-! ## Key Theorems to Prove

These theorems establish that the modal structure is correct and backward-compatible.
-/

/-- The improper prior gives the "self-contained" strength formula.
    This is the backward-compatibility theorem. -/
theorem improper_strength_self_contained
    (e_pos e_neg : ℝ≥0∞) :
    let ctx := BinaryContext.improper
    (ctx.α₀ + e_pos) / (ctx.α₀ + ctx.β₀ + e_pos + e_neg) = e_pos / (e_pos + e_neg) := by
  simp only [BinaryContext.improper, zero_add]

end Mettapedia.Logic.EvidenceClass
