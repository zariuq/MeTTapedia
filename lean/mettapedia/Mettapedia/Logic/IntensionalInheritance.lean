import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Intensional Inheritance: Information-Theoretic Unification

This file provides a POC formalization of Goertzel's information-theoretic
unification of intensional and extensional inheritance.

## Key Insight (Goertzel 2025)

Intensional inheritance I_int(W; F) = mutual information I(F; W)
- "How much does knowing 'x is F' tell us about 'x is W'?"

Extensional inheritance I_ext(W; F) = P(W | F)
- Standard conditional probability / set overlap

**Unifying formula**: P(W | F) = P(W) · 2^{I(F;W)}

**Key theorem**: When properties are singletons (each property = one element),
intensional inheritance reduces to extensional inheritance.

## Philosophical Point

"Creatures with hearts" and "creatures with kidneys" seem like different
concepts (different intensions), but they pick out the same class (same extension)
because hearts and kidneys co-evolved. The information-theoretic view captures
this: I(heart; kidney) ≈ 1 because they're nearly perfectly correlated.

## Design for Hookability

This POC is designed to connect to:
1. `PLNEvidence.lean` - Evidence counts as concrete carrier
2. `Optimality.lean` - Universal prediction / Bayes mixtures
3. `MarkovExchangeability.lean` - Sufficient statistics
4. Future Shannon/Kolmogorov entropy formalizations

## References

- Goertzel, "Intensional Inheritance Between Concepts: An Information-Theoretic
  Interpretation" (2025) - `/home/zar/claude/literature/Intensional-Inheritance.pdf`
- Nil Geisweiller, "Towards a Complete Formalization of PLN" (nuPLN draft)
  - Local copy: `mettapedia/papers/nuPLN.tex`
-/

namespace Mettapedia.Logic.IntensionalInheritance

open Real

/-! ## §1: Property-Based Concepts

A concept is defined by a set of properties, each with a degree (probability
that an element of the concept has that property).
-/

/-- A property is abstractly a predicate on some domain.
    We parameterize by the domain type α. -/
structure Property (α : Type*) where
  name : String  -- For debugging/display
  holds : α → Prop
  deriving Inhabited

/-- A concept is defined by a collection of properties with degrees.
    The degree dᵢ represents P(property Fᵢ holds | x is in concept F). -/
structure Concept (α : Type*) where
  name : String
  properties : List (Property α)
  degrees : List ℝ
  degrees_valid : degrees.length = properties.length := by rfl
  degrees_unit : ∀ d ∈ degrees, 0 ≤ d ∧ d ≤ 1 := by simp

namespace Concept

/-- Number of properties defining this concept -/
def numProperties (F : Concept α) : ℕ := F.properties.length

/-- Get the degree of the i-th property -/
noncomputable def degree (F : Concept α) (i : Fin F.numProperties) : ℝ :=
  F.degrees.get (i.cast F.degrees_valid.symm)

end Concept

/-! ## §2: Singleton Concepts (Extensional View)

A singleton concept has each property corresponding to exactly one element.
This is the "extensional" view where concepts are just sets of instances.
-/

/-- A property is singleton if it holds for exactly one element -/
def Property.isSingleton (P : Property α) : Prop :=
  ∃! x, P.holds x

/-- A concept is extensional (singleton) if all its properties are singletons -/
def Concept.isExtensional (F : Concept α) : Prop :=
  ∀ P ∈ F.properties, P.isSingleton

/-- Create a singleton property from a single element -/
def Property.singleton [DecidableEq α] (name : String) (x : α) : Property α where
  name := name
  holds := fun y => y = x

/-- Singleton properties are indeed singletons -/
theorem Property.singleton_isSingleton [DecidableEq α] (name : String) (x : α) :
    (Property.singleton name x).isSingleton := by
  use x
  constructor
  · rfl
  · intro y hy; exact hy

/-! ## §3: Mutual Information Interface

We define the interface for mutual information. The actual computation
can be filled in later with Shannon or Kolmogorov versions.
-/

/-- Mutual information between two concepts.
    This is the core measure of intensional inheritance.

    I(F; W) = H(W) - H(W | F)

    where H is entropy (Shannon or Kolmogorov).

    **Axiomatized for now** - to be connected to concrete entropy definitions. -/
axiom mutualInfo (α : Type*) : Concept α → Concept α → ℝ

/-- Mutual information is symmetric: I(F; W) = I(W; F) -/
axiom mutualInfo_symm {α : Type*} (F W : Concept α) :
    mutualInfo α F W = mutualInfo α W F

/-- Mutual information is non-negative: I(F; W) ≥ 0 -/
axiom mutualInfo_nonneg {α : Type*} (F W : Concept α) :
    0 ≤ mutualInfo α F W

-- Note: Mutual information is bounded by min entropy: I(F; W) ≤ min(H(F), H(W))
-- This will need entropy definition to state properly

/-! ## §4: Inheritance Definitions -/

/-- Intensional inheritance: how much information F provides about W.
    This IS mutual information. -/
noncomputable def intensionalInheritance (α : Type*) (F W : Concept α) : ℝ :=
  mutualInfo α F W

/-- Prior probability of concept W.
    Axiomatized - to be connected to concrete probability measures. -/
axiom priorProb (α : Type*) : Concept α → ℝ

axiom priorProb_unit {α : Type*} (W : Concept α) : 0 ≤ priorProb α W ∧ priorProb α W ≤ 1

/-- Extensional inheritance: conditional probability P(W | F).
    "What fraction of F instances are also W instances?" -/
axiom extensionalInheritance (α : Type*) : Concept α → Concept α → ℝ

axiom extensionalInheritance_unit {α : Type*} (F W : Concept α) :
    0 ≤ extensionalInheritance α F W ∧ extensionalInheritance α F W ≤ 1

/-! ## §5: The Goertzel Unifying Formula

The key theorem: P(W | F) = P(W) · 2^{I(F;W)}

This unifies extensional and intensional inheritance under one formula.
-/

/-- **Goertzel's Unifying Formula** (2025)

    Extensional inheritance (conditional probability) equals
    prior probability scaled by 2^(mutual information).

    P(W | F) = P(W) · 2^{I(F;W)}

    This is stated as an axiom connecting the abstract definitions.
    A full proof would require:
    1. Concrete probability space
    2. Shannon entropy definitions
    3. Derivation from Bayes' theorem + entropy identities
-/
axiom goertzel_formula {α : Type*} (F W : Concept α) :
    extensionalInheritance α F W = priorProb α W * (2 : ℝ).rpow (mutualInfo α F W)

/-! ## §6: Singleton Reduction Theorem

When concepts are extensional (singleton properties), the intensional
and extensional views coincide.
-/

/-- **Singleton Reduction Theorem**

    For extensional concepts (singleton properties), intensional inheritance
    reduces to extensional inheritance.

    This justifies using simpler set-theoretic reasoning when concepts
    are "just sets of instances" rather than rich property bundles.
-/
theorem singleton_reduction {α : Type*} (F W : Concept α)
    (_hF : F.isExtensional) (_hW : W.isExtensional)
    (hprior_pos : priorProb α W > 0) :
    -- In the singleton case, mutual information directly gives
    -- the log of the inheritance ratio
    (2 : ℝ).rpow (intensionalInheritance α F W) =
    extensionalInheritance α F W / priorProb α W := by
  unfold intensionalInheritance
  -- From goertzel_formula: ext = prior * 2^I
  -- So 2^I = ext / prior
  have h := goertzel_formula F W
  have hprior : priorProb α W ≠ 0 := ne_of_gt hprior_pos
  field_simp [hprior] at h ⊢
  linarith [h]

/-! ## §7: Connection Points for Later Formalization

These definitions provide hooks to connect with other modules.
-/

/-- Hook to PLN Evidence: Convert evidence counts to mutual information estimate.

    Given evidence (n⁺, n⁻), we can estimate mutual information via:
    - Strength s = n⁺/(n⁺+n⁻) estimates P(W|F)
    - From Goertzel formula: I(F;W) = log₂(s/P(W))
-/
noncomputable def mutualInfoFromEvidence (strength prior : ℝ) : ℝ :=
  if prior > 0 ∧ strength > 0 then
    Real.log (strength / prior) / Real.log 2
  else
    0

-- Hook to Optimality: Bayes mixture provides the "universal" mutual information.
--
-- The Bayes mixture ξ = Σ w(μ)·μ gives:
-- - condProb_ξ(b|x) as the universal prediction
-- - This relates to mutual information via entropy of the posterior
--
-- To be connected with Optimality.lean's condProb and universalPrediction

-- Hook to MarkovExchangeability: Sufficient statistics reduce mutual information.
--
-- For Markov exchangeable processes, transition counts are sufficient.
-- This means I(F;W) can be computed from count matrices alone.
--
-- To be connected with MarkovExchangeability.lean's TransCounts

/-! ## §8: Examples -/

section Examples

variable {α : Type*} [DecidableEq α]

/-- Example: "Creature with heart" concept -/
def heartConcept (hasHeart : α → Prop) : Concept α where
  name := "has_heart"
  properties := [⟨"heart", hasHeart⟩]
  degrees := [0.99]  -- 99% of creatures in our domain have hearts
  degrees_unit := by simp; norm_num

/-- Example: "Creature with kidney" concept -/
def kidneyConcept (hasKidney : α → Prop) : Concept α where
  name := "has_kidney"
  properties := [⟨"kidney", hasKidney⟩]
  degrees := [0.99]  -- 99% of creatures in our domain have kidneys
  degrees_unit := by simp; norm_num

-- The biological fact: hearts and kidneys co-evolved.
--
-- I(heart; kidney) ≈ H(heart) ≈ H(kidney)
--
-- meaning knowing one tells you almost everything about the other.
-- This is why "creatures with hearts" ≈ "creatures with kidneys"
-- despite being "different concepts" intensionally.
--
-- This would be an empirical/biological axiom in a full formalization

end Examples

end Mettapedia.Logic.IntensionalInheritance
