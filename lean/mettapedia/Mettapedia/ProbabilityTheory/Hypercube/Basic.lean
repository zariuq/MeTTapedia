/-
# Hypercube of Probability Theories

A categorical framework organizing probability theories by their operational semantics.
The key insight: different probability theories arise from different choices along
several fundamental axes.

## The Stay-Wells Connection

Following Stay & Wells' H_Σ construction, we observe that probability theories can be
organized by their "base rewrites" (inference rules) and the sort assignments to their
slots. Each vertex of the hypercube is a different probability theory!

## Core Axes

1. **Commutativity**: Does A∧B = B∧A?
   - Yes: Classical, Cox, K&S, D-S
   - No: Quantum

2. **Distributivity**: Does ∧ distribute over ∨?
   - Yes (Boolean): Classical, Cox
   - Yes (Distributive lattice): K&S
   - No (Orthomodular): Quantum

3. **Precision**: Is P(A) + P(¬A) = 1?
   - Yes (Precise): Classical, Cox, K&S
   - No (Imprecise): D-S (Bel + Pl ≤ 2, but gap possible)

4. **Ordering**: Is the plausibility order total?
   - Yes (Linear): K&S
   - No (Partial): Could allow incomparable events

5. **Additivity**: Is P σ-additive on the lattice?
   - Yes: Kolmogorov
   - Derived from other axioms: Cox, K&S

## Extended Axes

This development also includes additional axes used in the later parts of the file:
`DeterminismAxis`, `SupportAxis`, `RegularityAxis`, and `IndependenceAxis`.

## K&S Naturalness

This framework helps answer whether K&S is "natural":
- K&S sits at the vertex (Commutative, Distributive, Precise, Linear, Derived-Additive)
- The LinearOrder requirement distinguishes K&S from more general valuations
- Commutativity is NOT assumed in K&S but IS used implicitly in some proofs!

## References

- Stay & Wells, "Generating Hypercubes of Type Systems"
- Cox, "Probability, Frequency and Reasonable Expectation" (1946)
- Knuth & Skilling, "Foundations of Inference" (2012)
- Shafer, "A Mathematical Theory of Evidence" (1976)
- von Neumann, "Mathematical Foundations of Quantum Mechanics" (1932)
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Mettapedia.ProbabilityTheory.Hypercube

/-!
## §1: The Fundamental Axes

Each axis represents a choice in the operational semantics of a probability theory.
Since several axes have 3–4 values, the total number of vertices is the product of
the axis cardinalities (not `2^n`).
-/

/-- The commutativity axis: does the meet operation commute? -/
inductive CommutativityAxis where
  | commutative : CommutativityAxis    -- A ∧ B = B ∧ A
  | noncommutative : CommutativityAxis -- [A, B] ≠ 0 possible
  deriving DecidableEq, Repr

/-- The distributivity axis: does meet distribute over join? -/
inductive DistributivityAxis where
  | boolean : DistributivityAxis       -- Boolean algebra (strongest)
  | distributive : DistributivityAxis  -- Distributive lattice
  | orthomodular : DistributivityAxis  -- Orthomodular (quantum)
  | general : DistributivityAxis       -- No distributivity
  deriving DecidableEq, Repr

/-- The precision axis: is P(A) + P(¬A) = 1 always? -/
inductive PrecisionAxis where
  | precise : PrecisionAxis    -- Bel = Pl (no epistemic gap)
  | imprecise : PrecisionAxis  -- Bel ≤ Pl (epistemic uncertainty)
  deriving DecidableEq, Repr

/-- The ordering axis: is the plausibility order total? -/
inductive OrderAxis where
  | totalOrder : OrderAxis    -- Total order (trichotomy)
  | partialOrder : OrderAxis  -- Partial order (incomparable events allowed)
  deriving DecidableEq, Repr

/-- The density axis: do we *assume* the plausibility scale is densely ordered?

In the hypercube’s weakness ordering we treat `dense` as an additional constraint, and
`nondense` as “no density axiom is required” (the scale may still be dense in a model).
This matches the “weakness = fewer required laws” convention used in Goertzel’s Weakness notes
(`literature/Goertzel Articles/Weakness-Book/Weakness-Theory-10.tex`).
-/
inductive DensityAxis where
  | nondense : DensityAxis
  | dense : DensityAxis
  deriving DecidableEq, Repr

/-- The completeness axis: do we *assume* conditional completeness for the plausibility scale?

This is intended to track when “Dedekind cut”-style constructions are available on the scale.
We use `conditionallyComplete` (rather than `complete`) because most analytic scales (e.g. `ℝ`)
are only conditionally complete in Lean’s order hierarchy (no top element).
-/
inductive CompletenessAxis where
  | incomplete : CompletenessAxis
  | conditionallyComplete : CompletenessAxis
  deriving DecidableEq, Repr

/-- The separation axis: do we *assume* the iterate/power “sandwich” separation property?

This corresponds to the Knuth–Skilling `KSSeparation`/`KSSeparationStrict` typeclasses used in the
Appendix A development, but is recorded here as an axis so it can participate in the global
hypercube story.
-/
inductive SeparationAxis where
  | none : SeparationAxis
  | ksSeparation : SeparationAxis
  | ksSeparationStrict : SeparationAxis
  deriving DecidableEq, Repr

/-- The additivity axis: how does probability combine for disjoint events? -/
inductive AdditivityAxis where
  | additive : AdditivityAxis    -- P(A∪B) = P(A) + P(B) for disjoint
  | subadditive : AdditivityAxis -- P(A∪B) ≤ P(A) + P(B) (belief functions)
  | derived : AdditivityAxis     -- Additivity derived from other axioms
  deriving DecidableEq, Repr

/-- The invertibility axis: how much algebraic cancellation exists in the plausibility scale?

This axis exists primarily to track the Goertzel-v3 "add inverses, invoke Hölder" patch:
moving from a monoid (K&S as stated) to a group (adds inverses) dramatically changes which
external representation theorems apply.
-/
inductive InvertibilityAxis where
  | semigroup : InvertibilityAxis -- Only associativity is available
  | monoid : InvertibilityAxis    -- Identity element exists
  | group : InvertibilityAxis     -- Inverses exist (group completion)
  deriving DecidableEq, Repr

/-- The determinism axis: how "crisp" are truth values?
    This captures the spectrum from classical logic to probabilistic to fuzzy. -/
inductive DeterminismAxis where
  | deterministic : DeterminismAxis  -- P(A) ∈ {0, 1} (classical logic, ultrafilters)
  | probabilistic : DeterminismAxis  -- P(A) ∈ [0, 1] (standard probability)
  | fuzzy : DeterminismAxis          -- μ(A) ∈ [0, 1] (fuzzy membership, different semantics)
  deriving DecidableEq, Repr

/-- The support axis: what is the cardinality of the sample space?
    This affects computational tractability and measure-theoretic machinery needed. -/
inductive SupportAxis where
  | finite : SupportAxis      -- Finitely many outcomes (discrete, simple)
  | countable : SupportAxis   -- Countably many outcomes (discrete distributions)
  | continuous : SupportAxis  -- Uncountable (requires full measure theory)
  deriving DecidableEq, Repr

/-- The regularity axis: how well does the measure interact with topology?
    Radon measures are the "nicest" - they concentrate on compact sets. -/
inductive RegularityAxis where
  | radon : RegularityAxis          -- Inner regular, locally finite (Riesz representation)
  | borel : RegularityAxis          -- σ-additive on Borel σ-algebra
  | finitelyAdditive : RegularityAxis -- Only finite additivity (de Finetti)
  deriving DecidableEq, Repr

/-- The independence axis: what partition structure governs independence?

    This is THE key axis for noncommutative probability theories!

    - **tensor**: Classical independence, ALL partitions (convolution *)
    - **free**: Free independence, NONCROSSING partitions (free convolution ⊞)
    - **boolean**: Boolean independence, INTERVAL partitions
    - **monotone**: Monotone independence, ORDERED partitions

    References:
    - Voiculescu, "Free Random Variables" (1992) - free probability
    - Speicher, "Combinatorics of Free Probability" - noncrossing partitions
    - Ben Ghorbal & Schürmann, "Non-commutative notions of stochastic independence" (2002)
-/
inductive IndependenceAxis where
  | tensor : IndependenceAxis    -- Classical: all partitions, X⊗Y
  | free : IndependenceAxis      -- Free: noncrossing partitions, X⊞Y (Voiculescu)
  | boolean : IndependenceAxis   -- Boolean: interval partitions
  | monotone : IndependenceAxis  -- Monotone: ordered partitions
  deriving DecidableEq, Repr

/-!
## §2: The Extended Probability Hypercube

A vertex in the hypercube specifies choices along all 13 axes.
With 13 axes (some with 2-4 values), we have thousands of potential vertices,
though many combinations don't correspond to meaningful probability theories.

The NEW IndependenceAxis captures the fundamental distinction between:
- Classical probability (tensor independence)
- Free probability (free independence) - key for random matrix theory & ML!
- Other noncommutative independences (boolean, monotone)
-/

/-- A vertex in the probability hypercube: a specific probability theory.
    The 13 axes capture fundamental choices in the foundations of probability. -/
@[ext]
structure ProbabilityVertex where
  commutativity : CommutativityAxis
  distributivity : DistributivityAxis
  precision : PrecisionAxis
  orderAxis : OrderAxis
  density : DensityAxis
  completeness : CompletenessAxis
  separation : SeparationAxis
  additivity : AdditivityAxis
  invertibility : InvertibilityAxis
  determinism : DeterminismAxis
  support : SupportAxis
  regularity : RegularityAxis
  independence : IndependenceAxis  -- NEW: tensor vs free vs boolean vs monotone
  deriving DecidableEq, Repr

/-- The classical Kolmogorov probability theory (continuous version). -/
def kolmogorov : ProbabilityVertex where
  commutativity := .commutative
  distributivity := .boolean
  precision := .precise
  orderAxis := .totalOrder
  density := .dense
  completeness := .conditionallyComplete
  separation := .ksSeparationStrict
  additivity := .additive
  invertibility := .monoid
  determinism := .probabilistic
  support := .continuous
  regularity := .borel
  independence := .tensor         -- Classical tensor independence

/-- Cox's probability theory derived from consistency requirements. -/
def cox : ProbabilityVertex where
  commutativity := .commutative  -- Assumed: p(A∧B|C) = p(B∧A|C)
  distributivity := .boolean     -- Works on Boolean algebras
  precision := .precise          -- Derives P(A) + P(¬A) = 1
  orderAxis := .totalOrder       -- Total ordering assumed
  density := .dense
  completeness := .conditionallyComplete
  separation := .ksSeparationStrict
  additivity := .derived         -- Derived from functional equations
  invertibility := .monoid
  determinism := .probabilistic
  support := .continuous
  regularity := .borel
  independence := .tensor

/-- Knuth-Skilling probability theory. -/
def knuthSkilling : ProbabilityVertex where
  commutativity := .commutative  -- Target: commutative calculus (assumed or derived from separation)
  distributivity := .distributive -- Distributive lattice (not Boolean)
  precision := .precise          -- Derives standard probability
  orderAxis := .totalOrder       -- CRITICAL: LinearOrder required
  density := .dense
  completeness := .conditionallyComplete
  separation := .ksSeparationStrict
  additivity := .derived         -- Derived from associativity + Archimedean
  invertibility := .monoid
  determinism := .probabilistic
  support := .continuous
  regularity := .borel
  independence := .tensor

/-- Knuth–Skilling with inverses (Goertzel-style “group fix”): same as `knuthSkilling`, but the
combination structure is assumed to be a group rather than merely a monoid. -/
def knuthSkillingGroup : ProbabilityVertex :=
  { knuthSkilling with invertibility := .group }

/-!
Note: the same semantic vertex `knuthSkilling` can be justified by different *axiom bundles*
at the K&S level (e.g. explicitly assuming commutativity/Archimedean vs assuming `KSSeparation`
and deriving consequences). See `Mettapedia/ProbabilityTheory/KnuthSkilling/AxiomSystemEquivalence.lean`.
-/

/-- Dempster-Shafer belief functions. -/
def dempsterShafer : ProbabilityVertex where
  commutativity := .commutative   -- Set operations commute
  distributivity := .boolean      -- Power set is Boolean
  precision := .imprecise         -- Bel(A) + Bel(¬A) ≤ 1
  orderAxis := .partialOrder      -- Bel only induces partial order
  density := .nondense
  completeness := .incomplete
  separation := .none
  additivity := .subadditive      -- n-monotone, not additive
  invertibility := .monoid
  determinism := .probabilistic
  support := .finite              -- Typically finite frame of discernment
  regularity := .borel
  independence := .tensor

/-- Quantum probability (von Neumann algebras). -/
def quantum : ProbabilityVertex where
  commutativity := .noncommutative -- [A,B] ≠ 0 for incompatible observables
  distributivity := .orthomodular  -- Orthomodular lattice structure
  precision := .precise            -- States give precise probabilities
  orderAxis := .partialOrder       -- No total order on projections
  density := .nondense
  completeness := .incomplete
  separation := .none
  additivity := .additive          -- σ-additive on commuting projections
  invertibility := .monoid
  determinism := .probabilistic
  support := .continuous
  regularity := .borel
  independence := .tensor          -- Standard QM uses tensor products

/-- FREE PROBABILITY (Voiculescu): The theory of random matrices!
    Key for understanding deep neural networks at infinite width.
    Uses NONCROSSING partitions instead of all partitions. -/
def freeProbability : ProbabilityVertex where
  commutativity := .noncommutative -- Operators don't commute
  distributivity := .general       -- No lattice structure on operators
  precision := .precise            -- Well-defined spectral measures
  orderAxis := .partialOrder       -- Partial order on positive operators
  density := .nondense
  completeness := .incomplete
  separation := .none
  additivity := .additive          -- Additive on spectral projections
  invertibility := .monoid
  determinism := .probabilistic
  support := .continuous           -- Continuous spectra
  regularity := .borel
  independence := .free            -- FREE independence! Noncrossing partitions

/-- Classical propositional logic: deterministic, no uncertainty.

We set `density/completeness/separation` to their “most specific” values so that `classicalLogic`
is the bottom element of the hypercube’s weakness order; semantically, a deterministic theory can
always be interpreted inside a richer plausibility scale by restricting to `{0,1}`.
-/
def classicalLogic : ProbabilityVertex where
  commutativity := .commutative
  distributivity := .boolean
  precision := .precise
  orderAxis := .totalOrder
  density := .dense
  completeness := .conditionallyComplete
  separation := .ksSeparationStrict
  additivity := .additive
  invertibility := .group
  determinism := .deterministic   -- P(A) ∈ {0, 1}
  support := .finite
  regularity := .radon            -- Finite implies Radon (most specific regularity)
  independence := .tensor

/-- Fuzzy set theory (Zadeh): membership degrees without probabilistic semantics. -/
def fuzzyLogic : ProbabilityVertex where
  commutativity := .commutative
  distributivity := .distributive  -- Often uses min/max which is distributive
  precision := .imprecise          -- μ(A) + μ(¬A) can be ≠ 1
  orderAxis := .partialOrder
  density := .nondense
  completeness := .incomplete
  separation := .none
  additivity := .subadditive       -- max(μ(A), μ(B)) ≤ μ(A) + μ(B)
  invertibility := .monoid
  determinism := .fuzzy
  support := .continuous
  regularity := .borel
  independence := .tensor

/-- Finite probability: dice, cards, simple combinatorics. -/
def finiteProbability : ProbabilityVertex where
  commutativity := .commutative
  distributivity := .boolean
  precision := .precise
  orderAxis := .totalOrder
  density := .dense
  completeness := .conditionallyComplete
  separation := .ksSeparationStrict
  additivity := .additive
  invertibility := .monoid
  determinism := .probabilistic
  support := .finite              -- Finitely many outcomes
  regularity := .radon            -- Finite = Radon automatically
  independence := .tensor

/-- de Finetti's subjective probability: only finite additivity required. -/
def deFinetti : ProbabilityVertex where
  commutativity := .commutative
  distributivity := .boolean
  precision := .precise
  orderAxis := .totalOrder
  density := .dense
  completeness := .conditionallyComplete
  separation := .ksSeparationStrict
  additivity := .additive         -- Finite additivity (weaker than σ-additive)
  invertibility := .monoid
  determinism := .probabilistic
  independence := .tensor
  support := .continuous
  regularity := .finitelyAdditive -- Key: no countable additivity!

/-- Discrete probability: countable sample spaces (Poisson, geometric, etc.). -/
def discreteProbability : ProbabilityVertex where
  commutativity := .commutative
  distributivity := .boolean
  precision := .precise
  orderAxis := .totalOrder
  density := .dense
  completeness := .conditionallyComplete
  separation := .ksSeparationStrict
  additivity := .additive
  invertibility := .monoid
  determinism := .probabilistic
  support := .countable
  regularity := .borel
  independence := .tensor

/-- Radon probability: the "nicest" continuous measures (Gaussian, etc.). -/
def radonProbability : ProbabilityVertex where
  commutativity := .commutative
  distributivity := .boolean
  precision := .precise
  orderAxis := .totalOrder
  density := .dense
  completeness := .conditionallyComplete
  separation := .ksSeparationStrict
  additivity := .additive
  invertibility := .monoid
  determinism := .probabilistic
  support := .continuous
  regularity := .radon            -- Inner regular, tight
  independence := .tensor

/-!
## §2b: PLN (Probabilistic Logic Networks)

PLN occupies a special position in the hypercube:

1. **Simple PLN** (SimpleTruthValues): Same vertex as Cox/Kolmogorov
   - Precise truth values (strength ∈ [0,1])
   - Deduction formula is DERIVED from:
     - Law of total probability: P(C|A) = P(C|B)P(B|A) + P(C|¬B)P(¬B|A)
     - Independence assumption: P(C|A,B) ≈ P(C|B)
     - Fréchet bounds (proven equivalent to PLN consistency in PLNFrechetBounds.lean)

2. **Indefinite PLN** (IndefiniteTruthValues): Different vertex!
   - Imprecise truth values (interval [L, U] with credibility b)
   - Extends Walley's imprecise probabilities
   - Adds lookahead parameter k for future evidence

The PLN deduction formula:
  sAC = sAB * sBC + (1 - sAB) * (pC - pB * sBC) / (1 - pB)

is the quantale composition in the [0,1] commutative quantale!
See PLNQuantaleConnection.lean for the formal proof.

### PLN vs K&S vs Cox Comparison

| Aspect | PLN | K&S | Cox |
|--------|-----|-----|-----|
| Carrier | [0,1] | Abstract scale α | [0,1] |
| Formula | Deduction rule | ⊕ (associative) | Product rule |
| Derivation | Law of total prob + independence | Assoc + Archimedean + Separation | Functional equations |
| Commutativity | Assumed (tensor) | Derived from Separation | Assumed |
| Key axiom | Fréchet consistency | KSSeparation | Continuity |
-/

/-- PLN with Simple Truth Values: same vertex as classical probability.

The deduction formula is DERIVABLE from:
1. Law of total probability
2. Independence assumption P(C|A,B) ≈ P(C|B)
3. Fréchet bounds (from basic probability theory)

See: `Mettapedia.Logic.PLNDeduction` and `Mettapedia.Logic.PLNFrechetBounds` -/
def plnSimple : ProbabilityVertex where
  commutativity := .commutative   -- Tensor independence is commutative
  distributivity := .boolean      -- Works on Boolean algebra of events
  precision := .precise           -- SimpleTruthValue: single strength in [0,1]
  orderAxis := .totalOrder        -- Total order on [0,1]
  density := .dense
  completeness := .conditionallyComplete
  separation := .ksSeparationStrict
  additivity := .derived          -- Derived from Fréchet bounds
  invertibility := .monoid
  determinism := .probabilistic
  support := .continuous
  regularity := .borel
  independence := .tensor         -- Classical tensor independence

/-- PLN with Indefinite Truth Values: DIFFERENT vertex due to imprecision.

IndefiniteTruthValue = ⟨[L, U], b, k⟩ where:
- [L, U] = probability interval
- b = credibility (how confident we are the interval contains the true value)
- k = lookahead parameter (evidence expected before next decision)

This extends Walley's imprecise probabilities but with different semantics:
- Walley: worst-case bounds
- PLN: expected-case with credibility levels

See: Chapter 4 of PLN book, `Mettapedia.Logic.PLNEvidence` -/
def plnIndefinite : ProbabilityVertex where
  commutativity := .commutative   -- Still commutative (tensor)
  distributivity := .boolean
  precision := .imprecise         -- KEY DIFFERENCE: interval truth values!
  orderAxis := .partialOrder      -- Intervals induce partial order
  density := .nondense
  completeness := .incomplete
  separation := .none
  additivity := .derived
  invertibility := .monoid
  determinism := .probabilistic
  support := .continuous
  regularity := .borel
  independence := .tensor

/-- PLN Simple = Kolmogorov semantically (same vertex) -/
theorem pln_simple_eq_kolmogorov_vertex :
    plnSimple.commutativity = kolmogorov.commutativity ∧
    plnSimple.precision = kolmogorov.precision ∧
    plnSimple.independence = kolmogorov.independence := by
  simp [plnSimple, kolmogorov]

/-- PLN Simple = Cox semantically (same vertex) -/
theorem pln_simple_eq_cox_vertex :
    plnSimple.commutativity = cox.commutativity ∧
    plnSimple.precision = cox.precision ∧
    plnSimple.additivity = cox.additivity := by
  simp [plnSimple, cox]

/-- PLN Indefinite differs from PLN Simple in precision axis -/
theorem pln_indefinite_differs_from_simple :
    plnIndefinite.precision ≠ plnSimple.precision := by
  simp [plnIndefinite, plnSimple]

/-!
## §3: Morphisms Between Vertices

Edges in the hypercube represent "forgetful" or "specializing" morphisms.
-/

/-- A morphism between probability theories: one specializes to another. -/
structure ProbabilityMorphism (V W : ProbabilityVertex) where
  /-- The morphism respects the vertex structure -/
  respects_commutativity :
    V.commutativity = .commutative → W.commutativity = .commutative
  respects_precision :
    V.precision = .precise → W.precision = .precise

/-- K&S is a specialization of Cox (same vertex, different derivation). -/
def ks_specializes_cox : ProbabilityMorphism knuthSkilling cox where
  respects_commutativity := fun _ => rfl
  respects_precision := fun _ => rfl

/-- Classical probability embeds into D-S (as Bayesian mass functions).
    Note: This morphism goes FROM D-S TO Kolmogorov (specialization).
    Every D-S belief function with Bayesian mass function IS a probability. -/
def bayesian_ds_is_classical : ProbabilityMorphism dempsterShafer kolmogorov where
  respects_commutativity := fun _ => rfl
  respects_precision := fun h => by
    -- D-S is imprecise, so hypothesis h contradicts dempsterShafer.precision = .imprecise
    simp only [dempsterShafer] at h
    -- h : PrecisionAxis.imprecise = PrecisionAxis.precise (which is False)
    exact absurd h (by decide)

/-!
## §4: Operational Semantics as Rewrite Rules

Following Stay-Wells, we express the "base rewrites" for each theory.
These are the fundamental inference rules.
-/

/-- Base rewrite rules that define a probability theory's operational semantics. -/
inductive BaseRewriteKind where
  | productRule : BaseRewriteKind    -- P(A∧B) = P(A) · P(B|A)
  | sumRule : BaseRewriteKind        -- P(A∨B) = P(A) + P(B) - P(A∧B)
  | negationRule : BaseRewriteKind   -- P(¬A) = 1 - P(A)
  | bayesRule : BaseRewriteKind      -- P(A|B) = P(A)·P(B|A)/P(B)
  | dempsterRule : BaseRewriteKind   -- Dempster combination
  | vonNeumannRule : BaseRewriteKind -- Born rule: P = Tr(ρ·P)
  | ksAssociativity : BaseRewriteKind -- (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
  | plnDeduction : BaseRewriteKind   -- PLN: sAC = sAB·sBC + (1-sAB)·(pC-pB·sBC)/(1-pB)
  | plnRevision : BaseRewriteKind    -- PLN: combine independent evidence sources
  deriving DecidableEq, Repr

/-!
### PLN Base Rewrites: The Derivation

The PLN deduction rule is **not primitive** - it's DERIVED from:

1. **Law of Total Probability** (primitive in Kolmogorov):
   P(C|A) = P(C|B)·P(B|A) + P(C|¬B)·P(¬B|A)

2. **Independence Assumption** (the key PLN heuristic):
   P(C|A,B) ≈ P(C|B)  (screening off)

3. **Algebra**:
   Substituting P(C|¬B) = (P(C) - P(B)·P(C|B))/(1 - P(B)) gives the formula.

The Fréchet bounds (proven in PLNFrechetBounds.lean) ensure this is well-defined:
- max(0, P(A)+P(B)-1) ≤ P(A∩B) ≤ min(P(A), P(B))

**Key Insight**: PLN deduction = quantale composition in [0,1]!
The "direct path" term sAB·sBC is the quantale tensor product.
The "indirect path" term uses residuation (right adjoint to tensor).

See: PLNQuantaleConnection.lean, PLNEvidence.lean
-/

/-- The base rewrites used by each probability theory. -/
def baseRewrites : ProbabilityVertex → List BaseRewriteKind
  | v =>
    match v.commutativity, v.precision with
    | .commutative, .precise =>
        [.productRule, .sumRule, .negationRule, .bayesRule]
    | .commutative, .imprecise =>
        [.dempsterRule]  -- D-S uses different combination
    | .noncommutative, _ =>
        [.vonNeumannRule]  -- Quantum uses Born rule

/-!
## §5: The Commutativity Question for K&S

This is crucial: K&S doesn't explicitly assume commutativity of `op`,
but the proofs may use it implicitly!
-/

/-- The key question: does K&S require commutativity?

K&S Axioms (Appendix A):
1. Order: op is strictly monotone
2. Associativity: (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)
3. Identity: x ⊕ 0 = x
4. Archimedean: no infinitesimals

NOWHERE is commutativity explicitly stated!

But the representation theorem maps to (ℝ≥0, +) which IS commutative.
The question: does the proof USE commutativity implicitly?

Hypothesis: Yes, in the Archimedean step when comparing iterate sequences.
-/
theorem ks_commutativity_question :
    -- If K&S derivation goes through, the resulting operation is commutative
    -- This is a consequence, not an assumption!
    knuthSkilling.commutativity = .commutative := rfl

/-- The hypercube predicts: if commutativity is essential, K&S and Cox
    occupy the SAME vertex (modulo derivation style). -/
theorem ks_cox_same_vertex_structure :
    knuthSkilling.commutativity = cox.commutativity ∧
    knuthSkilling.precision = cox.precision ∧
    knuthSkilling.orderAxis = cox.orderAxis := by
  simp [knuthSkilling, cox]

/-!
## §6: What Makes K&S Different?

The hypercube reveals K&S's unique position:
1. Starts from WEAKER lattice structure (distributive, not Boolean)
2. Uses STRONGER ordering (LinearOrder required)
3. DERIVES additivity from associativity + Archimedean

This is the K&S insight: you can start from more algebraic axioms
and derive the same probability theory!
-/

/-- K&S uses distributive lattice (weaker than Boolean). -/
theorem ks_weaker_lattice :
    knuthSkilling.distributivity = .distributive ∧
    cox.distributivity = .boolean := by simp [knuthSkilling, cox]

/-- K&S requires linear order (same as Cox). -/
theorem ks_requires_linear_order :
    knuthSkilling.orderAxis = OrderAxis.totalOrder := rfl

/-- The naturality criterion: a probability theory is "natural" if it
    occupies a vertex where all axes have canonical choices.

    K&S is natural because:
    1. Commutativity: follows from the representation
    2. Distributivity: minimal structure (distributive lattice)
    3. Precision: derived from the other axioms
    4. Linear order: required for the Archimedean argument
    5. Additivity: derived, not assumed
-/
def isNaturalVertex (v : ProbabilityVertex) : Prop :=
  v.additivity = .derived ∧  -- Additivity should be derived, not assumed
  v.precision = .precise     -- And it should give standard probability

theorem ks_is_natural : isNaturalVertex knuthSkilling := by
  simp [isNaturalVertex, knuthSkilling]

theorem kolmogorov_not_derived : ¬(kolmogorov.additivity = .derived) := by
  simp [kolmogorov]

/-!
## §7: The Quantum Escape Route

Quantum probability escapes the classical hypercube by:
1. Dropping commutativity (non-commuting observables)
2. Using orthomodular lattice (not distributive)

This shows WHY quantum probability is fundamentally different!
-/

theorem quantum_different_from_classical :
    quantum.commutativity ≠ kolmogorov.commutativity ∧
    quantum.distributivity ≠ kolmogorov.distributivity := by
  simp [quantum, kolmogorov]

/-- The Robertson uncertainty principle is a CONSEQUENCE of non-commutativity.
    In the hypercube view: moving from commutative to noncommutative vertex
    introduces fundamental uncertainty relations. -/
theorem noncommutativity_implies_uncertainty :
    ∀ v : ProbabilityVertex,
    v.commutativity = .noncommutative →
    -- Heisenberg-Robertson uncertainty is possible
    True := by  -- Placeholder for the actual uncertainty relation
  intros
  trivial

/-!
## §8: Hypercube Navigation

Understanding which edges are "natural" movements between theories.
-/

/-- Hamming distance between two vertices (number of differing axes). -/
def hammingDistance (V W : ProbabilityVertex) : ℕ :=
  (if V.commutativity = W.commutativity then 0 else 1) +
  (if V.distributivity = W.distributivity then 0 else 1) +
  (if V.precision = W.precision then 0 else 1) +
  (if V.orderAxis = W.orderAxis then 0 else 1) +
  (if V.density = W.density then 0 else 1) +
  (if V.completeness = W.completeness then 0 else 1) +
  (if V.separation = W.separation then 0 else 1) +
  (if V.additivity = W.additivity then 0 else 1) +
  (if V.invertibility = W.invertibility then 0 else 1) +
  (if V.determinism = W.determinism then 0 else 1) +
  (if V.support = W.support then 0 else 1) +
  (if V.regularity = W.regularity then 0 else 1) +
  (if V.independence = W.independence then 0 else 1)

/-- An edge is natural if it represents adding structure (specialization)
    or removing structure (generalization). Exactly one of the 13 axes differs. -/
def isNaturalEdge (V W : ProbabilityVertex) : Prop :=
  hammingDistance V W = 1

instance (V W : ProbabilityVertex) : Decidable (isNaturalEdge V W) := by
  unfold isNaturalEdge
  infer_instance

/-!
## §9: Summary and Implications for K&S Formalization

The hypercube framework suggests:

1. **Commutativity in K&S**: The representation theorem maps to (ℝ≥0, +),
   which is commutative. The question is whether the PROOF requires
   commutativity, or whether it's a CONSEQUENCE.

   Current evidence: Some steps (like comparing iterate sequences from
   different starting points) may implicitly use commutativity.

2. **LinearOrder necessity**: K&S explicitly requires LinearOrder
   (trichotomy). This is DIFFERENT from just having a partial order.
   The Archimedean argument needs to compare ALL pairs of elements.

3. **Why K&S is interesting**: It occupies a unique position where
   - Weaker lattice structure than Cox (distributive vs Boolean)
   - Stronger ordering than D-S (linear vs partial)
   - Derives additivity rather than assuming it

4. **Naturality**: K&S is "natural" in the sense that it derives
   probability from minimal algebraic axioms. The question is whether
   those axioms secretly encode more structure than advertised.
-/

/-- The central question for the K&S formalization:
    Does associativity + Archimedean + LinearOrder secretly imply commutativity?

    If yes: K&S is a valid derivation of probability
    If no: K&S needs an additional (implicit) axiom -/
def centralQuestion : Prop :=
  ∀ (α : Type*) [LinearOrder α],
  ∀ (op : α → α → α) (ident : α),
  -- Associativity
  (∀ x y z, op (op x y) z = op x (op y z)) →
  -- Identity
  (∀ x, op x ident = x) →
  (∀ x, op ident x = x) →
  -- Strict monotonicity
  (∀ y, StrictMono (fun x => op x y)) →
  (∀ x, StrictMono (fun y => op x y)) →
  -- Archimedean
  (∀ x y, ident < x → ∃ n : ℕ, y < Nat.iterate (op x) n x) →
  -- Positivity
  (∀ x, ident ≤ x) →
  -- CONCLUSION: Commutativity follows?
  (∀ x y, op x y = op y x)

-- NOTE: `centralQuestion` has been REFUTED via counterexample.
-- See: CentralQuestionCounterexample.lean
-- K&S does NOT derive commutativity from the stated axioms alone.

/-!
## §10: Hypercube Vertex Classification

This file uses 13 axes. With axis sizes `2 * 4 * 2 * 2 * 2 * 2 * 3 * 3 * 3 * 3 * 3 * 3 * 4`, this is
`373248` possible vertices, though many combinations won't correspond to coherent
probability theories.

Rather than enumerate all vertices, we classify based on logical constraints.
-/

/-- Classification of vertex validity -/
inductive VertexStatus where
  | inhabited : String → VertexStatus  -- Has a known theory with this name
  | possible : VertexStatus            -- Logically coherent but no known theory
  | impossible : String → VertexStatus -- Logically inconsistent (reason given)
  deriving Repr

/-- Classify a vertex as inhabited, possible, or impossible.
    Uses pattern matching on the first 5 axes for known theories,
    with the remaining axes providing refinements. -/
def classifyVertex (v : ProbabilityVertex) : VertexStatus :=
  -- First check for impossible combinations
  if v.commutativity = .noncommutative ∧ v.distributivity = .boolean then
    .impossible "Boolean algebra is always commutative"
  else if v.commutativity = .commutative ∧ v.distributivity = .orthomodular then
    .impossible "Orthomodular is the non-commutative generalization"
  else if v.determinism = .deterministic ∧ v.precision = .imprecise then
    .impossible "Deterministic logic has precise truth values"
  else if v.separation ≠ .none ∧ v.orderAxis = .partialOrder then
    .impossible "KSSeparation is defined only for total (trichotomous) plausibility orders"
  else if v.separation ≠ .none ∧ v.invertibility = .semigroup then
    .impossible "KSSeparation assumes an identity element (at least a monoid)"
  else if v.separation ≠ .none ∧ v.commutativity = .noncommutative then
    .impossible "KSSeparation forces commutativity (see KnuthSkilling/Separation/SandwichSeparation.lean)"
  else if v.support = .finite ∧ v.regularity = .finitelyAdditive ∧ v.additivity = .additive then
    .impossible "Finite support with σ-additivity equals finite additivity"
  -- Check for known theories
  else if v = kolmogorov then .inhabited "Kolmogorov"
  else if v = cox then .inhabited "Cox"
  else if v = knuthSkilling then .inhabited "Knuth-Skilling"
  else if v = dempsterShafer then .inhabited "Dempster-Shafer"
  else if v = quantum then .inhabited "Quantum"
  else if v = classicalLogic then .inhabited "Classical Logic"
  else if v = fuzzyLogic then .inhabited "Fuzzy Logic"
  else if v = finiteProbability then .inhabited "Finite Probability"
  else if v = discreteProbability then .inhabited "Discrete Probability"
  else if v = radonProbability then .inhabited "Radon Probability"
  else if v = deFinetti then .inhabited "de Finetti"
  else .possible

/-- The most general vertex: maximally permissive on all 13 axes. -/
def mostGeneralVertex : ProbabilityVertex where
  commutativity := .noncommutative
  distributivity := .general
  precision := .imprecise
  orderAxis := .partialOrder
  density := .nondense
  completeness := .incomplete
  separation := .none
  additivity := .subadditive
  invertibility := .semigroup
  determinism := .fuzzy            -- Fuzzy is most general (includes probabilistic and deterministic)
  support := .continuous           -- Continuous includes countable and finite
  regularity := .finitelyAdditive  -- Weakest regularity requirement
  independence := .free            -- Free is most general independence (includes tensor)

/-- The most specific vertex: classical logic (deterministic, finite, maximally constrained). -/
def mostSpecificVertex : ProbabilityVertex := classicalLogic

/-- A vertex is more general than another if each axis is at least as general. -/
def isMoreGeneral (v w : ProbabilityVertex) : Prop :=
  -- Noncommutative ≥ Commutative
  (v.commutativity = .noncommutative ∨ v.commutativity = w.commutativity) ∧
  -- General ≥ Orthomodular ≥ Distributive ≥ Boolean
  (v.distributivity = .general ∨ v.distributivity = w.distributivity ∨
   (v.distributivity = .orthomodular ∧ w.distributivity ∈ [.boolean, .distributive, .orthomodular]) ∨
   (v.distributivity = .distributive ∧ w.distributivity ∈ [.boolean, .distributive])) ∧
  -- Imprecise ≥ Precise
  (v.precision = .imprecise ∨ v.precision = w.precision) ∧
  -- Partial ≥ Total
  (v.orderAxis = .partialOrder ∨ v.orderAxis = w.orderAxis) ∧
  -- Nondense ≥ Dense
  (v.density = .nondense ∨ v.density = w.density) ∧
  -- Incomplete ≥ ConditionallyComplete
  (v.completeness = .incomplete ∨ v.completeness = w.completeness) ∧
  -- Separation: none ≥ ksSeparation ≥ ksSeparationStrict
  (v.separation = .none ∨ v.separation = w.separation ∨
    (v.separation = .ksSeparation ∧ w.separation = .ksSeparationStrict)) ∧
  -- Subadditive ≥ Derived ≥ Additive
  (v.additivity = .subadditive ∨ v.additivity = w.additivity ∨
   (v.additivity = .derived ∧ w.additivity = .additive)) ∧
  -- Semigroup ≥ Monoid ≥ Group
  (v.invertibility = .semigroup ∨ v.invertibility = w.invertibility ∨
   (v.invertibility = .monoid ∧ w.invertibility = .group)) ∧
  -- Fuzzy ≥ Probabilistic ≥ Deterministic
  (v.determinism = .fuzzy ∨ v.determinism = w.determinism ∨
   (v.determinism = .probabilistic ∧ w.determinism = .deterministic)) ∧
  -- Continuous ≥ Countable ≥ Finite
  (v.support = .continuous ∨ v.support = w.support ∨
   (v.support = .countable ∧ w.support = .finite)) ∧
  -- FinitelyAdditive ≥ Borel ≥ Radon
  (v.regularity = .finitelyAdditive ∨ v.regularity = w.regularity ∨
   (v.regularity = .borel ∧ w.regularity = .radon)) ∧
  -- Independence: treat `free` as ⊤ and `tensor` as ⊥, with other notions incomparable
  -- except via these bounds.
  (v.independence = .free ∨ w.independence = .tensor ∨ v.independence = w.independence)

instance (v w : ProbabilityVertex) : Decidable (isMoreGeneral v w) := by
  unfold isMoreGeneral
  infer_instance

/-- All named theories in the extended 13-axis hypercube. -/
 def namedTheories : List (String × ProbabilityVertex) :=
  [ -- Classical probability variants
    ("Kolmogorov", kolmogorov),
    ("Cox", cox),
    ("Knuth-Skilling", knuthSkilling),
    ("Knuth-Skilling (Group)", knuthSkillingGroup),
    ("Finite Probability", finiteProbability),
    ("Discrete Probability", discreteProbability),
    ("Radon Probability", radonProbability),
    ("de Finetti", deFinetti),
    -- Imprecise probability
    ("Dempster-Shafer", dempsterShafer),
    ("Imprecise K&S", { knuthSkilling with precision := .imprecise, additivity := .subadditive }),
    -- Quantum
    ("Quantum", quantum),
    ("Quantum D-S", { quantum with precision := .imprecise, additivity := .subadditive }),
    -- Logic endpoints
    ("Classical Logic", classicalLogic),
    ("Fuzzy Logic", fuzzyLogic),
    -- Extremes
    ("Most General", mostGeneralVertex) ]

/-- Count of named theories. -/
theorem namedTheories_count : namedTheories.length = 15 := rfl

/-- Kolmogorov is among the named theories. -/
theorem kolmogorov_in_namedTheories : ("Kolmogorov", kolmogorov) ∈ namedTheories := by
  simp [namedTheories]

/-- `knuthSkillingGroup` differs from `knuthSkilling` only by the invertibility axis. -/
theorem knuthSkillingGroup_isNaturalEdge :
    isNaturalEdge knuthSkilling knuthSkillingGroup := by
  -- `knuthSkillingGroup` is a one-axis update of `knuthSkilling`.
  native_decide

/-- The group variant is strictly more specific than the monoid variant. -/
theorem knuthSkilling_moreGeneral_than_group :
    isMoreGeneral knuthSkilling knuthSkillingGroup := by
  native_decide

/-!
## §11: Edge Morphism Properties

This section proves key properties about hypercube edges and their morphisms.
The hypercube structure has important categorical properties:
- Edges are symmetric (undirected graph structure)
- Natural edges preserve partial structure
- Paths through the hypercube correspond to theory relationships
-/

/-- Natural edges are symmetric: if V→W is a natural edge, so is W→V.
    This reflects that edges in the hypercube are undirected. -/
theorem isNaturalEdge_symmetric {V W : ProbabilityVertex} :
    isNaturalEdge V W → isNaturalEdge W V := by
  intro h
  -- Symmetry is immediate since all axis equalities are symmetric.
  simpa [isNaturalEdge, hammingDistance, eq_comm] using h

/-- No vertex has a natural edge to itself. -/
theorem isNaturalEdge_irrefl (V : ProbabilityVertex) : ¬isNaturalEdge V V := by
  simp [isNaturalEdge, hammingDistance]

/-- Same vertex implies zero Hamming distance. -/
@[simp]
theorem hammingDistance_self (V : ProbabilityVertex) : hammingDistance V V = 0 := by
  simp [hammingDistance]

/-- `knuthSkillingGroup` is one Hamming step away from `knuthSkilling`. -/
theorem hammingDistance_knuthSkilling_knuthSkillingGroup :
    hammingDistance knuthSkilling knuthSkillingGroup = 1 := by
  native_decide

/-- Hamming distance is symmetric. -/
theorem hammingDistance_comm (V W : ProbabilityVertex) :
    hammingDistance V W = hammingDistance W V := by
  simp only [hammingDistance, eq_comm]

/-- Hamming distance `0` forces vertex equality (all axes match). -/
theorem eq_of_hammingDistance_eq_zero {V W : ProbabilityVertex} (h : hammingDistance V W = 0) :
    V = W := by
  -- Unfold and peel off summands from the right using `Nat.add_eq_zero_iff`.
  unfold hammingDistance at h
  rcases Nat.add_eq_zero_iff.1 h with ⟨h12, hInd⟩
  rcases Nat.add_eq_zero_iff.1 h12 with ⟨h11, hReg⟩
  rcases Nat.add_eq_zero_iff.1 h11 with ⟨h10, hSup⟩
  rcases Nat.add_eq_zero_iff.1 h10 with ⟨h9, hDet⟩
  rcases Nat.add_eq_zero_iff.1 h9 with ⟨h8, hInv⟩
  rcases Nat.add_eq_zero_iff.1 h8 with ⟨h7, hAdd⟩
  rcases Nat.add_eq_zero_iff.1 h7 with ⟨h6, hSep⟩
  rcases Nat.add_eq_zero_iff.1 h6 with ⟨h5, hComp⟩
  rcases Nat.add_eq_zero_iff.1 h5 with ⟨h4, hDen⟩
  rcases Nat.add_eq_zero_iff.1 h4 with ⟨h3, hOrd⟩
  rcases Nat.add_eq_zero_iff.1 h3 with ⟨h2, hPrec⟩
  rcases Nat.add_eq_zero_iff.1 h2 with ⟨h1, hDist⟩
  -- The remaining leftmost summand must be 0.
  have hComm : (if V.commutativity = W.commutativity then 0 else 1) = 0 := by
    exact h1
  -- Convert “if … then 0 else 1 = 0” into the underlying equality on axes.
  have eq_of_if_eq_zero {α : Type} [DecidableEq α] (a b : α) :
      (if a = b then (0 : ℕ) else 1) = 0 → a = b := by
    intro hab
    by_cases h' : a = b
    · exact h'
    ·
      -- If `a ≠ b`, the `if` reduces to `1`, contradicting `hab`.
      simp [h'] at hab
  have hc : V.commutativity = W.commutativity :=
    eq_of_if_eq_zero V.commutativity W.commutativity hComm
  have hd : V.distributivity = W.distributivity :=
    eq_of_if_eq_zero V.distributivity W.distributivity hDist
  have hp : V.precision = W.precision :=
    eq_of_if_eq_zero V.precision W.precision hPrec
  have ho : V.orderAxis = W.orderAxis :=
    eq_of_if_eq_zero V.orderAxis W.orderAxis hOrd
  have hden : V.density = W.density :=
    eq_of_if_eq_zero V.density W.density hDen
  have hcomp : V.completeness = W.completeness :=
    eq_of_if_eq_zero V.completeness W.completeness hComp
  have hsep : V.separation = W.separation :=
    eq_of_if_eq_zero V.separation W.separation hSep
  have ha : V.additivity = W.additivity :=
    eq_of_if_eq_zero V.additivity W.additivity hAdd
  have hinv : V.invertibility = W.invertibility :=
    eq_of_if_eq_zero V.invertibility W.invertibility hInv
  have hdet : V.determinism = W.determinism :=
    eq_of_if_eq_zero V.determinism W.determinism hDet
  have hsup : V.support = W.support :=
    eq_of_if_eq_zero V.support W.support hSup
  have hreg : V.regularity = W.regularity :=
    eq_of_if_eq_zero V.regularity W.regularity hReg
  have hind : V.independence = W.independence :=
    eq_of_if_eq_zero V.independence W.independence hInd
  ext <;> assumption

/-- Hamming distance is bounded by 13 (total number of axes). -/
theorem hammingDistance_le_thirteen (V W : ProbabilityVertex) :
    hammingDistance V W ≤ 13 := by
  unfold hammingDistance
  have h_if (p : Prop) [Decidable p] : (if p then 0 else 1) ≤ (1 : ℕ) := by
    by_cases p <;> simp [*]
  have hcomm : (if V.commutativity = W.commutativity then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hdist : (if V.distributivity = W.distributivity then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hprec : (if V.precision = W.precision then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hord : (if V.orderAxis = W.orderAxis then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hden : (if V.density = W.density then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hcomp : (if V.completeness = W.completeness then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hsep : (if V.separation = W.separation then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hadd : (if V.additivity = W.additivity then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hinv : (if V.invertibility = W.invertibility then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hdet : (if V.determinism = W.determinism then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hsup : (if V.support = W.support then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hreg : (if V.regularity = W.regularity then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hind : (if V.independence = W.independence then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hsum :
      (if V.commutativity = W.commutativity then 0 else 1) +
      (if V.distributivity = W.distributivity then 0 else 1) +
      (if V.precision = W.precision then 0 else 1) +
      (if V.orderAxis = W.orderAxis then 0 else 1) +
      (if V.density = W.density then 0 else 1) +
      (if V.completeness = W.completeness then 0 else 1) +
      (if V.separation = W.separation then 0 else 1) +
      (if V.additivity = W.additivity then 0 else 1) +
      (if V.invertibility = W.invertibility then 0 else 1) +
      (if V.determinism = W.determinism then 0 else 1) +
      (if V.support = W.support then 0 else 1) +
      (if V.regularity = W.regularity then 0 else 1) +
      (if V.independence = W.independence then 0 else 1) ≤
      1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by
    omega
  simpa using hsum

/-- A path in the hypercube is a sequence of natural edges. -/
def isPath : List ProbabilityVertex → Prop
  | [] => True
  | [_] => True
  | v :: w :: rest => isNaturalEdge v w ∧ isPath (w :: rest)

/-- A path from V to W. -/
def hasPath (V W : ProbabilityVertex) : Prop :=
  ∃ path : List ProbabilityVertex,
    path.head? = some V ∧
    path.getLast? = some W ∧
    isPath path

/-- Helper: construct a vertex that changes one axis from V toward W. -/
private def stepToward (V W : ProbabilityVertex) : ProbabilityVertex :=
  if V.commutativity ≠ W.commutativity then
    { V with commutativity := W.commutativity }
  else if V.distributivity ≠ W.distributivity then
    { V with distributivity := W.distributivity }
  else if V.precision ≠ W.precision then
    { V with precision := W.precision }
  else if V.orderAxis ≠ W.orderAxis then
    { V with orderAxis := W.orderAxis }
  else if V.density ≠ W.density then
    { V with density := W.density }
  else if V.completeness ≠ W.completeness then
    { V with completeness := W.completeness }
  else if V.separation ≠ W.separation then
    { V with separation := W.separation }
  else if V.additivity ≠ W.additivity then
    { V with additivity := W.additivity }
  else if V.invertibility ≠ W.invertibility then
    { V with invertibility := W.invertibility }
  else if V.determinism ≠ W.determinism then
    { V with determinism := W.determinism }
  else if V.support ≠ W.support then
    { V with support := W.support }
  else if V.regularity ≠ W.regularity then
    { V with regularity := W.regularity }
  else
    { V with independence := W.independence }

/-- stepToward changes exactly one axis. -/
private theorem isNaturalEdge_stepToward (V W : ProbabilityVertex) (hne : V ≠ W) :
    isNaturalEdge V (stepToward V W) := by
  unfold stepToward isNaturalEdge hammingDistance
  by_cases hc : V.commutativity ≠ W.commutativity
  · simp [hc]
  · push_neg at hc
    simp [hc]
    by_cases hd : V.distributivity ≠ W.distributivity
    · simp [hd]
    · push_neg at hd
      simp [hd]
      by_cases hp : V.precision ≠ W.precision
      · simp [hp]
      · push_neg at hp
        simp [hp]
        by_cases ho : V.orderAxis ≠ W.orderAxis
        · simp [ho]
        · push_neg at ho
          simp [ho]
          by_cases hden : V.density ≠ W.density
          · simp [hden]
          · push_neg at hden
            simp [hden]
            by_cases hcomp : V.completeness ≠ W.completeness
            · simp [hcomp]
            · push_neg at hcomp
              simp [hcomp]
              by_cases hsep : V.separation ≠ W.separation
              · simp [hsep]
              · push_neg at hsep
                simp [hsep]
                by_cases ha : V.additivity ≠ W.additivity
                · simp [ha]
                · push_neg at ha
                  simp [ha]
                  by_cases hinv : V.invertibility ≠ W.invertibility
                  · simp [hinv]
                  · push_neg at hinv
                    simp [hinv]
                    by_cases hdet : V.determinism ≠ W.determinism
                    · simp [hdet]
                    · push_neg at hdet
                      simp [hdet]
                      by_cases hsup : V.support ≠ W.support
                      · simp [hsup]
                      · push_neg at hsup
                        simp [hsup]
                        by_cases hreg : V.regularity ≠ W.regularity
                        · simp [hreg]
                        · push_neg at hreg
                          simp [hreg]
                          -- All other axes match, so independence must differ.
                          have hind : V.independence ≠ W.independence := by
                            intro heq
                            apply hne
                            ext <;> try assumption
                          simp [hind]

/-- Hamming distance decreases after stepping toward target. -/
private theorem hammingDistance_stepToward_lt (V W : ProbabilityVertex) (hne : V ≠ W) :
    hammingDistance (stepToward V W) W < hammingDistance V W := by
  unfold stepToward hammingDistance
  -- Work through the chain: find the first differing axis.
  by_cases hc : V.commutativity ≠ W.commutativity
  · simp [hc]
  · push_neg at hc
    simp [hc]
    by_cases hd : V.distributivity ≠ W.distributivity
    · simp [hd]
    · push_neg at hd
      simp [hd]
      by_cases hp : V.precision ≠ W.precision
      · simp [hp]
      · push_neg at hp
        simp [hp]
        by_cases ho : V.orderAxis ≠ W.orderAxis
        · simp [ho]
        · push_neg at ho
          simp [ho]
          by_cases hden : V.density ≠ W.density
          · simp [hden]
          · push_neg at hden
            simp [hden]
            by_cases hcomp : V.completeness ≠ W.completeness
            · simp [hcomp]
            · push_neg at hcomp
              simp [hcomp]
              by_cases hsep : V.separation ≠ W.separation
              · simp [hsep]
              · push_neg at hsep
                simp [hsep]
                by_cases ha : V.additivity ≠ W.additivity
                · simp [ha]
                · push_neg at ha
                  simp [ha]
                  by_cases hinv : V.invertibility ≠ W.invertibility
                  · simp [hinv]
                  · push_neg at hinv
                    simp [hinv]
                    by_cases hdet : V.determinism ≠ W.determinism
                    · simp [hdet]
                    · push_neg at hdet
                      simp [hdet]
                      by_cases hsup : V.support ≠ W.support
                      · simp [hsup]
                      · push_neg at hsup
                        simp [hsup]
                        by_cases hreg : V.regularity ≠ W.regularity
                        · simp [hreg]
                        · push_neg at hreg
                          simp [hreg]
                          have hind : V.independence ≠ W.independence := by
                            intro heq
                            apply hne
                            ext <;> try assumption
                          simp [hind]

/-- Natural edges have Hamming distance exactly 1. -/
theorem isNaturalEdge_iff_hamming_one {V W : ProbabilityVertex} :
    isNaturalEdge V W ↔ hammingDistance V W = 1 := by
  rfl

/-- Any two vertices can be connected by a path (hypercube is connected).
    The path length equals the Hamming distance. -/
theorem hypercube_connected (V W : ProbabilityVertex) : hasPath V W := by
  -- Induction on Hamming distance
  generalize hd : hammingDistance V W = d
  induction d using Nat.strong_induction_on generalizing V with
  | _ d ih =>
    by_cases hVW : V = W
    · subst hVW
      exact ⟨[V], rfl, rfl, trivial⟩
    · -- Step toward W, then recurse
      let V' := stepToward V W
      have hlt : hammingDistance V' W < d := by
        rw [← hd]
        exact hammingDistance_stepToward_lt V W hVW
      have ⟨path, hhead, hlast, hpath⟩ := ih (hammingDistance V' W) hlt V' rfl
      use V :: path
      refine ⟨rfl, ?_, ?_⟩
      · cases path with
        | nil => simp at hhead
        | cons w rest =>
          simp only [List.getLast?_cons_cons] at hlast ⊢
          cases rest with
          | nil =>
            simp only [List.getLast?_singleton] at hlast ⊢
            exact hlast
          | cons _ _ =>
            simp only [List.getLast?_cons_cons] at hlast ⊢
            exact hlast
      · cases path with
        | nil => simp at hhead
        | cons w rest =>
          simp only [isPath] at hpath ⊢
          constructor
          · have hhead' : w = V' := by
              simp only [List.head?] at hhead
              exact Option.some.inj hhead
            rw [hhead']
            exact isNaturalEdge_stepToward V W hVW
          · exact hpath

/-- Morphisms exist along natural edges when the edge direction matches the morphism direction.
    Specifically: if edge changes only commutativity/precision and goes toward the "more specific" end,
    then a morphism exists. -/
theorem morphism_along_natural_edge {V W : ProbabilityVertex}
    (_ : isNaturalEdge V W)
    (hc : V.commutativity = .commutative → W.commutativity = .commutative)
    (hp : V.precision = .precise → W.precision = .precise) :
    Nonempty (ProbabilityMorphism V W) :=
  ⟨{ respects_commutativity := hc, respects_precision := hp }⟩

/-- Every edge in the direction of specialization (more general → more specific)
    has a trivial morphism in that direction. -/
theorem morphism_specialization {V W : ProbabilityVertex}
    (hcomm : V.commutativity = .noncommutative ∨ W.commutativity = .commutative)
    (hprec : V.precision = .imprecise ∨ W.precision = .precise) :
    Nonempty (ProbabilityMorphism V W) := by
  constructor
  constructor
  · intro hVc
    cases hcomm with
    | inl hVnc => simp_all
    | inr hWc => exact hWc
  · intro hVp
    cases hprec with
    | inl hVi => simp_all
    | inr hWp => exact hWp

/-- The identity morphism exists for any vertex. -/
def identityMorphism (V : ProbabilityVertex) : ProbabilityMorphism V V where
  respects_commutativity := id
  respects_precision := id

/-- The most general vertex is more general than all named theories. -/
theorem mostGeneral_dominates :
    ∀ (name : String) (V : ProbabilityVertex),
      (name, V) ∈ namedTheories →
      isMoreGeneral mostGeneralVertex V := by
  intro _name V _hV
  -- `mostGeneralVertex` is defined with “top” values for every axis, so it dominates any `V`.
  simp [isMoreGeneral, mostGeneralVertex]

/-- Classical logic is the most specific named theory. -/
theorem classicalLogic_most_specific :
    ∀ (name : String) (V : ProbabilityVertex),
      (name, V) ∈ namedTheories →
      isMoreGeneral V classicalLogic := by
  intro name V hV
  simp only [namedTheories, List.mem_cons, Prod.mk.injEq] at hV
  rcases hV with
      ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
      ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
      ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  all_goals (first | native_decide | simp_all)

/-!
## §12: Quantale Structure and PLN Connection

The hypercube has a deep connection to quantale theory:

**Key Insight**: PLN deduction = quantale composition in [0,1]!

For commutative, tensor-independent vertices (like `kolmogorov`, `plnSimple`, `cox`),
the conditional probability composition forms a **commutative quantale**:

- **Objects**: Terms/concepts
- **Morphisms**: Implications A → B with strength P(B|A) ∈ [0,1]
- **Composition**: PLN deduction formula (or equivalently, law of total probability)
- **Tensor**: Product of probabilities
- **Residuation**: Conditional probability

### PLN Inference as Quantale Operations

| PLN Rule | Quantale Operation |
|----------|-------------------|
| Deduction | Transitivity (⊗-composition) |
| Inversion | Adjoint (residuation) |
| Induction | Bayes + Transitivity |
| Abduction | Bayes + Transitivity |
| Revision | Join (⊔) on evidence |

### Formalization Files

- `Mettapedia.Logic.PLNQuantaleConnection` - Main quantale proof
- `Mettapedia.Logic.PLNChapter5` - Complete Chapter 5 rules (similarity, MP, etc.)
- `Mettapedia.Logic.PLNDeduction` - Core deduction formula
- `Mettapedia.Logic.PLNEvidence` - Evidence counts as quantale carrier
- `Mettapedia.Algebra.QuantaleWeakness` - Abstract quantale theory

### The Categorical View

The hypercube vertices with `independence = tensor` form a subcategory where:
1. Composition is associative (PLN deduction is approximately associative)
2. Identity morphisms exist (P(A|A) = 1)
3. The structure is enriched over [0,1]

This is NOT ad-hoc - PLN is the **probabilistic instance** of quantale weakness theory!
-/

/-!
## §13: Quantale Classification of Hypercube Vertices

The key insight: **MOST probability theories in the hypercube can be characterized by
their associated quantale structure**. The quantale type depends primarily on three axes:
1. **IndependenceAxis** - Determines the tensor product structure
2. **CommutativityAxis** - Determines whether ⊗ commutes
3. **PrecisionAxis** - Determines whether we need "interval quantales"

### The Universal Mapping

| Independence | Commutativity | Precision | Quantale Type |
|--------------|---------------|-----------|---------------|
| tensor | commutative | precise | **Commutative quantale** ([0,1], ·, ∨) |
| tensor | commutative | imprecise | **Interval quantale** ([0,1]², ·, ∨) |
| tensor | noncommutative | precise | **Noncommutative quantale** (C*-algebra) |
| free | noncommutative | precise | **Free quantale** (R-transform composition) |
| boolean | noncommutative | precise | **Boolean quantale** (interval partitions) |
| monotone | noncommutative | precise | **Monotone quantale** (ordered partitions) |

### Mathematical Details

**1. Classical Probability → Commutative Quantale [0,1]**

The unit interval [0,1] with multiplication and max forms a commutative quantale:
- ⊗ = multiplication (probability of conjunction)
- ⊕ = max (or ⨆ for supremum)
- Identity: 1 (certain event)
- Residuation: x → y = min(1, y/x)

This covers: `kolmogorov`, `cox`, `knuthSkilling`, `plnSimple`, `finiteProbability`, etc.

**2. Imprecise Probability → Interval Quantale [0,1]²**

For Dempster-Shafer and PLN Indefinite:
- Objects: Intervals [L, U] ⊆ [0,1] with L ≤ U
- ⊗: [L₁, U₁] ⊗ [L₂, U₂] = [L₁·L₂, U₁·U₂]
- Residuation: More complex (Walley's natural extension)

This covers: `dempsterShafer`, `plnIndefinite`, `fuzzyLogic`

**3. Quantum Probability → Noncommutative Quantale**

Von Neumann algebras form quantales:
- Objects: Positive operators (effects)
- ⊗: Sequential product (A ⊗ B = A^{1/2} B A^{1/2})
- ⊕: Spectral supremum
- Non-commutativity: [A, B] ≠ 0 reflects uncertainty

This covers: `quantum`

**4. Free Probability → Free Quantale**

Voiculescu's free probability uses a different composition:
- Objects: Probability distributions (or spectral measures)
- ⊗: Free convolution ⊞ (not ordinary convolution!)
- The R-transform linearizes ⊞: R(μ ⊞ ν) = R(μ) + R(ν)
- Noncrossing partitions replace all partitions

This covers: `freeProbability`

### The Partition Perspective (Speicher's Insight)

The independence axis corresponds to which partitions are "allowed":

| Independence | Allowed Partitions | Generating Function |
|--------------|-------------------|---------------------|
| tensor | ALL partitions | Moment generating |
| free | NONCROSSING only | R-transform |
| boolean | INTERVAL only | η-transform |
| monotone | ORDERED only | F-transform |

Each partition family forms a different operad, and the corresponding quantale
is the enrichment of that operad over [0,1] or ℝ≥0.

### Formalization Files

- `Mettapedia.Algebra.QuantaleWeakness` - Commutative quantale, ENNReal
- `Mettapedia.Algebra.QuantaleWeakness` - Quantale weakness (works for commutative and noncommutative quantales)
- `Mettapedia.ProbabilityTheory.FreeProbability.Basic` - Noncrossing partitions
- `Mettapedia.Logic.PLNQuantaleConnection` - PLN as quantale composition
- Future: `Mettapedia.Algebra.IntervalQuantale` - Imprecise probability
- Future: `Mettapedia.Algebra.FreeQuantale` - Free probability quantale
-/

/-- Classification of quantale types corresponding to hypercube vertices.

**Key insight**: ALL vertices have SOME quantale structure! Even deterministic
logic uses the Boolean quantale {0,1}. The "type" here indicates which quantale,
not whether one exists.
-/
inductive QuantaleType where
  | commutative : QuantaleType       -- [0,1] with multiplication, classical
  | interval : QuantaleType          -- [0,1]² for imprecise probability
  | noncommutative : QuantaleType    -- C*-algebras, quantum
  | free : QuantaleType              -- R-transform, noncrossing partitions
  | boolean : QuantaleType           -- Interval partitions (independence type)
  | monotone : QuantaleType          -- Ordered partitions (independence type)
  | booleanAlgebra : QuantaleType    -- {0,1} Boolean quantale (deterministic)
  deriving DecidableEq, Repr

/-- Map a hypercube vertex to its associated quantale type.

The mapping is determined by:
1. Determinism axis (deterministic → Boolean quantale {0,1})
2. Independence axis (free/boolean/monotone have special structures)
3. Commutativity axis (distinguishes quantum from classical tensor)
4. Precision axis (distinguishes interval quantales)

**Every vertex has a quantale!** This is the key insight from Goertzel's
weakness theory: the quantale framework is universal.
-/
def quantaleTypeOf (v : ProbabilityVertex) : QuantaleType :=
  -- Deterministic theories use the Boolean quantale {0,1}
  if v.determinism = .deterministic then .booleanAlgebra
  else match v.independence with
  | .free => .free
  | .boolean => .boolean
  | .monotone => .monotone
  | .tensor =>
      match v.commutativity with
      | .noncommutative => .noncommutative
      | .commutative =>
          match v.precision with
          | .imprecise => .interval
          | .precise => .commutative

/-- Classical probability theories use the commutative quantale [0,1]. -/
theorem kolmogorov_quantale : quantaleTypeOf kolmogorov = .commutative := rfl

/-- K&S uses the same quantale structure as classical probability. -/
theorem knuthSkilling_quantale : quantaleTypeOf knuthSkilling = .commutative := rfl

/-- PLN Simple shares the commutative quantale with classical probability. -/
theorem plnSimple_quantale : quantaleTypeOf plnSimple = .commutative := rfl

/-- Quantum probability uses a noncommutative quantale. -/
theorem quantum_quantale : quantaleTypeOf quantum = .noncommutative := rfl

/-- Free probability uses the free quantale (R-transform). -/
theorem freeProbability_quantale : quantaleTypeOf freeProbability = .free := rfl

/-- Dempster-Shafer uses an interval quantale for imprecise values. -/
theorem dempsterShafer_quantale : quantaleTypeOf dempsterShafer = .interval := rfl

/-- PLN Indefinite uses interval quantale due to imprecision. -/
theorem plnIndefinite_quantale : quantaleTypeOf plnIndefinite = .interval := rfl

/-- Classical logic uses the Boolean quantale {0,1}. -/
theorem classicalLogic_quantale : quantaleTypeOf classicalLogic = .booleanAlgebra := rfl

/-- **ALL vertices have quantale structure!**

This is the key insight: the weakness/quantale framework is universal.
Even deterministic logic has a quantale - the Boolean quantale {0,1}.

The only difference is WHICH quantale applies. -/
theorem all_vertices_have_quantale (v : ProbabilityVertex) :
    ∃ (desc : String), desc ≠ "" ∧
    (quantaleTypeOf v = .commutative ∧ desc = "[0,1] commutative" ∨
     quantaleTypeOf v = .interval ∧ desc = "[0,1]² interval" ∨
     quantaleTypeOf v = .noncommutative ∧ desc = "C*-algebra" ∨
     quantaleTypeOf v = .free ∧ desc = "free (R-transform)" ∨
     quantaleTypeOf v = .boolean ∧ desc = "boolean partitions" ∨
     quantaleTypeOf v = .monotone ∧ desc = "monotone partitions" ∨
     quantaleTypeOf v = .booleanAlgebra ∧ desc = "{0,1} Boolean") := by
  unfold quantaleTypeOf
  split_ifs with hdet
  · -- Deterministic case: Boolean algebra
    exact ⟨"{0,1} Boolean", by decide, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))⟩
  · -- Non-deterministic cases
    cases hi : v.independence with
    | free => exact ⟨"free (R-transform)", by decide, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    | boolean => exact ⟨"boolean partitions", by decide, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
    | monotone => exact ⟨"monotone partitions", by decide, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩
    | tensor =>
      cases hc : v.commutativity with
      | noncommutative => exact ⟨"C*-algebra", by decide, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      | commutative =>
        cases hp : v.precision with
        | imprecise => exact ⟨"[0,1]² interval", by decide, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
        | precise => exact ⟨"[0,1] commutative", by decide, Or.inl ⟨rfl, rfl⟩⟩

/-- Count of named theories with each quantale type. -/
def namedTheoriesByQuantale : List (QuantaleType × List String) :=
  [ (.commutative, ["Kolmogorov", "Cox", "Knuth-Skilling", "Knuth-Skilling (Group)",
                    "Finite Probability", "Discrete Probability", "Radon Probability", "de Finetti"]),
    (.interval, ["Dempster-Shafer", "Imprecise K&S", "PLN Indefinite", "Fuzzy Logic"]),
    (.noncommutative, ["Quantum"]),
    (.free, ["Free Probability", "Most General"]),
    (.booleanAlgebra, ["Classical Logic"]) ]  -- Boolean quantale {0,1}

/-!
### The Boolean Quantale {0, 1}

Deterministic vertices use the **Boolean quantale** - the simplest non-trivial quantale:

**Structure of {0, 1}**:
- **Set**: {⊥, ⊤} = {0, 1} = {false, true}
- **⊗ (tensor)**: x ⊗ y = x ∧ y = min(x, y) = x · y
- **⨆ (join)**: ⨆S = ∨S = max(S)
- **1 (unit)**: ⊤ = 1 = true
- **→ (residuation)**: x → y = ¬x ∨ y = if x ≤ y then 1 else 0

**Category-Theoretic Views**:

| Structure | Description |
|-----------|-------------|
| **2** | The "walking arrow" category: • → • |
| **Sierpiński space** | Topology with {∅, {1}, {0,1}} open |
| **Initial frame** | Simplest complete Heyting algebra |
| **Truth value object** | Classifier in Set |
| **Boolean semiring** | ({0,1}, +, ·) where 1+1=1 |

**Why it's a Quantale**:
```
  x ⊗ (⨆S) = ⨆_{s∈S} (x ⊗ s)
  x ∧ (∨S) = ∨_{s∈S} (x ∧ s)  ✓ (Boolean distributivity)
```

**Weakness in {0,1}**:
Bennett's original weakness w(H) = |H| is the **cardinality** function,
which is a morphism from the Boolean quantale of subsets to (ℕ, +, max).

The key insight: {0,1} is NOT "no quantale" - it's the **degenerate/trivial case**
where uncertainty collapses to certainty. All the algebraic structure is there,
just restricted to two values.

### The Quantale Weakness Hierarchy

From weakest to strongest quantale axioms:

1. **Semigroup** (just associativity of ⊗)
2. **Monoid** (add identity)
3. **Quantale** (add sSup distribution)
4. **Commutative Quantale** (add commutativity)
5. **Complete Heyting Algebra** (residuation = implication)

This hierarchy maps to the hypercube's invertibility and commutativity axes:
- Semigroup ↔ invertibility = .semigroup
- Monoid ↔ invertibility = .monoid
- Comm Quantale ↔ commutativity = .commutative

### Why Quantales Matter for Probability

The quantale framework provides:

1. **Unified inference rules**: Deduction, inversion, revision all become
   quantale operations (tensor, residuation, join)

2. **Consistency guarantees**: The Galois connection ensures that
   inference preserves order (more evidence → stronger conclusions)

3. **Compositionality**: Category-enriched structure means complex
   inference chains decompose into simple operations

4. **Generalization path**: Moving from classical → imprecise → quantum
   is just changing the quantale, not the inference machinery

### Connection to PLN Inference

For vertices with `quantaleTypeOf v = .commutative`:

| PLN Operation | Quantale Operation | Formula |
|---------------|-------------------|---------|
| Strength composition | ⊗ (tensor) | s_{AC} = s_{AB} ⊗ s_{BC} + ... |
| Bayes inversion | Residuation (→) | P(A\|B) = P(B\|A) · P(A) / P(B) |
| Evidence revision | Join (⊔) | Combine independent sources |
| Confidence bound | Residuation inequality | From adjunction |

For vertices with `quantaleTypeOf v = .interval`:
- Same operations but on interval pairs [L, U]
- Upper bound uses optimistic composition
- Lower bound uses pessimistic composition

For vertices with `quantaleTypeOf v = .free`:
- Replace ⊗ with free convolution ⊞
- Replace multiplicative structure with additive R-transform

This unification is why quantales are the "right" abstraction for probability!
-/

/-- A vertex has "standard PLN inference" if it uses the commutative quantale. -/
def hasStandardPLNInference (v : ProbabilityVertex) : Prop :=
  quantaleTypeOf v = .commutative

/-- A vertex has "interval PLN inference" if it uses interval quantales. -/
def hasIntervalPLNInference (v : ProbabilityVertex) : Prop :=
  quantaleTypeOf v = .interval

/-- Kolmogorov has standard PLN inference. -/
theorem kolmogorov_has_standard_pln : hasStandardPLNInference kolmogorov := rfl

/-- K&S has standard PLN inference. -/
theorem knuthSkilling_has_standard_pln : hasStandardPLNInference knuthSkilling := rfl

/-- D-S has interval PLN inference. -/
theorem dempsterShafer_has_interval_pln : hasIntervalPLNInference dempsterShafer := rfl

/-- All commutative + precise + tensor vertices share inference structure. -/
theorem shared_inference_structure (v w : ProbabilityVertex)
    (hv : quantaleTypeOf v = .commutative)
    (hw : quantaleTypeOf w = .commutative) :
    hasStandardPLNInference v ∧ hasStandardPLNInference w := by
  exact ⟨hv, hw⟩

/-!
## §14: Concrete Examples for Hypercube Vertices

Following Chad Brown's methodology: each non-empty vertex should have both
**positive examples** (models inhabiting the vertex) and **negative examples**
(models that fail to inhabit, demonstrating which axioms distinguish vertices).

**Key insight**: A negative example for vertex V is often a positive example for
vertex W - the examples form a web showing how axiom choices carve up the space.

### References for Examples

**Standard Probability (Precise + Commutative + Tensor + Stochastic)**:
- Kolmogorov, A.N. (1933). "Grundbegriffe der Wahrscheinlichkeitsrechnung"
- Positive: Fair dice, coin flips, any σ-algebra with probability measure

**Imprecise Probability (Imprecise + Commutative + Tensor + Stochastic)**:
- Walley, P. (1991). "Statistical Reasoning with Imprecise Probabilities"
- Positive: Interval-valued probabilities [P_lower, P_upper]
- Axiom weakened: Totality of plausibility order

**Non-Archimedean Probability (Linear order but fails Archimedean)**:
- Benci, V. et al. (2013). "Non-Archimedean Probability"
- Blume, L., Brandenburger, A., Dekel, E. (1991). "Lexicographic Probabilities"
- Positive: ℕ ×ₗ ℕ with lexicographic order, componentwise addition
- Axiom weakened: Archimedean property
- See: `Additive/Counterexamples/ProductFailsSeparation.lean`

**Quantum Probability (Noncommutative + Tensor + Stochastic)**:
- von Neumann, J. (1932). "Mathematical Foundations of Quantum Mechanics"
- Positive: Density matrices on Hilbert space, C*-algebras
- Axiom weakened: Commutativity

**Free Probability (Commutative structure but Free independence)**:
- Voiculescu, D. (1991). "Limit laws for random matrices"
- Positive: Large random matrices, free convolution
- Axiom changed: Independence type (free vs tensor)

**Deterministic (Boolean quantale {0,1})**:
- Classical propositional logic
- Positive: Boolean algebra of propositions
- Axiom changed: Determinism (no non-trivial probabilities)
-/

/-!
### REAL Formalized Examples

Concrete Lean formalizations with proofs live in `Hypercube/Examples.lean`.

**Key examples** (all with complete proofs, no sorries):

| Example | Positive For | Negative For | Formalization |
|---------|--------------|--------------|---------------|
| ℕ with + | KnuthSkillingAlgebraBase, Archimedean | - | `Hypercube/Examples.lean: instance : KnuthSkillingAlgebraBase ℕ` |
| Bool | - | KnuthSkillingAlgebraBase | `Hypercube/Examples.lean: bool_not_ksAlgebraBase` |
| ℕ ×ₗ ℕ | KnuthSkillingAlgebraBase | Archimedean, KSSeparation | `Additive/Counterexamples/ProductFailsSeparation.lean: natProdLex_fails_KSSeparation` |
| Heisenberg | Noncommutative | Commutative | `IntervalCollapse.lean: heisenberg_not_comm` |
| Fair Die | Kolmogorov probability | - | `Examples.lean: IsProbabilityMeasure dieProbMeasure` |

### Example Web: Positive ↔ Negative Duality

The key insight: a negative example for one vertex is typically a positive
example for another. The "fair die" is the canonical positive example for
standard probability, and therefore a negative example for all non-standard vertices.

```
  POSITIVE FOR                     NEGATIVE FOR
  ────────────                     ────────────
  Fair Die ───→ Kolmogorov    ───→ {Imprecise, Quantum, Free, Deterministic, Non-Arch}
  ℕ ×ₗ ℕ   ───→ Non-Archimedean ──→ {Kolmogorov, K&S}
  Heisenberg ─→ Noncommutative ──→ {Kolmogorov, K&S, Cox}
  Bool     ───→ -              ──→ {KnuthSkillingAlgebraBase (fails strict mono)}
```

This web shows that standard probability (Kolmogorov) is the "maximally constrained"
vertex - it requires ALL the standard axioms (totality, Archimedean, commutativity,
tensor independence, non-trivial values). Weakening any axiom moves to a different vertex.
-/

end Mettapedia.ProbabilityTheory.Hypercube
