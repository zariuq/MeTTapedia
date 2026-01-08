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

A vertex in the hypercube specifies choices along all 10 axes.
With 10 axes (some with 2-4 values), we have thousands of potential vertices,
though many combinations don't correspond to meaningful probability theories.

The NEW IndependenceAxis captures the fundamental distinction between:
- Classical probability (tensor independence)
- Free probability (free independence) - key for random matrix theory & ML!
- Other noncommutative independences (boolean, monotone)
-/

/-- A vertex in the probability hypercube: a specific probability theory.
    The 10 axes capture fundamental choices in the foundations of probability. -/
@[ext]
structure ProbabilityVertex where
  commutativity : CommutativityAxis
  distributivity : DistributivityAxis
  precision : PrecisionAxis
  orderAxis : OrderAxis
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
  additivity := .derived         -- Derived from functional equations
  invertibility := .monoid
  determinism := .probabilistic
  support := .continuous
  regularity := .borel
  independence := .tensor

/-- Knuth-Skilling probability theory. -/
def knuthSkilling : ProbabilityVertex where
  commutativity := .commutative  -- K&S target; Goertzel v4 assumes, v5 aims to derive from KSSeparation
  distributivity := .distributive -- Distributive lattice (not Boolean)
  precision := .precise          -- Derives standard probability
  orderAxis := .totalOrder       -- CRITICAL: LinearOrder required
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

/-- Knuth–Skilling with commutativity taken as an explicit axiom (Goertzel v4).

This is the same semantic vertex as `knuthSkilling`; the distinction is *proof-theoretic*:
v4 explicitly strengthens the axiom package to avoid the `NewAtomCommutes` blocker. -/
def knuthSkillingV4 : ProbabilityVertex :=
  knuthSkilling

/-- Knuth–Skilling with `KSSeparation` as the “single strengthening” (Goertzel v5).

This is again the same semantic vertex as `knuthSkilling`; the distinction is *proof-theoretic*:
v5 proposes deriving commutativity from the separation/density axiom. -/
def knuthSkillingV5 : ProbabilityVertex :=
  knuthSkilling

/-- Dempster-Shafer belief functions. -/
def dempsterShafer : ProbabilityVertex where
  commutativity := .commutative   -- Set operations commute
  distributivity := .boolean      -- Power set is Boolean
  precision := .imprecise         -- Bel(A) + Bel(¬A) ≤ 1
  orderAxis := .partialOrder      -- Bel only induces partial order
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
  additivity := .additive          -- Additive on spectral projections
  invertibility := .monoid
  determinism := .probabilistic
  support := .continuous           -- Continuous spectra
  regularity := .borel
  independence := .free            -- FREE independence! Noncrossing partitions

/-- Classical propositional logic: deterministic, no uncertainty.
    This is the most specific vertex in the hypercube. -/
def classicalLogic : ProbabilityVertex where
  commutativity := .commutative
  distributivity := .boolean
  precision := .precise
  orderAxis := .totalOrder
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
  additivity := .additive
  invertibility := .monoid
  determinism := .probabilistic
  support := .continuous
  regularity := .radon            -- Inner regular, tight
  independence := .tensor

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
  deriving DecidableEq, Repr

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

/-- An edge is natural if it represents adding structure (specialization)
    or removing structure (generalization). Exactly one of the 10 axes differs. -/
def isNaturalEdge (V W : ProbabilityVertex) : Prop :=
  -- Exactly one axis differs (Hamming distance 1)
  (V.commutativity ≠ W.commutativity ∧ V.distributivity = W.distributivity ∧
   V.precision = W.precision ∧ V.orderAxis = W.orderAxis ∧ V.additivity = W.additivity ∧
   V.invertibility = W.invertibility ∧ V.determinism = W.determinism ∧ V.support = W.support ∧
   V.regularity = W.regularity ∧ V.independence = W.independence) ∨
  (V.commutativity = W.commutativity ∧ V.distributivity ≠ W.distributivity ∧
   V.precision = W.precision ∧ V.orderAxis = W.orderAxis ∧ V.additivity = W.additivity ∧
   V.invertibility = W.invertibility ∧ V.determinism = W.determinism ∧ V.support = W.support ∧
   V.regularity = W.regularity ∧ V.independence = W.independence) ∨
  (V.commutativity = W.commutativity ∧ V.distributivity = W.distributivity ∧
   V.precision ≠ W.precision ∧ V.orderAxis = W.orderAxis ∧ V.additivity = W.additivity ∧
   V.invertibility = W.invertibility ∧ V.determinism = W.determinism ∧ V.support = W.support ∧
   V.regularity = W.regularity ∧ V.independence = W.independence) ∨
  (V.commutativity = W.commutativity ∧ V.distributivity = W.distributivity ∧
   V.precision = W.precision ∧ V.orderAxis ≠ W.orderAxis ∧ V.additivity = W.additivity ∧
   V.invertibility = W.invertibility ∧ V.determinism = W.determinism ∧ V.support = W.support ∧
   V.regularity = W.regularity ∧ V.independence = W.independence) ∨
  (V.commutativity = W.commutativity ∧ V.distributivity = W.distributivity ∧
   V.precision = W.precision ∧ V.orderAxis = W.orderAxis ∧ V.additivity ≠ W.additivity ∧
   V.invertibility = W.invertibility ∧ V.determinism = W.determinism ∧ V.support = W.support ∧
   V.regularity = W.regularity ∧ V.independence = W.independence) ∨
  (V.commutativity = W.commutativity ∧ V.distributivity = W.distributivity ∧
   V.precision = W.precision ∧ V.orderAxis = W.orderAxis ∧ V.additivity = W.additivity ∧
   V.invertibility ≠ W.invertibility ∧ V.determinism = W.determinism ∧ V.support = W.support ∧
   V.regularity = W.regularity ∧ V.independence = W.independence) ∨
  (V.commutativity = W.commutativity ∧ V.distributivity = W.distributivity ∧
   V.precision = W.precision ∧ V.orderAxis = W.orderAxis ∧ V.additivity = W.additivity ∧
   V.invertibility = W.invertibility ∧ V.determinism ≠ W.determinism ∧ V.support = W.support ∧
   V.regularity = W.regularity ∧ V.independence = W.independence) ∨
  (V.commutativity = W.commutativity ∧ V.distributivity = W.distributivity ∧
   V.precision = W.precision ∧ V.orderAxis = W.orderAxis ∧ V.additivity = W.additivity ∧
   V.invertibility = W.invertibility ∧ V.determinism = W.determinism ∧ V.support ≠ W.support ∧
   V.regularity = W.regularity ∧ V.independence = W.independence) ∨
  (V.commutativity = W.commutativity ∧ V.distributivity = W.distributivity ∧
   V.precision = W.precision ∧ V.orderAxis = W.orderAxis ∧ V.additivity = W.additivity ∧
   V.invertibility = W.invertibility ∧ V.determinism = W.determinism ∧ V.support = W.support ∧
   V.regularity ≠ W.regularity ∧ V.independence = W.independence) ∨
  (V.commutativity = W.commutativity ∧ V.distributivity = W.distributivity ∧
   V.precision = W.precision ∧ V.orderAxis = W.orderAxis ∧ V.additivity = W.additivity ∧
   V.invertibility = W.invertibility ∧ V.determinism = W.determinism ∧ V.support = W.support ∧
   V.regularity = W.regularity ∧ V.independence ≠ W.independence)

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

This file uses 10 axes. With axis sizes `2 * 4 * 2 * 2 * 3 * 3 * 3 * 3 * 3 * 4`, this is
`31104` possible vertices, though many combinations won't correspond to coherent
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

/-- The most general vertex: maximally permissive on all 10 axes. -/
def mostGeneralVertex : ProbabilityVertex where
  commutativity := .noncommutative
  distributivity := .general
  precision := .imprecise
  orderAxis := .partialOrder
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

/-- All named theories in the extended 10-axis hypercube. -/
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
  -- Use the “invertibility differs” disjunct.
  unfold isNaturalEdge knuthSkillingGroup
  right; right; right; right; right; left
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  decide

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
  unfold isNaturalEdge at h ⊢
  -- Each disjunct swaps V and W with symmetric equalities
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  all_goals (
    first
    | left; obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h1
      exact ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm, g.symm, h.symm, i.symm, j.symm⟩
    | right; left; obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h2
      exact ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm, g.symm, h.symm, i.symm, j.symm⟩
    | right; right; left; obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h3
      exact ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm, g.symm, h.symm, i.symm, j.symm⟩
    | right; right; right; left; obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h4
      exact ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm, g.symm, h.symm, i.symm, j.symm⟩
    | right; right; right; right; left; obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h5
      exact ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm, g.symm, h.symm, i.symm, j.symm⟩
    | right; right; right; right; right; left; obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h6
      exact ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm, g.symm, h.symm, i.symm, j.symm⟩
    | right; right; right; right; right; right; left; obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h7
      exact ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm, g.symm, h.symm, i.symm, j.symm⟩
    | right; right; right; right; right; right; right; left; obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h8
      exact ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm, g.symm, h.symm, i.symm, j.symm⟩
    | right; right; right; right; right; right; right; right; left; obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h9
      exact ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm, g.symm, h.symm, i.symm, j.symm⟩
    | right; right; right; right; right; right; right; right; right; obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h10
      exact ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm, g.symm, h.symm, i.symm, j.symm⟩
  )

/-- No vertex has a natural edge to itself. -/
theorem isNaturalEdge_irrefl (V : ProbabilityVertex) : ¬isNaturalEdge V V := by
  intro h
  unfold isNaturalEdge at h
  rcases h with ⟨hne, _⟩ | ⟨_, hne, _⟩ | ⟨_, _, hne, _⟩ | ⟨_, _, _, hne, _⟩ |
               ⟨_, _, _, _, hne, _⟩ | ⟨_, _, _, _, _, hne, _⟩ | ⟨_, _, _, _, _, _, hne, _⟩ |
               ⟨_, _, _, _, _, _, _, hne, _⟩ | ⟨_, _, _, _, _, _, _, _, hne, _⟩ |
               ⟨_, _, _, _, _, _, _, _, _, hne⟩
  all_goals exact hne rfl

/-- Hamming distance between two vertices (number of differing axes). -/
def hammingDistance (V W : ProbabilityVertex) : ℕ :=
  (if V.commutativity = W.commutativity then 0 else 1) +
  (if V.distributivity = W.distributivity then 0 else 1) +
  (if V.precision = W.precision then 0 else 1) +
  (if V.orderAxis = W.orderAxis then 0 else 1) +
  (if V.additivity = W.additivity then 0 else 1) +
  (if V.invertibility = W.invertibility then 0 else 1) +
  (if V.determinism = W.determinism then 0 else 1) +
  (if V.support = W.support then 0 else 1) +
  (if V.regularity = W.regularity then 0 else 1) +
  (if V.independence = W.independence then 0 else 1)

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
  rcases Nat.add_eq_zero_iff.1 h with ⟨h9, hInd⟩
  rcases Nat.add_eq_zero_iff.1 h9 with ⟨h8, hReg⟩
  rcases Nat.add_eq_zero_iff.1 h8 with ⟨h7, hSup⟩
  rcases Nat.add_eq_zero_iff.1 h7 with ⟨h6, hDet⟩
  rcases Nat.add_eq_zero_iff.1 h6 with ⟨h5, hInv⟩
  rcases Nat.add_eq_zero_iff.1 h5 with ⟨h4, hAdd⟩
  rcases Nat.add_eq_zero_iff.1 h4 with ⟨h3, hOrd⟩
  rcases Nat.add_eq_zero_iff.1 h3 with ⟨h2, hPrec⟩
  rcases Nat.add_eq_zero_iff.1 h2 with ⟨h1, hDist⟩
  -- The remaining leftmost summand must be 0.
  have hComm : (if V.commutativity = W.commutativity then 0 else 1) = 0 := by
    simpa using h1
  -- Convert “if … then 0 else 1 = 0” into the underlying equality on axes.
  have eq_of_if_eq_zero {α : Type} [DecidableEq α] (a b : α) :
      (if a = b then (0 : ℕ) else 1) = 0 → a = b := by
    intro hab
    by_cases h' : a = b
    · exact h'
    ·
      -- If `a ≠ b`, the `if` reduces to `1`, contradicting `hab`.
      have : (1 : ℕ) = 0 := by
        simpa [h'] using hab
      exact False.elim (Nat.one_ne_zero this)
  have hc : V.commutativity = W.commutativity :=
    eq_of_if_eq_zero V.commutativity W.commutativity hComm
  have hd : V.distributivity = W.distributivity :=
    eq_of_if_eq_zero V.distributivity W.distributivity hDist
  have hp : V.precision = W.precision :=
    eq_of_if_eq_zero V.precision W.precision hPrec
  have ho : V.orderAxis = W.orderAxis :=
    eq_of_if_eq_zero V.orderAxis W.orderAxis hOrd
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

/-- Hamming distance is bounded by 10 (total number of axes). -/
theorem hammingDistance_le_ten (V W : ProbabilityVertex) :
    hammingDistance V W ≤ 10 := by
  unfold hammingDistance
  have h_if (p : Prop) [Decidable p] : (if p then 0 else 1) ≤ (1 : ℕ) := by
    by_cases p <;> simp [*]
  have hcomm : (if V.commutativity = W.commutativity then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hdist : (if V.distributivity = W.distributivity then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hprec : (if V.precision = W.precision then 0 else 1) ≤ (1 : ℕ) := h_if _
  have hord : (if V.orderAxis = W.orderAxis then 0 else 1) ≤ (1 : ℕ) := h_if _
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
      (if V.additivity = W.additivity then 0 else 1) +
      (if V.invertibility = W.invertibility then 0 else 1) +
      (if V.determinism = W.determinism then 0 else 1) +
      (if V.support = W.support then 0 else 1) +
      (if V.regularity = W.regularity then 0 else 1) +
      (if V.independence = W.independence then 0 else 1) ≤
      1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by
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
  unfold stepToward isNaturalEdge
  by_cases hc : V.commutativity ≠ W.commutativity
  · simp only [hc, ne_eq]; left; exact ⟨hc, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · push_neg at hc
    simp only [hc, ne_eq]
    by_cases hd : V.distributivity ≠ W.distributivity
    · simp only [hd]; right; left; exact ⟨rfl, hd, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · push_neg at hd
      simp only [hd]
      by_cases hp : V.precision ≠ W.precision
      · simp only [hp]; right; right; left; exact ⟨rfl, rfl, hp, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · push_neg at hp
        simp only [hp]
        by_cases ho : V.orderAxis ≠ W.orderAxis
        · simp only [ho]; right; right; right; left; exact ⟨rfl, rfl, rfl, ho, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · push_neg at ho
          simp only [ho]
          by_cases ha : V.additivity ≠ W.additivity
          · simp only [ha]; right; right; right; right; left; exact ⟨rfl, rfl, rfl, rfl, ha, rfl, rfl, rfl, rfl, rfl⟩
          · push_neg at ha
            simp only [ha]
            by_cases hinv : V.invertibility ≠ W.invertibility
            · simp only [hinv]
              right; right; right; right; right; left
              exact ⟨rfl, rfl, rfl, rfl, rfl, hinv, rfl, rfl, rfl, rfl⟩
            · push_neg at hinv
              simp only [hinv]
              by_cases hdet : V.determinism ≠ W.determinism
              · simp only [hdet]
                right; right; right; right; right; right; left
                exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hdet, rfl, rfl, rfl⟩
              · push_neg at hdet
                simp only [hdet]
                by_cases hsup : V.support ≠ W.support
                · simp only [hsup]
                  right; right; right; right; right; right; right; left
                  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hsup, rfl, rfl⟩
                · push_neg at hsup
                  simp only [hsup]
                  by_cases hreg : V.regularity ≠ W.regularity
                  · simp only [hreg]
                    right; right; right; right; right; right; right; right; left
                    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hreg, rfl⟩
                  · push_neg at hreg
                    simp only [hreg]
                    -- All other axes match, so independence must differ
                    have hind : V.independence ≠ W.independence := by
                      intro heq
                      apply hne
                      ext <;> try assumption
                    right; right; right; right; right; right; right; right; right
                    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hind⟩

/-- Hamming distance decreases after stepping toward target. -/
private theorem hammingDistance_stepToward_lt (V W : ProbabilityVertex) (hne : V ≠ W) :
    hammingDistance (stepToward V W) W < hammingDistance V W := by
  unfold stepToward hammingDistance
  -- Work through the chain: find the first differing axis.
  by_cases hc : V.commutativity ≠ W.commutativity
  · simp [hc] <;> omega
  · push_neg at hc
    simp [hc]
    by_cases hd : V.distributivity ≠ W.distributivity
    · simp [hd] <;> omega
    · push_neg at hd
      simp [hd]
      by_cases hp : V.precision ≠ W.precision
      · simp [hp] <;> omega
      · push_neg at hp
        simp [hp]
        by_cases ho : V.orderAxis ≠ W.orderAxis
        · simp [ho] <;> omega
        · push_neg at ho
          simp [ho]
          by_cases ha : V.additivity ≠ W.additivity
          · simp [ha] <;> omega
          · push_neg at ha
            simp [ha]
            by_cases hinv : V.invertibility ≠ W.invertibility
            · simp [hinv] <;> omega
            · push_neg at hinv
              simp [hinv]
              by_cases hdet : V.determinism ≠ W.determinism
              · simp [hdet] <;> omega
              · push_neg at hdet
                simp [hdet]
                by_cases hsup : V.support ≠ W.support
                · simp [hsup] <;> omega
                · push_neg at hsup
                  simp [hsup]
                  by_cases hreg : V.regularity ≠ W.regularity
                  · simp [hreg] <;> omega
                  · push_neg at hreg
                    simp [hreg]
                    have hind : V.independence ≠ W.independence := by
                      intro heq
                      apply hne
                      ext <;> try assumption
                    simp [hind] <;> omega

/-- Natural edges have Hamming distance exactly 1. -/
theorem isNaturalEdge_iff_hamming_one {V W : ProbabilityVertex} :
    isNaturalEdge V W ↔ hammingDistance V W = 1 := by
  constructor
  · intro h
    simp only [isNaturalEdge, hammingDistance] at h ⊢
    rcases h with
        ⟨hne, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ |
        ⟨h0, hne, h2, h3, h4, h5, h6, h7, h8, h9⟩ |
        ⟨h0, h1, hne, h3, h4, h5, h6, h7, h8, h9⟩ |
        ⟨h0, h1, h2, hne, h4, h5, h6, h7, h8, h9⟩ |
        ⟨h0, h1, h2, h3, hne, h5, h6, h7, h8, h9⟩ |
        ⟨h0, h1, h2, h3, h4, hne, h6, h7, h8, h9⟩ |
        ⟨h0, h1, h2, h3, h4, h5, hne, h7, h8, h9⟩ |
        ⟨h0, h1, h2, h3, h4, h5, h6, hne, h8, h9⟩ |
        ⟨h0, h1, h2, h3, h4, h5, h6, h7, hne, h9⟩ |
        ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hne⟩
    all_goals simp [*]
  · intro h
    have hne : V ≠ W := by
      intro hVW
      subst hVW
      simpa [hammingDistance] using h
    have hEdge : isNaturalEdge V (stepToward V W) :=
      isNaturalEdge_stepToward V W hne
    have hlt : hammingDistance (stepToward V W) W < 1 := by
      simpa [h] using (hammingDistance_stepToward_lt V W hne)
    have hz : hammingDistance (stepToward V W) W = 0 := (Nat.lt_one_iff).1 hlt
    have hEq : stepToward V W = W := eq_of_hammingDistance_eq_zero hz
    simpa [hEq] using hEdge

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

end Mettapedia.ProbabilityTheory.Hypercube
