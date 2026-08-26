import Mettapedia.Enactive.AxisIndependence
import Mettapedia.InformationTheory.AdditiveMessageValuation

/-!
# Diagonal, entropy, graphtropy, and message-valued razors

This module keeps four specializations of constrained selection distinct:

* diagonal pair cardinality recovers Bennett's finite completion count;
* logical entropy may be maximized as diversity or minimized as indistinction;
* graphtropy rewards missing edges only when its input is declared to be a
  distinction graph;
* an MDL-like message profile minimizes an explicitly chosen additive
  valuation.

The diagonal used in the first result is the map `u ↦ (u, u)`.  It is the
diagonal morphism in the category of types, but the cardinality theorem below
is not a Cantor--Lawvere diagonal argument: no evaluator, self-application,
point-surjectivity, fixed-point-free map, or negation is involved.

References:

* M. T. Bennett, *The Wrong Razor* (2026), for completion weakness and its
  contrast with code length.
* B. Goertzel, *Weakness Is All You Need: Quantale Weakness as a Unifying
  Principle for Cognition* (2026), for the diagonal specialization,
  layer-relative valuations, logical entropy, graphtropy, and generalized-MDL
  motivation.
* D. Ellerman, *An Introduction to Logical Entropy and Its Relation to Shannon
  Entropy* (2017), for logical entropy as distinction probability.
* C. S. Wallace and D. M. Boulton, *An Information Measure for Classification*
  (1968), and J. Rissanen, *Modeling by Shortest Data Description* (1978), for
  two-part message criteria.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.QuantaleRazorValuations

open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.Enactive.Razor
open Mettapedia.InformationTheory.AdditiveMessageValuation

universe uCandidate uWorld

/-! ## Exact diagonal recovery -/

section DiagonalRecovery

variable {World : Type uWorld}

/-- Maximize Bennett's finite admitted-world count. -/
def bennettCardinalityCriterion
    (admissible : Finset World → Prop) : Criterion (Finset World) :=
  Criterion.ofBenefit admissible bennettWeakness

/-- Maximize the cardinality of the induced diagonal pair event. -/
def diagonalPairCardinalityCriterion
    (admissible : Finset World → Prop) : Criterion (Finset World) :=
  Criterion.ofBenefit admissible fun worlds =>
    pairDistinctionWeakness (inducedDiagonalEvent worlds)

/-- Goertzel's unit-weight diagonal specialization preserves and reflects the
finite Bennett preference exactly. -/
theorem diagonalPair_atLeastAsGood_iff_bennett
    (admissible : Finset World → Prop) (left right : Finset World) :
    (diagonalPairCardinalityCriterion admissible).atLeastAsGood left right ↔
      (bennettCardinalityCriterion admissible).atLeastAsGood left right := by
  exact pairDistinctionWeakness_inducedDiagonalEvent_le_iff right left

/-- The complete-pair construction is a different numerical presentation:
two worlds give four pairs, whereas the diagonal gives two. -/
theorem completePair_and_diagonal_are_not_the_same_measure :
    pairDistinctionWeakness
        (inducedPairEvent (Finset.univ : Finset Bool)) = 4 ∧
      pairDistinctionWeakness
        (inducedDiagonalEvent (Finset.univ : Finset Bool)) = 2 := by
  decide

end DiagonalRecovery

/-! ## Logical diversity and indistinction have opposite polarity -/

section LogicalEntropyProfiles

variable {World : Type uWorld} [Fintype World]

/-- Logical entropy with the propositionally irrelevant decidability evidence
hidden from the candidate type. -/
noncomputable def logicalEntropyScore (relation : Setoid World) : ℚ :=
  by
    classical
    exact (Finset.univ.filter fun pair : World × World =>
      ¬ relation.r pair.1 pair.2).card /
        (Fintype.card World * Fintype.card World : ℕ)

/-- Hiding the decidability witness changes no mathematical content. -/
theorem logicalEntropyScore_eq_uniformLogicalEntropy
    (relation : Setoid World) [DecidableRel relation.r] :
    logicalEntropyScore relation = uniformLogicalEntropy relation := by
  classical
  unfold logicalEntropyScore uniformLogicalEntropy setoidDistinctionSet
  congr 2
  congr 1
  ext pair
  simp

/-- Prefer partitions that distinguish more pairs. -/
noncomputable def logicalDiversityCriterion
    (admissible : Setoid World → Prop) : Criterion (Setoid World) :=
  Criterion.ofBenefit admissible logicalEntropyScore

/-- Prefer partitions that leave more pairs indistinguished.  This uses the
same score as `logicalDiversityCriterion` with the opposite polarity. -/
noncomputable def logicalIndistinctionCriterion
    (admissible : Setoid World → Prop) : Criterion (Setoid World) :=
  Criterion.ofCost admissible logicalEntropyScore

theorem bool_discrete_uniformLogicalEntropy :
    logicalEntropyScore (discreteSetoid' Bool) = 1 / 2 := by
  rw [logicalEntropyScore_eq_uniformLogicalEntropy]
  have eventCard :
      (setoidDistinctionSet (discreteSetoid' Bool)).card = 2 := by
    decide
  unfold uniformLogicalEntropy
  rw [eventCard]
  norm_num

theorem bool_indiscrete_uniformLogicalEntropy :
    logicalEntropyScore (indiscreteSetoid' Bool) = 0 := by
  rw [logicalEntropyScore_eq_uniformLogicalEntropy,
    uniformLogicalEntropy_indiscrete]

/-- Positive/negative polarity control: diversity strictly prefers the
discrete partition, while indistinction strictly prefers the indiscrete one. -/
theorem logical_entropy_polarity_reverses_preference :
    (logicalDiversityCriterion (World := Bool) (fun _ => True)).atLeastAsGood
        (discreteSetoid' Bool) (indiscreteSetoid' Bool) ∧
      ¬ (logicalDiversityCriterion (World := Bool) (fun _ => True)).atLeastAsGood
        (indiscreteSetoid' Bool) (discreteSetoid' Bool) ∧
      (logicalIndistinctionCriterion (World := Bool) (fun _ => True)).atLeastAsGood
        (indiscreteSetoid' Bool) (discreteSetoid' Bool) ∧
      ¬ (logicalIndistinctionCriterion (World := Bool) (fun _ => True)).atLeastAsGood
        (discreteSetoid' Bool) (indiscreteSetoid' Bool) := by
  change
    logicalEntropyScore (indiscreteSetoid' Bool) ≤
        logicalEntropyScore (discreteSetoid' Bool) ∧
      ¬ logicalEntropyScore (discreteSetoid' Bool) ≤
        logicalEntropyScore (indiscreteSetoid' Bool) ∧
      logicalEntropyScore (indiscreteSetoid' Bool) ≤
        logicalEntropyScore (discreteSetoid' Bool) ∧
      ¬ logicalEntropyScore (discreteSetoid' Bool) ≤
        logicalEntropyScore (indiscreteSetoid' Bool)
  rw [bool_discrete_uniformLogicalEntropy,
    bool_indiscrete_uniformLogicalEntropy]
  norm_num

end LogicalEntropyProfiles

/-! ## Graphtropy as missing distinction -/

section GraphtropyProfile

variable {World : Type uWorld} [Fintype World] [DecidableEq World]

/-- When the input edges are declared distinctions, maximize the normalized
mass of off-diagonal pairs that remain indistinguished. -/
noncomputable def graphtropyCriterion
    (admissible : Finset (World × World) → Prop) :
    Criterion (Finset (World × World)) :=
  Criterion.ofBenefit admissible graphtropy

/-- Adding distinction edges can only make a graph weakly worse for the
graphtropy-as-indistinction profile. -/
theorem distinctionEdgeInclusion_implies_graphtropyPreference
    (admissible : Finset (World × World) → Prop)
    {small large : Finset (World × World)} (included : small ⊆ large) :
    (graphtropyCriterion admissible).atLeastAsGood small large :=
  graphtropy_antitone included

/-- On two vertices the empty distinction graph is strictly preferred to the
complete distinction graph.  Calling the edges similarities instead would
reverse the interpretation, hence edge polarity is part of the profile. -/
theorem bool_graphtropy_strict_control :
    (graphtropyCriterion (World := Bool) (fun _ => True)).atLeastAsGood
        ∅ Finset.univ ∧
      ¬ (graphtropyCriterion (World := Bool) (fun _ => True)).atLeastAsGood
        Finset.univ ∅ := by
  have emptyValue :
      graphtropy (∅ : Finset (Bool × Bool)) = 1 / 2 := by
    unfold graphtropy
    have eventValue :
        graphIndistinctionEvent (∅ : Finset (Bool × Bool)) =
          {(false, true), (true, false)} := by
      decide
    rw [eventValue]
    norm_num
  change graphtropy (Finset.univ : Finset (Bool × Bool)) ≤ graphtropy ∅ ∧
    ¬ graphtropy ∅ ≤ graphtropy (Finset.univ : Finset (Bool × Bool))
  rw [graphtropy_univ, emptyValue]
  norm_num

end GraphtropyProfile

/-! ## Additive message valuation -/

section MessageProfile

variable {Candidate : Type uCandidate}

/-- Minimize the explicitly valued composite of model and data messages. -/
def additiveMessageCriterion {Atom Cost : Type*} [AddCommMonoid Cost]
    [Preorder Cost]
    (adequate : Candidate → Prop)
    (valuation : Valuation Atom Cost)
    (modelMessage dataGivenModelMessage : Candidate → Multiset Atom) :
    Criterion Candidate :=
  Criterion.ofCost adequate fun candidate =>
    valuation.value (modelMessage candidate + dataGivenModelMessage candidate)

/-- Unit atomic cost recovers the ordinary two-part length ordering exactly. -/
theorem unitMessage_atLeastAsGood_iff_twoPartCode
    {Atom : Type*} (adequate : Candidate → Prop)
    (modelMessage dataGivenModelMessage : Candidate → Multiset Atom)
    (left right : Candidate) :
    (additiveMessageCriterion adequate unitNat modelMessage
      dataGivenModelMessage).atLeastAsGood left right ↔
      (twoPartCode adequate (fun candidate => (modelMessage candidate).card)
        (fun candidate => (dataGivenModelMessage candidate).card)).atLeastAsGood
          left right := by
  simp [additiveMessageCriterion, twoPartCode]

/-- Nonuniform atomic cost is not determined by message length.  Thus the
generalized message profile is representation-relative, as advertised, and
does not silently preserve the MDL length ordering. -/
theorem nonuniform_message_value_not_determined_by_length :
    ¬ (WeightedCanary.weightedBool.value).FactorsThrough Multiset.card :=
  WeightedCanary.weightedValue_not_factorsThrough_card

end MessageProfile

/-! ## Published layer relativity -/

/-- The existing concrete candidate family supplies both collisions: finite
completion count does not determine nonuniform quantale weakness, and the
nonuniform score does not determine completion count. -/
theorem nonuniform_quantale_and_bennett_are_independent :
    Mettapedia.Enactive.AxisIndependence.PairwiseIndependent
      Mettapedia.Enactive.AxisIndependence.completionWeakness
      Mettapedia.Enactive.AxisIndependence.weightedQuantaleWeakness :=
  Mettapedia.Enactive.AxisIndependence.completionWeakness_weightedQuantaleWeakness_independent

end Mettapedia.Enactive.QuantaleRazorValuations

#print axioms Mettapedia.Enactive.QuantaleRazorValuations.diagonalPair_atLeastAsGood_iff_bennett
#print axioms Mettapedia.Enactive.QuantaleRazorValuations.logical_entropy_polarity_reverses_preference
#print axioms Mettapedia.Enactive.QuantaleRazorValuations.bool_graphtropy_strict_control
#print axioms Mettapedia.Enactive.QuantaleRazorValuations.unitMessage_atLeastAsGood_iff_twoPartCode
#print axioms Mettapedia.Enactive.QuantaleRazorValuations.nonuniform_quantale_and_bennett_are_independent
