import Mathlib.Tactic
import Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation
import Mettapedia.PLN.InferenceControl.CertifiedChaining.EstimatorEnvelope
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathDependency

/-!
# Dependence-aware two-hop chain composition

This module packages the first constructor-disciplined surface for composing
PLN strengths across two hops.  The strength envelope is derived before the
candidate estimate is checked; confidence is kept as a separate coordinate.
-/

namespace Mettapedia.PLN.InferenceControl.CertifiedChaining.DependenceAwareChainComposition

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory
open Mettapedia.PLN.InferenceControl.CertifiedChaining.EstimatorEnvelope
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathDependency
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathFrechet
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

noncomputable section

/-! ## Link and source constructors -/

/-- A point strength interval with an independent confidence coordinate. -/
def pointStrengthITV (strength confidence : ℝ)
    (hstrength : strength ∈ Set.Icc (0 : ℝ) 1)
    (hconfidence : confidence ∈ Set.Icc (0 : ℝ) 1) : ITV where
  lower := strength
  upper := strength
  credibility := confidence
  lower_le_upper := le_rfl
  lower_in_unit := hstrength
  upper_in_unit := hstrength
  credibility_in_unit := hconfidence

/-- One certified chain link.  Its envelope constrains strength only;
confidence is tracked for later horizon theorems. -/
structure ChainLinkCert where
  sourceSupport : Finset ℕ
  strength : ℝ
  confidence : ℝ
  strengthEnvelope : ITV
  strength_mem_envelope :
    strengthEnvelope.lower ≤ strength ∧ strength ≤ strengthEnvelope.upper
  confidence_mem_unit :
    confidence ∈ Set.Icc (0 : ℝ) 1

namespace ChainLinkCert

theorem strength_mem_unit (link : ChainLinkCert) :
    link.strength ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_trans link.strengthEnvelope.lower_in_unit.1
      link.strength_mem_envelope.1,
    le_trans link.strength_mem_envelope.2
      link.strengthEnvelope.upper_in_unit.2⟩

/-- Constructor for an exact point-strength link. -/
def point (sourceSupport : Finset ℕ) (strength confidence : ℝ)
    (hstrength : strength ∈ Set.Icc (0 : ℝ) 1)
    (hconfidence : confidence ∈ Set.Icc (0 : ℝ) 1) :
    ChainLinkCert where
  sourceSupport := sourceSupport
  strength := strength
  confidence := confidence
  strengthEnvelope := pointStrengthITV strength confidence hstrength hconfidence
  strength_mem_envelope := by simp [pointStrengthITV]
  confidence_mem_unit := hconfidence

end ChainLinkCert

/-- Bernoulli source probabilities used to compute overlap-corrected support. -/
structure SourceProfile where
  prob : ℕ → ℝ≥0
  prob_le_one : ∀ s, prob s ≤ 1

/-- Strength of a single finite source support under a source profile. -/
def sourceStrength (profile : SourceProfile) (S : Finset ℕ) : ℝ :=
  (infiniteFactMeasure profile.prob profile.prob_le_one).real (sourceEvent S)

/-- Strength of the union of two finite source supports. -/
def sourceUnionStrength
    (profile : SourceProfile) (S T : Finset ℕ) : ℝ :=
  (infiniteFactMeasure profile.prob profile.prob_le_one).real
    (sourceEvent S ∪ sourceEvent T)

theorem sourceUnionStrength_mem_unit
    (profile : SourceProfile) (S T : Finset ℕ) :
    sourceUnionStrength profile S T ∈ Set.Icc (0 : ℝ) 1 := by
  unfold sourceUnionStrength
  exact measureReal_mem_unit_of_probability
    (infiniteFactMeasure profile.prob profile.prob_le_one)
    (sourceEvent S ∪ sourceEvent T)

theorem sourceUnionStrength_eq_add_sub_overlap
    (profile : SourceProfile) (S T : Finset ℕ) :
    sourceUnionStrength profile S T =
      sourceStrength profile S + sourceStrength profile T -
        (∏ s ∈ S ∪ T, ((profile.prob s : ℝ≥0) : ℝ)) := by
  unfold sourceUnionStrength sourceStrength
  exact sourcePair_union_eq_add_sub_overlap
    profile.prob profile.prob_le_one S T

theorem sourceUnionStrength_eq_noisyOr_of_disjoint
    (profile : SourceProfile) {S T : Finset ℕ} (hdisj : Disjoint S T) :
    sourceUnionStrength profile S T =
      noisyOrFrequency
        (fun i : Fin 2 =>
          if i = 0 then sourceStrength profile S else sourceStrength profile T) := by
  unfold sourceUnionStrength sourceStrength
  exact sourcePair_disjoint_union_eq_noisyOr
    profile.prob profile.prob_le_one hdisj

/-! ## BN exactness bridge -/

/-- The compiled chain d-separation side condition constructs the conditional
independence fact needed by the screening-off theorem. -/
theorem chainBN_hciCA_of_compiled_dsep
    (cpt : chainBN.DiscreteCPT)
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    [HasLocalMarkovProperty chainBN cpt.jointMeasure]
    (hcond :
      (CompiledPlan.deductionSide Three.A Three.B Three.C).holds (bn := chainBN)) :
    CondIndepVertices chainBN cpt.jointMeasure
      ({Three.C} : Set Three) ({Three.A} : Set Three) ({Three.B} : Set Three) :=
  ChainExample.chain_hciCA_of_dsep (cpt := cpt) hcond

/-- The same constructed d-separation condition feeds the numeric
screening-off multiplication identity. -/
theorem chainBN_screeningOffMulEq_of_compiled_dsep
    (cpt : chainBN.DiscreteCPT)
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, MeasurableSingletonClass (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    [HasLocalMarkovProperty chainBN cpt.jointMeasure]
    (hcond :
      (CompiledPlan.deductionSide Three.A Three.B Three.C).holds (bn := chainBN))
    (valA : chainBN.stateSpace Three.A)
    (valB : chainBN.stateSpace Three.B)
    (valC : chainBN.stateSpace Three.C) :
    cpt.jointMeasure
        (BayesianNetwork.eventEq (bn := chainBN) Three.A valA ∩
          BayesianNetwork.eventEq (bn := chainBN) Three.C valC ∩
          BayesianNetwork.eventEq (bn := chainBN) Three.B valB) *
      cpt.jointMeasure (BayesianNetwork.eventEq (bn := chainBN) Three.B valB) =
    cpt.jointMeasure
        (BayesianNetwork.eventEq (bn := chainBN) Three.A valA ∩
          BayesianNetwork.eventEq (bn := chainBN) Three.B valB) *
      cpt.jointMeasure
        (BayesianNetwork.eventEq (bn := chainBN) Three.C valC ∩
          BayesianNetwork.eventEq (bn := chainBN) Three.B valB) := by
  exact Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation.BNWorldModel.screeningOffMulEq_of_condIndepVertices_CA
    (bn := chainBN) Three.A Three.B Three.C valA valB valC cpt
    (chainBN_hciCA_of_compiled_dsep (cpt := cpt) hcond)

/-! ## Two-hop composition data -/

/-- Product-exactness data for the semantic A-to-B, B-to-C part of a chain. -/
structure TwoHopProductExactness (left right : ChainLinkCert) where
  productStrength : ℝ
  productStrength_eq : productStrength = left.strength * right.strength
  productStrength_mem_unit : productStrength ∈ Set.Icc (0 : ℝ) 1

namespace TwoHopProductExactness

/-- Constructor for the product-exact branch from two unit-strength links. -/
def of_linkStrengths (left right : ChainLinkCert) :
    TwoHopProductExactness left right where
  productStrength := left.strength * right.strength
  productStrength_eq := rfl
  productStrength_mem_unit := by
    have hl := left.strength_mem_unit
    have hr := right.strength_mem_unit
    constructor
    · exact mul_nonneg hl.1 hr.1
    · have hmul_le_left :
        left.strength * right.strength ≤ left.strength * 1 :=
        mul_le_mul_of_nonneg_left hr.2 hl.1
      nlinarith [hmul_le_left, hl.2]

end TwoHopProductExactness

/-- Source-coupling evidence is constructed from a source profile and supports;
the corrected strength is then computed from that data. -/
inductive TwoHopSourceCoupling
    (profile : SourceProfile) (leftSupport rightSupport : Finset ℕ) : Type
  | fromSourceUnion :
      TwoHopSourceCoupling profile leftSupport rightSupport

namespace TwoHopSourceCoupling

def correctedStrength
    {profile : SourceProfile} {leftSupport rightSupport : Finset ℕ}
    (_coupling : TwoHopSourceCoupling profile leftSupport rightSupport) : ℝ :=
  sourceUnionStrength profile leftSupport rightSupport

theorem correctedStrength_mem_unit
    {profile : SourceProfile} {leftSupport rightSupport : Finset ℕ}
    (coupling : TwoHopSourceCoupling profile leftSupport rightSupport) :
    coupling.correctedStrength ∈ Set.Icc (0 : ℝ) 1 := by
  cases coupling
  exact sourceUnionStrength_mem_unit profile leftSupport rightSupport

end TwoHopSourceCoupling

/-- The two-hop datum carries constructed product exactness and constructed
source coupling; no loose exactness hypothesis is left behind. -/
structure TwoHopChainDatum where
  left : ChainLinkCert
  right : ChainLinkCert
  productExactness : TwoHopProductExactness left right
  sourceProfile : SourceProfile
  sourceCoupling :
    TwoHopSourceCoupling sourceProfile left.sourceSupport right.sourceSupport

/-- The two W1 strength candidates: product-exact and source-corrected. -/
def chainFrequencies (d : TwoHopChainDatum) : Fin 2 → ℝ :=
  fun i =>
    if i = 0 then d.productExactness.productStrength
    else d.sourceCoupling.correctedStrength

theorem chainFrequencies_mem_unit (d : TwoHopChainDatum) :
    ∀ i, chainFrequencies d i ∈ Set.Icc (0 : ℝ) 1 := by
  intro i
  fin_cases i
  · simp [chainFrequencies, d.productExactness.productStrength_mem_unit]
  · simp [chainFrequencies, d.sourceCoupling.correctedStrength_mem_unit]

/-- Two-hop composition as the existing two-path Frechet input.  The confidence
field is deliberately not used to smuggle strength containment. -/
def chainMultiPathInput (d : TwoHopChainDatum) : MultiPathInput 1 where
  frequency := chainFrequencies d
  frequency_mem_unit := chainFrequencies_mem_unit d
  confidence := fun _ => 0
  confidence_le_one := by intro _; simp

/-- The precomputed strength envelope for the composed A-to-C estimate. -/
def chainCredalEnvelope (d : TwoHopChainDatum) : ITV :=
  frechetUnionITV (chainMultiPathInput d)

/-- The W1 composed strength estimate: noisy-OR over the constructed product
and source-corrected candidates. -/
def twoHopComposedEstimate (d : TwoHopChainDatum) : ℝ :=
  noisyOrFrequency (chainFrequencies d)

/-- W1 crown: the composed two-hop strength lands in the precomputed envelope. -/
theorem twoHopChainComposition_mem_credalEnvelope
    (d : TwoHopChainDatum) :
    (chainCredalEnvelope d).lower ≤ twoHopComposedEstimate d ∧
      twoHopComposedEstimate d ≤ (chainCredalEnvelope d).upper := by
  simpa [chainCredalEnvelope, twoHopComposedEstimate, chainMultiPathInput]
    using noisyOrFrequency_mem_frechetUnionITV (chainMultiPathInput d)

/-- Canary against vacuous `[0,1]` use: a positive product candidate forces the
derived envelope's lower endpoint above zero. -/
theorem chainCredalEnvelope_lower_ne_zero_of_product_pos
    (d : TwoHopChainDatum) (hprod : 0 < d.productExactness.productStrength) :
    (chainCredalEnvelope d).lower ≠ 0 := by
  have hle :
      d.productExactness.productStrength ≤ (chainCredalEnvelope d).lower := by
    rw [chainCredalEnvelope, frechetUnionITV_lower]
    simpa [chainMultiPathInput, chainFrequencies]
      using frequency_le_maxFrequency (chainFrequencies d) (0 : Fin 2)
  intro hzero
  nlinarith

/-! ## W3: nonempty n-hop chain composition -/

/-- Strength of the union of a nonempty family of source supports. -/
def sourceSupportsUnionStrength
    {n : ℕ} (profile : SourceProfile) (supports : Fin (n + 1) → Finset ℕ) : ℝ :=
  (infiniteFactMeasure profile.prob profile.prob_le_one).real
    (Set.iUnion fun i => sourceEvent (supports i))

theorem sourceSupportsUnionStrength_mem_unit
    {n : ℕ} (profile : SourceProfile) (supports : Fin (n + 1) → Finset ℕ) :
    sourceSupportsUnionStrength profile supports ∈ Set.Icc (0 : ℝ) 1 := by
  unfold sourceSupportsUnionStrength
  exact measureReal_mem_unit_of_probability
    (infiniteFactMeasure profile.prob profile.prob_le_one)
    (Set.iUnion fun i => sourceEvent (supports i))

theorem sourceSupportsUnionStrength_eq_noisyOr_of_pairwiseDisjoint
    {n : ℕ} (profile : SourceProfile) (supports : Fin (n + 1) → Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (supports i) (supports j))) :
    sourceSupportsUnionStrength profile supports =
      noisyOrFrequency (fun i => sourceStrength profile (supports i)) := by
  unfold sourceSupportsUnionStrength sourceStrength
  exact sourceEvents_pairwiseDisjoint_union_eq_noisyOrFrequency
    profile.prob profile.prob_le_one supports hdisj

theorem sourceSupportsUnionStrength_eq_max_of_allEqual
    {n : ℕ} (profile : SourceProfile) (supports : Fin (n + 1) → Finset ℕ)
    (hEq : ∀ i j, supports i = supports j) :
    sourceSupportsUnionStrength profile supports =
      maxFrequency n (fun i => sourceStrength profile (supports i)) := by
  unfold sourceSupportsUnionStrength sourceStrength
  exact sourceEvents_allEqual_union_eq_maxFrequency
    profile.prob profile.prob_le_one supports hEq

/-- Product strength of a nonempty path of certified links. -/
def pathProductStrength {n : ℕ} (links : Fin (n + 1) → ChainLinkCert) : ℝ :=
  ∏ i, (links i).strength

theorem pathProductStrength_mem_unit
    {n : ℕ} (links : Fin (n + 1) → ChainLinkCert) :
    pathProductStrength links ∈ Set.Icc (0 : ℝ) 1 := by
  unfold pathProductStrength
  constructor
  · exact Finset.prod_nonneg (fun i _ => (links i).strength_mem_unit.1)
  · have hle : (∏ i, (links i).strength) ≤ ∏ _i : Fin (n + 1), (1 : ℝ) := by
      exact Finset.prod_le_prod
        (fun i _ => (links i).strength_mem_unit.1)
        (fun i _ => (links i).strength_mem_unit.2)
    simpa using hle

/-- Product-exactness data for a nonempty path. -/
structure PathProductExactness {n : ℕ} (links : Fin (n + 1) → ChainLinkCert) where
  productStrength : ℝ
  productStrength_eq : productStrength = pathProductStrength links
  productStrength_mem_unit : productStrength ∈ Set.Icc (0 : ℝ) 1

namespace PathProductExactness

/-- Constructor for the path-product branch from unit-strength links. -/
def of_links {n : ℕ} (links : Fin (n + 1) → ChainLinkCert) :
    PathProductExactness links where
  productStrength := pathProductStrength links
  productStrength_eq := rfl
  productStrength_mem_unit := pathProductStrength_mem_unit links

end PathProductExactness

/-- Source coupling for a whole path is constructed from the profile and every
link's source support. -/
inductive PathSourceCoupling
    {n : ℕ} (profile : SourceProfile) (links : Fin (n + 1) → ChainLinkCert) : Type
  | fromSourceUnion : PathSourceCoupling profile links

namespace PathSourceCoupling

def correctedStrength
    {n : ℕ} {profile : SourceProfile} {links : Fin (n + 1) → ChainLinkCert}
    (_coupling : PathSourceCoupling profile links) : ℝ :=
  sourceSupportsUnionStrength profile (fun i => (links i).sourceSupport)

theorem correctedStrength_mem_unit
    {n : ℕ} {profile : SourceProfile} {links : Fin (n + 1) → ChainLinkCert}
    (coupling : PathSourceCoupling profile links) :
    coupling.correctedStrength ∈ Set.Icc (0 : ℝ) 1 := by
  cases coupling
  exact sourceSupportsUnionStrength_mem_unit profile
    (fun i => (links i).sourceSupport)

end PathSourceCoupling

/-- An n-hop datum over a nonempty path of links. -/
structure PathChainDatum (n : ℕ) where
  links : Fin (n + 1) → ChainLinkCert
  productExactness : PathProductExactness links
  sourceProfile : SourceProfile
  sourceCoupling : PathSourceCoupling sourceProfile links

/-- The two W3 path candidates: path product and n-ary source correction. -/
def pathChainFrequencies {n : ℕ} (d : PathChainDatum n) : Fin 2 → ℝ :=
  fun i =>
    if i = 0 then d.productExactness.productStrength
    else d.sourceCoupling.correctedStrength

theorem pathChainFrequencies_mem_unit {n : ℕ} (d : PathChainDatum n) :
    ∀ i, pathChainFrequencies d i ∈ Set.Icc (0 : ℝ) 1 := by
  intro i
  fin_cases i
  · simp [pathChainFrequencies, d.productExactness.productStrength_mem_unit]
  · simp [pathChainFrequencies, d.sourceCoupling.correctedStrength_mem_unit]

/-- W3 path composition as a two-candidate Frechet input. -/
def pathChainMultiPathInput {n : ℕ} (d : PathChainDatum n) : MultiPathInput 1 where
  frequency := pathChainFrequencies d
  frequency_mem_unit := pathChainFrequencies_mem_unit d
  confidence := fun _ => 0
  confidence_le_one := by intro _; simp

/-- The precomputed n-hop path envelope. -/
def pathCredalEnvelope {n : ℕ} (d : PathChainDatum n) : ITV :=
  frechetUnionITV (pathChainMultiPathInput d)

/-- The n-hop composed strength estimate. -/
def chainCompositionEstimate {n : ℕ} (d : PathChainDatum n) : ℝ :=
  noisyOrFrequency (pathChainFrequencies d)

/-- W3 crown: any constructed nonempty path estimate lands in its precomputed
path envelope. -/
theorem chainComposition_mem_credalEnvelope
    {n : ℕ} (d : PathChainDatum n) :
    (pathCredalEnvelope d).lower ≤ chainCompositionEstimate d ∧
      chainCompositionEstimate d ≤ (pathCredalEnvelope d).upper := by
  simpa [pathCredalEnvelope, chainCompositionEstimate, pathChainMultiPathInput]
    using noisyOrFrequency_mem_frechetUnionITV (pathChainMultiPathInput d)

/-- List-level path products compose by append, giving the reusable algebraic
associativity surface for path segmentation. -/
def linkStrengthProductList (links : List ChainLinkCert) : ℝ :=
  (links.map fun link => link.strength).prod

theorem linkStrengthProductList_append (xs ys : List ChainLinkCert) :
    linkStrengthProductList (xs ++ ys) =
      linkStrengthProductList xs * linkStrengthProductList ys := by
  simp [linkStrengthProductList, List.map_append]

theorem linkStrengthProductList_append_assoc
    (xs ys zs : List ChainLinkCert) :
    linkStrengthProductList ((xs ++ ys) ++ zs) =
      linkStrengthProductList (xs ++ (ys ++ zs)) := by
  simp [List.append_assoc]

/-! ## W4: chain horizon and confidence decay -/

/-- The vacuous strength interval. -/
def unitStrengthITV : ITV where
  lower := 0
  upper := 1
  credibility := 0
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

/-- Width of a strength interval. -/
def chainEnvelopeWidth (itv : ITV) : ℝ :=
  itv.upper - itv.lower

theorem chainEnvelopeWidth_nonneg (itv : ITV) :
    0 ≤ chainEnvelopeWidth itv := by
  unfold chainEnvelopeWidth
  linarith [itv.lower_le_upper]

theorem chainEnvelopeWidth_le_one (itv : ITV) :
    chainEnvelopeWidth itv ≤ 1 := by
  unfold chainEnvelopeWidth
  linarith [itv.lower_in_unit.1, itv.upper_in_unit.2]

theorem unitStrengthITV_width_eq_one :
    chainEnvelopeWidth unitStrengthITV = 1 := by
  norm_num [chainEnvelopeWidth, unitStrengthITV]

/-- Product of the confidence coordinates along a nonempty path. -/
def pathConfidenceProduct {n : ℕ} (links : Fin (n + 1) → ChainLinkCert) : ℝ :=
  ∏ i, (links i).confidence

theorem pathConfidenceProduct_mem_unit
    {n : ℕ} (links : Fin (n + 1) → ChainLinkCert) :
    pathConfidenceProduct links ∈ Set.Icc (0 : ℝ) 1 := by
  unfold pathConfidenceProduct
  constructor
  · exact Finset.prod_nonneg (fun i _ => (links i).confidence_mem_unit.1)
  · have hle : (∏ i, (links i).confidence) ≤ ∏ _i : Fin (n + 1), (1 : ℝ) := by
      exact Finset.prod_le_prod
        (fun i _ => (links i).confidence_mem_unit.1)
        (fun i _ => (links i).confidence_mem_unit.2)
    simpa using hle

theorem pathConfidenceProduct_le_link_confidence
    {n : ℕ} (links : Fin (n + 1) → ChainLinkCert) (i : Fin (n + 1)) :
    pathConfidenceProduct links ≤ (links i).confidence := by
  unfold pathConfidenceProduct
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have hprod_nonneg : 0 ≤ ∏ x ∈ Finset.univ.erase i, (links x).confidence := by
    exact Finset.prod_nonneg (fun j _ => (links j).confidence_mem_unit.1)
  have hprod_le_one : ∏ x ∈ Finset.univ.erase i, (links x).confidence ≤ 1 := by
    have hle :
        (∏ x ∈ Finset.univ.erase i, (links x).confidence) ≤
          ∏ _x ∈ Finset.univ.erase i, (1 : ℝ) := by
      exact Finset.prod_le_prod
        (fun j _ => (links j).confidence_mem_unit.1)
        (fun j _ => (links j).confidence_mem_unit.2)
    simpa using hle
  nlinarith [(links i).confidence_mem_unit.1, (links i).confidence_mem_unit.2]

/-- Minimum link confidence along a nonempty path. -/
def pathMinConfidence {n : ℕ} (links : Fin (n + 1) → ChainLinkCert) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => (links i).confidence)

/-- The path confidence product never exceeds the weakest link. -/
theorem pathChainConfidence_le_min
    {n : ℕ} (d : PathChainDatum n) :
    pathConfidenceProduct d.links ≤ pathMinConfidence d.links := by
  unfold pathMinConfidence
  exact Finset.le_inf' Finset.univ_nonempty
    (fun i => (d.links i).confidence)
    (fun i _ => pathConfidenceProduct_le_link_confidence d.links i)

/-- List-level confidence product for append/segmentation laws. -/
def linkConfidenceProductList (links : List ChainLinkCert) : ℝ :=
  (links.map fun link => link.confidence).prod

theorem linkConfidenceProductList_nonneg (links : List ChainLinkCert) :
    0 ≤ linkConfidenceProductList links := by
  induction links with
  | nil =>
      norm_num [linkConfidenceProductList]
  | cons link rest ih =>
      simp [linkConfidenceProductList]
      exact mul_nonneg link.confidence_mem_unit.1 ih

theorem linkConfidenceProductList_le_one (links : List ChainLinkCert) :
    linkConfidenceProductList links ≤ 1 := by
  induction links with
  | nil =>
      norm_num [linkConfidenceProductList]
  | cons link rest ih =>
      simp [linkConfidenceProductList]
      have hmul :
          link.confidence * linkConfidenceProductList rest ≤ (1 : ℝ) * 1 :=
        mul_le_mul link.confidence_mem_unit.2 ih
          (linkConfidenceProductList_nonneg rest) zero_le_one
      simpa [linkConfidenceProductList] using hmul

theorem linkConfidenceProductList_append (xs ys : List ChainLinkCert) :
    linkConfidenceProductList (xs ++ ys) =
      linkConfidenceProductList xs * linkConfidenceProductList ys := by
  simp [linkConfidenceProductList, List.map_append]

/-- Confidence-loss width induced by chaining. -/
def confidenceLossWidthList (links : List ChainLinkCert) : ℝ :=
  1 - linkConfidenceProductList links

/-- Appending links never narrows the confidence-loss horizon width. -/
theorem chainConfidenceHorizon_width_monotone_append
    (xs ys : List ChainLinkCert) :
    confidenceLossWidthList xs ≤ confidenceLossWidthList (xs ++ ys) := by
  rw [confidenceLossWidthList, confidenceLossWidthList,
    linkConfidenceProductList_append]
  have hle :
      linkConfidenceProductList xs * linkConfidenceProductList ys ≤
        linkConfidenceProductList xs * 1 :=
    mul_le_mul_of_nonneg_left
      (linkConfidenceProductList_le_one ys)
      (linkConfidenceProductList_nonneg xs)
  nlinarith

/-- A fixed horizon policy: below `threshold`, the strength envelope becomes
the precommitted vacuous interval. -/
structure HorizonPolicy where
  threshold : ℝ
  threshold_mem_unit : threshold ∈ Set.Icc (0 : ℝ) 1

/-- Path-level confidence product attached to a constructed datum. -/
def pathChainConfidence {n : ℕ} (d : PathChainDatum n) : ℝ :=
  pathConfidenceProduct d.links

theorem pathChainConfidence_mem_unit {n : ℕ} (d : PathChainDatum n) :
    pathChainConfidence d ∈ Set.Icc (0 : ℝ) 1 :=
  pathConfidenceProduct_mem_unit d.links

theorem pathChainConfidence_eq_product {n : ℕ} (d : PathChainDatum n) :
    pathChainConfidence d = ∏ i, (d.links i).confidence := rfl

/-- Fixed confidence-gated horizon envelope.  The branch is chosen from
precomputed path confidence, not from whether the estimate happens to fit. -/
def horizonEnvelope {n : ℕ} (policy : HorizonPolicy) (d : PathChainDatum n) : ITV :=
  if policy.threshold ≤ pathChainConfidence d then pathCredalEnvelope d
  else unitStrengthITV

/-- A path is informative when the fixed horizon interval is not full width. -/
def chainInformative {n : ℕ} (policy : HorizonPolicy) (d : PathChainDatum n) : Prop :=
  chainEnvelopeWidth (horizonEnvelope policy d) < 1

/-- A path is vacuous when the fixed horizon interval is exactly `[0,1]`. -/
def chainVacuous {n : ℕ} (policy : HorizonPolicy) (d : PathChainDatum n) : Prop :=
  horizonEnvelope policy d = unitStrengthITV

theorem horizonEnvelope_eq_unit_of_confidence_lt
    {n : ℕ} (policy : HorizonPolicy) (d : PathChainDatum n)
    (hconf : pathChainConfidence d < policy.threshold) :
    horizonEnvelope policy d = unitStrengthITV := by
  simp [horizonEnvelope, not_le_of_gt hconf]

theorem horizonEnvelope_width_eq_one_of_confidence_lt
    {n : ℕ} (policy : HorizonPolicy) (d : PathChainDatum n)
    (hconf : pathChainConfidence d < policy.threshold) :
    chainEnvelopeWidth (horizonEnvelope policy d) = 1 := by
  rw [horizonEnvelope_eq_unit_of_confidence_lt policy d hconf,
    unitStrengthITV_width_eq_one]

theorem chainVacuous_of_confidence_lt
    {n : ℕ} (policy : HorizonPolicy) (d : PathChainDatum n)
    (hconf : pathChainConfidence d < policy.threshold) :
    chainVacuous policy d :=
  horizonEnvelope_eq_unit_of_confidence_lt policy d hconf

theorem not_chainInformative_of_confidence_lt
    {n : ℕ} (policy : HorizonPolicy) (d : PathChainDatum n)
    (hconf : pathChainConfidence d < policy.threshold) :
    ¬ chainInformative policy d := by
  intro hinfo
  rw [chainInformative,
    horizonEnvelope_width_eq_one_of_confidence_lt policy d hconf] at hinfo
  norm_num at hinfo

/-- W4 horizon crown: with this fixed policy, informativeness is exactly
confidence above threshold plus a non-vacuous underlying path envelope. -/
theorem chainInformative_iff
    {n : ℕ} (policy : HorizonPolicy) (d : PathChainDatum n) :
    chainInformative policy d ↔
      policy.threshold ≤ pathChainConfidence d ∧
        chainEnvelopeWidth (pathCredalEnvelope d) < 1 := by
  by_cases hconf : policy.threshold ≤ pathChainConfidence d
  · simp [chainInformative, horizonEnvelope, hconf]
  · have hlt : pathChainConfidence d < policy.threshold := lt_of_not_ge hconf
    constructor
    · intro hinfo
      exact False.elim (not_chainInformative_of_confidence_lt policy d hlt hinfo)
    · intro hpair
      exact False.elim (hconf hpair.1)

/-- Once the appended/extended path is past the confidence horizon, its fixed
envelope has maximal width, so no earlier horizon envelope can be wider. -/
theorem chainCredalEnvelope_width_monotone_to_vacuous
    {n m : ℕ} (policy : HorizonPolicy)
    (base : PathChainDatum n) (extended : PathChainDatum m)
    (hext : pathChainConfidence extended < policy.threshold) :
    chainEnvelopeWidth (horizonEnvelope policy base) ≤
      chainEnvelopeWidth (horizonEnvelope policy extended) := by
  rw [horizonEnvelope_width_eq_one_of_confidence_lt policy extended hext]
  exact chainEnvelopeWidth_le_one (horizonEnvelope policy base)

/-! ## R3 adapter guardrails: non-tautological scalar soundness -/

/-- A scalar chain estimator outputs a strength value. -/
structure ScalarChainEstimator where
  estimateStrengthTwoHop : TwoHopChainDatum → ℝ

/-- Soundness for a scalar estimator is envelope membership.  Its unfolding is
not a theorem crown; the content theorems below construct or refute it. -/
def ScalarEstimatorSoundOnTwoHop
    (estimator : ScalarChainEstimator) (d : TwoHopChainDatum) : Prop :=
  (chainCredalEnvelope d).lower ≤ estimator.estimateStrengthTwoHop d ∧
    estimator.estimateStrengthTwoHop d ≤ (chainCredalEnvelope d).upper

/-- The naive product strength from the product-exact constructor. -/
def naiveProductStrength (d : TwoHopChainDatum) : ℝ :=
  d.productExactness.productStrength

/-- A constructed strength point inside the two-hop chain envelope. -/
structure TwoHopEnvelopePoint (d : TwoHopChainDatum) where
  value : ℝ
  mem_chainEnvelope :
    (chainCredalEnvelope d).lower ≤ value ∧
      value ≤ (chainCredalEnvelope d).upper

namespace TwoHopEnvelopePoint

/-- The W1 composed estimate as a reusable in-envelope point. -/
def composedEstimate (d : TwoHopChainDatum) : TwoHopEnvelopePoint d where
  value := twoHopComposedEstimate d
  mem_chainEnvelope := twoHopChainComposition_mem_credalEnvelope d

/-- The midpoint representative of the fixed chain envelope. -/
def midpoint (d : TwoHopChainDatum) : TwoHopEnvelopePoint d where
  value := (chainCredalEnvelope d).strength
  mem_chainEnvelope := itv_strength_mem_bounds (chainCredalEnvelope d)

end TwoHopEnvelopePoint

/-- A scalar estimator built by selecting between a certified chain-envelope
point and the chain envelope midpoint. -/
def calibratedSelectorScalarEstimator
    (selector : EnvelopeSelector) (point : ∀ d, TwoHopEnvelopePoint d) :
    ScalarChainEstimator where
  estimateStrengthTwoHop :=
    fun d => selector.select (point d).value (chainCredalEnvelope d).strength

/-- The canonical W2 adapter using the W1 composed estimate as its certified
primary point. -/
def calibratedComposedSelectorEstimator
    (selector : EnvelopeSelector) : ScalarChainEstimator :=
  calibratedSelectorScalarEstimator selector TwoHopEnvelopePoint.composedEstimate

/-- W2 positive crown: a calibrated selector gives a sound scalar estimator,
and the same calibration certificate is the finite-sample squared-loss
optimality witness for its selector weight. -/
theorem calibratedSelector_sound
    {n : ℕ} (hn : n ≠ 0)
    (sample : Fin n → SelectorSample)
    (selector : EnvelopeSelector)
    (hcal : empiricalCalibrationCondition sample selector.weight)
    (point : ∀ d, TwoHopEnvelopePoint d) :
    (∀ d, ScalarEstimatorSoundOnTwoHop
      (calibratedSelectorScalarEstimator selector point) d) ∧
      ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 →
        meanSquaredLossFixed sample selector.weight ≤
          meanSquaredLossFixed sample r := by
  constructor
  · intro d
    unfold ScalarEstimatorSoundOnTwoHop calibratedSelectorScalarEstimator
    exact selector.select_mem_ITV (chainCredalEnvelope d)
      (point d).mem_chainEnvelope
      (itv_strength_mem_bounds (chainCredalEnvelope d))
  · intro r hr
    exact empiricalCalibrationCondition_meanSquaredLoss_le_any_fixedWeight
      sample hn selector.weight r selector.weight_mem_unit hr hcal

/-- W2 positive constructor specialized to the W1 composed estimate. -/
theorem calibratedComposedSelector_sound
    {n : ℕ} (hn : n ≠ 0)
    (sample : Fin n → SelectorSample)
    (selector : EnvelopeSelector)
    (hcal : empiricalCalibrationCondition sample selector.weight) :
    (∀ d, ScalarEstimatorSoundOnTwoHop
      (calibratedComposedSelectorEstimator selector) d) ∧
      ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 →
        meanSquaredLossFixed sample selector.weight ≤
          meanSquaredLossFixed sample r :=
  calibratedSelector_sound hn sample selector hcal
    TwoHopEnvelopePoint.composedEstimate

/-- A calibrated selector supplies a loss-optimal weight, while envelope
membership is proved by convexity of the precomputed chain envelope. -/
theorem calibratedSelectorEstimate_mem_chainCredalEnvelope
    {n : ℕ} (hn : n ≠ 0)
    (sample : Fin n → SelectorSample)
    (selector : EnvelopeSelector)
    (hcal : empiricalCalibrationCondition sample selector.weight)
    (d : TwoHopChainDatum) {x y : ℝ}
    (hx : (chainCredalEnvelope d).lower ≤ x ∧
      x ≤ (chainCredalEnvelope d).upper)
    (hy : (chainCredalEnvelope d).lower ≤ y ∧
      y ≤ (chainCredalEnvelope d).upper) :
    ((chainCredalEnvelope d).lower ≤ selector.select x y ∧
      selector.select x y ≤ (chainCredalEnvelope d).upper) ∧
      ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 →
        meanSquaredLossFixed sample selector.weight ≤
          meanSquaredLossFixed sample r := by
  constructor
  · exact selector.select_mem_ITV (chainCredalEnvelope d) hx hy
  · intro r hr
    exact empiricalCalibrationCondition_meanSquaredLoss_le_any_fixedWeight
      sample hn selector.weight r selector.weight_mem_unit hr hcal

/-- A confidence-only estimator may change confidence, but its strength output
is fixed to the product strength. -/
structure ConfidenceOnlyEstimator where
  estimateConfidenceTwoHop : TwoHopChainDatum → ℝ
  estimateConfidence_mem_unit :
    ∀ d, estimateConfidenceTwoHop d ∈ Set.Icc (0 : ℝ) 1

namespace ConfidenceOnlyEstimator

def toScalar (_estimator : ConfidenceOnlyEstimator) : ScalarChainEstimator where
  estimateStrengthTwoHop := naiveProductStrength

end ConfidenceOnlyEstimator

/-- R3 negative theorem: changing only confidence cannot repair a strength
violation. -/
theorem confidenceOnlyEstimator_not_sound_on_strengthViolation
    (d : TwoHopChainDatum) (estimator : ConfidenceOnlyEstimator)
    (hgap : naiveProductStrength d < (chainCredalEnvelope d).lower) :
    ¬ ScalarEstimatorSoundOnTwoHop estimator.toScalar d := by
  intro hsound
  exact not_lt_of_ge hsound.1 hgap

/-- Simpler coordinate-consistent canary: a one-sided strength shrinker cannot
reach an envelope whose lower endpoint already exceeds the naive product. -/
theorem oneSidedStrengthShrinker_not_sound_on_underconfidence
    (d : TwoHopChainDatum) (shrink : ℝ → ℝ)
    (hshrink : ∀ s ∈ Set.Icc (0 : ℝ) 1, shrink s ≤ s)
    (hgap : naiveProductStrength d < (chainCredalEnvelope d).lower) :
    ¬ ((chainCredalEnvelope d).lower ≤ shrink (naiveProductStrength d) ∧
      shrink (naiveProductStrength d) ≤ (chainCredalEnvelope d).upper) := by
  intro hmem
  have hunit : naiveProductStrength d ∈ Set.Icc (0 : ℝ) 1 :=
    d.productExactness.productStrength_mem_unit
  have hle : shrink (naiveProductStrength d) ≤ naiveProductStrength d :=
    hshrink (naiveProductStrength d) hunit
  nlinarith

end

end Mettapedia.PLN.InferenceControl.CertifiedChaining.DependenceAwareChainComposition
