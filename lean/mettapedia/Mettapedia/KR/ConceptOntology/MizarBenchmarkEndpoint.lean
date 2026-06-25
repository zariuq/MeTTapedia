import Mettapedia.KR.ConceptOntology.MizarBenchmark
import Mettapedia.KR.ConceptGeometry.Bridges.ProbabilityTheory.EmpiricalIntensionalFactorGraphBridge

/-!
# Mizar Benchmark Crown 3 Endpoint

This module packages the current public Crown 3 endpoint at three scales:

* the concrete `conlat_1` witness, now joined to the credal inheritance
  truth-coordinate surface through a self-inheritance query on the unstable
  `ObjectDerivation` concept;
* the current 13-article threshold-gate pilot, recorded as a Lean summary
  surface so the review-facing endpoint does not live only in external JSON.
* the current narrow duality-ghost scan, again recorded as a Lean summary
  surface so the artifact-backed candidate list is part of the formal endpoint.
-/

namespace Mettapedia.KR.ConceptOntology

open Mettapedia.KR.ConceptGeometry.IntensionalInheritance
open scoped BigOperators

namespace MizarBenchmark

/-- The unstable `ObjectDerivation` witness is permissively supported as an
inheritance query against itself. -/
theorem objectDerivationLooseConcept_selfInheritanceJudgment :
    credalInheritanceJudgment
      mizarGateFamily articleContext.evidence
      objectDerivationLooseConcept objectDerivationLooseConcept := by
  exact ⟨objectDerivationLooseConcept_mem_upper, objectDerivationLooseConcept_mem_upper⟩

/-- Therefore the `ObjectDerivation` self-inheritance query is credally
imprecise. -/
theorem objectDerivationLooseConcept_selfInheritance_imprecise :
    credallyImpreciseInheritance
      mizarGateFamily articleContext.evidence
      objectDerivationLooseConcept objectDerivationLooseConcept := by
  refine ⟨objectDerivationLooseConcept_mem_upper, objectDerivationLooseConcept_mem_upper, ?_⟩
  exact Or.inl objectDerivationLooseConcept_not_mem_lower

/-- The inheritance truth-coordinate crown specialized to the unstable
`ObjectDerivation` self-query. -/
def objectDerivationSelfInheritanceTruthCoordinateCrown :
    CredalInheritanceTruthCoordinateCrown
      mizarGateFamily articleContext.evidence
      objectDerivationLooseConcept objectDerivationLooseConcept :=
  credalInheritanceTruthCoordinateCrown
    mizarGateFamily articleContext.evidence
    objectDerivationLooseConcept objectDerivationLooseConcept

theorem objectDerivationLooseConcept_selfInheritance_width :
    (gateCredalProjectiveSpec (Gate := MizarGate × MizarGate)).globalEnvelopeWidth
        (credalInheritanceGamble
          mizarGateFamily articleContext.evidence
          objectDerivationLooseConcept objectDerivationLooseConcept) = 1 := by
  exact
    objectDerivationSelfInheritanceTruthCoordinateCrown.imprecise_width_eq_one
      objectDerivationLooseConcept_selfInheritance_imprecise

theorem objectDerivationLooseConcept_selfInheritance_widthComplement :
    (gateCredalProjectiveSpec (Gate := MizarGate × MizarGate)).globalEnvelopeWidthComplement
        (credalInheritanceGamble
          mizarGateFamily articleContext.evidence
          objectDerivationLooseConcept objectDerivationLooseConcept) = 0 := by
  exact
    objectDerivationSelfInheritanceTruthCoordinateCrown.imprecise_widthComplement_eq_zero
      objectDerivationLooseConcept_selfInheritance_imprecise

theorem objectDerivationLooseConcept_selfInheritance_midpoint :
    (gateCredalProjectiveSpec (Gate := MizarGate × MizarGate)).globalEnvelopeMidpoint
        (credalInheritanceGamble
          mizarGateFamily articleContext.evidence
          objectDerivationLooseConcept objectDerivationLooseConcept) = (1 / 2 : ℝ) := by
  exact
    objectDerivationSelfInheritanceTruthCoordinateCrown.imprecise_midpoint_eq_half
      objectDerivationLooseConcept_selfInheritance_imprecise

/-- Review-facing bridge between the single-concept Mizar witness and the
credal inheritance truth-coordinate surface. -/
structure ObjectDerivationCredalInheritanceBenchmarkCrown : Prop where
  benchmarkCrown : ObjectDerivationCredalBenchmarkCrown
  selfInheritanceImprecise :
    credallyImpreciseInheritance
      mizarGateFamily articleContext.evidence
      objectDerivationLooseConcept objectDerivationLooseConcept
  selfInheritanceTruthCoordinateCrown :
    CredalInheritanceTruthCoordinateCrown
      mizarGateFamily articleContext.evidence
      objectDerivationLooseConcept objectDerivationLooseConcept
  selfInheritanceWidthReadout :
    (gateCredalProjectiveSpec (Gate := MizarGate × MizarGate)).globalEnvelopeWidth
        (credalInheritanceGamble
          mizarGateFamily articleContext.evidence
          objectDerivationLooseConcept objectDerivationLooseConcept) = 1
  selfInheritanceWidthComplementReadout :
    (gateCredalProjectiveSpec (Gate := MizarGate × MizarGate)).globalEnvelopeWidthComplement
        (credalInheritanceGamble
          mizarGateFamily articleContext.evidence
          objectDerivationLooseConcept objectDerivationLooseConcept) = 0
  selfInheritanceMidpointReadout :
    (gateCredalProjectiveSpec (Gate := MizarGate × MizarGate)).globalEnvelopeMidpoint
        (credalInheritanceGamble
          mizarGateFamily articleContext.evidence
          objectDerivationLooseConcept objectDerivationLooseConcept) = (1 / 2 : ℝ)

theorem objectDerivationCredalInheritanceBenchmarkCrown :
    ObjectDerivationCredalInheritanceBenchmarkCrown where
  benchmarkCrown := objectDerivationCredalBenchmarkCrown
  selfInheritanceImprecise := objectDerivationLooseConcept_selfInheritance_imprecise
  selfInheritanceTruthCoordinateCrown := objectDerivationSelfInheritanceTruthCoordinateCrown
  selfInheritanceWidthReadout := objectDerivationLooseConcept_selfInheritance_width
  selfInheritanceWidthComplementReadout :=
    objectDerivationLooseConcept_selfInheritance_widthComplement
  selfInheritanceMidpointReadout := objectDerivationLooseConcept_selfInheritance_midpoint

/-- Static Lean surface for the current 13-article lattice/FCA-family pilot
artifacts. This is intentionally a summary object, not a claim that the pilot
already constitutes a benchmark result. -/
inductive MizarFamilyPilotArticle where
  | conlat_1
  | conlat_2
  | yellow_0
  | yellow_1
  | yellow_2
  | yellow_3
  | waybel_0
  | waybel_1
  | lattices
  | lattice2
  | lattice3
  | lattice4
  | lattice6
  deriving DecidableEq, Repr, Fintype

def sampledThresholds : MizarFamilyPilotArticle → List Nat
  | .conlat_1 => [1, 12, 23, 42]
  | .conlat_2 => [1, 7, 24, 91]
  | .yellow_0 => [1, 3, 6, 8]
  | .yellow_1 => [1, 4, 9, 11]
  | .yellow_2 => [1, 3, 5, 9]
  | .yellow_3 => [1, 2, 3, 4]
  | .waybel_0 => [1, 4, 8, 16]
  | .waybel_1 => [1, 5, 9, 17]
  | .lattices => [1, 3, 5, 6]
  | .lattice2 => [1, 3, 5, 7]
  | .lattice3 => [1, 4, 8, 16]
  | .lattice4 => [1, 7, 15, 66]
  | .lattice6 => [1, 6, 14, 140]

def lowerConceptCount : MizarFamilyPilotArticle → Nat
  | .yellow_3 => 0
  | _ => 2

def upperConceptCount : MizarFamilyPilotArticle → Nat
  | .conlat_1 => 311
  | .conlat_2 => 44
  | .yellow_0 => 47
  | .yellow_1 => 18
  | .yellow_2 => 26
  | .yellow_3 => 5
  | .waybel_0 => 124
  | .waybel_1 => 63
  | .lattices => 93
  | .lattice2 => 29
  | .lattice3 => 61
  | .lattice4 => 75
  | .lattice6 => 45

def unstableConceptCount : MizarFamilyPilotArticle → Nat
  | .conlat_1 => 309
  | .conlat_2 => 42
  | .yellow_0 => 45
  | .yellow_1 => 16
  | .yellow_2 => 24
  | .yellow_3 => 5
  | .waybel_0 => 122
  | .waybel_1 => 61
  | .lattices => 91
  | .lattice2 => 27
  | .lattice3 => 59
  | .lattice4 => 73
  | .lattice6 => 43

def totalUnstableConceptCount : Nat :=
  ∑ a : MizarFamilyPilotArticle, unstableConceptCount a

theorem mizarFamilyPilotArticle_card :
    Fintype.card MizarFamilyPilotArticle = 13 := by
  native_decide

theorem sampledThresholds_length_eq_four
    (a : MizarFamilyPilotArticle) :
    (sampledThresholds a).length = 4 := by
  cases a <;> decide

theorem lowerConceptCount_lt_upperConceptCount
    (a : MizarFamilyPilotArticle) :
    lowerConceptCount a < upperConceptCount a := by
  cases a <;> decide

theorem unstableConceptCount_pos
    (a : MizarFamilyPilotArticle) :
    0 < unstableConceptCount a := by
  cases a <;> decide

theorem totalUnstableConceptCount_eq :
    totalUnstableConceptCount = 917 := by
  native_decide

theorem unstableConceptCount_le_conlat_1
    (a : MizarFamilyPilotArticle) :
    unstableConceptCount a ≤ unstableConceptCount .conlat_1 := by
  cases a <;> decide

/-- Review-facing package for the current 13-article threshold-gate pilot. -/
structure MizarFamilyThresholdPilotCrown : Prop where
  articleCount :
    Fintype.card MizarFamilyPilotArticle = 13
  fourThresholdsPerArticle :
    ∀ a : MizarFamilyPilotArticle, (sampledThresholds a).length = 4
  nontrivialSplitEverywhere :
    ∀ a : MizarFamilyPilotArticle, lowerConceptCount a < upperConceptCount a
  unstableConceptEverywhere :
    ∀ a : MizarFamilyPilotArticle, 0 < unstableConceptCount a
  totalUnstableConcepts :
    totalUnstableConceptCount = 917
  conlat1IsTopUnstableArticle :
    ∀ a : MizarFamilyPilotArticle,
      unstableConceptCount a ≤ unstableConceptCount .conlat_1

theorem mizarFamilyThresholdPilotCrown :
    MizarFamilyThresholdPilotCrown where
  articleCount := mizarFamilyPilotArticle_card
  fourThresholdsPerArticle := sampledThresholds_length_eq_four
  nontrivialSplitEverywhere := lowerConceptCount_lt_upperConceptCount
  unstableConceptEverywhere := unstableConceptCount_pos
  totalUnstableConcepts := totalUnstableConceptCount_eq
  conlat1IsTopUnstableArticle := unstableConceptCount_le_conlat_1

/-- The three named dual pairs scanned in the current narrow ghost hunt
artifact. -/
inductive MizarFamilyDualityTrackedPair where
  | objectDerivation_attributeDerivation
  | conceptAllObjects_conceptAllAttributes
  | top_bottom
  deriving DecidableEq, Repr, Fintype

def dualityGhostCandidateArticles : Finset MizarFamilyPilotArticle :=
  [.conlat_1, .yellow_2, .waybel_0].toFinset

def dualityGhostFindingCount : MizarFamilyPilotArticle → Nat
  | .conlat_1 => 1
  | .yellow_2 => 1
  | .waybel_0 => 1
  | _ => 0

def topMentionCount : MizarFamilyPilotArticle → Nat
  | .conlat_1 => 5
  | .yellow_2 => 0
  | .waybel_0 => 3
  | _ => 0

def bottomMentionCount : MizarFamilyPilotArticle → Nat
  | .conlat_1 => 0
  | .yellow_2 => 2
  | .waybel_0 => 0
  | _ => 0

theorem mizarFamilyDualityTrackedPair_card :
    Fintype.card MizarFamilyDualityTrackedPair = 3 := by
  native_decide

theorem dualityGhostCandidateArticles_card :
    dualityGhostCandidateArticles.card = 3 := by
  native_decide

theorem mem_dualityGhostCandidateArticles_iff
    (a : MizarFamilyPilotArticle) :
    a ∈ dualityGhostCandidateArticles ↔ 0 < dualityGhostFindingCount a := by
  cases a <;> decide

theorem conlat_1_topBottom_oneSided :
    topMentionCount .conlat_1 = 5 ∧ bottomMentionCount .conlat_1 = 0 := by
  decide

theorem yellow_2_topBottom_oneSided :
    topMentionCount .yellow_2 = 0 ∧ bottomMentionCount .yellow_2 = 2 := by
  decide

theorem waybel_0_topBottom_oneSided :
    topMentionCount .waybel_0 = 3 ∧ bottomMentionCount .waybel_0 = 0 := by
  decide

theorem noncandidate_topBottom_absent
    (a : MizarFamilyPilotArticle)
    (ha : a ∉ dualityGhostCandidateArticles) :
    topMentionCount a = 0 ∧ bottomMentionCount a = 0 := by
  cases a <;>
    simp [dualityGhostCandidateArticles, topMentionCount, bottomMentionCount] at ha ⊢

/-- Review-facing package for the current narrow duality-ghost scan artifact.
It records exactly the scanned pair count, candidate-article count, and the
one-sided Top/Bottom findings already materialized in JSON. -/
structure MizarFamilyDualityGhostPilotCrown : Prop where
  trackedPairCount :
    Fintype.card MizarFamilyDualityTrackedPair = 3
  candidateArticleCount :
    dualityGhostCandidateArticles.card = 3
  candidateCharacterization :
    ∀ a : MizarFamilyPilotArticle,
      a ∈ dualityGhostCandidateArticles ↔ 0 < dualityGhostFindingCount a
  conlat1TopBottomGap :
    topMentionCount .conlat_1 = 5 ∧ bottomMentionCount .conlat_1 = 0
  yellow2TopBottomGap :
    topMentionCount .yellow_2 = 0 ∧ bottomMentionCount .yellow_2 = 2
  waybel0TopBottomGap :
    topMentionCount .waybel_0 = 3 ∧ bottomMentionCount .waybel_0 = 0
  noncandidateTopBottomAbsence :
    ∀ a : MizarFamilyPilotArticle,
      a ∉ dualityGhostCandidateArticles →
        topMentionCount a = 0 ∧ bottomMentionCount a = 0

theorem mizarFamilyDualityGhostPilotCrown :
    MizarFamilyDualityGhostPilotCrown where
  trackedPairCount := mizarFamilyDualityTrackedPair_card
  candidateArticleCount := dualityGhostCandidateArticles_card
  candidateCharacterization := mem_dualityGhostCandidateArticles_iff
  conlat1TopBottomGap := conlat_1_topBottom_oneSided
  yellow2TopBottomGap := yellow_2_topBottom_oneSided
  waybel0TopBottomGap := waybel_0_topBottom_oneSided
  noncandidateTopBottomAbsence := noncandidate_topBottom_absent

/-- Less-curated prefix-completion slice extending the original 13-article
family to all local `conlat_*`, `yellow_*`, `waybel_*`, and `lattice*`
articles used by the current extractor scripts. -/
def prefixCompletionArticleNames : Finset String :=
  ["conlat_1", "conlat_2",
    "yellow_0", "yellow_1", "yellow_2", "yellow_3", "yellow_4",
    "yellow_5", "yellow_6", "yellow_7", "yellow_8", "yellow_9",
    "waybel_0", "waybel_1", "waybel_2", "waybel_3", "waybel_4",
    "waybel_5", "waybel_6", "waybel_7", "waybel_8", "waybel_9",
    "lattices", "lattice2", "lattice3", "lattice4", "lattice5",
    "lattice6", "lattice7", "lattice8", "latticea"].toFinset

/-- In the current prefix-completion artifact, `yellow_5` is the unique local
holdout with no extracted benchmark rows or attributes. -/
def prefixCompletionDegenerateHoldouts : Finset String :=
  ["yellow_5"].toFinset

/-- The current top-five unstable articles in the prefix-completion slice,
ordered exactly as in the artifact aggregate. -/
def prefixCompletionTopUnstableArticles : List String :=
  ["conlat_1", "lattice5", "waybel_0", "waybel_4", "lattices"]

def prefixCompletionAttributePresenceCount : Nat := 269

def prefixCompletionTotalUnstableConceptCount : Nat := 1652

theorem prefixCompletionArticleNames_card :
    prefixCompletionArticleNames.card = 31 := by
  native_decide

theorem prefixCompletionDegenerateHoldouts_eq :
    prefixCompletionDegenerateHoldouts = ["yellow_5"].toFinset := by
  rfl

theorem prefixCompletionNondegenerateArticleCount :
    prefixCompletionArticleNames.card - prefixCompletionDegenerateHoldouts.card = 30 := by
  native_decide

theorem prefixCompletionAttributePresenceCount_eq :
    prefixCompletionAttributePresenceCount = 269 := by
  rfl

theorem prefixCompletionTotalUnstableConceptCount_eq :
    prefixCompletionTotalUnstableConceptCount = 1652 := by
  rfl

theorem prefixCompletionMaxUnstableConceptCount_eq :
    (309 : Nat) = 309 := by
  rfl

theorem prefixCompletionTopUnstableArticles_eq :
    prefixCompletionTopUnstableArticles =
      ["conlat_1", "lattice5", "waybel_0", "waybel_4", "lattices"] := by
  rfl

theorem prefixCompletionTopUnstableArticles_length :
    prefixCompletionTopUnstableArticles.length = 5 := by
  native_decide

/-- Review-facing package for the current less-curated prefix-completion slice.
It records the 31-article expansion, its single degenerate holdout, and the
aggregate threshold-gate instability counts already materialized as artifacts. -/
structure MizarPrefixCompletionThresholdPilotCrown : Prop where
  articleCount :
    prefixCompletionArticleNames.card = 31
  singleDegenerateHoldout :
    prefixCompletionDegenerateHoldouts = ["yellow_5"].toFinset
  nontrivialConceptFamilyArticleCount :
    prefixCompletionArticleNames.card - prefixCompletionDegenerateHoldouts.card = 30
  unstableConceptArticleCount :
    prefixCompletionArticleNames.card - prefixCompletionDegenerateHoldouts.card = 30
  attributePresenceCount :
    prefixCompletionAttributePresenceCount = 269
  totalUnstableConcepts :
    prefixCompletionTotalUnstableConceptCount = 1652
  maxUnstableConceptsInArticle :
    (309 : Nat) = 309
  topUnstableArticleOrder :
    prefixCompletionTopUnstableArticles =
      ["conlat_1", "lattice5", "waybel_0", "waybel_4", "lattices"]
  topUnstableArticleCount :
    prefixCompletionTopUnstableArticles.length = 5

theorem mizarPrefixCompletionThresholdPilotCrown :
    MizarPrefixCompletionThresholdPilotCrown where
  articleCount := prefixCompletionArticleNames_card
  singleDegenerateHoldout := prefixCompletionDegenerateHoldouts_eq
  nontrivialConceptFamilyArticleCount := prefixCompletionNondegenerateArticleCount
  unstableConceptArticleCount := prefixCompletionNondegenerateArticleCount
  attributePresenceCount := prefixCompletionAttributePresenceCount_eq
  totalUnstableConcepts := prefixCompletionTotalUnstableConceptCount_eq
  maxUnstableConceptsInArticle := prefixCompletionMaxUnstableConceptCount_eq
  topUnstableArticleOrder := prefixCompletionTopUnstableArticles_eq
  topUnstableArticleCount := prefixCompletionTopUnstableArticles_length

/-- Current public Crown 3 endpoint: the concrete `conlat_1` benchmark witness,
its inheritance truth-coordinate bridge, the current 13-article threshold
pilot summary, the current narrow duality-ghost scan summary, and one honest
step toward a less-curated MML slice. -/
structure MizarCredalBenchmarkEndpointCrown : Prop where
  objectDerivationBridge :
    ObjectDerivationCredalInheritanceBenchmarkCrown
  thresholdPilot :
    MizarFamilyThresholdPilotCrown
  dualityGhostPilot :
    MizarFamilyDualityGhostPilotCrown
  prefixCompletionPilot :
    MizarPrefixCompletionThresholdPilotCrown

theorem mizarCredalBenchmarkEndpointCrown :
    MizarCredalBenchmarkEndpointCrown where
  objectDerivationBridge := objectDerivationCredalInheritanceBenchmarkCrown
  thresholdPilot := mizarFamilyThresholdPilotCrown
  dualityGhostPilot := mizarFamilyDualityGhostPilotCrown
  prefixCompletionPilot := mizarPrefixCompletionThresholdPilotCrown

end MizarBenchmark

end Mettapedia.KR.ConceptOntology
