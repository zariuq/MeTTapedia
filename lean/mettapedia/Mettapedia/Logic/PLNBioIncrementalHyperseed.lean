import Mettapedia.Logic.PLNBioHypothesisGeneration
import Mettapedia.Logic.WorldModel
import Mettapedia.Hyperseed.Basic

/-!
# Incremental Bio Hyperseed Example

Small genomics-style incremental observation fixture built on the new WM /
sufficient-statistics foundation:

- observations seed mechanism queries through `Hyperseed.traceSeed`,
- Hyperseed closure derives relevance hypotheses,
- the induced sufficient-statistics world model keeps exact observation counts.

This is intentionally not the full ProbLog compilation lane. It demonstrates the
incremental use-case that static noisy-OR semantics does not capture directly:
the same hypothesis can remain derivable while its evidential payload grows as
more observations arrive.
-/

namespace Mettapedia.Logic.PLNBioIncrementalHyperseed

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.ProbLogDistributionSemantics
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelAdditive
open Mettapedia.Logic.PLNWorldModelFixpointClosure
open Mettapedia.Logic.PLNNoisyOr
open Mettapedia.Logic.SufficientStatisticSurface
open Mettapedia.Logic.PLNBioHypothesisGeneration
open Mettapedia.Hyperseed
open scoped ENNReal

inductive CandidatePair where
  | pairA
  | pairB
  deriving DecidableEq, Fintype

inductive Mechanism where
  | regulatory
  | eqtl
  | abc
  deriving DecidableEq, Fintype

structure BioObservation where
  pair : CandidatePair
  mechanism : Mechanism
  deriving DecidableEq, Fintype

inductive BioQuery where
  | mechanism : CandidatePair → Mechanism → BioQuery
  | relevant : CandidatePair → BioQuery
  deriving DecidableEq, Fintype

def unitPositiveEvidence : BinaryEvidence :=
  { pos := 1, neg := 0 }

def unitNegativeEvidence : BinaryEvidence :=
  { pos := 0, neg := 1 }

def queryPair : BioQuery → CandidatePair
  | .mechanism p _ => p
  | .relevant p => p

/-- Every observation contributes one count unit to every query, but it does so
as positive evidence exactly for the matching candidate and as negative evidence
otherwise. This keeps the WM count/confidence contract available while still
letting candidate-specific strengths differ. -/
def bioSurface : SufficientStatisticSurface BioObservation BioQuery BinaryEvidence where
  observe o q := if o.pair = queryPair q then unitPositiveEvidence else unitNegativeEvidence

theorem bioSurface_unitObservation :
    UnitObservation bioSurface := by
  intro o q
  by_cases h : o.pair = queryPair q
  · simp [bioSurface, h,
      Mettapedia.Logic.ConjugateEvidenceSurface.instConjugateEvidenceBeta,
      unitPositiveEvidence]
  · simp [bioSurface, h,
      Mettapedia.Logic.ConjugateEvidenceSurface.instConjugateEvidenceBeta,
      unitNegativeEvidence]

noncomputable instance : EvidenceType (Multiset BioObservation) :=
  multisetEvidenceType BioObservation

noncomputable instance : BinaryWorldModel (Multiset BioObservation) BioQuery :=
  worldModelOfAtomicEvidence bioSurface.observe

noncomputable instance : WorldModel (Multiset BioObservation) BioQuery BinaryEvidence :=
  bioSurface.inducedWorldModel

private noncomputable abbrev bioWMEvidence : Multiset BioObservation → BioQuery → BinaryEvidence :=
  (inferInstance : WorldModel (Multiset BioObservation) BioQuery BinaryEvidence).evidence

theorem bioSurface_observe_eq_of_samePair
    (o : BioObservation) {q₁ q₂ : BioQuery}
    (hpair : queryPair q₁ = queryPair q₂) :
    bioSurface.observe o q₁ = bioSurface.observe o q₂ := by
  cases q₁ <;> cases q₂ <;> cases hpair <;> rfl

theorem bioSurface_aggregate_eq_of_samePair
    (σ : Multiset BioObservation) {q₁ q₂ : BioQuery}
    (hpair : queryPair q₁ = queryPair q₂) :
    aggregate bioSurface σ q₁ = aggregate bioSurface σ q₂ := by
  cases q₁ <;> cases q₂ <;> cases hpair <;> rfl

theorem bioQueryEq_mechanism_relevant
    (p : CandidatePair) (m : Mechanism) :
    WMQueryEq (State := Multiset BioObservation) (Query := BioQuery)
      (.mechanism p m) (.relevant p) := by
  intro σ
  change additiveExtension bioSurface.observe σ (.mechanism p m) =
      additiveExtension bioSurface.observe σ (.relevant p)
  rw [← aggregate_eq_additiveExtension (S := bioSurface),
    ← aggregate_eq_additiveExtension (S := bioSurface)]
  exact bioSurface_aggregate_eq_of_samePair σ rfl

abbrev relevanceRule (p : CandidatePair) (m : Mechanism) :
    WMConsequenceRuleOn (Multiset BioObservation) BioQuery where
  side := fun _ => True
  premise := .mechanism p m
  conclusion := .relevant p
  sound := by
    intro σ _
    have hEq :=
      WMQueryEq.to_queryStrength
        (State := Multiset BioObservation) (Query := BioQuery)
        (bioQueryEq_mechanism_relevant p m) σ
    simp [hEq]

def bioRules : RulePool bioSurface :=
  { r | ∃ p m, r = relevanceRule p m }

theorem relevanceRule_mem_bioRules
    (p : CandidatePair) (m : Mechanism) :
    relevanceRule p m ∈ bioRules := by
  exact ⟨p, m, rfl⟩

/-- Frontier seeding from concrete biological observations to mechanism queries. -/
def bioFrontier (o : BioObservation) : Set BioQuery :=
  { .mechanism o.pair o.mechanism }

def obsAEqtl : BioObservation :=
  ⟨.pairA, .eqtl⟩

def obsAAbc : BioObservation :=
  ⟨.pairA, .abc⟩

def obsBEqtl : BioObservation :=
  ⟨.pairB, .eqtl⟩

def pairABatch₁ : Multiset BioObservation := {obsAEqtl}

def pairABatch₂ : Multiset BioObservation := {obsAAbc}

def pairATrace : Multiset BioObservation := pairABatch₁ + pairABatch₂

def pairBTrace : Multiset BioObservation := {obsBEqtl}

def pairARepeatEqtlTrace : Multiset BioObservation := pairABatch₁ + pairABatch₁

/-- Static ProbLog-style view of a trace: whether the trace contains at least one
instance of a mechanism for a candidate pair. Multiplicity is intentionally
forgotten here. -/
def supportsMechanism
    (σ : Multiset BioObservation) (p : CandidatePair) (m : Mechanism) : Prop :=
  ∃ o ∈ σ, o.pair = p ∧ o.mechanism = m

def bioMechanismOfIndex : Fin 3 → Mechanism
  | ⟨0, _⟩ => .regulatory
  | ⟨1, _⟩ => .eqtl
  | ⟨2, _⟩ => .abc

noncomputable def bioMechanismWeight : Mechanism → ℝ≥0∞
  | .regulatory => bioWeights regulatoryEffect
  | .eqtl => bioWeights eqtlAssociation
  | .abc => bioWeights activityByContact

theorem bioMechanismWeight_le_one (m : Mechanism) :
    bioMechanismWeight m ≤ 1 := by
  cases m
  · simpa [bioMechanismWeight, regulatoryEffect] using
      (bioWeights_le_one regulatoryEffect)
  · simpa [bioMechanismWeight, eqtlAssociation] using
      (bioWeights_le_one eqtlAssociation)
  · simpa [bioMechanismWeight, activityByContact] using
      (bioWeights_le_one activityByContact)

/-- Project a trace onto the static three-mechanism ProbLog weight profile. -/
noncomputable def projectedBioWeights
    (p : CandidatePair) (σ : Multiset BioObservation) : ProbAssignment 3 := by
  classical
  intro i
  exact
    if supportsMechanism σ p (bioMechanismOfIndex i)
    then bioMechanismWeight (bioMechanismOfIndex i)
    else 0

theorem projectedBioWeights_le_one
    (p : CandidatePair) (σ : Multiset BioObservation) :
    ∀ i : Fin 3, projectedBioWeights p σ i ≤ 1 := by
  classical
  intro i
  by_cases h : supportsMechanism σ p (bioMechanismOfIndex i)
  · simpa [projectedBioWeights, h] using
      (bioMechanismWeight_le_one (bioMechanismOfIndex i))
  · simp [projectedBioWeights, h]

/-- Static ProbLog-style score for one candidate pair on the observed trace. -/
noncomputable def staticBioScore
    (p : CandidatePair) (σ : Multiset BioObservation) : ℝ :=
  (queryProb (projectedBioWeights p σ) geneRelevantQuery).toReal

theorem staticBioScore_eq_noisyOr
    (p : CandidatePair) (σ : Multiset BioObservation) :
    staticBioScore p σ =
      noisyOrMulti
        (List.ofFn
          (fun i : Fin 3 => (projectedBioWeights p σ i).toReal)) := by
  unfold staticBioScore
  have hq : geneRelevantQuery = anyTrue (List.finRange 3) := by
    unfold geneRelevantQuery regulatoryEffect eqtlAssociation activityByContact anyTrue
    funext w
    simp [List.finRange, List.any]
  rw [hq]
  exact
    queryProb_anyTrue_toReal_eq_noisyOrMulti
      (projectedBioWeights p σ) (projectedBioWeights_le_one p σ) (by norm_num)

/-- Support-profile quotient of the raw observation state for one candidate pair:
the finite set of biological mechanisms observed at least once for that pair. -/
noncomputable def supportProfile
    (p : CandidatePair) (σ : Multiset BioObservation) : Finset Mechanism := by
  classical
  exact Finset.univ.filter (fun m => supportsMechanism σ p m)

@[simp] theorem mem_supportProfile
    (p : CandidatePair) (σ : Multiset BioObservation) (m : Mechanism) :
    m ∈ supportProfile p σ ↔ supportsMechanism σ p m := by
  classical
  simp [supportProfile]

theorem supportsMechanism_add
    (σ₁ σ₂ : Multiset BioObservation) (p : CandidatePair) (m : Mechanism) :
    supportsMechanism (σ₁ + σ₂) p m ↔
      supportsMechanism σ₁ p m ∨ supportsMechanism σ₂ p m := by
  constructor
  · rintro ⟨o, ho, hp, hm⟩
    rw [Multiset.mem_add] at ho
    rcases ho with ho | ho
    · exact Or.inl ⟨o, ho, hp, hm⟩
    · exact Or.inr ⟨o, ho, hp, hm⟩
  · intro h
    rcases h with h | h
    · rcases h with ⟨o, ho, hp, hm⟩
      exact ⟨o, by simpa [Multiset.mem_add] using Or.inl ho, hp, hm⟩
    · rcases h with ⟨o, ho, hp, hm⟩
      exact ⟨o, by simpa [Multiset.mem_add] using Or.inr ho, hp, hm⟩

theorem supportProfile_add
    (p : CandidatePair) (σ₁ σ₂ : Multiset BioObservation) :
    supportProfile p (σ₁ + σ₂) = supportProfile p σ₁ ∪ supportProfile p σ₂ := by
  classical
  ext m
  simp [supportsMechanism_add]

/-- Static ProbLog-style weights derived from a support profile. -/
noncomputable def projectedBioWeightsOfSupportProfile
    (profile : Finset Mechanism) : ProbAssignment 3 := by
  intro i
  exact
    if bioMechanismOfIndex i ∈ profile
    then bioMechanismWeight (bioMechanismOfIndex i)
    else 0

/-- Static ProbLog-style score derived from a support profile. -/
noncomputable def staticBioScoreOfSupportProfile
    (profile : Finset Mechanism) : ℝ :=
  (queryProb (projectedBioWeightsOfSupportProfile profile) geneRelevantQuery).toReal

theorem projectedBioWeights_eq_projectedBioWeightsOfSupportProfile
    (p : CandidatePair) (σ : Multiset BioObservation) :
    projectedBioWeights p σ =
      projectedBioWeightsOfSupportProfile (supportProfile p σ) := by
  classical
  funext i
  by_cases h : supportsMechanism σ p (bioMechanismOfIndex i)
  · have hm : bioMechanismOfIndex i ∈ supportProfile p σ := by
      simpa using h
    simp [projectedBioWeights, projectedBioWeightsOfSupportProfile, h, hm]
  · have hm : bioMechanismOfIndex i ∉ supportProfile p σ := by
      simpa using h
    simp [projectedBioWeights, projectedBioWeightsOfSupportProfile, h, hm]

theorem staticBioScore_eq_staticBioScoreOfSupportProfile
    (p : CandidatePair) (σ : Multiset BioObservation) :
    staticBioScore p σ =
      staticBioScoreOfSupportProfile (supportProfile p σ) := by
  unfold staticBioScore staticBioScoreOfSupportProfile
  rw [projectedBioWeights_eq_projectedBioWeightsOfSupportProfile]

theorem staticBioScore_eq_of_supportProfile_eq
    (p : CandidatePair) {σ₁ σ₂ : Multiset BioObservation}
    (hprof : supportProfile p σ₁ = supportProfile p σ₂) :
    staticBioScore p σ₁ = staticBioScore p σ₂ := by
  rw [staticBioScore_eq_staticBioScoreOfSupportProfile,
    staticBioScore_eq_staticBioScoreOfSupportProfile, hprof]

/-- Canonical evidence view for a probability weight: positive mass `w` and
complement mass `1-w`. This is the exact evidence shape needed to feed the
existing ProbLog-to-evidence noisy-OR theorem. -/
noncomputable def evidenceOfWeight (w : ℝ≥0∞) : BinaryEvidence :=
  ⟨w, 1 - w⟩

theorem evidenceOfWeight_toStrength (w : ℝ≥0∞) (hw : w ≤ 1) :
    BinaryEvidence.toStrength (evidenceOfWeight w) = w := by
  have htotal : (evidenceOfWeight w).total = 1 := by
    unfold evidenceOfWeight BinaryEvidence.total
    simpa [add_comm] using (tsub_add_cancel_of_le hw : 1 - w + w = 1)
  unfold BinaryEvidence.toStrength
  rw [if_neg]
  · rw [htotal]
    simp [evidenceOfWeight]
  · simp [htotal]

theorem projectedBioWeightsOfSupportProfile_le_one
    (profile : Finset Mechanism) :
    ∀ i : Fin 3, projectedBioWeightsOfSupportProfile profile i ≤ 1 := by
  intro i
  by_cases h : bioMechanismOfIndex i ∈ profile
  · simpa [projectedBioWeightsOfSupportProfile, h] using
      (bioMechanismWeight_le_one (bioMechanismOfIndex i))
  · simp [projectedBioWeightsOfSupportProfile, h]

/-- BinaryEvidence-coded view of a support profile, suitable for the existing
`queryProb_from_evidence` bridge. -/
noncomputable def supportProfileEvidence
    (profile : Finset Mechanism) : Fin 3 → BinaryEvidence :=
  fun i => evidenceOfWeight (projectedBioWeightsOfSupportProfile profile i)

theorem supportProfileEvidence_matches_projectedBioWeights
    (profile : Finset Mechanism) (i : Fin 3) :
    projectedBioWeightsOfSupportProfile profile i =
      BinaryEvidence.toStrength (supportProfileEvidence profile i) := by
  unfold supportProfileEvidence
  symm
  exact evidenceOfWeight_toStrength
    (projectedBioWeightsOfSupportProfile profile i)
    (projectedBioWeightsOfSupportProfile_le_one profile i)

/-- The support-profile quotient feeds directly into the existing
ProbLog-to-evidence noisy-OR bridge. -/
theorem staticBioScoreOfSupportProfile_eq_supportProfileEvidence_noisyOr
    (profile : Finset Mechanism) :
    staticBioScoreOfSupportProfile profile =
      noisyOrMulti
        (List.ofFn
          (fun i : Fin 3 =>
            (BinaryEvidence.toStrength (supportProfileEvidence profile i)).toReal)) := by
  unfold staticBioScoreOfSupportProfile
  exact queryProb_from_evidence
    (supportProfileEvidence profile)
    (projectedBioWeightsOfSupportProfile profile)
    (supportProfileEvidence_matches_projectedBioWeights profile)
    (projectedBioWeightsOfSupportProfile_le_one profile)
    (by norm_num)

/-- The full benchmark support profile recovers the original rejuve-bio
mechanism assignment exactly. -/
theorem projectedBioWeightsOfSupportProfile_univ_eq_bioWeights :
    projectedBioWeightsOfSupportProfile (Finset.univ : Finset Mechanism) =
      bioWeights := by
  funext i
  fin_cases i <;>
    simp [projectedBioWeightsOfSupportProfile, bioMechanismOfIndex,
      bioMechanismWeight, bioWeights]

theorem staticBioScoreOfSupportProfile_univ_eq_bioBenchmark :
    staticBioScoreOfSupportProfile (Finset.univ : Finset Mechanism) =
      (queryProb bioWeights geneRelevantQuery).toReal := by
  unfold staticBioScoreOfSupportProfile
  rw [projectedBioWeightsOfSupportProfile_univ_eq_bioWeights]

/-- Direct comparison with the existing specialized bio theorem:
the rejuve-bio benchmark score is exactly the noisy-OR over the support-profile
evidence view when all three benchmark mechanisms are present. -/
theorem bio_queryProb_from_evidence_via_supportProfile_univ :
    (queryProb bioWeights geneRelevantQuery).toReal =
      noisyOrMulti
        (List.ofFn
          (fun i : Fin 3 =>
            (BinaryEvidence.toStrength
              (supportProfileEvidence (Finset.univ : Finset Mechanism) i)).toReal)) := by
  have hp_match :
      ∀ i : Fin 3,
        bioWeights i =
          BinaryEvidence.toStrength
            (supportProfileEvidence (Finset.univ : Finset Mechanism) i) := by
    intro i
    calc
      bioWeights i =
          projectedBioWeightsOfSupportProfile (Finset.univ : Finset Mechanism) i := by
            symm
            exact congrArg (fun f => f i) projectedBioWeightsOfSupportProfile_univ_eq_bioWeights
      _ =
          BinaryEvidence.toStrength
            (supportProfileEvidence (Finset.univ : Finset Mechanism) i) := by
            exact supportProfileEvidence_matches_projectedBioWeights
              (Finset.univ : Finset Mechanism) i
  exact bio_queryProb_from_evidence
    (supportProfileEvidence (Finset.univ : Finset Mechanism)) hp_match

noncomputable def eqtlOnlyWeights : ProbAssignment 3
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => bioWeights eqtlAssociation
  | ⟨2, _⟩ => 0

noncomputable def eqtlAbcWeights : ProbAssignment 3
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => bioWeights eqtlAssociation
  | ⟨2, _⟩ => bioWeights activityByContact

theorem projectedBioWeights_pairABatch₁ :
    projectedBioWeights .pairA pairABatch₁ = eqtlOnlyWeights := by
  funext i
  fin_cases i <;>
    simp [projectedBioWeights, eqtlOnlyWeights, supportsMechanism,
      bioMechanismOfIndex, bioMechanismWeight, pairABatch₁,
      obsAEqtl, bioWeights]

theorem projectedBioWeights_pairATrace :
    projectedBioWeights .pairA pairATrace = eqtlAbcWeights := by
  funext i
  fin_cases i <;>
    simp [projectedBioWeights, eqtlAbcWeights, supportsMechanism,
      bioMechanismOfIndex, bioMechanismWeight, pairATrace, pairABatch₁,
      pairABatch₂, obsAEqtl, obsAAbc, bioWeights]

theorem projectedBioWeights_pairARepeatEqtlTrace :
    projectedBioWeights .pairA pairARepeatEqtlTrace = eqtlOnlyWeights := by
  funext i
  fin_cases i <;>
    simp [projectedBioWeights, eqtlOnlyWeights, supportsMechanism,
      bioMechanismOfIndex, bioMechanismWeight, pairARepeatEqtlTrace,
      pairABatch₁, obsAEqtl, bioWeights]

theorem pairABatch₁_supportProfile_eq_gtexOnly :
    supportProfile .pairA pairABatch₁ = ({.eqtl} : Finset Mechanism) := by
  ext m
  cases m <;>
    simp [supportProfile, supportsMechanism, pairABatch₁, obsAEqtl]

theorem pairATrace_supportProfile_eq_gtexAbc :
    supportProfile .pairA pairATrace =
      (({.eqtl} : Finset Mechanism) ∪ {.abc}) := by
  ext m
  cases m <;>
    simp [supportProfile, supportsMechanism, pairATrace, pairABatch₁,
      pairABatch₂, obsAEqtl, obsAAbc]

theorem pairABatch₁_staticBioScore_eq_gtexOnlyBenchmark :
    staticBioScore .pairA pairABatch₁ =
      (queryProb eqtlOnlyWeights geneRelevantQuery).toReal := by
  unfold staticBioScore
  rw [projectedBioWeights_pairABatch₁]

theorem pairATrace_staticBioScore_eq_gtexAbcBenchmark :
    staticBioScore .pairA pairATrace =
      (queryProb eqtlAbcWeights geneRelevantQuery).toReal := by
  unfold staticBioScore
  rw [projectedBioWeights_pairATrace]

theorem relevant_of_mem_trace
    {σ : Multiset BioObservation} {o : BioObservation}
    (ho : o ∈ σ) :
    BioQuery.relevant o.pair ∈
      closureFromTrace bioSurface bioFrontier bioRules σ := by
  have hSeed :
      BioQuery.mechanism o.pair o.mechanism ∈ traceSeed bioFrontier σ := by
    exact ⟨o, ho, by simp [bioFrontier]⟩
  have hPrem :
      BioQuery.mechanism o.pair o.mechanism ∈
        closureFromTrace bioSurface bioFrontier bioRules σ := by
    exact
      seed_subset_closureFromTrace bioSurface bioFrontier bioRules σ hSeed
  exact
    leastRuleClosure_rule_closed
      (R := bioRules)
      (W := σ)
      (seed := traceSeed bioFrontier σ)
      (r := relevanceRule o.pair o.mechanism)
      (relevanceRule_mem_bioRules o.pair o.mechanism)
      trivial
      hPrem

theorem relevant_pairA_in_batch₁_closure :
    BioQuery.relevant .pairA ∈
      closureFromTrace bioSurface bioFrontier bioRules pairABatch₁ := by
  exact relevant_of_mem_trace (σ := pairABatch₁) (o := obsAEqtl) (by simp [pairABatch₁, obsAEqtl])

theorem relevant_pairA_in_total_closure :
    BioQuery.relevant .pairA ∈
      closureFromTrace bioSurface bioFrontier bioRules pairATrace := by
  exact relevant_of_mem_trace (σ := pairATrace) (o := obsAEqtl) (by simp [pairATrace, pairABatch₁])

theorem relevant_pairB_in_closure :
    BioQuery.relevant .pairB ∈
      closureFromTrace bioSurface bioFrontier bioRules pairBTrace := by
  exact relevant_of_mem_trace (σ := pairBTrace) (o := obsBEqtl) (by simp [pairBTrace, obsBEqtl])

theorem relevant_pairA_not_in_empty_closure :
    BioQuery.relevant .pairA ∉
      closureFromTrace bioSurface bioFrontier bioRules (0 : Multiset BioObservation) := by
  have hSub :
      closureFromTrace bioSurface bioFrontier bioRules (0 : Multiset BioObservation) ⊆
        (∅ : Set BioQuery) := by
    exact
      leastRuleClosure_least_of_seed_and_rules
        (R := bioRules)
        (W := (0 : Multiset BioObservation))
        (seed := traceSeed bioFrontier (0 : Multiset BioObservation))
        (S := (∅ : Set BioQuery))
        (by simp [traceSeed])
        (by
          intro r hr _ hprem
          cases hprem)
  intro hmem
  exact hSub hmem

theorem relevant_pairA_discovered_by_card :
    BioQuery.relevant .pairA ∈
      cascadeFromTrace bioSurface bioFrontier bioRules pairATrace (Fintype.card BioQuery) := by
  exact
    (mem_closureFromTrace_iff_mem_cascade_card_of_finite
      bioSurface bioFrontier bioRules pairATrace (.relevant .pairA)).mp
      relevant_pairA_in_total_closure

theorem pairABatch₁_count :
    AdditiveWorldModel.queryObservationCount
        (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
        pairABatch₁ (.relevant .pairA) = 1 := by
  simpa [pairABatch₁] using
    (wm_count_eq_card (S := bioSurface) bioSurface_unitObservation
      pairABatch₁ (.relevant .pairA))

theorem pairATrace_count :
    AdditiveWorldModel.queryObservationCount
        (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
        pairATrace (.relevant .pairA) = 2 := by
  simpa [pairATrace, pairABatch₁, pairABatch₂] using
    (wm_count_eq_card (S := bioSurface) bioSurface_unitObservation
      pairATrace (.relevant .pairA))

theorem pairBTrace_count :
    AdditiveWorldModel.queryObservationCount
        (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
        pairBTrace (.relevant .pairB) = 1 := by
  simpa [pairBTrace] using
    (wm_count_eq_card (S := bioSurface) bioSurface_unitObservation
      pairBTrace (.relevant .pairB))

theorem pairARepeatEqtlTrace_count :
    AdditiveWorldModel.queryObservationCount
        (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
        pairARepeatEqtlTrace (.relevant .pairA) = 2 := by
  simpa [pairARepeatEqtlTrace, pairABatch₁] using
    (wm_count_eq_card (S := bioSurface) bioSurface_unitObservation
      pairARepeatEqtlTrace (.relevant .pairA))

/-- Raw WM evidence is exactly additive across observation batches. -/
theorem bio_rawWM_evidence_add
    (σ₁ σ₂ : Multiset BioObservation) (q : BioQuery) :
    bioWMEvidence (σ₁ + σ₂) q = bioWMEvidence σ₁ q + bioWMEvidence σ₂ q := by
  simpa [bioWMEvidence] using
    (WorldModel.evidence_add'
      (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
      σ₁ σ₂ q)

/-- Concrete batchwise = bulk raw-WM theorem for the accumulated pair-A trace. -/
theorem pairATrace_rawWM_evidence_eq_batches (q : BioQuery) :
    bioWMEvidence pairATrace q =
      bioWMEvidence pairABatch₁ q + bioWMEvidence pairABatch₂ q := by
  simpa [pairATrace] using
    bio_rawWM_evidence_add pairABatch₁ pairABatch₂ q

theorem pairATrace_nontrivial :
    AdditiveWorldModel.queryObservationCount
        (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
        pairATrace (.relevant .pairA) ≠ 0 ∧
      (pairATrace + pairATrace : Multiset BioObservation) ≠ pairATrace := by
  have hTrace : pairATrace ≠ 0 := by
    simp [pairATrace, pairABatch₁, pairABatch₂]
  exact
    wm_nonempty_implies_nontrivial
      (S := bioSurface) bioSurface_unitObservation hTrace (.relevant .pairA)

theorem pairA_incremental_confidence_changes :
    AdditiveWorldModel.queryObservationConfidence
        (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
        1 pairABatch₁ (.relevant .pairA) ≠
      AdditiveWorldModel.queryObservationConfidence
        (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
        1 pairATrace (.relevant .pairA) := by
  rw [wm_confidence_eq_ratio (S := bioSurface) (κ := 1) bioSurface_unitObservation
      pairABatch₁ (.relevant .pairA),
    wm_confidence_eq_ratio (S := bioSurface) (κ := 1) bioSurface_unitObservation
      pairATrace (.relevant .pairA)]
  simp [pairABatch₁, pairATrace, pairABatch₂]
  intro hEq
  have hReal := congrArg ENNReal.toReal hEq
  norm_num at hReal

/-- Incremental result:
the same relevance hypothesis for pair A is already discovered after the first
batch and remains discovered after the second batch, but the WM evidence count
strictly increases from 1 to 2. -/
theorem pairA_incremental_relevance_persists_and_count_increases :
    BioQuery.relevant .pairA ∈
        closureFromTrace bioSurface bioFrontier bioRules pairABatch₁ ∧
      BioQuery.relevant .pairA ∈
        closureFromTrace bioSurface bioFrontier bioRules pairATrace ∧
      AdditiveWorldModel.queryObservationCount
          (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
          pairABatch₁ (.relevant .pairA) = 1 ∧
      AdditiveWorldModel.queryObservationCount
          (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
          pairATrace (.relevant .pairA) = 2 ∧
      AdditiveWorldModel.queryObservationConfidence
          (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
          1 pairABatch₁ (.relevant .pairA) ≠
        AdditiveWorldModel.queryObservationConfidence
          (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
          1 pairATrace (.relevant .pairA) := by
  exact ⟨relevant_pairA_in_batch₁_closure, relevant_pairA_in_total_closure,
    pairABatch₁_count, pairATrace_count, pairA_incremental_confidence_changes⟩

/-- Two candidate pairs can both trigger the same relevance closure pattern while
still carrying different evidential payloads. This is the key incremental
distinction that binary activation alone does not expose. -/
theorem pairA_pairB_same_discovery_different_counts :
    BioQuery.relevant .pairA ∈
        closureFromTrace bioSurface bioFrontier bioRules pairATrace ∧
      BioQuery.relevant .pairB ∈
        closureFromTrace bioSurface bioFrontier bioRules pairBTrace ∧
      AdditiveWorldModel.queryObservationCount
          (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
          pairATrace (.relevant .pairA) = 2 ∧
      AdditiveWorldModel.queryObservationCount
          (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
          pairBTrace (.relevant .pairB) = 1 := by
  exact ⟨relevant_pairA_in_total_closure, relevant_pairB_in_closure,
    pairATrace_count, pairBTrace_count⟩

theorem pairABatch₁_staticScore_lt_pairATrace_staticScore :
    staticBioScore .pairA pairABatch₁ <
      staticBioScore .pairA pairATrace := by
  rw [staticBioScore_eq_noisyOr, staticBioScore_eq_noisyOr]
  rw [projectedBioWeights_pairABatch₁, projectedBioWeights_pairATrace]
  rw [noisyOrMulti_ofFn_eq, noisyOrMulti_ofFn_eq]
  rw [Fin.prod_univ_three, Fin.prod_univ_three]
  norm_num [eqtlOnlyWeights, eqtlAbcWeights, bioWeights,
    regulatoryEffect, eqtlAssociation, activityByContact]

theorem pairARepeatEqtlTrace_staticScore_eq_pairABatch₁ :
    staticBioScore .pairA pairARepeatEqtlTrace =
      staticBioScore .pairA pairABatch₁ := by
  apply staticBioScore_eq_of_supportProfile_eq (p := .pairA)
  ext m
  cases m <;>
    simp [supportProfile, supportsMechanism, pairARepeatEqtlTrace, pairABatch₁,
      obsAEqtl]

/-- The static ProbLog-style score depends only on the support-profile quotient
of the raw observation state, not on repeated evidence multiplicity. -/
theorem staticBioScore_batches_eq_bulk
    (p : CandidatePair) (σ₁ σ₂ : Multiset BioObservation) :
    staticBioScore p (σ₁ + σ₂) =
      staticBioScoreOfSupportProfile (supportProfile p σ₁ ∪ supportProfile p σ₂) := by
  rw [staticBioScore_eq_staticBioScoreOfSupportProfile, supportProfile_add]

/-- Clean composition theorem: batchwise raw WM accumulation induces the same
final static score as bulk scoring, once we pass through the support-profile
quotient. -/
theorem pairA_incremental_rawWM_induces_bulk_staticScore :
    staticBioScore .pairA pairATrace =
      staticBioScoreOfSupportProfile
        (supportProfile .pairA pairABatch₁ ∪ supportProfile .pairA pairABatch₂) := by
  simpa [pairATrace] using
    staticBioScore_batches_eq_bulk (p := .pairA) pairABatch₁ pairABatch₂

/-- Adding a new mechanism batch changes the static ProbLog-style score, while
repeating the same mechanism leaves the static score unchanged even though the
WM evidence count increases. This shows that the incremental WM does not
collapse to the static score: it strictly refines it by remembering repeated
support. -/
theorem pairA_static_vs_incremental_comparison :
    staticBioScore .pairA pairABatch₁ <
        staticBioScore .pairA pairATrace ∧
      staticBioScore .pairA pairARepeatEqtlTrace =
        staticBioScore .pairA pairABatch₁ ∧
      AdditiveWorldModel.queryObservationCount
          (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
          pairABatch₁ (.relevant .pairA) = 1 ∧
      AdditiveWorldModel.queryObservationCount
          (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
          pairARepeatEqtlTrace (.relevant .pairA) = 2 := by
  exact ⟨pairABatch₁_staticScore_lt_pairATrace_staticScore,
    pairARepeatEqtlTrace_staticScore_eq_pairABatch₁,
    pairABatch₁_count, pairARepeatEqtlTrace_count⟩

/-- **Observation-count monotonicity**: adding more observations never decreases
the query observation count. Combined with `confidenceFromN_mono` (in
`Convergence/ConfidenceConvergence.lean`), this closes the incremental
confidence story: more observations → higher count → higher confidence. -/
theorem queryObservationCount_mono_add
    (σ₁ σ₂ : Multiset BioObservation) (q : BioQuery) :
    AdditiveWorldModel.queryObservationCount
        (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
        σ₁ q ≤
      AdditiveWorldModel.queryObservationCount
          (State := Multiset BioObservation) (Query := BioQuery) (Ev := BinaryEvidence)
          (σ₁ + σ₂) q := by
  rw [wm_count_eq_card (S := bioSurface) bioSurface_unitObservation σ₁ q,
    wm_count_eq_card (S := bioSurface) bioSurface_unitObservation (σ₁ + σ₂) q,
    Multiset.card_add]
  exact_mod_cast Nat.le_add_right σ₁.card σ₂.card

/-! ## §7 Which-Provenance → Support-Profile Bridge

The Which semiring in `ProbLogCompilation.lean` computes the set of active
probabilistic fact indices `active : Finset (Fin n)`.  For the bio instantiation,
the mapping `bioMechanismOfIndex : Fin 3 → Mechanism` is a bijection, so the
provenance active set projects exactly to the bio `supportProfile`.

This closes the loop: the abstract provenance layer (Which semiring tracking which
facts fire) and the concrete bio layer (which mechanisms are observed) compute the
same static quotient, guaranteeing that the projected weights and noisy-OR score
are identical whether derived from provenance lineage or observation traces. -/

theorem bioMechanismOfIndex_injective : Function.Injective bioMechanismOfIndex := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [bioMechanismOfIndex]

theorem bioMechanismOfIndex_surjective : Function.Surjective bioMechanismOfIndex := by
  intro m
  cases m with
  | regulatory => exact ⟨⟨0, by omega⟩, rfl⟩
  | eqtl => exact ⟨⟨1, by omega⟩, rfl⟩
  | abc => exact ⟨⟨2, by omega⟩, rfl⟩

noncomputable def bioMechanismOfIndex_equiv : Fin 3 ≃ Mechanism :=
  Equiv.ofBijective bioMechanismOfIndex
    ⟨bioMechanismOfIndex_injective, bioMechanismOfIndex_surjective⟩

/-- The set of probabilistic fact indices whose mechanisms are observed in trace σ
for candidate pair p. This is the provenance-side active set. -/
noncomputable def bioActiveFacts
    (p : CandidatePair) (σ : Multiset BioObservation) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun i => supportsMechanism σ p (bioMechanismOfIndex i))

/-- **Which-Provenance → Support-Profile Bridge**: The image of the provenance
active set under `bioMechanismOfIndex` equals the bio support profile.

This is the key theorem connecting the abstract semiring provenance layer
(Which computes `bioActiveFacts`) to the bio observation layer
(`supportProfile` tracks which mechanisms are observed). -/
theorem bioActiveFacts_image_eq_supportProfile
    (p : CandidatePair) (σ : Multiset BioObservation) :
    (bioActiveFacts p σ).image bioMechanismOfIndex = supportProfile p σ := by
  classical
  ext m
  simp only [Finset.mem_image, mem_supportProfile]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp [bioActiveFacts] at hi
    exact hi
  · intro hm
    obtain ⟨i, hi⟩ := bioMechanismOfIndex_surjective m
    refine ⟨i, ?_, hi⟩
    simp only [bioActiveFacts, Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [hi]

/-- The provenance active set determines the projected bio weights: weights
derived from the Which-provenance active set equal weights from the observation
support profile. -/
theorem projectedBioWeightsOfActiveFacts_eq_projectedBioWeights
    (p : CandidatePair) (σ : Multiset BioObservation) :
    projectedBioWeightsOfSupportProfile
        ((bioActiveFacts p σ).image bioMechanismOfIndex) =
      projectedBioWeights p σ := by
  rw [bioActiveFacts_image_eq_supportProfile,
    ← projectedBioWeights_eq_projectedBioWeightsOfSupportProfile]

/-- Provenance active set determines static score: the noisy-OR score derived
from the Which-provenance active set equals the score from observations. -/
theorem staticBioScoreOfActiveFacts_eq_staticBioScore
    (p : CandidatePair) (σ : Multiset BioObservation) :
    staticBioScoreOfSupportProfile
        ((bioActiveFacts p σ).image bioMechanismOfIndex) =
      staticBioScore p σ := by
  unfold staticBioScoreOfSupportProfile staticBioScore
  rw [projectedBioWeightsOfActiveFacts_eq_projectedBioWeights]

/-- The active-facts set is monotone under observation accumulation:
more observations can only grow the active set. -/
theorem bioActiveFacts_mono_add
    (p : CandidatePair) (σ₁ σ₂ : Multiset BioObservation) :
    bioActiveFacts p σ₁ ⊆ bioActiveFacts p (σ₁ + σ₂) := by
  classical
  intro i
  simp only [bioActiveFacts, Finset.mem_filter, Finset.mem_univ, true_and]
  intro h
  exact (supportsMechanism_add σ₁ σ₂ p (bioMechanismOfIndex i)).mpr (Or.inl h)

end Mettapedia.Logic.PLNBioIncrementalHyperseed
