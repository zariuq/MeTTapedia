import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.ConjugateEvidenceSurface
import Mettapedia.Logic.EvidenceBeta
import Mettapedia.Logic.WorldModel

/-!
# Sufficient Statistic Surface

Minimal additive observation-encoder layer over the existing generic world-model
and conjugate-evidence foundations.

This file deliberately stays below any family-specific posterior API. It only
packages the structure that Beta/Bernoulli, Dirichlet/Multinomial, and
Normal-Gamma observations already share:

- an observation encoder into an additive evidence carrier
- multiset aggregation via the generic additive extension
- observation-count / confidence transport when the carrier is conjugate

It does **not** impose a common posterior parameter interface.
-/

namespace Mettapedia.Logic

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelAdditive
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.ConjugateEvidenceSurface
open Mettapedia.Logic.EvidenceDirichlet
open Mettapedia.Logic.EvidenceNormalGamma

/-- A query-indexed observation encoder into an additive evidence carrier. -/
structure SufficientStatisticSurface (Obs Query Ev : Type*) where
  observe : Obs → Query → Ev

namespace SufficientStatisticSurface

variable {Obs Query Ev : Type*}

/-- Lift a query-independent observation statistic into a query-indexed surface. -/
def ofObservationMap (f : Obs → Ev) : SufficientStatisticSurface Obs Query Ev where
  observe o _ := f o

section Additive

variable [AddCommMonoid Ev] (S : SufficientStatisticSurface Obs Query Ev)

/-- Aggregate a multiset of observations query-wise using the generic additive
extension. -/
noncomputable def aggregate (σ : Multiset Obs) (q : Query) : Ev :=
  genAdditiveExtension S.observe σ q

@[simp] theorem aggregate_zero (q : Query) :
    aggregate S 0 q = 0 := by
  simp [aggregate]

@[simp] theorem aggregate_singleton (o : Obs) (q : Query) :
    aggregate S ({o} : Multiset Obs) q = S.observe o q := by
  simp [aggregate]

theorem aggregate_cons (o : Obs) (σ : Multiset Obs) (q : Query) :
    aggregate S (o ::ₘ σ) q = S.observe o q + aggregate S σ q := by
  simpa [aggregate] using genAdditiveExtension_cons S.observe o σ q

theorem aggregate_add (σ₁ σ₂ : Multiset Obs) (q : Query) :
    aggregate S (σ₁ + σ₂) q = aggregate S σ₁ q + aggregate S σ₂ q := by
  simpa [aggregate] using genAdditiveExtension_add S.observe σ₁ σ₂ q

/-- The aggregation induced by a sufficient-statistic surface is the canonical
generic additive extension. -/
theorem aggregate_isAdditiveExtension :
    GenIsAdditiveExtension S.observe (aggregate S) :=
  genIsAdditiveExtension_genAdditiveExtension S.observe

/-- The aggregation induced by a sufficient-statistic surface is uniquely
determined by the additive-extension laws. -/
theorem aggregate_eq_of_isAdditiveExtension
    {E : Multiset Obs → Query → Ev}
    (hE : GenIsAdditiveExtension S.observe E) :
    E = aggregate S :=
  eq_genAdditiveExtension S.observe hE

@[simp] theorem aggregate_eq_genAdditiveExtension
    (σ : Multiset Obs) (q : Query) :
    aggregate S σ q = genAdditiveExtension S.observe σ q :=
  rfl

/-- The canonical additive extension of the surface exists uniquely. -/
theorem existsUnique_aggregate :
    ∃! E : Multiset Obs → Query → Ev, GenIsAdditiveExtension S.observe E := by
  simpa [aggregate] using genExistsUnique_additiveExtension S.observe

/-- The sufficient-statistic surface induces a generic world model over multisets
of observations. -/
noncomputable def inducedWorldModel :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    AdditiveWorldModel (Multiset Obs) Query Ev :=
  AdditiveWorldModel.genericWorldModelOfAtomicEvidence S.observe

/-- The evidence extracted by the induced generic world model is exactly the
canonical additive extension of the observation encoder. -/
@[simp] theorem inducedWorldModel_evidence_eq_aggregate
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q =
      aggregate S σ q := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  rfl

/-- The induced generic world model is exactly the canonical multiset-based
additive world model on the same observation encoder. -/
@[simp] theorem inducedWorldModel_eq_genericWorldModelOfAtomicEvidence :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    (S.inducedWorldModel : AdditiveWorldModel (Multiset Obs) Query Ev) =
      AdditiveWorldModel.genericWorldModelOfAtomicEvidence S.observe := by
  rfl

/-- The evidence function of the induced world model satisfies the universal
additive-extension property. -/
theorem inducedWorldModel_evidence_isAdditiveExtension :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    GenIsAdditiveExtension S.observe
      (fun σ q =>
        letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
        AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  simpa [inducedWorldModel_evidence_eq_aggregate (S := S)] using
    aggregate_isAdditiveExtension (S := S)

/-- The evidence extracted by the induced generic world model is the canonical
generic additive extension of the atomic observation encoder. -/
@[simp] theorem inducedWorldModel_evidence_eq_genAdditiveExtension
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q =
      genAdditiveExtension S.observe σ q := by
  simp [aggregate, inducedWorldModel_evidence_eq_aggregate (S := S)]

/-- The induced generic world-model evidence is the unique additive extension of
the sufficient-statistic surface. This states the universal property directly
with the world-model extractor as witness. -/
theorem existsUnique_inducedWorldModelEvidence_additiveExtension :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    ∃! E : Multiset Obs → Query → Ev, GenIsAdditiveExtension S.observe E := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  refine ⟨
    (fun σ q =>
      letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
      AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q),
    inducedWorldModel_evidence_isAdditiveExtension (S := S),
    ?_⟩
  intro E hE
  ext σ q
  rw [aggregate_eq_of_isAdditiveExtension (S := S) hE]
  exact (inducedWorldModel_evidence_eq_aggregate (S := S) σ q).symm

/-- Any additive extension of the observation encoder agrees with the evidence
extracted by the induced world model. -/
theorem inducedWorldModel_evidence_eq_of_isAdditiveExtension
    {E : Multiset Obs → Query → Ev}
    (hE : GenIsAdditiveExtension S.observe E) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    E =
      (fun σ q =>
        letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
        AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  ext σ q
  rw [aggregate_eq_of_isAdditiveExtension (S := S) hE]
  exact (inducedWorldModel_evidence_eq_aggregate (S := S) σ q).symm

end Additive

section GenericMultisetClassification

variable {Obs Query Ev : Type*}
variable [AddCommMonoid Ev]

/-- A generic world model over multisets of observations, using the canonical
multiset revision structure. -/
abbrev MultisetGenericWorldModel (Obs Query Ev : Type*) [AddCommMonoid Ev] :=
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  AdditiveWorldModel (Multiset Obs) Query Ev

/-- Extract the singleton observation surface from a generic multiset world
model. This is the atomic observation encoder that the classification theorem
recovers. -/
def singletonSurface (G : MultisetGenericWorldModel Obs Query Ev) :
    SufficientStatisticSurface Obs Query Ev where
  observe o q :=
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := G
    AdditiveWorldModel.extract
      (State := Multiset Obs) (Query := Query) (Ev := Ev) ({o} : Multiset Obs) q

@[simp] theorem singletonSurface_observe_eq_evidence_singleton
    (G : MultisetGenericWorldModel Obs Query Ev) (o : Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := G
    (singletonSurface (Obs := Obs) (Query := Query) (Ev := Ev) G).observe o q =
      AdditiveWorldModel.extract
        (State := Multiset Obs) (Query := Query) (Ev := Ev) ({o} : Multiset Obs) q := by
  rfl

/-- A zero-preserving generic multiset world model is the additive extension of
its singleton observation surface. This is the paper-facing classification
theorem in its honest form: additivity alone does not determine `evidence 0`. -/
theorem evidence_isAdditiveExtension_of_zero
    (G : MultisetGenericWorldModel Obs Query Ev)
    (hzero :
      ∀ q,
        letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
        letI : AdditiveWorldModel (Multiset Obs) Query Ev := G
        AdditiveWorldModel.extract
          (State := Multiset Obs) (Query := Query) (Ev := Ev) (0 : Multiset Obs) q = 0) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    GenIsAdditiveExtension
      (singletonSurface (Obs := Obs) (Query := Query) (Ev := Ev) G).observe
      (fun σ q =>
        letI : AdditiveWorldModel (Multiset Obs) Query Ev := G
        AdditiveWorldModel.extract
          (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := G
  refine
    { zero := hzero
      singleton := ?_
      add := ?_ }
  · intro o q
    rfl
  · intro σ₁ σ₂ q
    exact AdditiveWorldModel.extract_add
      (State := Multiset Obs) (Query := Query) (Ev := Ev) σ₁ σ₂ q

/-- Classification theorem: a zero-preserving additive generic multiset world
model is recovered pointwise by aggregating its singleton observation surface. -/
@[simp] theorem evidence_eq_aggregate_singletonSurface_of_zero
    (G : MultisetGenericWorldModel Obs Query Ev)
    (hzero :
      ∀ q,
        letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
        letI : AdditiveWorldModel (Multiset Obs) Query Ev := G
        AdditiveWorldModel.extract
          (State := Multiset Obs) (Query := Query) (Ev := Ev) (0 : Multiset Obs) q = 0)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := G
    AdditiveWorldModel.extract
        (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q =
      aggregate
        (singletonSurface (Obs := Obs) (Query := Query) (Ev := Ev) G) σ q := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := G
  have hEq :=
    aggregate_eq_of_isAdditiveExtension
      (S := singletonSurface (Obs := Obs) (Query := Query) (Ev := Ev) G)
      (E := fun σ q =>
        AdditiveWorldModel.extract
          (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q)
      (evidence_isAdditiveExtension_of_zero
        (Obs := Obs) (Query := Query) (Ev := Ev) G hzero)
  exact congrFun (congrFun hEq σ) q

/-- The induced world model built from the singleton surface of a zero-preserving
generic multiset world model recovers the original evidence extractor pointwise. -/
@[simp] theorem inducedWorldModel_evidence_eq_of_singletonSurface_zero
    (G : MultisetGenericWorldModel Obs Query Ev)
    (hzero :
      ∀ q,
        letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
        letI : AdditiveWorldModel (Multiset Obs) Query Ev := G
        AdditiveWorldModel.extract
          (State := Multiset Obs) (Query := Query) (Ev := Ev) (0 : Multiset Obs) q = 0)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev :=
      (singletonSurface (Obs := Obs) (Query := Query) (Ev := Ev) G).inducedWorldModel
    AdditiveWorldModel.extract
        (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q =
      letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
      letI : AdditiveWorldModel (Multiset Obs) Query Ev := G
      AdditiveWorldModel.extract
        (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q := by
  rw [inducedWorldModel_evidence_eq_aggregate]
  exact
    (evidence_eq_aggregate_singletonSurface_of_zero
      (Obs := Obs) (Query := Query) (Ev := Ev) G hzero σ q).symm

/-- Uniqueness form of the classification theorem: once `evidence 0 = 0`, the
original evidence extractor is the unique additive extension of the singleton
surface. -/
theorem existsUnique_additiveExtension_of_singletonSurface_zero
    (G : MultisetGenericWorldModel Obs Query Ev)
    (hzero :
      ∀ q,
        letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
        letI : AdditiveWorldModel (Multiset Obs) Query Ev := G
        AdditiveWorldModel.extract
          (State := Multiset Obs) (Query := Query) (Ev := Ev) (0 : Multiset Obs) q = 0) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    ∃! E : Multiset Obs → Query → Ev,
      GenIsAdditiveExtension
        (singletonSurface (Obs := Obs) (Query := Query) (Ev := Ev) G).observe E := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  refine ⟨
    (fun σ q =>
      letI : AdditiveWorldModel (Multiset Obs) Query Ev := G
      AdditiveWorldModel.extract
        (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q),
    evidence_isAdditiveExtension_of_zero (Obs := Obs) (Query := Query) (Ev := Ev) G hzero,
    ?_⟩
  intro E hE
  ext σ q
  rw [aggregate_eq_of_isAdditiveExtension
    (S := singletonSurface (Obs := Obs) (Query := Query) (Ev := Ev) G) hE]
  exact
    (evidence_eq_aggregate_singletonSurface_of_zero
      (Obs := Obs) (Query := Query) (Ev := Ev) G hzero σ q).symm

end GenericMultisetClassification

section AdditiveEvidence

variable {Obs Query : Type*}
variable (S : SufficientStatisticSurface Obs Query BinaryEvidence)

@[simp] theorem aggregate_eq_additiveExtension
    (σ : Multiset Obs) (q : Query) :
    aggregate S σ q = additiveExtension S.observe σ q :=
  rfl

/-- In the binary evidence specialization, the induced generic world model
agrees pointwise with the existing additive `BinaryWorldModel` construction. -/
@[simp] theorem inducedWorldModel_evidence_eq_worldModelOfAtomicEvidence
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence := S.inducedWorldModel
    letI : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
    AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := BinaryEvidence) σ q =
      BinaryWorldModel.evidence (State := Multiset Obs) (Query := Query) σ q := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence := S.inducedWorldModel
  letI : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  rw [inducedWorldModel_evidence_eq_aggregate (S := S), aggregate_eq_additiveExtension (S := S)]
  rfl

/-- Binary observation counts computed through the induced generic world model
match the original `BinaryWorldModel` total-evidence view. -/
@[simp] theorem queryObservationCount_inducedWorldModel_eq_worldModel_total
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence := S.inducedWorldModel
    letI : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
    AdditiveWorldModel.queryObservationCount
        (State := Multiset Obs) (Query := Query) (Ev := BinaryEvidence) σ q =
      (BinaryWorldModel.evidence (State := Multiset Obs) (Query := Query) σ q).total := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence := S.inducedWorldModel
  letI : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  exact
    AdditiveWorldModel.queryObservationCount_eq_binary_total
      (State := Multiset Obs) (Query := Query) σ q

/-- Binary observation confidence computed through the induced generic world
model matches the original `BinaryWorldModel.queryConfidence` view. -/
theorem queryObservationConfidence_inducedWorldModel_eq_worldModel_queryConfidence
    (κ : ℝ≥0∞) (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence := S.inducedWorldModel
    letI : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
    AdditiveWorldModel.queryObservationConfidence
        (State := Multiset Obs) (Query := Query) (Ev := BinaryEvidence) κ σ q =
      BinaryWorldModel.queryConfidence (State := Multiset Obs) (Query := Query) κ σ q := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence := S.inducedWorldModel
  letI : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  simpa using
    AdditiveWorldModel.queryObservationConfidence_eq_queryConfidence
      (State := Multiset Obs) (Query := Query) κ σ q

end AdditiveEvidence

section Posterior

variable [AddCommMonoid Ev]

/-- A multiset-level conjugate-posterior surface over an additive sufficient
statistic. The posterior update is stated directly over batches of observations,
without imposing a fake common posterior-on-evidence API on all families. -/
structure ConjugatePosteriorSurface (Obs Query Ev Prior : Type*) [AddCommMonoid Ev] where
  stat : SufficientStatisticSurface Obs Query Ev
  posterior : Prior → Multiset Obs → Query → Prior
  posterior_zero : ∀ prior q, posterior prior 0 q = prior
  posterior_add :
    ∀ prior σ₁ σ₂ q,
      posterior prior (σ₁ + σ₂) q = posterior (posterior prior σ₁ q) σ₂ q

namespace ConjugatePosteriorSurface

variable {Prior : Type*}
variable (P : ConjugatePosteriorSurface Obs Query Ev Prior)

@[simp] theorem posterior_zero_apply (prior : Prior) (q : Query) :
    P.posterior prior 0 q = prior :=
  P.posterior_zero prior q

theorem posterior_cons (prior : Prior) (o : Obs) (σ : Multiset Obs) (q : Query) :
    P.posterior prior (o ::ₘ σ) q =
      P.posterior (P.posterior prior ({o} : Multiset Obs) q) σ q := by
  simpa using P.posterior_add prior ({o} : Multiset Obs) σ q

theorem posterior_add_apply (prior : Prior) (σ₁ σ₂ : Multiset Obs) (q : Query) :
    P.posterior prior (σ₁ + σ₂) q =
      P.posterior (P.posterior prior σ₁ q) σ₂ q :=
  P.posterior_add prior σ₁ σ₂ q

theorem posterior_double_ne_single_of_nonempty
    (hneq : ∀ prior {σ : Multiset Obs}, σ ≠ 0 → P.posterior prior σ q ≠ prior)
    (prior : Prior) {σ : Multiset Obs} (hσ : σ ≠ 0) :
    P.posterior prior (σ + σ) q ≠ P.posterior prior σ q := by
  rw [P.posterior_add_apply prior σ σ q]
  exact hneq (P.posterior prior σ q) hσ

theorem posterior_double_singleton_ne_singleton
    (hneq : ∀ prior {σ : Multiset Obs}, σ ≠ 0 → P.posterior prior σ q ≠ prior)
    (prior : Prior) (o : Obs) :
    P.posterior prior (({o} : Multiset Obs) + ({o} : Multiset Obs)) q ≠
      P.posterior prior ({o} : Multiset Obs) q := by
  exact P.posterior_double_ne_single_of_nonempty hneq prior (by simp)

theorem not_posterior_add_idempotent_of_observation
    (hneq : ∀ prior {σ : Multiset Obs}, σ ≠ 0 → P.posterior prior σ q ≠ prior)
    (prior : Prior) (o : Obs) :
    ¬ ∀ σ : Multiset Obs, P.posterior prior (σ + σ) q = P.posterior prior σ q := by
  intro hidem
  exact P.posterior_double_singleton_ne_singleton hneq prior o (hidem ({o} : Multiset Obs))

/-- Fixing a prior still rules out global additive idempotence across all
queries when every nonempty batch changes every prior state. -/
theorem not_posterior_add_idempotent
    [Nonempty Obs] [Nonempty Query]
    (prior : Prior)
    (hneq : ∀ prior' {σ : Multiset Obs} (q : Query), σ ≠ 0 → P.posterior prior' σ q ≠ prior') :
    ¬ ∀ q σ, P.posterior prior (σ + σ) q = P.posterior prior σ q := by
  let o : Obs := Classical.choice ‹Nonempty Obs›
  let q : Query := Classical.choice ‹Nonempty Query›
  intro hidem
  exact
    P.not_posterior_add_idempotent_of_observation
      (hneq := fun prior' {σ} hσ => hneq prior' q hσ)
      (prior := prior) o
      (fun σ => by simpa using hidem q σ)

/-- If every nonempty batch changes the posterior at every query, then global
additive idempotence of the posterior update law is impossible. -/
theorem not_global_posterior_add_idempotent
    [Nonempty Obs] [Nonempty Query] [Nonempty Prior]
    (hneq : ∀ prior {σ : Multiset Obs} (q : Query), σ ≠ 0 → P.posterior prior σ q ≠ prior) :
    ¬ ∀ prior q σ, P.posterior prior (σ + σ) q = P.posterior prior σ q := by
  intro hidem
  let prior : Prior := Classical.choice ‹Nonempty Prior›
  let o : Obs := Classical.choice ‹Nonempty Obs›
  let q : Query := Classical.choice ‹Nonempty Query›
  exact
    P.not_posterior_add_idempotent_of_observation
      (hneq := fun prior {σ} hσ => hneq prior q hσ)
      (prior := prior) o
      (hidem prior q)

/-- If a posterior update factors through the canonical sufficient statistic,
then it factors through any other additive extension of the same atomic
observation encoder. -/
theorem posterior_eq_of_isAdditiveExtension
    (lift : Prior → Query → Ev → Prior)
    (hlift :
      ∀ prior σ q,
        P.posterior prior σ q = lift prior q (SufficientStatisticSurface.aggregate P.stat σ q))
    {E : Multiset Obs → Query → Ev}
    (hE : GenIsAdditiveExtension P.stat.observe E)
    (prior : Prior) (σ : Multiset Obs) (q : Query) :
    P.posterior prior σ q = lift prior q (E σ q) := by
  rw [hlift]
  have hEq : E = SufficientStatisticSurface.aggregate P.stat :=
    SufficientStatisticSurface.aggregate_eq_of_isAdditiveExtension (S := P.stat) hE
  simp [hEq]

/-- The posterior also factors through the evidence extracted by the induced
generic world model of the sufficient-statistic surface. -/
theorem posterior_eq_of_inducedWorldModelEvidence
    (lift : Prior → Query → Ev → Prior)
    (hlift :
      ∀ prior σ q,
        P.posterior prior σ q = lift prior q (SufficientStatisticSurface.aggregate P.stat σ q))
    (prior : Prior) (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := P.stat.inducedWorldModel
    P.posterior prior σ q =
      lift prior q
        (AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := P.stat.inducedWorldModel
  simpa [SufficientStatisticSurface.inducedWorldModel_evidence_eq_aggregate (S := P.stat)] using
    hlift prior σ q

/-- If a posterior factors through the canonical sufficient statistic via an
injective lift, then distinct aggregate evidence yields distinct posterior
states. -/
theorem posterior_ne_of_aggregate_ne
    (lift : Prior → Query → Ev → Prior)
    (hlift :
      ∀ prior σ q,
        P.posterior prior σ q = lift prior q (SufficientStatisticSurface.aggregate P.stat σ q))
    (hinj : ∀ prior q, Function.Injective (lift prior q))
    (prior : Prior) {σ₁ σ₂ : Multiset Obs} (q : Query)
    (hneq :
      SufficientStatisticSurface.aggregate P.stat σ₁ q ≠
        SufficientStatisticSurface.aggregate P.stat σ₂ q) :
    P.posterior prior σ₁ q ≠ P.posterior prior σ₂ q := by
  intro hEq
  apply hneq
  apply hinj prior q
  rw [← hlift prior σ₁ q, ← hlift prior σ₂ q]
  exact hEq

/-- The same injective-lift argument applies after replacing the canonical
aggregate with any additive extension of the atomic observation encoder. -/
theorem posterior_ne_of_isAdditiveExtension_ne
    (lift : Prior → Query → Ev → Prior)
    (hlift :
      ∀ prior σ q,
        P.posterior prior σ q = lift prior q (SufficientStatisticSurface.aggregate P.stat σ q))
    (hinj : ∀ prior q, Function.Injective (lift prior q))
    {E : Multiset Obs → Query → Ev}
    (hE : GenIsAdditiveExtension P.stat.observe E)
    (prior : Prior) {σ₁ σ₂ : Multiset Obs} (q : Query)
    (hneq : E σ₁ q ≠ E σ₂ q) :
    P.posterior prior σ₁ q ≠ P.posterior prior σ₂ q := by
  have hEqE := SufficientStatisticSurface.aggregate_eq_of_isAdditiveExtension (S := P.stat) hE
  exact
    P.posterior_ne_of_aggregate_ne
      (lift := lift) (hlift := hlift) (hinj := hinj) (prior := prior) (q := q)
      (by
        intro hAgg
        apply hneq
        have hσ₁ : E σ₁ q = SufficientStatisticSurface.aggregate P.stat σ₁ q :=
          congrFun (congrFun hEqE σ₁) q
        have hσ₂ : E σ₂ q = SufficientStatisticSurface.aggregate P.stat σ₂ q :=
          congrFun (congrFun hEqE σ₂) q
        calc
          E σ₁ q = SufficientStatisticSurface.aggregate P.stat σ₁ q := hσ₁
          _ = SufficientStatisticSurface.aggregate P.stat σ₂ q := hAgg
          _ = E σ₂ q := hσ₂.symm)

/-- In particular, if the induced generic world model extracts distinct
evidence batches, then the corresponding posterior states are distinct. -/
theorem posterior_ne_of_inducedWorldModelEvidence_ne
    (lift : Prior → Query → Ev → Prior)
    (hlift :
      ∀ prior σ q,
        P.posterior prior σ q = lift prior q (SufficientStatisticSurface.aggregate P.stat σ q))
    (hinj : ∀ prior q, Function.Injective (lift prior q))
    (prior : Prior) {σ₁ σ₂ : Multiset Obs} (q : Query)
    (hneq :
      letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
      letI : AdditiveWorldModel (Multiset Obs) Query Ev := P.stat.inducedWorldModel
      AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := Ev) σ₁ q ≠
        AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := Ev) σ₂ q) :
    P.posterior prior σ₁ q ≠ P.posterior prior σ₂ q := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := P.stat.inducedWorldModel
  exact
    P.posterior_ne_of_aggregate_ne
      (lift := lift) (hlift := hlift) (hinj := hinj) (prior := prior) (q := q)
      (by
        simpa [SufficientStatisticSurface.inducedWorldModel_evidence_eq_aggregate (S := P.stat)] using
          hneq)

end ConjugatePosteriorSurface

end Posterior

section Conjugate

variable [ConjugateEvidence Ev] (S : SufficientStatisticSurface Obs Query Ev)

/-- Every atomic observation contributes exactly one observation-count unit. -/
def UnitObservation : Prop :=
  ∀ o q, ConjugateEvidence.observationCount (S.observe o q) = 1

/-- Under unit observations, aggregate observation count is just multiset
cardinality. -/
theorem aggregate_observationCount_of_unit
    (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    ConjugateEvidence.observationCount (aggregate S σ q) =
      (σ.card : ℝ≥0∞) := by
  simpa [aggregate, UnitObservation] using
    observationCount_genAdditiveExtension_of_unit S.observe hunit σ q

/-- Under unit observations, aggregate confidence is the usual
`n / (n + κ)` confidence law. -/
theorem aggregate_observationConfidence_of_unit
    (κ : ℝ≥0∞) (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    observationConfidence κ (aggregate S σ q) =
      (σ.card : ℝ≥0∞) / ((σ.card : ℝ≥0∞) + κ) := by
  simpa [aggregate, UnitObservation] using
    observationConfidence_genAdditiveExtension_of_unit κ S.observe hunit σ q

theorem aggregate_observationCount_ne_top_of_unit
    (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    ConjugateEvidence.observationCount (aggregate S σ q) ≠ ⊤ := by
  rw [aggregate_observationCount_of_unit (S := S) hunit σ q]
  simp

theorem aggregate_observationCount_ne_zero_of_unit_nonempty
    (hunit : UnitObservation S)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    ConjugateEvidence.observationCount (aggregate S σ q) ≠ 0 := by
  rw [aggregate_observationCount_of_unit (S := S) hunit]
  have hcard : σ.card ≠ 0 := by
    simpa [Multiset.card_eq_zero] using hσ
  exact_mod_cast hcard

theorem aggregate_not_add_idempotent_of_unit_nonempty
    (hunit : UnitObservation S)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    aggregate S σ q + aggregate S σ q ≠ aggregate S σ q := by
  apply not_add_idempotent_of_finite_nonzero_observationCount
  · exact aggregate_observationCount_ne_top_of_unit (S := S) hunit σ q
  · exact aggregate_observationCount_ne_zero_of_unit_nonempty (S := S) hunit hσ q

/-- Under unit observations, aggregating the same nonempty batch twice cannot
collapse to aggregating it once. -/
theorem aggregate_double_ne_single_of_unit_nonempty
    (hunit : UnitObservation S)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    aggregate S (σ + σ) q ≠ aggregate S σ q := by
  rw [aggregate_add]
  exact aggregate_not_add_idempotent_of_unit_nonempty (S := S) hunit hσ q

/-- The generic world model induced by a unit-observation surface has observation
count equal to multiset cardinality. -/
@[simp] theorem evidence_inducedWorldModel_eq_aggregate
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q =
      aggregate S σ q := by
  exact inducedWorldModel_evidence_eq_aggregate (S := S) σ q

/-- At the induced generic world-model layer, aggregating the same nonempty batch
twice cannot collapse to aggregating it once. -/
theorem evidence_inducedWorldModel_double_ne_single_of_unit_nonempty
    (hunit : UnitObservation S)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := Ev) (σ + σ) q ≠
      AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  simpa [evidence_inducedWorldModel_eq_aggregate (S := S)] using
    aggregate_double_ne_single_of_unit_nonempty (S := S) hunit hσ q

/-- For the induced generic world model, query observation count is just the
conjugate-evidence observation count of the aggregated sufficient statistic. -/
@[simp] theorem queryObservationCount_inducedWorldModel_eq_aggregate_observationCount
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    AdditiveWorldModel.queryObservationCount
        (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q =
      ConjugateEvidence.observationCount (aggregate S σ q) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  simp [AdditiveWorldModel.queryObservationCount,
    evidence_inducedWorldModel_eq_aggregate (S := S)]

/-- For the induced generic world model, query confidence is just the abstract
count-based confidence of the aggregated sufficient statistic. -/
@[simp] theorem queryObservationConfidence_inducedWorldModel_eq_aggregate_observationConfidence
    (κ : ℝ≥0∞) (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    AdditiveWorldModel.queryObservationConfidence
        (State := Multiset Obs) (Query := Query) (Ev := Ev) κ σ q =
      observationConfidence κ (aggregate S σ q) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  simp [AdditiveWorldModel.queryObservationConfidence,
    evidence_inducedWorldModel_eq_aggregate (S := S)]

/-- The generic world model induced by a unit-observation surface has observation
count equal to multiset cardinality. -/
theorem queryObservationCount_inducedWorldModel_of_unit
    (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    AdditiveWorldModel.queryObservationCount (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q =
      (σ.card : ℝ≥0∞) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  simpa [UnitObservation] using
    AdditiveWorldModel.queryObservationCount_of_unit S.observe hunit σ q

/-- The generic world model induced by a unit-observation surface has confidence
equal to the standard `n / (n + κ)` law. -/
theorem queryObservationConfidence_inducedWorldModel_of_unit
    (κ : ℝ≥0∞) (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    AdditiveWorldModel.queryObservationConfidence (State := Multiset Obs) (Query := Query) (Ev := Ev) κ σ q =
      (σ.card : ℝ≥0∞) / ((σ.card : ℝ≥0∞) + κ) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  simpa [UnitObservation] using
    AdditiveWorldModel.queryObservationConfidence_of_unit κ S.observe hunit σ q

/-- In a unit-observation induced world model, an idempotent revision fragment
must have zero observation count at every query. -/
theorem queryObservationCount_inducedWorldModel_eq_zero_of_revision_idempotent_of_unit
    (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query)
    (hidem :
      letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
      letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
      (σ + σ : Multiset Obs) = σ) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    AdditiveWorldModel.queryObservationCount
        (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q = 0 := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  apply AdditiveWorldModel.queryObservationCount_eq_zero_of_revision_idempotent
    (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q
  · rw [queryObservationCount_inducedWorldModel_of_unit (S := S) hunit]
    simp
  · exact hidem

/-- In a unit-observation induced world model, any revision-idempotent
observation fragment is trivial: the multiset must be empty. -/
theorem revision_idempotent_inducedWorldModel_implies_empty_of_unit
    (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query)
    (hidem :
      letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
      letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
      (σ + σ : Multiset Obs) = σ) :
    σ = 0 := by
  have hzero :=
    queryObservationCount_inducedWorldModel_eq_zero_of_revision_idempotent_of_unit
      (S := S) hunit σ q hidem
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  rw [queryObservationCount_inducedWorldModel_of_unit (S := S) hunit] at hzero
  have hcard : σ.card = 0 := by
    exact_mod_cast hzero
  simpa [Multiset.card_eq_zero] using hcard

/-- In a unit-observation induced world model, no state can be both
revision-idempotent and have nonzero query observation count. This packages the
WM-layer contradiction directly in terms of the generic query-count view. -/
theorem not_exists_revision_idempotent_inducedWorldModel_with_nonzero_queryObservationCount_of_unit
    (hunit : UnitObservation S) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    ¬ ∃ σ : Multiset Obs,
        AdditiveWorldModel.queryObservationCount
            (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q ≠ 0 ∧
        (σ + σ : Multiset Obs) = σ := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  intro hExists
  rcases hExists with ⟨σ, hcount, hidem⟩
  exact
    hcount
      (queryObservationCount_inducedWorldModel_eq_zero_of_revision_idempotent_of_unit
        (S := S) hunit σ q hidem)

/-- In a unit-observation induced world model, revision idempotence of an
observation fragment is equivalent to zero query observation count. Since the
count is just multiset cardinality in this setting, idempotent revision is
exactly the trivial empty-fragment case. -/
theorem revision_idempotent_inducedWorldModel_iff_queryObservationCount_eq_zero_of_unit
    (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    ((σ + σ : Multiset Obs) = σ ↔
      AdditiveWorldModel.queryObservationCount
          (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q = 0) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  constructor
  · exact
      queryObservationCount_inducedWorldModel_eq_zero_of_revision_idempotent_of_unit
        (S := S) hunit σ q
  · intro hcount
    rw [queryObservationCount_inducedWorldModel_of_unit (S := S) hunit] at hcount
    have hcard : σ.card = 0 := by
      exact_mod_cast hcount
    have hσ : σ = 0 := by
      simpa [Multiset.card_eq_zero] using hcard
    simp [hσ]

/-- Under unit observations, zero query observation count in the induced world
model is exactly the empty observation fragment. -/
theorem queryObservationCount_inducedWorldModel_eq_zero_iff_empty_of_unit
    (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    (AdditiveWorldModel.queryObservationCount
        (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q = 0 ↔
      σ = 0) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  constructor
  · intro hcount
    rw [queryObservationCount_inducedWorldModel_of_unit (S := S) hunit] at hcount
    have hcard : σ.card = 0 := by
      exact_mod_cast hcount
    simpa [Multiset.card_eq_zero] using hcard
  · intro hσ
    subst hσ
    rw [queryObservationCount_inducedWorldModel_of_unit (S := S) hunit]
    simp

/-- Under unit observations, nonzero query observation count in the induced
world model is exactly the nonempty-fragment case. -/
theorem queryObservationCount_inducedWorldModel_ne_zero_iff_nonempty_of_unit
    (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    (AdditiveWorldModel.queryObservationCount
        (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q ≠ 0 ↔
      σ ≠ 0) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  constructor
  · intro hcount hσ
    exact
      hcount
        ((queryObservationCount_inducedWorldModel_eq_zero_iff_empty_of_unit
          (S := S) hunit σ q).2 hσ)
  · intro hσ hcount
    exact
      hσ
        ((queryObservationCount_inducedWorldModel_eq_zero_iff_empty_of_unit
          (S := S) hunit σ q).1 hcount)

/-- Under unit observations, induced-world-model revision idempotence is
exactly the empty-fragment case. -/
theorem revision_idempotent_inducedWorldModel_iff_empty_of_unit
    (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    ((σ + σ : Multiset Obs) = σ ↔ σ = 0) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  constructor
  · exact revision_idempotent_inducedWorldModel_implies_empty_of_unit (S := S) hunit σ q
  · intro hσ
    simp [hσ]

/-- Under unit observations, induced-world-model revision is non-idempotent
exactly on nonempty observation fragments. -/
theorem revision_not_idempotent_inducedWorldModel_iff_nonempty_of_unit
    (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    ((σ + σ : Multiset Obs) ≠ σ ↔ σ ≠ 0) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  constructor
  · intro hneq hσ
    exact hneq (by simp [hσ])
  · intro hσ hidem
    have hzero : σ = 0 := by
      exact
        (revision_idempotent_inducedWorldModel_iff_empty_of_unit
          (S := S) hunit σ q).mp hidem
    exact hσ hzero

/-- Under unit observations, induced-world-model revision is non-idempotent
exactly when the query observation count is nonzero. This is the WM-facing
dual of the idempotence = triviality principle. -/
theorem revision_not_idempotent_inducedWorldModel_iff_queryObservationCount_ne_zero_of_unit
    (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    ((σ + σ : Multiset Obs) ≠ σ ↔
      AdditiveWorldModel.queryObservationCount
          (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q ≠ 0) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  rw [queryObservationCount_inducedWorldModel_ne_zero_iff_nonempty_of_unit (S := S) hunit σ q]
  exact revision_not_idempotent_inducedWorldModel_iff_nonempty_of_unit (S := S) hunit σ q

/-- In the induced generic world model, a nonempty unit-observation batch cannot
be idempotent under additive revision. This packages the generic WM no-go theorem
through the sufficient-statistics surface. -/
theorem revision_not_idempotent_inducedWorldModel_of_unit_nonempty
    (hunit : UnitObservation S)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    (σ + σ : Multiset Obs) ≠ σ := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
  apply AdditiveWorldModel.not_revision_idempotent_of_finite_nonzero_queryObservationCount
    (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q
  · rw [queryObservationCount_inducedWorldModel_of_unit (S := S) hunit]
    simp
  · rw [queryObservationCount_inducedWorldModel_of_unit (S := S) hunit]
    exact_mod_cast (Multiset.card_pos.mpr hσ).ne'

/-- For any inhabited unit-observation surface, the induced generic world model
cannot satisfy globally idempotent revision. -/
theorem not_global_revision_idempotent_inducedWorldModel_of_unit
    (hunit : UnitObservation S) [Nonempty Obs] [Nonempty Query] :
    ¬ ∀ W : Multiset Obs, W + W = W := by
  intro hidem
  let o : Obs := Classical.choice ‹Nonempty Obs›
  let q : Query := Classical.choice ‹Nonempty Query›
  have hneq :
      (({o} : Multiset Obs) + ({o} : Multiset Obs) : Multiset Obs) ≠ ({o} : Multiset Obs) := by
    simpa using
      revision_not_idempotent_inducedWorldModel_of_unit_nonempty
        (S := S) hunit (σ := ({o} : Multiset Obs)) (by simp) q
  exact hneq (hidem ({o} : Multiset Obs))

end Conjugate

/-! ## WM / Sufficient-Statistics Contract

### How to use this layer

A `SufficientStatisticSurface Obs Query Ev` encodes raw observations into an
additive evidence carrier. From this single definition, the layer automatically
provides:

1. **Canonical additive extension** (`aggregate`): uniquely determined multiset
   aggregation satisfying `aggregate S {o} q = S.observe o q` and
   `aggregate S (σ₁ + σ₂) q = aggregate S σ₁ q + aggregate S σ₂ q`.
   - Witness: `aggregate_isAdditiveExtension`
   - Uniqueness: `aggregate_eq_of_isAdditiveExtension`
   - Exists-unique: `existsUnique_aggregate`

2. **Induced `WorldModel`** (`inducedWorldModel`): a world model over
   `Multiset Obs` whose evidence function is exactly the canonical aggregate.
   - Bridge: `inducedWorldModel_evidence_eq_aggregate`

3. **Count/confidence transport** (requires `[ConjugateEvidence Ev]`):
   - Generic: `queryObservationCount_inducedWorldModel_eq_aggregate_observationCount`,
     `queryObservationConfidence_inducedWorldModel_eq_aggregate_observationConfidence`
   - Under `UnitObservation S` (each observation contributes count 1):
     `wm_count_eq_card` (count = multiset cardinality),
     `wm_confidence_eq_ratio` (confidence = n/(n+κ))

4. **Revision idempotence / no-go** (strongest iff normal forms, under `UnitObservation`):
   - `queryObservationCount_inducedWorldModel_eq_zero_iff_empty_of_unit`
   - `queryObservationCount_inducedWorldModel_ne_zero_iff_nonempty_of_unit`
   - `revision_idempotent_inducedWorldModel_iff_empty_of_unit` (σ+σ=σ ↔ σ=0)
   - `revision_idempotent_inducedWorldModel_iff_queryObservationCount_eq_zero_of_unit`
   - `revision_not_idempotent_inducedWorldModel_iff_queryObservationCount_ne_zero_of_unit`
   - `revision_not_idempotent_inducedWorldModel_iff_nonempty_of_unit` (σ+σ≠σ ↔ σ≠0)
   - `not_global_revision_idempotent_inducedWorldModel_of_unit`

5. **Posterior factoring** (via `ConjugatePosteriorSurface`):
   - `posterior_eq_of_isAdditiveExtension`, `posterior_eq_of_inducedWorldModelEvidence`
   - `posterior_ne_of_aggregate_ne` (injective lift ⇒ distinct evidence ⇒ distinct posterior)

### Assumptions

- `[AddCommMonoid Ev]` — generic additive extension and aggregation
- `[ConjugateEvidence Ev]` — observation count/confidence transport
- `UnitObservation S` — each atomic observation contributes exactly 1 count unit

### Design boundary

This layer does **not** impose a common posterior parameter API across families.
Each conjugate family (Beta, Dirichlet, Normal-Gamma) defines its own posterior
parameters and update law. The shared contract is the sufficient-statistic
aggregation and its transport through the generic world model.

**Gaussian caveat**: full evidence injectivity is false for Normal-Gamma (the
sum-of-squares statistic is not injective over raw data). The true theorem is
realizable-evidence recovery: for any `Realizable` evidence value, there exists
a concrete observation sequence producing it. See `gaussianRealizableEvidence`
in the Gaussian family section below.
-/

section WMContract

variable {Obs Query Ev : Type*} [ConjugateEvidence Ev]
    (S : SufficientStatisticSurface Obs Query Ev)

/-- Short alias: under unit observations, query observation count = multiset
cardinality. This is the most commonly needed downstream theorem. -/
theorem wm_count_eq_card (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    AdditiveWorldModel.queryObservationCount
        (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q =
      (σ.card : ℝ≥0∞) :=
  queryObservationCount_inducedWorldModel_of_unit (S := S) hunit σ q

/-- Short alias: under unit observations, query confidence = n/(n+κ). -/
theorem wm_confidence_eq_ratio (κ : ℝ≥0∞) (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    AdditiveWorldModel.queryObservationConfidence
        (State := Multiset Obs) (Query := Query) (Ev := Ev) κ σ q =
      (σ.card : ℝ≥0∞) / ((σ.card : ℝ≥0∞) + κ) :=
  queryObservationConfidence_inducedWorldModel_of_unit (S := S) κ hunit σ q

end WMContract

/-! ## Canonical Conjugate-Family Surfaces -/

/-- One Bernoulli observation contributes either one unit of positive evidence or
one unit of negative evidence. -/
def bernoulliObservation (b : Bool) : BinaryEvidence :=
  if b then ⟨1, 0⟩ else ⟨0, 1⟩

/-- Query-indexed Bernoulli/Beta sufficient-statistic surface. -/
def bernoulliStatistic (classify : Obs → Query → Bool) :
    SufficientStatisticSurface Obs Query BinaryEvidence where
  observe o q := bernoulliObservation (classify o q)

theorem bernoulliStatistic_unitObservation
    (classify : Obs → Query → Bool) :
    UnitObservation (bernoulliStatistic classify) := by
  intro o q
  by_cases h : classify o q
  · simp [bernoulliStatistic, bernoulliObservation, h,
      Mettapedia.Logic.ConjugateEvidenceSurface.instConjugateEvidenceBeta]
  · simp [bernoulliStatistic, bernoulliObservation, h,
      Mettapedia.Logic.ConjugateEvidenceSurface.instConjugateEvidenceBeta]

theorem bernoulliStatistic_queryObservationCount
    (classify : Obs → Query → Bool)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence :=
      (bernoulliStatistic classify).inducedWorldModel
    AdditiveWorldModel.queryObservationCount (State := Multiset Obs) (Query := Query) (Ev := BinaryEvidence) σ q =
      (σ.card : ℝ≥0∞) := by
  simpa using
    queryObservationCount_inducedWorldModel_of_unit
      (S := bernoulliStatistic classify)
      (bernoulliStatistic_unitObservation classify) σ q

theorem bernoulliStatistic_queryObservationConfidence
    (κ : ℝ≥0∞) (classify : Obs → Query → Bool)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence :=
      (bernoulliStatistic classify).inducedWorldModel
    AdditiveWorldModel.queryObservationConfidence
        (State := Multiset Obs) (Query := Query) (Ev := BinaryEvidence) κ σ q =
      (σ.card : ℝ≥0∞) / ((σ.card : ℝ≥0∞) + κ) := by
  simpa using
    queryObservationConfidence_inducedWorldModel_of_unit
      (S := bernoulliStatistic classify)
      κ (bernoulliStatistic_unitObservation classify) σ q

theorem bernoulliStatistic_queryEvidence_double_ne_single_of_nonempty
    (classify : Obs → Query → Bool)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence :=
      (bernoulliStatistic classify).inducedWorldModel
    AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := BinaryEvidence) (σ + σ) q ≠
      AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := BinaryEvidence) σ q := by
  simpa using
    evidence_inducedWorldModel_double_ne_single_of_unit_nonempty
      (S := bernoulliStatistic classify)
      (bernoulliStatistic_unitObservation classify) hσ q

theorem bernoulliStatistic_revision_not_idempotent_of_nonempty
    (classify : Obs → Query → Bool)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence :=
      (bernoulliStatistic classify).inducedWorldModel
    (σ + σ : Multiset Obs) ≠ σ := by
  simpa using
    revision_not_idempotent_inducedWorldModel_of_unit_nonempty
      (S := bernoulliStatistic classify)
      (bernoulliStatistic_unitObservation classify) hσ q

theorem bernoulliStatistic_not_global_revision_idempotent
    [Nonempty Obs] [Nonempty Query]
    (classify : Obs → Query → Bool) :
    ¬ ∀ W : Multiset Obs, W + W = W := by
  simpa using
    not_global_revision_idempotent_inducedWorldModel_of_unit
      (S := bernoulliStatistic classify)
      (bernoulliStatistic_unitObservation classify)

theorem bernoulliStatistic_aggregate_pos
    (classify : Obs → Query → Bool)
    (σ : Multiset Obs) (q : Query) :
    (aggregate (bernoulliStatistic classify) σ q).pos =
      (σ.countP (fun o => classify o q = true) : ℝ≥0∞) := by
  induction σ using Multiset.induction_on with
  | empty =>
      rw [aggregate_zero]
      rw [show (0 : BinaryEvidence) = BinaryEvidence.zero by rfl]
      simp [BinaryEvidence.zero, Multiset.countP_zero]
  | @cons o σ ih =>
      by_cases h : classify o q = true
      · rw [aggregate_cons]
        rw [BinaryEvidence.hplus_def]
        rw [ih]
        simp [bernoulliStatistic, bernoulliObservation, h,
          Multiset.countP_cons_of_pos, Nat.cast_add, add_comm]
      · rw [aggregate_cons]
        rw [BinaryEvidence.hplus_def]
        rw [ih]
        simp [bernoulliStatistic, bernoulliObservation, h,
          Multiset.countP_cons_of_neg]

theorem bernoulliStatistic_aggregate_neg
    (classify : Obs → Query → Bool)
    (σ : Multiset Obs) (q : Query) :
    (aggregate (bernoulliStatistic classify) σ q).neg =
      (σ.countP (fun o => classify o q = false) : ℝ≥0∞) := by
  induction σ using Multiset.induction_on with
  | empty =>
      rw [aggregate_zero]
      rw [show (0 : BinaryEvidence) = BinaryEvidence.zero by rfl]
      simp [BinaryEvidence.zero, Multiset.countP_zero]
  | @cons o σ ih =>
      by_cases h : classify o q = true
      · rw [aggregate_cons]
        rw [BinaryEvidence.hplus_def]
        rw [ih]
        simp [bernoulliStatistic, bernoulliObservation, h,
          Multiset.countP_cons_of_neg]
      · have hfalse : classify o q = false := by
          cases hc : classify o q <;> simp_all
        rw [aggregate_cons]
        rw [BinaryEvidence.hplus_def]
        rw [ih]
        simp [bernoulliStatistic, bernoulliObservation, hfalse,
          Multiset.countP_cons_of_pos, Nat.cast_add, add_comm]

theorem bernoulliStatistic_beta_hplus
    (classify : Obs → Query → Bool)
    (σ₁ σ₂ : Multiset Obs) (q : Query) :
    let e₁ := aggregate (bernoulliStatistic classify) σ₁ q
    let e₂ := aggregate (bernoulliStatistic classify) σ₂ q
    aggregate (bernoulliStatistic classify) (σ₁ + σ₂) q = e₁ + e₂ := by
  simpa [aggregate] using
    aggregate_add (S := bernoulliStatistic classify) σ₁ σ₂ q

theorem bernoulliStatistic_beta_conjugate_update
    (prior_param : ℝ) (hprior : 0 < prior_param)
    (classify : Obs → Query → Bool)
    (σ₁ σ₂ : Multiset Obs) (q : Query) :
    let n₁_pos := σ₁.countP (fun o => classify o q = true)
    let n₁_neg := σ₁.countP (fun o => classify o q = false)
    let n₂_pos := σ₂.countP (fun o => classify o q = true)
    let n₂_neg := σ₂.countP (fun o => classify o q = false)
    let params₁ : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams :=
      { prior_param := prior_param
        prior_pos := hprior
        evidence_pos := n₁_pos
        evidence_neg := n₁_neg }
    let paramsCombined : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams :=
      { prior_param := prior_param
        prior_pos := hprior
        evidence_pos := n₁_pos + n₂_pos
        evidence_neg := n₁_neg + n₂_neg }
    Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.alpha paramsCombined =
      Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.alpha params₁ + n₂_pos ∧
    Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.beta paramsCombined =
      Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.beta params₁ + n₂_neg := by
  simpa using
    Mettapedia.Logic.EvidenceBeta.evidence_aggregation_is_conjugate_update
      prior_param hprior
      (σ₁.countP (fun o => classify o q = true))
      (σ₁.countP (fun o => classify o q = false))
      (σ₂.countP (fun o => classify o q = true))
      (σ₂.countP (fun o => classify o q = false))

/-- Bernoulli/Beta posterior update as a function of positive/negative counts. -/
def bernoulliPosteriorFromCounts
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams)
    (nPos nNeg : ℕ) :
    Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams :=
  { prior_param := params.prior_param
    prior_pos := params.prior_pos
    evidence_pos := params.evidence_pos + nPos
    evidence_neg := params.evidence_neg + nNeg }

/-- Bernoulli/Beta posterior surface over batches of Boolean-classified
observations. -/
def bernoulliConjugatePosteriorSurface
    (classify : Obs → Query → Bool) :
    ConjugatePosteriorSurface Obs Query BinaryEvidence Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams where
  stat := bernoulliStatistic classify
  posterior params σ q :=
    { prior_param := params.prior_param
      prior_pos := params.prior_pos
      evidence_pos := params.evidence_pos + σ.countP (fun o => classify o q = true)
      evidence_neg := params.evidence_neg + σ.countP (fun o => classify o q = false) }
  posterior_zero params q := by
    cases params
    simp
  posterior_add params σ₁ σ₂ q := by
    cases params
    simp [Multiset.countP_add, add_assoc]

theorem bernoulliConjugatePosteriorSurface_eq_bernoulliPosteriorFromCounts
    (classify : Obs → Query → Bool)
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams)
    (σ : Multiset Obs) (q : Query) :
    (bernoulliConjugatePosteriorSurface classify).posterior params σ q =
      bernoulliPosteriorFromCounts params
        (σ.countP (fun o => classify o q = true))
        (σ.countP (fun o => classify o q = false)) := by
  cases params
  rfl

private theorem bernoulliPosCount_eq_genAdditiveExtension
    (classify : Obs → Query → Bool)
    (σ : Multiset Obs) (q : Query) :
    genAdditiveExtension
        (fun o q => if classify o q = true then (1 : ℕ) else 0) σ q =
      σ.countP (fun o => classify o q = true) := by
  induction σ using Multiset.induction_on with
  | empty =>
      simp [genAdditiveExtension_zero]
  | @cons o σ ih =>
      by_cases h : classify o q = true
      · rw [genAdditiveExtension_cons]
        simp [h, ih, Multiset.countP_cons_of_pos, Nat.add_comm]
      · rw [genAdditiveExtension_cons]
        simp [h, ih, Multiset.countP_cons_of_neg]

private theorem bernoulliNegCount_eq_genAdditiveExtension
    (classify : Obs → Query → Bool)
    (σ : Multiset Obs) (q : Query) :
    genAdditiveExtension
        (fun o q => if classify o q = false then (1 : ℕ) else 0) σ q =
      σ.countP (fun o => classify o q = false) := by
  induction σ using Multiset.induction_on with
  | empty =>
      simp [genAdditiveExtension_zero]
  | @cons o σ ih =>
      by_cases h : classify o q = false
      · rw [genAdditiveExtension_cons]
        simp [h, ih, Multiset.countP_cons_of_pos, Nat.add_comm]
      · rw [genAdditiveExtension_cons]
        simp [h, ih, Multiset.countP_cons_of_neg]

theorem bernoulliConjugatePosteriorSurface_eq_of_countExtensions
    (classify : Obs → Query → Bool)
    {Epos Eneg : Multiset Obs → Query → ℕ}
    (hEpos :
      GenIsAdditiveExtension
        (fun o q => if classify o q = true then (1 : ℕ) else 0) Epos)
    (hEneg :
      GenIsAdditiveExtension
        (fun o q => if classify o q = false then (1 : ℕ) else 0) Eneg)
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams)
    (σ : Multiset Obs) (q : Query) :
    (bernoulliConjugatePosteriorSurface classify).posterior params σ q =
      bernoulliPosteriorFromCounts params (Epos σ q) (Eneg σ q) := by
  rw [bernoulliConjugatePosteriorSurface_eq_bernoulliPosteriorFromCounts]
  have hpos :
      Epos σ q =
        σ.countP (fun o => classify o q = true) := by
    calc
      Epos σ q =
          genAdditiveExtension
            (fun o q => if classify o q = true then (1 : ℕ) else 0) σ q := by
              rw [eq_genAdditiveExtension _ hEpos]
      _ = σ.countP (fun o => classify o q = true) := by
              exact bernoulliPosCount_eq_genAdditiveExtension classify σ q
  have hneg :
      Eneg σ q =
        σ.countP (fun o => classify o q = false) := by
    calc
      Eneg σ q =
          genAdditiveExtension
            (fun o q => if classify o q = false then (1 : ℕ) else 0) σ q := by
              rw [eq_genAdditiveExtension _ hEneg]
      _ = σ.countP (fun o => classify o q = false) := by
              exact bernoulliNegCount_eq_genAdditiveExtension classify σ q
  simp [hpos, hneg]

theorem bernoulliStatistic_inducedWorldModelEvidence_pos_neg
    (classify : Obs → Query → Bool)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence :=
      (bernoulliStatistic classify).inducedWorldModel
    let e :=
      AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := BinaryEvidence) σ q
    e.pos = (σ.countP (fun o => classify o q = true) : ℝ≥0∞) ∧
      e.neg = (σ.countP (fun o => classify o q = false) : ℝ≥0∞) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence :=
    (bernoulliStatistic classify).inducedWorldModel
  constructor
  · rw [SufficientStatisticSurface.inducedWorldModel_evidence_eq_aggregate
      (S := bernoulliStatistic classify)]
    exact bernoulliStatistic_aggregate_pos classify σ q
  · rw [SufficientStatisticSurface.inducedWorldModel_evidence_eq_aggregate
      (S := bernoulliStatistic classify)]
    exact bernoulliStatistic_aggregate_neg classify σ q

theorem bernoulliConjugatePosteriorSurface_exists_counts_of_inducedWorldModelEvidence
    (classify : Obs → Query → Bool)
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence :=
      (bernoulliStatistic classify).inducedWorldModel
    let e :=
      AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := BinaryEvidence) σ q
    ∃ nPos nNeg : ℕ,
      e.pos = (nPos : ℝ≥0∞) ∧
      e.neg = (nNeg : ℝ≥0∞) ∧
      (bernoulliConjugatePosteriorSurface classify).posterior params σ q =
        bernoulliPosteriorFromCounts params nPos nNeg := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence :=
    (bernoulliStatistic classify).inducedWorldModel
  refine ⟨σ.countP (fun o => classify o q = true),
    σ.countP (fun o => classify o q = false), ?_, ?_, ?_⟩
  · exact (bernoulliStatistic_inducedWorldModelEvidence_pos_neg classify σ q).1
  · exact (bernoulliStatistic_inducedWorldModelEvidence_pos_neg classify σ q).2
  · exact bernoulliConjugatePosteriorSurface_eq_bernoulliPosteriorFromCounts
      classify params σ q

/-- Bernoulli posterior update as a function of the binary evidence extracted by
the induced world model. -/
private noncomputable def bernoulliCountsOfEvidence (e : BinaryEvidence) : ℕ × ℕ :=
  by
    classical
    exact
      if h : ∃ c : ℕ × ℕ,
          e.pos = (c.1 : ℝ≥0∞) ∧ e.neg = (c.2 : ℝ≥0∞) then
        Classical.choose h
      else
        (0, 0)

private theorem bernoulliCountsOfEvidence_eq
    (e : BinaryEvidence) {nPos nNeg : ℕ}
    (hpos : e.pos = (nPos : ℝ≥0∞))
    (hneg : e.neg = (nNeg : ℝ≥0∞)) :
    bernoulliCountsOfEvidence e = (nPos, nNeg) := by
  classical
  unfold bernoulliCountsOfEvidence
  let c : ℕ × ℕ := (nPos, nNeg)
  have hex :
      ∃ c : ℕ × ℕ, e.pos = (c.1 : ℝ≥0∞) ∧ e.neg = (c.2 : ℝ≥0∞) :=
    ⟨c, hpos, hneg⟩
  rw [dif_pos hex]
  have hchoose := Classical.choose_spec hex
  apply Prod.ext
  · have hcast :
        ((Classical.choose hex).1 : ℝ≥0∞) = (nPos : ℝ≥0∞) := by
      calc
        ((Classical.choose hex).1 : ℝ≥0∞) = e.pos := by
          simpa using hchoose.1.symm
        _ = (nPos : ℝ≥0∞) := hpos
    exact_mod_cast hcast
  · have hcast :
        ((Classical.choose hex).2 : ℝ≥0∞) = (nNeg : ℝ≥0∞) := by
      calc
        ((Classical.choose hex).2 : ℝ≥0∞) = e.neg := by
          simpa using hchoose.2.symm
        _ = (nNeg : ℝ≥0∞) := hneg
    exact_mod_cast hcast

private noncomputable def bernoulliPosteriorFromEvidence
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams)
    (e : BinaryEvidence) :
    Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams :=
  let c := bernoulliCountsOfEvidence e
  bernoulliPosteriorFromCounts params c.1 c.2

theorem bernoulliConjugatePosteriorSurface_eq_of_inducedWorldModelEvidence
    (classify : Obs → Query → Bool)
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence :=
      (bernoulliStatistic classify).inducedWorldModel
    (bernoulliConjugatePosteriorSurface classify).posterior params σ q =
      bernoulliPosteriorFromEvidence params
        (AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query)
          (Ev := BinaryEvidence) σ q) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence :=
    (bernoulliStatistic classify).inducedWorldModel
  refine
    ConjugatePosteriorSurface.posterior_eq_of_inducedWorldModelEvidence
      (P := bernoulliConjugatePosteriorSurface classify)
      (lift := fun prior _ e => bernoulliPosteriorFromEvidence prior e)
      (hlift := ?_)
      params σ q
  intro prior τ r
  rw [bernoulliConjugatePosteriorSurface_eq_bernoulliPosteriorFromCounts]
  unfold bernoulliPosteriorFromEvidence
  have hpos :
      (SufficientStatisticSurface.aggregate (bernoulliStatistic classify) τ r).pos =
        (τ.countP (fun o => classify o r = true) : ℝ≥0∞) := by
    simpa using bernoulliStatistic_aggregate_pos classify τ r
  have hneg :
      (SufficientStatisticSurface.aggregate (bernoulliStatistic classify) τ r).neg =
        (τ.countP (fun o => classify o r = false) : ℝ≥0∞) := by
    simpa using bernoulliStatistic_aggregate_neg classify τ r
  have hcounts :
      bernoulliCountsOfEvidence
          (SufficientStatisticSurface.aggregate (bernoulliStatistic classify) τ r) =
        (τ.countP (fun o => classify o r = true),
          τ.countP (fun o => classify o r = false)) :=
    bernoulliCountsOfEvidence_eq
      (SufficientStatisticSurface.aggregate (bernoulliStatistic classify) τ r) hpos hneg
  change
    bernoulliPosteriorFromCounts prior
        (τ.countP (fun o => classify o r = true))
        (τ.countP (fun o => classify o r = false)) =
      bernoulliPosteriorFromEvidence prior
        ((bernoulliStatistic classify).aggregate τ r)
  unfold bernoulliPosteriorFromEvidence
  rw [hcounts]

theorem bernoulliConjugatePosteriorSurface_ne_of_inducedWorldModelEvidence_ne
    (classify : Obs → Query → Bool)
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams)
    {σ₁ σ₂ : Multiset Obs} (q : Query)
    (hneq :
      letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
      letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence :=
        (bernoulliStatistic classify).inducedWorldModel
      AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := BinaryEvidence) σ₁ q ≠
        AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := BinaryEvidence) σ₂ q) :
    (bernoulliConjugatePosteriorSurface classify).posterior params σ₁ q ≠
      (bernoulliConjugatePosteriorSurface classify).posterior params σ₂ q := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query BinaryEvidence :=
    (bernoulliStatistic classify).inducedWorldModel
  intro hEq
  let e₁ :=
    AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := BinaryEvidence) σ₁ q
  let e₂ :=
    AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query) (Ev := BinaryEvidence) σ₂ q
  have hEqLift :
      bernoulliPosteriorFromEvidence params e₁ =
        bernoulliPosteriorFromEvidence params e₂ := by
    rw [← bernoulliConjugatePosteriorSurface_eq_of_inducedWorldModelEvidence
        (classify := classify) (params := params) (σ := σ₁) (q := q),
      ← bernoulliConjugatePosteriorSurface_eq_of_inducedWorldModelEvidence
        (classify := classify) (params := params) (σ := σ₂) (q := q)]
    simpa [e₁, e₂] using hEq
  have hpos₁ :
      e₁.pos = (σ₁.countP (fun o => classify o q = true) : ℝ≥0∞) := by
    simpa [e₁] using (bernoulliStatistic_inducedWorldModelEvidence_pos_neg classify σ₁ q).1
  have hneg₁ :
      e₁.neg = (σ₁.countP (fun o => classify o q = false) : ℝ≥0∞) := by
    simpa [e₁] using (bernoulliStatistic_inducedWorldModelEvidence_pos_neg classify σ₁ q).2
  have hpos₂ :
      e₂.pos = (σ₂.countP (fun o => classify o q = true) : ℝ≥0∞) := by
    simpa [e₂] using (bernoulliStatistic_inducedWorldModelEvidence_pos_neg classify σ₂ q).1
  have hneg₂ :
      e₂.neg = (σ₂.countP (fun o => classify o q = false) : ℝ≥0∞) := by
    simpa [e₂] using (bernoulliStatistic_inducedWorldModelEvidence_pos_neg classify σ₂ q).2
  have hcounts₁ :
      bernoulliCountsOfEvidence e₁ =
        (σ₁.countP (fun o => classify o q = true),
          σ₁.countP (fun o => classify o q = false)) :=
    bernoulliCountsOfEvidence_eq e₁ hpos₁ hneg₁
  have hcounts₂ :
      bernoulliCountsOfEvidence e₂ =
        (σ₂.countP (fun o => classify o q = true),
          σ₂.countP (fun o => classify o q = false)) :=
    bernoulliCountsOfEvidence_eq e₂ hpos₂ hneg₂
  rw [show bernoulliPosteriorFromEvidence params e₁ =
      bernoulliPosteriorFromCounts params
        (σ₁.countP (fun o => classify o q = true))
        (σ₁.countP (fun o => classify o q = false)) by
        unfold bernoulliPosteriorFromEvidence
        rw [hcounts₁],
      show bernoulliPosteriorFromEvidence params e₂ =
      bernoulliPosteriorFromCounts params
        (σ₂.countP (fun o => classify o q = true))
        (σ₂.countP (fun o => classify o q = false)) by
        unfold bernoulliPosteriorFromEvidence
        rw [hcounts₂]] at hEqLift
  have hposCount :
      σ₁.countP (fun o => classify o q = true) =
        σ₂.countP (fun o => classify o q = true) := by
    have hfield :=
      congrArg Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.evidence_pos hEqLift
    have hfield' :
        params.evidence_pos + σ₁.countP (fun o => classify o q = true) =
          params.evidence_pos + σ₂.countP (fun o => classify o q = true) := by
      simpa [bernoulliPosteriorFromCounts] using hfield
    exact Nat.add_left_cancel hfield'
  have hnegCount :
      σ₁.countP (fun o => classify o q = false) =
        σ₂.countP (fun o => classify o q = false) := by
    have hfield :=
      congrArg Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.evidence_neg hEqLift
    have hfield' :
        params.evidence_neg + σ₁.countP (fun o => classify o q = false) =
          params.evidence_neg + σ₂.countP (fun o => classify o q = false) := by
      simpa [bernoulliPosteriorFromCounts] using hfield
    exact Nat.add_left_cancel hfield'
  apply hneq
  apply BinaryEvidence.ext'
  · calc
      e₁.pos = (σ₁.countP (fun o => classify o q = true) : ℝ≥0∞) := hpos₁
      _ = (σ₂.countP (fun o => classify o q = true) : ℝ≥0∞) := by simp [hposCount]
      _ = e₂.pos := hpos₂.symm
  · calc
      e₁.neg = (σ₁.countP (fun o => classify o q = false) : ℝ≥0∞) := hneg₁
      _ = (σ₂.countP (fun o => classify o q = false) : ℝ≥0∞) := by simp [hnegCount]
      _ = e₂.neg := hneg₂.symm

theorem bernoulliConjugatePosteriorSurface_alpha_beta
    (classify : Obs → Query → Bool)
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams)
    (σ : Multiset Obs) (q : Query) :
    let params' := (bernoulliConjugatePosteriorSurface classify).posterior params σ q
    Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.alpha params' =
      Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.alpha params +
        σ.countP (fun o => classify o q = true) ∧
    Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.beta params' =
      Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.beta params +
        σ.countP (fun o => classify o q = false) := by
  cases params
  simp [bernoulliConjugatePosteriorSurface,
    Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.alpha,
    Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.beta, add_assoc]

theorem bernoulliConjugatePosteriorSurface_alpha_beta_via_evidenceBeta
    (classify : Obs → Query → Bool)
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams)
    (σ : Multiset Obs) (q : Query) :
    let params' := (bernoulliConjugatePosteriorSurface classify).posterior params σ q
    Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.alpha params' =
      Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.alpha params +
        σ.countP (fun o => classify o q = true) ∧
    Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.beta params' =
      Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.beta params +
        σ.countP (fun o => classify o q = false) := by
  cases params with
  | mk prior_param prior_pos evidence_pos evidence_neg =>
      dsimp [bernoulliConjugatePosteriorSurface, bernoulliPosteriorFromCounts,
        Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.alpha,
        Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.beta]
      exact
        Mettapedia.Logic.EvidenceBeta.evidence_aggregation_is_conjugate_update
          prior_param prior_pos evidence_pos evidence_neg
          (σ.countP (fun o => classify o q = true))
          (σ.countP (fun o => classify o q = false))

private theorem countP_true_add_countP_false
    (f : Obs → Bool) (σ : Multiset Obs) :
    σ.countP (fun o => f o = true) + σ.countP (fun o => f o = false) = σ.card := by
  induction σ using Multiset.induction_on with
  | empty =>
      simp
  | @cons o σ ih =>
      cases h : f o <;> simp [h]
      all_goals omega

theorem bernoulliConjugatePosteriorSurface_totalPseudoCount
    (classify : Obs → Query → Bool)
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams)
    (σ : Multiset Obs) (q : Query) :
    let params' := (bernoulliConjugatePosteriorSurface classify).posterior params σ q
    Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.alpha params' +
        Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.beta params' =
    Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.alpha params +
        Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams.beta params +
        (σ.card : ℝ) := by
  dsimp
  rcases bernoulliConjugatePosteriorSurface_alpha_beta classify params σ q with ⟨hα, hβ⟩
  rw [hα, hβ]
  have hcount :
      ((σ.countP (fun o => classify o q = true) : ℕ) : ℝ) +
          ((σ.countP (fun o => classify o q = false) : ℕ) : ℝ) =
        (σ.card : ℝ) := by
    exact_mod_cast countP_true_add_countP_false (fun o => classify o q) σ
  linarith

theorem bernoulliConjugatePosteriorSurface_ne_of_nonempty
    (classify : Obs → Query → Bool)
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    (bernoulliConjugatePosteriorSurface classify).posterior params σ q ≠ params := by
  intro hEq
  have hsum :=
    bernoulliConjugatePosteriorSurface_totalPseudoCount
      (classify := classify) (params := params) (σ := σ) (q := q)
  rw [hEq] at hsum
  have hcard_pos_nat : 0 < σ.card := Multiset.card_pos.mpr hσ
  have hcard_pos : (0 : ℝ) < (σ.card : ℝ) := by
    exact_mod_cast hcard_pos_nat
  linarith

theorem bernoulliConjugatePosteriorSurface_double_ne_single_of_nonempty
    (classify : Obs → Query → Bool)
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    (bernoulliConjugatePosteriorSurface classify).posterior params (σ + σ) q ≠
      (bernoulliConjugatePosteriorSurface classify).posterior params σ q := by
  exact
    ConjugatePosteriorSurface.posterior_double_ne_single_of_nonempty
      (P := bernoulliConjugatePosteriorSurface classify)
      (hneq := fun prior {τ} hτ =>
        bernoulliConjugatePosteriorSurface_ne_of_nonempty
          (classify := classify) (params := prior) hτ q)
      params hσ

theorem bernoulliConjugatePosteriorSurface_not_add_idempotent
    (classify : Obs → Query → Bool)
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams)
    (o : Obs) (q : Query) :
    ¬ ∀ σ : Multiset Obs,
        (bernoulliConjugatePosteriorSurface classify).posterior params (σ + σ) q =
          (bernoulliConjugatePosteriorSurface classify).posterior params σ q := by
  exact
    ConjugatePosteriorSurface.not_posterior_add_idempotent_of_observation
      (P := bernoulliConjugatePosteriorSurface classify)
      (hneq := fun prior {τ} hτ =>
        bernoulliConjugatePosteriorSurface_ne_of_nonempty
          (classify := classify) (params := prior) hτ q)
      params o

theorem bernoulliConjugatePosteriorSurface_not_add_idempotent_global
    [Nonempty Obs] [Nonempty Query]
    (classify : Obs → Query → Bool)
    (params : Mettapedia.Logic.EvidenceBeta.EvidenceBetaParams) :
    ¬ ∀ q σ,
        (bernoulliConjugatePosteriorSurface classify).posterior params (σ + σ) q =
          (bernoulliConjugatePosteriorSurface classify).posterior params σ q := by
  exact
    ConjugatePosteriorSurface.not_posterior_add_idempotent
      (P := bernoulliConjugatePosteriorSurface classify)
      (prior := params)
      (hneq := fun prior' {τ} q hτ =>
        bernoulliConjugatePosteriorSurface_ne_of_nonempty
          (classify := classify) (params := prior') hτ q)

/-- One categorical observation contributes one count in exactly one component. -/
def categoricalObservation {k : ℕ} (i : Fin k) : MultiEvidence k :=
  ⟨fun j => if j = i then 1 else 0⟩

theorem categoricalObservation_total_one {k : ℕ} (i : Fin k) :
    (categoricalObservation i).total = 1 := by
  simp [categoricalObservation, MultiEvidence.total]

/-- Query-indexed categorical/Dirichlet sufficient-statistic surface. -/
def categoricalStatistic {k : ℕ} (classify : Obs → Query → Fin k) :
    SufficientStatisticSurface Obs Query (MultiEvidence k) where
  observe o q := categoricalObservation (classify o q)

theorem categoricalStatistic_unitObservation {k : ℕ}
    (classify : Obs → Query → Fin k) :
    UnitObservation (categoricalStatistic classify) := by
  intro o q
  change (↑(categoricalObservation (classify o q)).total : ℝ≥0∞) = 1
  simp [categoricalObservation_total_one]

theorem categoricalStatistic_queryObservationCount {k : ℕ}
    (classify : Obs → Query → Fin k)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query (MultiEvidence k) :=
      (categoricalStatistic classify).inducedWorldModel
    AdditiveWorldModel.queryObservationCount
        (State := Multiset Obs) (Query := Query) (Ev := MultiEvidence k) σ q =
      (σ.card : ℝ≥0∞) := by
  simpa using
    queryObservationCount_inducedWorldModel_of_unit
      (S := categoricalStatistic classify)
      (categoricalStatistic_unitObservation classify) σ q

theorem categoricalStatistic_queryObservationConfidence {k : ℕ}
    (κ : ℝ≥0∞) (classify : Obs → Query → Fin k)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query (MultiEvidence k) :=
      (categoricalStatistic classify).inducedWorldModel
    AdditiveWorldModel.queryObservationConfidence
        (State := Multiset Obs) (Query := Query) (Ev := MultiEvidence k) κ σ q =
      (σ.card : ℝ≥0∞) / ((σ.card : ℝ≥0∞) + κ) := by
  simpa using
    queryObservationConfidence_inducedWorldModel_of_unit
      (S := categoricalStatistic classify)
      κ (categoricalStatistic_unitObservation classify) σ q

theorem categoricalStatistic_queryEvidence_double_ne_single_of_nonempty {k : ℕ}
    (classify : Obs → Query → Fin k)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query (MultiEvidence k) :=
      (categoricalStatistic classify).inducedWorldModel
    AdditiveWorldModel.extract
        (State := Multiset Obs) (Query := Query) (Ev := MultiEvidence k) (σ + σ) q ≠
      AdditiveWorldModel.extract
        (State := Multiset Obs) (Query := Query) (Ev := MultiEvidence k) σ q := by
  simpa using
    evidence_inducedWorldModel_double_ne_single_of_unit_nonempty
      (S := categoricalStatistic classify)
      (categoricalStatistic_unitObservation classify) hσ q

theorem categoricalStatistic_revision_not_idempotent_of_nonempty {k : ℕ}
    (classify : Obs → Query → Fin k)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query (MultiEvidence k) :=
      (categoricalStatistic classify).inducedWorldModel
    (σ + σ : Multiset Obs) ≠ σ := by
  simpa using
    revision_not_idempotent_inducedWorldModel_of_unit_nonempty
      (S := categoricalStatistic classify)
      (categoricalStatistic_unitObservation classify) hσ q

theorem categoricalStatistic_not_global_revision_idempotent {k : ℕ}
    [Nonempty Obs] [Nonempty Query]
    (classify : Obs → Query → Fin k) :
    ¬ ∀ W : Multiset Obs, W + W = W := by
  simpa using
    not_global_revision_idempotent_inducedWorldModel_of_unit
      (S := categoricalStatistic classify)
      (categoricalStatistic_unitObservation classify)

theorem categoricalStatistic_dirichlet_update {k : ℕ}
    (prior : DirichletParams k)
    (classify : Obs → Query → Fin k)
    (σ₁ σ₂ : Multiset Obs) (q : Query) (i : Fin k) :
    let e₁ := aggregate (categoricalStatistic classify) σ₁ q
    let e₂ := aggregate (categoricalStatistic classify) σ₂ q
    (⟨prior, aggregate (categoricalStatistic classify) (σ₁ + σ₂) q⟩ : EvidenceDirichletParams k).posteriorParam i =
      (⟨prior, e₁⟩ : EvidenceDirichletParams k).posteriorParam i + e₂.counts i := by
  let e₁ := aggregate (categoricalStatistic classify) σ₁ q
  let e₂ := aggregate (categoricalStatistic classify) σ₂ q
  have hadd :
      aggregate (categoricalStatistic classify) (σ₁ + σ₂) q = e₁ + e₂ := by
    simpa [e₁, e₂] using
      aggregate_add (S := categoricalStatistic classify) σ₁ σ₂ q
  rw [hadd]
  simpa [e₁, e₂] using dirichlet_hplus_is_update (prior := prior) e₁ e₂ i

/-- Dirichlet posterior update as a function of aggregated categorical
evidence. -/
def categoricalPosteriorFromAggregate {k : ℕ}
    (params : EvidenceDirichletParams k)
    (e : MultiEvidence k) :
    EvidenceDirichletParams k :=
  { prior := params.prior
    evidence := params.evidence + e }

/-- Categorical/Dirichlet posterior surface over batches of classified
observations. -/
noncomputable def categoricalConjugatePosteriorSurface {k : ℕ}
    (classify : Obs → Query → Fin k) :
    ConjugatePosteriorSurface Obs Query (MultiEvidence k) (EvidenceDirichletParams k) where
  stat := categoricalStatistic classify
  posterior params σ q :=
    { prior := params.prior
      evidence := params.evidence + aggregate (categoricalStatistic classify) σ q }
  posterior_zero params q := by
    cases params
    simp
  posterior_add params σ₁ σ₂ q := by
    cases params
    rw [aggregate_add]
    simp [add_assoc]

theorem categoricalConjugatePosteriorSurface_eq_categoricalPosteriorFromAggregate {k : ℕ}
    (classify : Obs → Query → Fin k)
    (params : EvidenceDirichletParams k)
    (σ : Multiset Obs) (q : Query) :
    (categoricalConjugatePosteriorSurface classify).posterior params σ q =
      categoricalPosteriorFromAggregate params
        (aggregate (categoricalStatistic classify) σ q) := by
  rfl

theorem categoricalConjugatePosteriorSurface_eq_of_isAdditiveExtension {k : ℕ}
    (classify : Obs → Query → Fin k)
    {E : Multiset Obs → Query → MultiEvidence k}
    (hE : GenIsAdditiveExtension (categoricalStatistic classify).observe E)
    (params : EvidenceDirichletParams k)
    (σ : Multiset Obs) (q : Query) :
    (categoricalConjugatePosteriorSurface classify).posterior params σ q =
      categoricalPosteriorFromAggregate params (E σ q) := by
  exact
    ConjugatePosteriorSurface.posterior_eq_of_isAdditiveExtension
      (P := categoricalConjugatePosteriorSurface classify)
      (lift := fun prior _ e => categoricalPosteriorFromAggregate prior e)
      (hlift := fun prior τ r =>
        categoricalConjugatePosteriorSurface_eq_categoricalPosteriorFromAggregate
          (classify := classify) (params := prior) (σ := τ) (q := r))
      hE params σ q

theorem categoricalConjugatePosteriorSurface_eq_of_inducedWorldModelEvidence {k : ℕ}
    (classify : Obs → Query → Fin k)
    (params : EvidenceDirichletParams k)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query (MultiEvidence k) :=
      (categoricalStatistic classify).inducedWorldModel
    (categoricalConjugatePosteriorSurface classify).posterior params σ q =
      categoricalPosteriorFromAggregate params
        (AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query)
          (Ev := MultiEvidence k) σ q) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query (MultiEvidence k) :=
    (categoricalStatistic classify).inducedWorldModel
  simpa using
    ConjugatePosteriorSurface.posterior_eq_of_inducedWorldModelEvidence
      (P := categoricalConjugatePosteriorSurface classify)
      (lift := fun prior _ e => categoricalPosteriorFromAggregate prior e)
      (hlift := fun prior τ r =>
        categoricalConjugatePosteriorSurface_eq_categoricalPosteriorFromAggregate
          (classify := classify) (params := prior) (σ := τ) (q := r))
      params σ q

private theorem categoricalPosteriorFromAggregate_injective {k : ℕ}
    (params : EvidenceDirichletParams k) :
    Function.Injective (categoricalPosteriorFromAggregate params) := by
  intro e₁ e₂ hEq
  have hEvidence :
      params.evidence + e₁ = params.evidence + e₂ := by
    simpa [categoricalPosteriorFromAggregate] using
      congrArg EvidenceDirichletParams.evidence hEq
  ext i
  have hcount := congrArg (fun e : MultiEvidence k => e.counts i) hEvidence
  change params.evidence.counts i + e₁.counts i =
      params.evidence.counts i + e₂.counts i at hcount
  exact Nat.add_left_cancel hcount

theorem categoricalConjugatePosteriorSurface_ne_of_inducedWorldModelEvidence_ne {k : ℕ}
    (classify : Obs → Query → Fin k)
    (params : EvidenceDirichletParams k)
    {σ₁ σ₂ : Multiset Obs} (q : Query)
    (hneq :
      letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
      letI : AdditiveWorldModel (Multiset Obs) Query (MultiEvidence k) :=
        (categoricalStatistic classify).inducedWorldModel
      AdditiveWorldModel.extract
          (State := Multiset Obs) (Query := Query) (Ev := MultiEvidence k) σ₁ q ≠
        AdditiveWorldModel.extract
          (State := Multiset Obs) (Query := Query) (Ev := MultiEvidence k) σ₂ q) :
    (categoricalConjugatePosteriorSurface classify).posterior params σ₁ q ≠
      (categoricalConjugatePosteriorSurface classify).posterior params σ₂ q := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query (MultiEvidence k) :=
    (categoricalStatistic classify).inducedWorldModel
  exact
    ConjugatePosteriorSurface.posterior_ne_of_inducedWorldModelEvidence_ne
      (P := categoricalConjugatePosteriorSurface classify)
      (lift := fun prior _ e => categoricalPosteriorFromAggregate prior e)
      (hlift := fun prior τ r =>
        categoricalConjugatePosteriorSurface_eq_categoricalPosteriorFromAggregate
          (classify := classify) (params := prior) (σ := τ) (q := r))
      (hinj := fun prior _ => categoricalPosteriorFromAggregate_injective prior)
      params q hneq

theorem categoricalConjugatePosteriorSurface_update {k : ℕ}
    (classify : Obs → Query → Fin k)
    (params : EvidenceDirichletParams k)
    (σ : Multiset Obs) (q : Query) (i : Fin k) :
    let params' := (categoricalConjugatePosteriorSurface classify).posterior params σ q
    params'.posteriorParam i =
      params.posteriorParam i +
        (aggregate (categoricalStatistic classify) σ q).counts i := by
  cases params with
  | mk prior evidence =>
      change
          prior.priorParams i +
              ↑((evidence + aggregate (categoricalStatistic classify) σ q).counts i) =
            (prior.priorParams i + ↑(evidence.counts i)) +
              (aggregate (categoricalStatistic classify) σ q).counts i
      rw [show (evidence + aggregate (categoricalStatistic classify) σ q).counts i =
          evidence.counts i + (aggregate (categoricalStatistic classify) σ q).counts i by
            rfl]
      rw [Nat.cast_add]
      ring

theorem categoricalConjugatePosteriorSurface_update_via_evidenceDirichlet {k : ℕ}
    (classify : Obs → Query → Fin k)
    (params : EvidenceDirichletParams k)
    (σ : Multiset Obs) (q : Query) (i : Fin k) :
    let params' := (categoricalConjugatePosteriorSurface classify).posterior params σ q
    params'.posteriorParam i =
      params.posteriorParam i +
        (aggregate (categoricalStatistic classify) σ q).counts i := by
  cases params with
  | mk prior evidence =>
      simpa [categoricalConjugatePosteriorSurface,
        categoricalPosteriorFromAggregate] using
        Mettapedia.Logic.EvidenceDirichlet.evidence_aggregation_is_dirichlet_update
          prior evidence (aggregate (categoricalStatistic classify) σ q) i

theorem categoricalStatistic_aggregate_total {k : ℕ}
    (classify : Obs → Query → Fin k)
    (σ : Multiset Obs) (q : Query) :
    (aggregate (categoricalStatistic classify) σ q).total = σ.card := by
  induction σ using Multiset.induction_on with
  | empty =>
      rw [aggregate_zero]
      have hz : (0 : MultiEvidence k).counts = fun _ => 0 := rfl
      simp [MultiEvidence.total, hz]
  | @cons o σ ih =>
      rw [aggregate_cons, MultiEvidence.total_hplus, ih]
      simp [categoricalStatistic, categoricalObservation_total_one, Nat.add_comm]

theorem evidenceDirichletParams_totalConcentration {k : ℕ}
    (params : EvidenceDirichletParams k) :
    params.toPosterior.totalConcentration =
      params.prior.totalConcentration + (params.evidence.total : ℝ) := by
  cases params with
  | mk prior evidence =>
      simp [EvidenceDirichletParams.toPosterior, DirichletParams.totalConcentration,
        EvidenceDirichletParams.posteriorParam, MultiEvidence.total,
        Finset.sum_add_distrib, Nat.cast_sum]

theorem categoricalConjugatePosteriorSurface_totalConcentration {k : ℕ}
    (classify : Obs → Query → Fin k)
    (params : EvidenceDirichletParams k)
    (σ : Multiset Obs) (q : Query) :
    ((categoricalConjugatePosteriorSurface classify).posterior params σ q).toPosterior.totalConcentration =
      params.toPosterior.totalConcentration + (σ.card : ℝ) := by
  rw [categoricalConjugatePosteriorSurface_eq_categoricalPosteriorFromAggregate]
  simp [categoricalPosteriorFromAggregate, evidenceDirichletParams_totalConcentration,
    MultiEvidence.total_hplus, Nat.cast_add]
  have hcard :
      ((genAdditiveExtension (categoricalStatistic classify).observe σ q).total : ℝ) =
        σ.card := by
    simpa [SufficientStatisticSurface.aggregate] using
      congrArg (fun n : ℕ => (n : ℝ))
        (categoricalStatistic_aggregate_total classify σ q)
  rw [hcard]
  ring

theorem categoricalConjugatePosteriorSurface_toPosterior_ne_of_nonempty {k : ℕ}
    (classify : Obs → Query → Fin k)
    (params : EvidenceDirichletParams k)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    ((categoricalConjugatePosteriorSurface classify).posterior params σ q).toPosterior ≠
      params.toPosterior := by
  intro hEq
  have hconc := congrArg DirichletParams.totalConcentration hEq
  rw [categoricalConjugatePosteriorSurface_totalConcentration (classify := classify)
      (params := params) (σ := σ) (q := q)] at hconc
  rw [evidenceDirichletParams_totalConcentration (params := params)] at hconc
  have hcard_pos_nat : 0 < σ.card := Multiset.card_pos.mpr hσ
  have hcard_pos : (0 : ℝ) < (σ.card : ℝ) := by
    exact_mod_cast hcard_pos_nat
  linarith

theorem categoricalConjugatePosteriorSurface_ne_of_nonempty {k : ℕ}
    (classify : Obs → Query → Fin k)
    (params : EvidenceDirichletParams k)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    (categoricalConjugatePosteriorSurface classify).posterior params σ q ≠ params := by
  intro hEq
  apply categoricalConjugatePosteriorSurface_toPosterior_ne_of_nonempty
    (classify := classify) (params := params) hσ q
  exact congrArg EvidenceDirichletParams.toPosterior hEq

theorem categoricalConjugatePosteriorSurface_double_ne_single_of_nonempty {k : ℕ}
    (classify : Obs → Query → Fin k)
    (params : EvidenceDirichletParams k)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    (categoricalConjugatePosteriorSurface classify).posterior params (σ + σ) q ≠
      (categoricalConjugatePosteriorSurface classify).posterior params σ q := by
  exact
    ConjugatePosteriorSurface.posterior_double_ne_single_of_nonempty
      (P := categoricalConjugatePosteriorSurface classify)
      (hneq := fun prior {τ} hτ =>
        categoricalConjugatePosteriorSurface_ne_of_nonempty
          (classify := classify) (params := prior) hτ q)
      params hσ

theorem categoricalConjugatePosteriorSurface_not_add_idempotent {k : ℕ}
    (classify : Obs → Query → Fin k)
    (params : EvidenceDirichletParams k)
    (o : Obs) (q : Query) :
    ¬ ∀ σ : Multiset Obs,
        (categoricalConjugatePosteriorSurface classify).posterior params (σ + σ) q =
          (categoricalConjugatePosteriorSurface classify).posterior params σ q := by
  exact
    ConjugatePosteriorSurface.not_posterior_add_idempotent_of_observation
      (P := categoricalConjugatePosteriorSurface classify)
      (hneq := fun prior {τ} hτ =>
        categoricalConjugatePosteriorSurface_ne_of_nonempty
          (classify := classify) (params := prior) hτ q)
      params o

theorem categoricalConjugatePosteriorSurface_not_add_idempotent_global {k : ℕ}
    [Nonempty Obs] [Nonempty Query]
    (classify : Obs → Query → Fin k)
    (params : EvidenceDirichletParams k) :
    ¬ ∀ q σ,
        (categoricalConjugatePosteriorSurface classify).posterior params (σ + σ) q =
          (categoricalConjugatePosteriorSurface classify).posterior params σ q := by
  exact
    ConjugatePosteriorSurface.not_posterior_add_idempotent
      (P := categoricalConjugatePosteriorSurface classify)
      (prior := params)
      (hneq := fun prior' {τ} q hτ =>
        categoricalConjugatePosteriorSurface_ne_of_nonempty
          (classify := classify) (params := prior') hτ q)

/-- Query-indexed Gaussian/Normal-Gamma sufficient-statistic surface. -/
def gaussianStatistic (value : Obs → Query → ℝ) :
    SufficientStatisticSurface Obs Query NormalGammaEvidence where
  observe o q := NormalGammaEvidence.single (value o q)

theorem gaussianStatistic_unitObservation
    (value : Obs → Query → ℝ) :
    UnitObservation (gaussianStatistic value) := by
  intro o q
  change (↑(NormalGammaEvidence.single (value o q)).n : ℝ≥0∞) = 1
  simp [NormalGammaEvidence.single]

theorem gaussianStatistic_queryObservationCount
    (value : Obs → Query → ℝ)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query NormalGammaEvidence :=
      (gaussianStatistic value).inducedWorldModel
    AdditiveWorldModel.queryObservationCount
        (State := Multiset Obs) (Query := Query) (Ev := NormalGammaEvidence) σ q =
      (σ.card : ℝ≥0∞) := by
  simpa using
    queryObservationCount_inducedWorldModel_of_unit
      (S := gaussianStatistic value)
      (gaussianStatistic_unitObservation value) σ q

theorem gaussianStatistic_queryObservationConfidence
    (κ : ℝ≥0∞) (value : Obs → Query → ℝ)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query NormalGammaEvidence :=
      (gaussianStatistic value).inducedWorldModel
    AdditiveWorldModel.queryObservationConfidence
        (State := Multiset Obs) (Query := Query) (Ev := NormalGammaEvidence) κ σ q =
      (σ.card : ℝ≥0∞) / ((σ.card : ℝ≥0∞) + κ) := by
  simpa using
    queryObservationConfidence_inducedWorldModel_of_unit
      (S := gaussianStatistic value)
      κ (gaussianStatistic_unitObservation value) σ q

theorem gaussianStatistic_queryEvidence_double_ne_single_of_nonempty
    (value : Obs → Query → ℝ)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query NormalGammaEvidence :=
      (gaussianStatistic value).inducedWorldModel
    AdditiveWorldModel.extract
        (State := Multiset Obs) (Query := Query) (Ev := NormalGammaEvidence) (σ + σ) q ≠
      AdditiveWorldModel.extract
        (State := Multiset Obs) (Query := Query) (Ev := NormalGammaEvidence) σ q := by
  simpa using
    evidence_inducedWorldModel_double_ne_single_of_unit_nonempty
      (S := gaussianStatistic value)
      (gaussianStatistic_unitObservation value) hσ q

theorem gaussianStatistic_revision_not_idempotent_of_nonempty
    (value : Obs → Query → ℝ)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query NormalGammaEvidence :=
      (gaussianStatistic value).inducedWorldModel
    (σ + σ : Multiset Obs) ≠ σ := by
  simpa using
    revision_not_idempotent_inducedWorldModel_of_unit_nonempty
      (S := gaussianStatistic value)
      (gaussianStatistic_unitObservation value) hσ q

theorem gaussianStatistic_not_global_revision_idempotent
    [Nonempty Obs] [Nonempty Query]
    (value : Obs → Query → ℝ) :
    ¬ ∀ W : Multiset Obs, W + W = W := by
  simpa using
    not_global_revision_idempotent_inducedWorldModel_of_unit
      (S := gaussianStatistic value)
      (gaussianStatistic_unitObservation value)

theorem gaussianStatistic_normalGamma_sufficient_statistics
    (value : Obs → Query → ℝ)
    (σ₁ σ₂ : Multiset Obs) (q : Query) :
    let e₁ := aggregate (gaussianStatistic value) σ₁ q
    let e₂ := aggregate (gaussianStatistic value) σ₂ q
    let e := aggregate (gaussianStatistic value) (σ₁ + σ₂) q
    e.n = e₁.n + e₂.n ∧
    e.sum = e₁.sum + e₂.sum ∧
    e.sumSq = e₁.sumSq + e₂.sumSq := by
  let e₁ := aggregate (gaussianStatistic value) σ₁ q
  let e₂ := aggregate (gaussianStatistic value) σ₂ q
  have hadd :
      aggregate (gaussianStatistic value) (σ₁ + σ₂) q = e₁ + e₂ := by
    simpa [e₁, e₂] using
      aggregate_add (S := gaussianStatistic value) σ₁ σ₂ q
  rw [hadd]
  exact normalGamma_hplus_sufficient_statistics e₁ e₂

theorem gaussianStatistic_aggregate_realizable
    (value : Obs → Query → ℝ)
    (σ : Multiset Obs) (q : Query) :
    (aggregate (gaussianStatistic value) σ q).Realizable := by
  induction σ using Multiset.induction_on with
  | empty =>
      simpa [aggregate_zero] using
        (NormalGammaEvidence.realizable_zero : (0 : NormalGammaEvidence).Realizable)
  | @cons o σ ih =>
      rw [aggregate_cons]
      simpa [gaussianStatistic] using
        (NormalGammaEvidence.realizable_hplus
          (NormalGammaEvidence.realizable_single (value o q)) ih)

theorem gaussianStatistic_normalGamma_conjugate_update
    (prior : NormalGammaPrior)
    (value : Obs → Query → ℝ)
    (σ₁ σ₂ : Multiset Obs) (q : Query) :
    let e₁ := aggregate (gaussianStatistic value) σ₁ q
    let e₂ := aggregate (gaussianStatistic value) σ₂ q
    posterior prior (aggregate (gaussianStatistic value) (σ₁ + σ₂) q) =
      posterior (posterior prior e₁) e₂ := by
  let e₁ := aggregate (gaussianStatistic value) σ₁ q
  let e₂ := aggregate (gaussianStatistic value) σ₂ q
  have h₁ : e₁.Realizable := by
    simpa [e₁] using gaussianStatistic_aggregate_realizable value σ₁ q
  have h₂ : e₂.Realizable := by
    simpa [e₂] using gaussianStatistic_aggregate_realizable value σ₂ q
  have hadd :
      aggregate (gaussianStatistic value) (σ₁ + σ₂) q = e₁ + e₂ := by
    simpa [e₁, e₂] using
      aggregate_add (S := gaussianStatistic value) σ₁ σ₂ q
  rw [hadd]
  exact posterior_hplus_of_realizable prior e₁ e₂ h₁ h₂

/-- Normal-Gamma posterior update as a function of aggregated Gaussian
evidence. -/
noncomputable def gaussianPosteriorFromAggregate
    (prior : NormalGammaPrior)
    (e : NormalGammaEvidence) :
    NormalGammaPrior :=
  posterior prior e

/-- Gaussian/Normal-Gamma posterior surface over batches of numeric
observations. -/
noncomputable def gaussianConjugatePosteriorSurface
    (value : Obs → Query → ℝ) :
    ConjugatePosteriorSurface Obs Query NormalGammaEvidence NormalGammaPrior where
  stat := gaussianStatistic value
  posterior prior σ q := posterior prior (aggregate (gaussianStatistic value) σ q)
  posterior_zero prior q := by
    ext
    · simpa [aggregate_zero] using
        (show (posterior prior (0 : NormalGammaEvidence)).μ₀ = prior.μ₀ by
          have hn0 : ((0 : NormalGammaEvidence).n : ℝ) = 0 := by
            change ((0 : Nat) : ℝ) = 0
            norm_num
          have hs0 : (0 : NormalGammaEvidence).sum = 0 := by
            rfl
          rw [posterior_mu_eq_of_realizable prior (0 : NormalGammaEvidence)
              NormalGammaEvidence.realizable_zero]
          rw [hn0, hs0]
          field_simp [ne_of_gt prior.κ₀_pos]
          ring)
    · simp
    · simp
    · simpa [aggregate_zero] using
        (show (posterior prior (0 : NormalGammaEvidence)).β₀ = prior.β₀ by
          have hn0 : ((0 : NormalGammaEvidence).n : ℝ) = 0 := by
            change ((0 : Nat) : ℝ) = 0
            norm_num
          have hs0 : (0 : NormalGammaEvidence).sum = 0 := by
            rfl
          have hss0 : (0 : NormalGammaEvidence).sumSq = 0 := by
            rfl
          rw [posterior_beta_eq_of_realizable prior (0 : NormalGammaEvidence)
              NormalGammaEvidence.realizable_zero]
          rw [hn0, hs0, hss0]
          field_simp [ne_of_gt prior.κ₀_pos]
          ring)
  posterior_add prior σ₁ σ₂ q := by
    simpa using gaussianStatistic_normalGamma_conjugate_update prior value σ₁ σ₂ q

theorem gaussianConjugatePosteriorSurface_eq_gaussianPosteriorFromAggregate
    (value : Obs → Query → ℝ)
    (prior : NormalGammaPrior)
    (σ : Multiset Obs) (q : Query) :
    (gaussianConjugatePosteriorSurface value).posterior prior σ q =
      gaussianPosteriorFromAggregate prior
        (aggregate (gaussianStatistic value) σ q) := by
  rfl

theorem gaussianConjugatePosteriorSurface_eq_of_isAdditiveExtension
    (value : Obs → Query → ℝ)
    {E : Multiset Obs → Query → NormalGammaEvidence}
    (hE : GenIsAdditiveExtension (gaussianStatistic value).observe E)
    (prior : NormalGammaPrior)
    (σ : Multiset Obs) (q : Query) :
    (gaussianConjugatePosteriorSurface value).posterior prior σ q =
      gaussianPosteriorFromAggregate prior (E σ q) := by
  exact
    ConjugatePosteriorSurface.posterior_eq_of_isAdditiveExtension
      (P := gaussianConjugatePosteriorSurface value)
      (lift := fun prior' _ e => gaussianPosteriorFromAggregate prior' e)
      (hlift := fun prior' τ r =>
        gaussianConjugatePosteriorSurface_eq_gaussianPosteriorFromAggregate
          (value := value) (prior := prior') (σ := τ) (q := r))
      hE prior σ q

theorem gaussianConjugatePosteriorSurface_eq_of_inducedWorldModelEvidence
    (value : Obs → Query → ℝ)
    (prior : NormalGammaPrior)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query NormalGammaEvidence :=
      (gaussianStatistic value).inducedWorldModel
    (gaussianConjugatePosteriorSurface value).posterior prior σ q =
      gaussianPosteriorFromAggregate prior
        (AdditiveWorldModel.extract (State := Multiset Obs) (Query := Query)
          (Ev := NormalGammaEvidence) σ q) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : AdditiveWorldModel (Multiset Obs) Query NormalGammaEvidence :=
    (gaussianStatistic value).inducedWorldModel
  simpa using
    ConjugatePosteriorSurface.posterior_eq_of_inducedWorldModelEvidence
      (P := gaussianConjugatePosteriorSurface value)
      (lift := fun prior' _ e => gaussianPosteriorFromAggregate prior' e)
      (hlift := fun prior' τ r =>
        gaussianConjugatePosteriorSurface_eq_gaussianPosteriorFromAggregate
          (value := value) (prior := prior') (σ := τ) (q := r))
      prior σ q

private theorem gaussianPosteriorFromAggregate_eq_imp_eq_of_realizable
    (prior : NormalGammaPrior)
    {e₁ e₂ : NormalGammaEvidence}
    (hreal₁ : e₁.Realizable) (hreal₂ : e₂.Realizable)
    (hEq :
      gaussianPosteriorFromAggregate prior e₁ =
        gaussianPosteriorFromAggregate prior e₂) :
    e₁ = e₂ := by
  have hnReal : (e₁.n : ℝ) = e₂.n := by
    simpa [gaussianPosteriorFromAggregate] using
      congrArg NormalGammaPrior.κ₀ hEq
  have hn : e₁.n = e₂.n := by
    exact_mod_cast hnReal
  have hκn_pos : 0 < prior.κ₀ + (e₁.n : ℝ) := by
    have hn_nonneg : 0 ≤ (e₁.n : ℝ) := Nat.cast_nonneg _
    linarith [prior.κ₀_pos, hn_nonneg]
  have hκn_ne : prior.κ₀ + (e₁.n : ℝ) ≠ 0 := ne_of_gt hκn_pos
  have hμ :
      (prior.κ₀ * prior.μ₀ + e₁.sum) / (prior.κ₀ + e₁.n) =
        (prior.κ₀ * prior.μ₀ + e₂.sum) / (prior.κ₀ + e₁.n) := by
    have hμRaw := congrArg NormalGammaPrior.μ₀ hEq
    rw [gaussianPosteriorFromAggregate,
      posterior_mu_eq_of_realizable prior e₁ hreal₁,
      gaussianPosteriorFromAggregate,
      posterior_mu_eq_of_realizable prior e₂ hreal₂] at hμRaw
    simpa [hn] using hμRaw
  have hs : e₁.sum = e₂.sum := by
    field_simp [hκn_ne] at hμ
    linarith
  have hβ :
      prior.β₀ +
          (e₁.sumSq + prior.κ₀ * prior.μ₀ ^ 2 -
              (prior.κ₀ * prior.μ₀ + e₁.sum) ^ 2 / (prior.κ₀ + e₁.n)) / 2 =
        prior.β₀ +
          (e₂.sumSq + prior.κ₀ * prior.μ₀ ^ 2 -
              (prior.κ₀ * prior.μ₀ + e₁.sum) ^ 2 / (prior.κ₀ + e₁.n)) / 2 := by
    have hβRaw := congrArg NormalGammaPrior.β₀ hEq
    rw [gaussianPosteriorFromAggregate,
      posterior_beta_eq_of_realizable prior e₁ hreal₁,
      gaussianPosteriorFromAggregate,
      posterior_beta_eq_of_realizable prior e₂ hreal₂] at hβRaw
    simpa [hn, hs] using hβRaw
  have hsumSq : e₁.sumSq = e₂.sumSq := by
    linarith
  exact NormalGammaEvidence.ext hn hs hsumSq

theorem gaussianConjugatePosteriorSurface_ne_of_inducedWorldModelEvidence_ne
    (value : Obs → Query → ℝ)
    (prior : NormalGammaPrior)
    {σ₁ σ₂ : Multiset Obs} (q : Query)
    (hneq :
      letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
      letI : AdditiveWorldModel (Multiset Obs) Query NormalGammaEvidence :=
        (gaussianStatistic value).inducedWorldModel
      AdditiveWorldModel.extract
          (State := Multiset Obs) (Query := Query) (Ev := NormalGammaEvidence) σ₁ q ≠
        AdditiveWorldModel.extract
          (State := Multiset Obs) (Query := Query) (Ev := NormalGammaEvidence) σ₂ q) :
    (gaussianConjugatePosteriorSurface value).posterior prior σ₁ q ≠
      (gaussianConjugatePosteriorSurface value).posterior prior σ₂ q := by
  let e₁ := aggregate (gaussianStatistic value) σ₁ q
  let e₂ := aggregate (gaussianStatistic value) σ₂ q
  have hneqAgg : e₁ ≠ e₂ := by
    intro hEqAgg
    apply hneq
    simpa [e₁, e₂,
      SufficientStatisticSurface.inducedWorldModel_evidence_eq_aggregate
        (S := gaussianStatistic value)] using hEqAgg
  intro hEq
  apply hneqAgg
  exact
    gaussianPosteriorFromAggregate_eq_imp_eq_of_realizable
      (prior := prior)
      (hreal₁ := by
        simpa [e₁] using gaussianStatistic_aggregate_realizable value σ₁ q)
      (hreal₂ := by
        simpa [e₂] using gaussianStatistic_aggregate_realizable value σ₂ q)
      (by
        rw [← gaussianConjugatePosteriorSurface_eq_gaussianPosteriorFromAggregate
            (value := value) (prior := prior) (σ := σ₁) (q := q),
          ← gaussianConjugatePosteriorSurface_eq_gaussianPosteriorFromAggregate
            (value := value) (prior := prior) (σ := σ₂) (q := q)]
        exact hEq)

theorem gaussianConjugatePosteriorSurface_hplus
    (value : Obs → Query → ℝ)
    (prior : NormalGammaPrior)
    (σ₁ σ₂ : Multiset Obs) (q : Query) :
    let P := gaussianConjugatePosteriorSurface value
    P.posterior prior (σ₁ + σ₂) q =
      P.posterior (P.posterior prior σ₁ q) σ₂ q := by
  simpa using
    (gaussianConjugatePosteriorSurface value).posterior_add prior σ₁ σ₂ q

theorem gaussianConjugatePosteriorSurface_hplus_via_evidenceNormalGamma
    (value : Obs → Query → ℝ)
    (prior : NormalGammaPrior)
    (σ₁ σ₂ : Multiset Obs) (q : Query) :
    let e₁ := aggregate (gaussianStatistic value) σ₁ q
    let e₂ := aggregate (gaussianStatistic value) σ₂ q
    (gaussianConjugatePosteriorSurface value).posterior prior (σ₁ + σ₂) q =
      posterior (posterior prior e₁) e₂ := by
  simpa [gaussianConjugatePosteriorSurface_eq_gaussianPosteriorFromAggregate]
    using gaussianStatistic_normalGamma_conjugate_update prior value σ₁ σ₂ q

theorem gaussianStatistic_aggregate_n
    (value : Obs → Query → ℝ)
    (σ : Multiset Obs) (q : Query) :
    (aggregate (gaussianStatistic value) σ q).n = σ.card := by
  induction σ using Multiset.induction_on with
  | empty =>
      change (0 : NormalGammaEvidence).n = 0
      rfl
  | @cons o σ ih =>
      rw [aggregate_cons, hplus_n, ih]
      simp [gaussianStatistic, NormalGammaEvidence.single, Nat.add_comm]

theorem gaussianConjugatePosteriorSurface_kappa
    (value : Obs → Query → ℝ)
    (prior : NormalGammaPrior)
    (σ : Multiset Obs) (q : Query) :
    ((gaussianConjugatePosteriorSurface value).posterior prior σ q).κ₀ =
      prior.κ₀ + (σ.card : ℝ) := by
  rw [gaussianConjugatePosteriorSurface, posterior_kappa, gaussianStatistic_aggregate_n]

theorem gaussianConjugatePosteriorSurface_alpha
    (value : Obs → Query → ℝ)
    (prior : NormalGammaPrior)
    (σ : Multiset Obs) (q : Query) :
    ((gaussianConjugatePosteriorSurface value).posterior prior σ q).α₀ =
      prior.α₀ + (σ.card : ℝ) / 2 := by
  rw [gaussianConjugatePosteriorSurface, posterior_alpha, gaussianStatistic_aggregate_n]

theorem gaussianConjugatePosteriorSurface_ne_of_nonempty
    (value : Obs → Query → ℝ)
    (prior : NormalGammaPrior)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    (gaussianConjugatePosteriorSurface value).posterior prior σ q ≠ prior := by
  intro hEq
  have hkappa := congrArg NormalGammaPrior.κ₀ hEq
  rw [gaussianConjugatePosteriorSurface_kappa (value := value) (prior := prior)
      (σ := σ) (q := q)] at hkappa
  have hcard_pos_nat : 0 < σ.card := Multiset.card_pos.mpr hσ
  have hcard_pos : (0 : ℝ) < (σ.card : ℝ) := by
    exact_mod_cast hcard_pos_nat
  linarith

theorem gaussianConjugatePosteriorSurface_double_ne_single_of_nonempty
    (value : Obs → Query → ℝ)
    (prior : NormalGammaPrior)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    (gaussianConjugatePosteriorSurface value).posterior prior (σ + σ) q ≠
      (gaussianConjugatePosteriorSurface value).posterior prior σ q := by
  exact
    ConjugatePosteriorSurface.posterior_double_ne_single_of_nonempty
      (P := gaussianConjugatePosteriorSurface value)
      (hneq := fun prior' {τ} hτ =>
        gaussianConjugatePosteriorSurface_ne_of_nonempty
          (value := value) (prior := prior') hτ q)
      prior hσ

theorem gaussianConjugatePosteriorSurface_not_add_idempotent
    (value : Obs → Query → ℝ)
    (prior : NormalGammaPrior)
    (o : Obs) (q : Query) :
    ¬ ∀ σ : Multiset Obs,
        (gaussianConjugatePosteriorSurface value).posterior prior (σ + σ) q =
          (gaussianConjugatePosteriorSurface value).posterior prior σ q := by
  exact
    ConjugatePosteriorSurface.not_posterior_add_idempotent_of_observation
      (P := gaussianConjugatePosteriorSurface value)
      (hneq := fun prior' {τ} hτ =>
        gaussianConjugatePosteriorSurface_ne_of_nonempty
          (value := value) (prior := prior') hτ q)
      prior o

theorem gaussianConjugatePosteriorSurface_not_add_idempotent_global
    [Nonempty Obs] [Nonempty Query]
    (value : Obs → Query → ℝ)
    (prior : NormalGammaPrior) :
    ¬ ∀ q σ,
        (gaussianConjugatePosteriorSurface value).posterior prior (σ + σ) q =
          (gaussianConjugatePosteriorSurface value).posterior prior σ q := by
  exact
    ConjugatePosteriorSurface.not_posterior_add_idempotent
      (P := gaussianConjugatePosteriorSurface value)
      (prior := prior)
      (hneq := fun prior' {τ} q hτ =>
        gaussianConjugatePosteriorSurface_ne_of_nonempty
          (value := value) (prior := prior') hτ q)

/-! ## Contract use-site validation

These theorems demonstrate that a downstream consumer can derive useful results
using only the WM contract surface, without touching family-specific posterior
facts. They serve as smoke tests for the contract's completeness and
discoverability. -/

section ContractUseSite

variable {Obs Query Ev : Type*} [ConjugateEvidence Ev]
    (S : SufficientStatisticSurface Obs Query Ev)

/-- Contract use-site: for any unit-observation surface, a nonempty observation
batch produces nonzero count AND non-idempotent revision simultaneously. This
combines the two main contract pillars in the most direct downstream form. -/
theorem wm_nonempty_implies_nontrivial
    (hunit : UnitObservation S)
    {σ : Multiset Obs} (hσ : σ ≠ 0) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    AdditiveWorldModel.queryObservationCount
        (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q ≠ 0 ∧
      (σ + σ : Multiset Obs) ≠ σ := by
  exact ⟨
    (queryObservationCount_inducedWorldModel_ne_zero_iff_nonempty_of_unit
      (S := S) hunit σ q).2 hσ,
    (revision_not_idempotent_inducedWorldModel_iff_nonempty_of_unit
      (S := S) hunit σ q).2 hσ⟩

/-- Contract use-site: for any unit-observation surface, trivial revision and
zero count and empty fragment are all equivalent. This packages the full
triviality equivalence chain in one statement. -/
theorem wm_trivial_iff
    (hunit : UnitObservation S)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    letI : AdditiveWorldModel (Multiset Obs) Query Ev := S.inducedWorldModel
    ((σ + σ : Multiset Obs) = σ ↔ σ = 0) ∧
    (AdditiveWorldModel.queryObservationCount
        (State := Multiset Obs) (Query := Query) (Ev := Ev) σ q = 0 ↔ σ = 0) := by
  exact ⟨
    revision_idempotent_inducedWorldModel_iff_empty_of_unit (S := S) hunit σ q,
    queryObservationCount_inducedWorldModel_eq_zero_iff_empty_of_unit
      (S := S) hunit σ q⟩

end ContractUseSite

end SufficientStatisticSurface

end Mettapedia.Logic
