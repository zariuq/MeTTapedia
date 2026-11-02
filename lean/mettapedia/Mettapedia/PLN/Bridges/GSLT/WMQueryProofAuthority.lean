import Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
import Mettapedia.GSLT.LanguageDef.SubmissionOutcomeProfile
import Mettapedia.PLN.Bridges.Languages.PLNWMOSLFBridge

/-!
# Occurrence-exact WM query evidence as a CertificateGSLT/SemanticService authority

World-model state construction, query extraction, and semantic inference are
different judgment families.  This module gives the first two a small exact
authority without claiming completeness for every PLN inference rule.

An `OccurrenceRevision` records a binary revision tree whose leaf multiset is
exactly the selected evidence-source multiset.  Equal source payloads retain
multiplicity.  A certificate is a concrete `RevisionTree`; replay checks its
leaf multiset, resulting state, and the claimed binary evidence. The resulting
linear judgment consumes each supplied occurrence exactly once. Distinctness of
actual observations is a separate input contract; `LedgerQueryClaim` uses an
identified registry to enforce it rather than inferring it from equal payloads.

The checker is exact for the independently defined `QueryMeaning`.  It also
projects to the existing multiset-indexed and set-indexed WM judgments, and
then to the existing OSLF atom semantics.  A separately admitted exact
CertificateGSLT definition of the same judgment is proved extensionally equivalent
to revision-tree replay.
-/

namespace Mettapedia.PLN.Bridges.GSLT.WMQueryProofAuthority

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.SubmissionOutcomeProfile
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.EvidenceSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.PLN.Bridges.Languages.PLNWMOSLFBridge
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.WorldModel

set_option autoImplicit false

universe uState uQuery uObservation uCertificate uAuthority

/-! ## Occurrence-exact revision semantics -/

/-- A posterior state built from exactly the named multiset of source
occurrences.  The context is an index, not merely a membership side condition:
revision combines the source multisets of both subderivations. -/
inductive OccurrenceRevision {State : Type uState} [EvidenceType State] :
    Multiset State → State → Prop where
  | source (state : State) : OccurrenceRevision {state} state
  | revise {leftSources rightSources : Multiset State}
      {left right : State} :
      OccurrenceRevision leftSources left →
      OccurrenceRevision rightSources right →
      OccurrenceRevision (leftSources + rightSources) (left + right)

namespace OccurrenceRevision

variable {State : Type uState} [EvidenceType State]

/-- Exact revision refines the canonical resource-consuming WM judgment. -/
theorem toLinearJudgment {sources : Multiset State} {world : State}
    (derivation : OccurrenceRevision sources world) :
    LinearJudgment sources world := by
  induction derivation with
  | source state => exact .base state
  | revise _ _ leftIH rightIH => exact .revise leftIH rightIH

/-- The canonical linear judgment also supplies an occurrence-exact revision. -/
theorem ofLinearJudgment {sources : Multiset State} {world : State}
    (derivation : LinearJudgment sources world) :
    OccurrenceRevision sources world := by
  induction derivation with
  | base state => exact .source state
  | revise _ _ leftIH rightIH => exact .revise leftIH rightIH

/-- This erasure forgets exact consumption into reusable source permissions;
it is a consequence of acceptance, never the checker's acceptance criterion. -/
theorem toWMJudgmentMulti {sources : Multiset State} {world : State}
    (derivation : OccurrenceRevision sources world) :
    WMJudgmentMulti sources world := derivation.toLinearJudgment.toMulti

/-- Further erasure forgets multiplicity but retains the approved source set. -/
theorem toWMJudgmentCtx {sources : Multiset State} {world : State}
    (derivation : OccurrenceRevision sources world) :
    WMJudgmentCtx {state | state ∈ sources} world :=
  derivation.toWMJudgmentMulti.toCtx

end OccurrenceRevision

/-! ## Concrete revision-tree certificates -/

/-- A finite proof term for exact source revision. -/
inductive RevisionTree (State : Type uState) where
  | source (state : State)
  | revise (left right : RevisionTree State)
deriving Repr

namespace RevisionTree

variable {State : Type uState} [EvidenceType State]

/-- Source occurrences used by a tree, with multiplicity. -/
def sources : RevisionTree State → Multiset State
  | .source state => {state}
  | .revise left right => left.sources + right.sources

/-- Posterior state computed by the revision tree. -/
def result : RevisionTree State → State
  | .source state => state
  | .revise left right => left.result + right.result

/-- Interpret leaf identities without changing the authored revision tree. -/
def map {Other : Type*} (resolve : State → Other) : RevisionTree State → RevisionTree Other
  | .source state => .source (resolve state)
  | .revise left right => .revise (left.map resolve) (right.map resolve)

omit [EvidenceType State] in
@[simp] theorem sources_map {Other : Type*} (resolve : State → Other) (tree : RevisionTree State) :
    (tree.map resolve).sources = tree.sources.map resolve := by
  induction tree <;> simp_all [map, sources, Multiset.map_add]

omit [EvidenceType State] in
/-- Every nonempty finite source bag has a revision-tree presentation. -/
theorem exists_sources {sources : Multiset State} (nonempty : sources ≠ 0) :
    ∃ tree : RevisionTree State, tree.sources = sources := by
  classical
  induction sources using Multiset.induction_on with
  | empty => exact (nonempty rfl).elim
  | cons state rest ih =>
      by_cases h : rest = 0
      · subst rest
        exact ⟨.source state, by simp [sources]⟩
      · obtain ⟨tree, ht⟩ := ih h
        exact ⟨.revise (.source state) tree, by simp [sources, ht, Multiset.singleton_add]⟩

/-- Every tree denotes an occurrence-exact WM revision. -/
theorem denotes : (tree : RevisionTree State) →
    OccurrenceRevision tree.sources tree.result
  | .source state => .source state
  | .revise left right => .revise left.denotes right.denotes

end RevisionTree

/-- Every occurrence-exact derivation has a finite revision-tree proof term. -/
theorem OccurrenceRevision.exists_revisionTree
    {State : Type uState} [EvidenceType State]
    {sources : Multiset State} {world : State}
    (derivation : OccurrenceRevision sources world) :
    ∃ tree : RevisionTree State,
      tree.sources = sources ∧ tree.result = world := by
  induction derivation with
  | source state => exact ⟨.source state, rfl, rfl⟩
  | revise left right leftIH rightIH =>
      obtain ⟨leftTree, leftSources, leftResult⟩ := leftIH
      obtain ⟨rightTree, rightSources, rightResult⟩ := rightIH
      refine ⟨.revise leftTree rightTree, ?_, ?_⟩
      · simp [RevisionTree.sources, leftSources, rightSources]
      · simp [RevisionTree.result, leftResult, rightResult]

/-! ## Exact query authority -/

/-- A finite-source world-model query claim.  The observation carrier is
explicit: binary counts, factors, distributions, and certified estimators are
different authority fibres rather than coerced into one scalar type. -/
structure QueryClaim (State : Type uState) (Query : Type uQuery)
    (Observation : Type uObservation) where
  sources : Multiset State
  world : State
  query : Query
  observation : Observation

/-- The state-revision half of a query claim, independent of how observations
are extracted or certified. -/
def RevisionMeaning
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} [EvidenceType State]
    (claim : QueryClaim State Query Observation) : Prop :=
  OccurrenceRevision claim.sources claim.world

/-- The observation half of a query claim.  This relation is stated
independently of any certificate format or replay algorithm. -/
def ObservationMeaning
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation}
    (observe : State → Query → Observation)
    (claim : QueryClaim State Query Observation) : Prop :=
  claim.observation = observe claim.world claim.query

/-- Full finite-source query meaning is the conjunction of exact revision and
the independently selected observation semantics. -/
def QueryMeaning
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} [EvidenceType State]
    (observe : State → Query → Observation)
    (claim : QueryClaim State Query Observation) : Prop :=
  RevisionMeaning claim ∧ ObservationMeaning observe claim

/-- Replay only the occurrence-sensitive revision proof term. -/
def revisionChecker
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation}
    [EvidenceType State] [DecidableEq State] :
    Checker (QueryClaim State Query Observation) (RevisionTree State) where
  check := fun claim tree =>
    decide (tree.sources = claim.sources) &&
      decide (tree.result = claim.world)

theorem revisionChecker_sound
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation}
    [EvidenceType State] [DecidableEq State] :
    (revisionChecker (State := State) (Query := Query)
      (Observation := Observation)).Sound RevisionMeaning := by
  intro claim tree accepted
  have checks : tree.sources = claim.sources ∧ tree.result = claim.world := by
    simpa [revisionChecker] using accepted
  have treeRevision := tree.denotes
  rw [checks.1, checks.2] at treeRevision
  exact treeRevision

theorem revisionChecker_complete
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation}
    [EvidenceType State] [DecidableEq State] :
    (revisionChecker (State := State) (Query := Query)
      (Observation := Observation)).CertificateComplete RevisionMeaning := by
  intro claim meaningful
  obtain ⟨tree, sourceIdentity, resultIdentity⟩ :=
    meaningful.exists_revisionTree
  refine ⟨tree, ?_⟩
  simp [revisionChecker, sourceIdentity, resultIdentity]

/-- Revision-tree replay is exact for occurrence-sensitive state revision. -/
theorem revisionChecker_authority
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation}
    [EvidenceType State] [DecidableEq State] :
    (revisionChecker (State := State) (Query := Query)
      (Observation := Observation)).Authority RevisionMeaning where
  sound := revisionChecker_sound
  complete := revisionChecker_complete

/-- Exact observation replay when the observation carrier has executable
equality.  Richer carriers need not use this checker: they may supply a factor,
normalization, posterior, or estimator certificate authority instead. -/
def exactObservationChecker
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} [DecidableEq Observation]
    (observe : State → Query → Observation) :
    Checker (QueryClaim State Query Observation) Unit where
  check := fun claim _ => decide (claim.observation = observe claim.world claim.query)

theorem exactObservationChecker_authority
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} [DecidableEq Observation]
    (observe : State → Query → Observation) :
    (exactObservationChecker observe).Authority (ObservationMeaning observe) := by
  constructor
  · intro claim _ accepted
    simpa [exactObservationChecker, ObservationMeaning] using accepted
  · intro claim meaningful
    exact ⟨(), by
      simpa [exactObservationChecker, ObservationMeaning] using meaningful⟩

/-- Compose exact revision replay with an independently justified observation
checker.  This is the query authority waist used by SemanticService. -/
def replayChecker
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} {ObservationCertificate : Type uCertificate}
    [EvidenceType State] [DecidableEq State]
    (observationChecker :
      Checker (QueryClaim State Query Observation) ObservationCertificate) :
    Checker (QueryClaim State Query Observation)
      (RevisionTree State × ObservationCertificate) :=
  Checker.conjunction revisionChecker observationChecker

theorem replayChecker_authority
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} {ObservationCertificate : Type uCertificate}
    [EvidenceType State] [DecidableEq State]
    (observe : State → Query → Observation)
    (observationChecker :
      Checker (QueryClaim State Query Observation) ObservationCertificate)
    (observationAuthority :
      observationChecker.Authority (ObservationMeaning observe)) :
    (replayChecker observationChecker).Authority (QueryMeaning observe) :=
  Checker.conjunction_authority revisionChecker_authority observationAuthority

theorem replayChecker_sound
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} {ObservationCertificate : Type uCertificate}
    [EvidenceType State] [DecidableEq State]
    (observe : State → Query → Observation)
    (observationChecker :
      Checker (QueryClaim State Query Observation) ObservationCertificate)
    (observationAuthority :
      observationChecker.Authority (ObservationMeaning observe)) :
    (replayChecker observationChecker).Sound (QueryMeaning observe) :=
  (replayChecker_authority observe observationChecker observationAuthority).sound

theorem replayChecker_complete
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} {ObservationCertificate : Type uCertificate}
    [EvidenceType State] [DecidableEq State]
    (observe : State → Query → Observation)
    (observationChecker :
      Checker (QueryClaim State Query Observation) ObservationCertificate)
    (observationAuthority :
      observationChecker.Authority (ObservationMeaning observe)) :
    (replayChecker observationChecker).CertificateComplete (QueryMeaning observe) :=
  (replayChecker_authority observe observationChecker observationAuthority).complete

/-- Accepted certificates consume exactly their claimed source occurrences. -/
theorem accepted_implies_LinearJudgment
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} {ObservationCertificate : Type uCertificate}
    [EvidenceType State] [DecidableEq State]
    (observe : State → Query → Observation)
    (observationChecker : Checker (QueryClaim State Query Observation) ObservationCertificate)
    (observationAuthority : observationChecker.Authority (ObservationMeaning observe))
    {claim : QueryClaim State Query Observation}
    {certificate : RevisionTree State × ObservationCertificate}
    (accepted : (replayChecker observationChecker).check claim certificate = true) :
    LinearJudgment claim.sources claim.world :=
  ((replayChecker_sound observe observationChecker observationAuthority)
    claim certificate accepted).1.toLinearJudgment

/-- Accepted state is the sum of exactly its source bag, which is nonempty. -/
theorem accepted_world_eq_sum
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} {ObservationCertificate : Type uCertificate}
    [EvidenceType State] [DecidableEq State]
    (observe : State → Query → Observation)
    (observationChecker : Checker (QueryClaim State Query Observation) ObservationCertificate)
    (observationAuthority : observationChecker.Authority (ObservationMeaning observe))
    {claim : QueryClaim State Query Observation}
    {certificate : RevisionTree State × ObservationCertificate}
    (accepted : (replayChecker observationChecker).check claim certificate = true) :
    claim.world = claim.sources.sum ∧ claim.sources ≠ 0 :=
  (accepted_implies_LinearJudgment observe observationChecker observationAuthority accepted).eq_sum

/-- Accepted evidence projects to the existing multiset-indexed WM calculus. -/
theorem accepted_implies_WMJudgmentMulti
    {State : Type uState} {Query : Type uQuery}
    {ObservationCertificate : Type uCertificate}
    [EvidenceType State] [BinaryWorldModel State Query] [DecidableEq State]
    (observationChecker :
      Checker (QueryClaim State Query BinaryEvidence) ObservationCertificate)
    (observationAuthority : observationChecker.Authority
      (ObservationMeaning
        (BinaryWorldModel.evidence (State := State) (Query := Query))))
    {claim : QueryClaim State Query BinaryEvidence}
    {certificate : RevisionTree State × ObservationCertificate}
    (accepted :
      (replayChecker observationChecker).check claim certificate = true) :
    WMJudgmentMulti claim.sources claim.world :=
  (accepted_implies_LinearJudgment BinaryWorldModel.evidence observationChecker
    observationAuthority accepted).toMulti

/-- Accepted evidence also gives the ordinary WM query judgment after erasing
source occurrence information. -/
theorem accepted_implies_WMQueryJudgment
    {State : Type uState} {Query : Type uQuery}
    {ObservationCertificate : Type uCertificate}
    [EvidenceType State] [BinaryWorldModel State Query] [DecidableEq State]
    (observationChecker :
      Checker (QueryClaim State Query BinaryEvidence) ObservationCertificate)
    (observationAuthority : observationChecker.Authority
      (ObservationMeaning
        (BinaryWorldModel.evidence (State := State) (Query := Query))))
    {claim : QueryClaim State Query BinaryEvidence}
    {certificate : RevisionTree State × ObservationCertificate}
    (accepted :
      (replayChecker observationChecker).check claim certificate = true) :
    WMQueryJudgment claim.world claim.query claim.observation := by
  have meaning :=
    (replayChecker_sound BinaryWorldModel.evidence observationChecker
      observationAuthority) claim certificate accepted
  exact ⟨meaning.1.toLinearJudgment.toWMJudgment, meaning.2⟩

/-! ## Identified observation ledgers

The registry is supplied explicitly. A finite set prevents reusing one identity;
different identities may have equal payloads. This certifies consumption relative
to that registry, not authenticity of arbitrary identifiers or probabilistic
independence. As with the raw revision calculus, the empty ledger has no derivation.
-/

/-- A query whose source occurrences come from distinct registered identities. -/
structure LedgerQueryClaim (Id : Type*) (State : Type uState) (Query : Type uQuery)
    (Observation : Type uObservation) where
  ledger : Finset Id
  world : State
  query : Query
  observation : Observation

/-- Resolve identities through the supplied registry, retaining equal payloads
as separate occurrences when they belong to different identities. -/
def LedgerQueryClaim.toQueryClaim
    {Id : Type*} {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} (registry : Id → State)
    (claim : LedgerQueryClaim Id State Query Observation) : QueryClaim State Query Observation :=
  ⟨claim.ledger.val.map registry, claim.world, claim.query, claim.observation⟩

/-- The independently stated ledger semantics: use every registered observation
once, sum its state payload, then apply the supplied observation semantics. -/
def LedgerQueryMeaning
    {Id : Type*} {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} [EvidenceType State]
    (registry : Id → State) (observe : State → Query → Observation)
    (claim : LedgerQueryClaim Id State Query Observation) : Prop :=
  claim.ledger.Nonempty ∧ claim.world = ∑ i ∈ claim.ledger, registry i ∧
    claim.observation = observe claim.world claim.query

theorem ledgerQueryMeaning_iff
    {Id : Type*} {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} [EvidenceType State]
    (registry : Id → State) (observe : State → Query → Observation)
    (claim : LedgerQueryClaim Id State Query Observation) :
    QueryMeaning observe (claim.toQueryClaim registry) ↔ LedgerQueryMeaning registry observe claim := by
  have nonempty : claim.ledger.val.map registry ≠ 0 ↔ claim.ledger.Nonempty := by
    simp [Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨revision, observation⟩
    have sums := revision.toLinearJudgment.eq_sum
    exact ⟨nonempty.mp sums.2, sums.1, observation⟩
  · rintro ⟨inhabited, total, observation⟩
    have linear := LinearJudgment.of_sum (nonempty.mpr inhabited)
    change LinearJudgment (claim.ledger.val.map registry)
      (∑ i ∈ claim.ledger, registry i) at linear
    rw [← total] at linear
    exact ⟨OccurrenceRevision.ofLinearJudgment linear, observation⟩

/-- Replay a revision tree against identities resolved through a fixed registry. -/
def ledgerReplayChecker
    {Id : Type*} {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} {ObservationCertificate : Type uCertificate}
    [DecidableEq Id] [EvidenceType State] [DecidableEq State]
    (registry : Id → State)
    (observationChecker : Checker (QueryClaim State Query Observation) ObservationCertificate) :
    Checker (LedgerQueryClaim Id State Query Observation)
      (RevisionTree Id × ObservationCertificate) where
  check claim certificate :=
    decide (certificate.1.sources = claim.ledger.val) &&
      (replayChecker observationChecker).check (claim.toQueryClaim registry)
        (certificate.1.map registry, certificate.2)

/-- Accepted ledger certificates retain exactly the declared observation IDs. -/
theorem accepted_implies_ledger_sources
    {Id : Type*} {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} {ObservationCertificate : Type uCertificate}
    [DecidableEq Id] [EvidenceType State] [DecidableEq State]
    (registry : Id → State)
    (observationChecker : Checker (QueryClaim State Query Observation) ObservationCertificate)
    {claim : LedgerQueryClaim Id State Query Observation}
    {certificate : RevisionTree Id × ObservationCertificate}
    (accepted : (ledgerReplayChecker registry observationChecker).check claim certificate = true) :
    certificate.1.sources = claim.ledger.val := by
  exact (Bool.and_eq_true_iff.mp accepted).1 |> of_decide_eq_true

theorem ledgerReplayChecker_authority
    {Id : Type*} {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} {ObservationCertificate : Type uCertificate}
    [DecidableEq Id] [EvidenceType State] [DecidableEq State]
    (registry : Id → State) (observe : State → Query → Observation)
    (observationChecker : Checker (QueryClaim State Query Observation) ObservationCertificate)
    (observationAuthority : observationChecker.Authority (ObservationMeaning observe)) :
    (ledgerReplayChecker registry observationChecker).Authority
      (LedgerQueryMeaning registry observe) := by
  constructor
  · intro claim certificate accepted
    exact (ledgerQueryMeaning_iff registry observe claim).mp
      ((replayChecker_sound observe observationChecker observationAuthority)
        (claim.toQueryClaim registry) (certificate.1.map registry, certificate.2)
        (Bool.and_eq_true_iff.mp accepted).2)
  · intro claim meaningful
    have nonempty : claim.ledger.val ≠ 0 := by
      simpa using meaningful.1.ne_empty
    obtain ⟨tree, sourceIds⟩ := RevisionTree.exists_sources nonempty
    have total : (tree.map registry).result = claim.world := by
      rw [(tree.map registry).denotes.toLinearJudgment.eq_sum.1,
        RevisionTree.sources_map, sourceIds]
      exact meaningful.2.1.symm
    obtain ⟨observationCertificate, observed⟩ :=
      observationAuthority.complete (claim.toQueryClaim registry) meaningful.2.2
    refine ⟨(tree, observationCertificate), ?_⟩
    simp [ledgerReplayChecker, replayChecker, Checker.conjunction, revisionChecker,
      RevisionTree.sources_map, sourceIds, total, LedgerQueryClaim.toQueryClaim] at observed ⊢
    exact observed

/-! ## SemanticService and CertificateGSLT authorities for the same judgment -/

/-- Occurrence-exact WM queries as one ordinary SemanticService authority fibre. -/
def family
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} {ObservationCertificate : Type uCertificate}
    [EvidenceType State] [DecidableEq State]
    (observe : State → Query → Observation)
    (observationChecker :
      Checker (QueryClaim State Query Observation) ObservationCertificate)
    (observationAuthority :
      observationChecker.Authority (ObservationMeaning observe)) :
    AuthorityFamily Unit where
  Claim := fun _ => QueryClaim State Query Observation
  Certificate := fun _ => RevisionTree State × ObservationCertificate
  checker := fun _ => replayChecker observationChecker
  Certified := fun _ => QueryMeaning observe
  Meaning := fun _ => QueryMeaning observe
  projection := fun _ =>
    (replayChecker_authority observe observationChecker
      observationAuthority).toProjection

/-- The identity-checked ledger interface as a SemanticService authority.
The source registry and observation checker are fixed by the authority owner. -/
def ledgerFamily
    {Id : Type*} {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} {ObservationCertificate : Type uCertificate}
    [DecidableEq Id] [EvidenceType State] [DecidableEq State]
    (registry : Id → State) (observe : State → Query → Observation)
    (observationChecker : Checker (QueryClaim State Query Observation) ObservationCertificate)
    (observationAuthority : observationChecker.Authority (ObservationMeaning observe)) :
    AuthorityFamily Unit where
  Claim := fun _ => LedgerQueryClaim Id State Query Observation
  Certificate := fun _ => RevisionTree Id × ObservationCertificate
  checker := fun _ => ledgerReplayChecker registry observationChecker
  Certified := fun _ => LedgerQueryMeaning registry observe
  Meaning := fun _ => LedgerQueryMeaning registry observe
  projection := fun _ =>
    (ledgerReplayChecker_authority registry observe observationChecker observationAuthority).toProjection

/-- Any exact CertificateGSLT definition for occurrence-exact WM query meaning. -/
def semanticCertificateGSLT
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} [EvidenceType State]
    (observe : State → Query → Observation)
    {definition : ValidatedCalculusLanguageDef}
    (adequacy : ExactJudgmentEncoding (QueryClaim State Query Observation)
      (QueryMeaning observe) definition) :
    SemanticallyCompleteCertificateGSLT (QueryClaim State Query Observation)
      (QueryMeaning observe) where
  definition := definition
  adequacy := adequacy

/-- Exact CertificateGSLT article replay and native revision-tree replay agree on
every claim.  This is certificate-format agreement, not an identification of
the two certificate types. -/
theorem certificateGSLT_article_iff_revisionTree
    {AuthorityId : Type uAuthority} (authorityId : AuthorityId)
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} {ObservationCertificate : Type uCertificate}
    [EvidenceType State] [DecidableEq State]
    (observe : State → Query → Observation)
    (observationChecker :
      Checker (QueryClaim State Query Observation) ObservationCertificate)
    (observationAuthority :
      observationChecker.Authority (ObservationMeaning observe))
    {definition : ValidatedCalculusLanguageDef}
    (adequacy : ExactJudgmentEncoding (QueryClaim State Query Observation)
      (QueryMeaning observe) definition)
    (claim : QueryClaim State Query Observation) :
    (∃ article,
        ((semanticCertificateGSLT observe adequacy).checker authorityId).check
          claim article = true) ↔
      ∃ certificate,
        (replayChecker observationChecker).check claim certificate = true := by
  constructor
  · rintro ⟨article, accepted⟩
    have meaningful :=
      ((semanticCertificateGSLT observe adequacy).checker_authority authorityId).sound
        claim article accepted
    exact (replayChecker_complete observe observationChecker
      observationAuthority) claim meaningful
  · rintro ⟨certificate, accepted⟩
    have meaningful := (replayChecker_sound observe observationChecker
      observationAuthority) claim certificate accepted
    exact ((semanticCertificateGSLT observe adequacy).checker_authority
      authorityId).complete
      claim meaningful

/-! ## Projection into the existing WM-to-OSLF semantics -/

/-- A checked occurrence-exact WM query supplies the exact evidence observed
by the existing OSLF atom semantics.  The OSLF relation remains a parameter:
this theorem concerns the atom valuation, not an unproved completeness claim
for the whole WM language definition. -/
theorem accepted_implies_oslf_atom_evidence
    {State : Type uState} {Query : Type uQuery}
    {ObservationCertificate : Type uCertificate}
    [EvidenceType State] [BinaryWorldModel State Query] [DecidableEq State]
    (observationChecker :
      Checker (QueryClaim State Query BinaryEvidence) ObservationCertificate)
    (observationAuthority : observationChecker.Authority
      (ObservationMeaning
        (BinaryWorldModel.evidence (State := State) (Query := Query))))
    (R : Pattern → Pattern → Prop)
    (queryOfAtom : String → Pattern → Query)
    (atom : String) (pattern : Pattern)
    {claim : QueryClaim State Query BinaryEvidence}
    {certificate : RevisionTree State × ObservationCertificate}
    (encoded : queryOfAtom atom pattern = claim.query)
    (accepted :
      (replayChecker observationChecker).check claim certificate = true) :
    semE R (wmEvidenceAtomSemQ claim.world queryOfAtom)
        (.atom atom) pattern = claim.observation := by
  apply wmQueryJudgment_semE_atom
  rw [encoded]
  exact accepted_implies_WMQueryJudgment observationChecker
    observationAuthority accepted

/-! ## Executable positive and negative witnesses -/

namespace Canary

private instance : EvidenceType Nat where

/-- A finite observation carrier used only to exercise executable replay. -/
def natObservation (state : Nat) (query : Bool) : Nat :=
  if query then state else state * 2

def natObservationChecker : Checker (QueryClaim Nat Bool Nat) Unit :=
  exactObservationChecker natObservation

theorem natObservationChecker_authority :
    natObservationChecker.Authority (ObservationMeaning natObservation) :=
  exactObservationChecker_authority natObservation

def goodClaim : QueryClaim Nat Bool Nat where
  sources := {2, 3}
  world := 5
  query := true
  observation := 5

def goodTree : RevisionTree Nat :=
  .revise (.source 2) (.source 3)

/-- Positive witness: both source occurrences, their revision, and the query
evidence replay exactly. -/
theorem good_article_accepted :
    (replayChecker natObservationChecker).check goodClaim (goodTree, ()) = true := by
  simp [replayChecker, Checker.conjunction, revisionChecker,
    natObservationChecker, exactObservationChecker, goodClaim, goodTree,
    RevisionTree.sources, RevisionTree.result, natObservation]

/-- Negative source witness: changing one leaf changes both the exact source
bag and the computed posterior, so replay fails. -/
theorem changed_source_rejected :
    (replayChecker natObservationChecker).check goodClaim
      (.revise (.source 2) (.source 4), ()) = false := by
  simp [replayChecker, Checker.conjunction, revisionChecker, goodClaim,
    RevisionTree.sources, RevisionTree.result]

def duplicateClaim : QueryClaim Nat Bool Nat where
  sources := {2, 2}
  world := 4
  query := false
  observation := 8

def duplicateTree : RevisionTree Nat :=
  .revise (.source 2) (.source 2)

/-- Positive multiplicity witness: two equal source payloads remain two
source occurrences and contribute twice. -/
theorem duplicate_occurrences_accepted :
    (replayChecker natObservationChecker).check
      duplicateClaim (duplicateTree, ()) = true := by
  simp [replayChecker, Checker.conjunction, revisionChecker,
    natObservationChecker, exactObservationChecker, duplicateClaim,
    duplicateTree, RevisionTree.sources, RevisionTree.result, natObservation]

/-- Negative multiplicity witness: one occurrence cannot certify a two-source
claim even when its payload is equal to both claimed occurrences. -/
theorem dropped_duplicate_rejected :
    (replayChecker natObservationChecker).check
      duplicateClaim (.source 2, ()) = false := by
  simp [replayChecker, Checker.conjunction, revisionChecker, duplicateClaim,
    RevisionTree.sources, RevisionTree.result]

/-- Isolate contraction: the doubled result and observation are correct, but
one supplied occurrence cannot authorize two leaves. -/
theorem reused_single_source_rejected :
    (replayChecker natObservationChecker).check
      (⟨{2}, 4, true, 4⟩ : QueryClaim Nat Bool Nat) (duplicateTree, ()) = false := by decide

/-- Two distinct registered observations happen to have the same value. -/
def equalPayloadRegistry (_ : Nat) : Nat := 2

/-- Equal payloads at different identities are legitimate distinct occurrences. -/
theorem distinct_ids_equal_payloads_accepted :
    (ledgerReplayChecker equalPayloadRegistry natObservationChecker).check
      (⟨{0, 1}, 4, false, 8⟩ : LedgerQueryClaim Nat Nat Bool Nat)
      (.revise (.source 0) (.source 1), ()) = true := by
  decide

/-- Repeating an identity does not enlarge its finite observation ledger. -/
theorem repeated_id_rejected :
    (ledgerReplayChecker equalPayloadRegistry natObservationChecker).check
      (⟨{0, 0}, 4, false, 8⟩ : LedgerQueryClaim Nat Nat Bool Nat)
      (.revise (.source 0) (.source 0), ()) = false := by
  decide

/-- A forged result is rejected even when the registered identities are distinct. -/
theorem incorrect_ledger_total_rejected :
    (ledgerReplayChecker equalPayloadRegistry natObservationChecker).check
      (⟨{0, 1}, 5, true, 5⟩ : LedgerQueryClaim Nat Nat Bool Nat)
      (.revise (.source 0) (.source 1), ()) = false := by
  decide

/-- Swapping an identity is rejected even when its payload and all counts agree. -/
theorem equal_payload_wrong_id_rejected :
    (ledgerReplayChecker equalPayloadRegistry natObservationChecker).check
      (⟨{0, 1}, 4, false, 8⟩ : LedgerQueryClaim Nat Nat Bool Nat)
      (.revise (.source 0) (.source 2), ()) = false := by decide

/-- Correct identities and total do not excuse an incorrect query readout. -/
theorem incorrect_ledger_observation_rejected :
    (ledgerReplayChecker equalPayloadRegistry natObservationChecker).check
      (⟨{0, 1}, 4, true, 5⟩ : LedgerQueryClaim Nat Nat Bool Nat)
      (.revise (.source 0) (.source 1), ()) = false := by decide

end Canary

end Mettapedia.PLN.Bridges.GSLT.WMQueryProofAuthority
