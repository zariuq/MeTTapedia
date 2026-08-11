import Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
import Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
import Mettapedia.PLN.Bridges.Languages.PLNWMOSLFBridge

/-!
# Occurrence-exact WM query evidence as a ProofGSLT/NIK authority

World-model state construction, query extraction, and semantic inference are
different judgment families.  This module gives the first two a small exact
authority without claiming completeness for every PLN inference rule.

An `OccurrenceRevision` records a binary revision tree whose leaf multiset is
exactly the selected evidence-source multiset.  Equal source payloads retain
multiplicity.  A certificate is a concrete `RevisionTree`; replay checks its
leaf multiset, resulting state, and the claimed binary evidence.

The checker is exact for the independently defined `QueryMeaning`.  It also
projects to the existing multiset-indexed and set-indexed WM judgments, and
then to the existing OSLF atom semantics.  A separately admitted exact
ProofGSLT presentation of the same judgment is proved extensionally equivalent
to revision-tree replay.
-/

namespace Mettapedia.PLN.Bridges.GSLT.WMQueryProofAuthority

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
open Mettapedia.GSLT.LanguageDef.ProofGSLT
open Mettapedia.OSLF.Framework.EvidenceSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.PLN.Bridges.Languages.PLNWMOSLFBridge
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel

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

/-- Forget exact occurrence consumption into the existing multiplicity-aware
WM judgment. -/
theorem toWMJudgmentMulti {sources : Multiset State} {world : State}
    (derivation : OccurrenceRevision sources world) :
    WMJudgmentMulti sources world := by
  induction derivation with
  | source state => exact WMJudgmentMulti.singleton_derivable state
  | revise left right leftIH rightIH =>
      exact WMJudgmentMulti.add_revise leftIH rightIH

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

/-- Every tree denotes an occurrence-exact WM revision. -/
def denotes : (tree : RevisionTree State) →
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
checker.  This is the query authority waist used by NIK. -/
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
  ((replayChecker_sound BinaryWorldModel.evidence observationChecker
    observationAuthority) claim certificate accepted).1.toWMJudgmentMulti

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
  exact ⟨meaning.1.toWMJudgmentMulti.toWMJudgment, meaning.2⟩

/-! ## NIK and ProofGSLT presentations of the same judgment -/

/-- Occurrence-exact WM queries as one ordinary NIK authority fibre. -/
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

/-- Any exact ProofGSLT presentation of occurrence-exact WM query meaning. -/
def semanticProofGSLT
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} [EvidenceType State]
    (observe : State → Query → Observation)
    {presentation : ValidatedPresentation}
    (adequacy : ExactJudgmentPresentation (QueryClaim State Query Observation)
      (QueryMeaning observe) presentation) :
    SemanticallyCompleteProofGSLT (QueryClaim State Query Observation)
      (QueryMeaning observe) where
  presentation := presentation
  adequacy := adequacy

/-- Exact ProofGSLT article replay and native revision-tree replay agree on
every claim.  This is certificate-format agreement, not an identification of
the two certificate types. -/
theorem proofGSLT_article_iff_revisionTree
    {AuthorityId : Type uAuthority} (authorityId : AuthorityId)
    {State : Type uState} {Query : Type uQuery}
    {Observation : Type uObservation} {ObservationCertificate : Type uCertificate}
    [EvidenceType State] [DecidableEq State]
    (observe : State → Query → Observation)
    (observationChecker :
      Checker (QueryClaim State Query Observation) ObservationCertificate)
    (observationAuthority :
      observationChecker.Authority (ObservationMeaning observe))
    {presentation : ValidatedPresentation}
    (adequacy : ExactJudgmentPresentation (QueryClaim State Query Observation)
      (QueryMeaning observe) presentation)
    (claim : QueryClaim State Query Observation) :
    (∃ article,
        ((semanticProofGSLT observe adequacy).checker authorityId).check
          claim article = true) ↔
      ∃ certificate,
        (replayChecker observationChecker).check claim certificate = true := by
  constructor
  · rintro ⟨article, accepted⟩
    have meaningful :=
      ((semanticProofGSLT observe adequacy).checker_authority authorityId).sound
        claim article accepted
    exact (replayChecker_complete observe observationChecker
      observationAuthority) claim meaningful
  · rintro ⟨certificate, accepted⟩
    have meaningful := (replayChecker_sound observe observationChecker
      observationAuthority) claim certificate accepted
    exact ((semanticProofGSLT observe adequacy).checker_authority
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

end Canary

end Mettapedia.PLN.Bridges.GSLT.WMQueryProofAuthority
