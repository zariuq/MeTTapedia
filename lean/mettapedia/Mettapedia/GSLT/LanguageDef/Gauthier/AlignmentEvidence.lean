/-
# Provenance-correct categorical evidence from structural alignments

An action observation retains its query, decoder prefix, alignment coordinate,
typed checker verdict, and lineage.  The innovation identity intentionally
forgets occurrence path, surface spelling, and descendant lineage while
retaining the causal root, action, and verdict.  Consequently repeated DAG
manifestations and common-ancestor descendants contribute once, whereas truly
independent roots add.

Budget-undetermined evidence has its own categorical channel.  It is never
silently converted to negative evidence.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.PartialPostfixAlignment
import Mettapedia.GSLT.LanguageDef.Gauthier.ProbeRigidity
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.EvidenceBridge
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.CommonAncestorIndependence
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.CausalEvidenceTransport
import Mettapedia.PLN.Bridges.PredictiveCoding.GradedTotalityRevision
import Mettapedia.PLN.WorldModel.SufficientStatisticSurface

namespace Mettapedia.GSLT.LanguageDef.GauthierAlignmentEvidence

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierPartialPostfixAlignment
open Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity
open Mettapedia.GSLT.LanguageDef.GauthierBigStepGSLT
open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
open Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
open Mettapedia.PLN.Bridges.PredictiveCoding
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet
open Mettapedia.PLN.WorldModel

/-- The actual memo grammar has sixteen operator actions. -/
def operatorCount : Nat := orgMemoSignature.length

theorem operatorCount_eq : operatorCount = 16 := orgMemoSignature_length

abbrev OperatorAction := Fin operatorCount

/-- Positive, negative, and budget-undetermined categorical sufficient
statistics. -/
@[ext]
structure GradedActionEvidence (k : Nat) where
  positive : MultiEvidence k
  negative : MultiEvidence k
  undetermined : MultiEvidence k

namespace GradedActionEvidence

def zero : GradedActionEvidence k :=
  ⟨MultiEvidence.zero, MultiEvidence.zero, MultiEvidence.zero⟩

def add (left right : GradedActionEvidence k) : GradedActionEvidence k :=
  ⟨left.positive + right.positive,
    left.negative + right.negative,
    left.undetermined + right.undetermined⟩

instance : Zero (GradedActionEvidence k) := ⟨zero⟩
instance : Add (GradedActionEvidence k) := ⟨add⟩

instance : AddCommMonoid (GradedActionEvidence k) where
  zero := zero
  add := add
  add_assoc := by intro a b c; ext i <;> exact Nat.add_assoc _ _ _
  zero_add := by intro a; ext i <;> exact Nat.zero_add _
  add_zero := by intro a; ext i <;> exact Nat.add_zero _
  add_comm := by intro a b; ext i <;> exact Nat.add_comm _ _
  nsmul := nsmulRec

def oneHot (action : Fin k) : MultiEvidence k :=
  ⟨fun queried => if queried = action then 1 else 0⟩

def ofVerdict (action : Fin k) : TotalityVerdict → GradedActionEvidence k
  | .provablyTotal => ⟨oneHot action, MultiEvidence.zero, MultiEvidence.zero⟩
  | .provablyPartial => ⟨MultiEvidence.zero, oneHot action, MultiEvidence.zero⟩
  | .undeterminedAtBudget =>
      ⟨MultiEvidence.zero, MultiEvidence.zero, oneHot action⟩

@[simp] theorem ofVerdict_total_positive_same (action : Fin k) :
    (ofVerdict action .provablyTotal).positive.counts action = 1 := by
  simp [ofVerdict, oneHot]

@[simp] theorem ofVerdict_partial_negative_same (action : Fin k) :
    (ofVerdict action .provablyPartial).negative.counts action = 1 := by
  simp [ofVerdict, oneHot]

@[simp] theorem ofVerdict_undetermined_only_undetermined (action : Fin k) :
    (ofVerdict action .undeterminedAtBudget).positive.counts action = 0 ∧
      (ofVerdict action .undeterminedAtBudget).negative.counts action = 0 ∧
      (ofVerdict action .undeterminedAtBudget).undetermined.counts action = 1 := by
  simp [ofVerdict, oneHot, MultiEvidence.zero]

end GradedActionEvidence

@[simp] theorem GradedActionEvidence.add_positive_counts
    (left right : GradedActionEvidence k) (action : Fin k) :
    (left + right).positive.counts action =
      left.positive.counts action + right.positive.counts action := rfl

@[simp] theorem GradedActionEvidence.add_negative_counts
    (left right : GradedActionEvidence k) (action : Fin k) :
    (left + right).negative.counts action =
      left.negative.counts action + right.negative.counts action := rfl

@[simp] theorem GradedActionEvidence.add_undetermined_counts
    (left right : GradedActionEvidence k) (action : Fin k) :
    (left + right).undetermined.counts action =
      left.undetermined.counts action + right.undetermined.counts action := rfl

/-- Query identity shared by observations at one live decoder state. -/
structure ActionQuery where
  targetQuery : Nat
  decoderPrefix : List Nat
  deriving DecidableEq, BEq, Repr

/-- The full observation record.  `sourceRoot` is the causal root obtained from
the lineage DAG; `sourceLineage` remains audit metadata. -/
structure ActionObservation where
  query : ActionQuery
  alignmentCoordinate : AlignmentCoordinate
  structuralSource : List Nat
  action : OperatorAction
  verdict : TotalityVerdict
  sourceLineage : Nat
  sourceRoot : Nat
  deriving DecidableEq, Repr

/-- Causal identity for precision accounting.  Occurrence path, surface
spelling, and descendant lineage are absent by design. -/
structure ActionInnovationId where
  query : ActionQuery
  action : OperatorAction
  verdict : TotalityVerdict
  sourceRoot : Nat
  deriving DecidableEq, Repr

def ActionObservation.innovationId (observation : ActionObservation) :
    ActionInnovationId :=
  { query := observation.query
    action := observation.action
    verdict := observation.verdict
    sourceRoot := observation.sourceRoot }

def evidenceOfInnovation (identity : ActionInnovationId) :
    GradedActionEvidence operatorCount :=
  GradedActionEvidence.ofVerdict identity.action identity.verdict

def observationPacket (observation : ActionObservation) :
    InnovationPacket ActionInnovationId (GradedActionEvidence operatorCount) :=
  ⟨observation.innovationId, evidenceOfInnovation observation.innovationId⟩

/-- The existing sufficient-statistic surface, specialized to aligned action
observations. -/
def actionEvidenceSurface :
    SufficientStatisticSurface ActionObservation ActionQuery
      (GradedActionEvidence operatorCount) where
  observe observation query :=
    if observation.query = query then
      evidenceOfInnovation observation.innovationId
    else 0

/-- Provenance-correct aggregation is a sum over distinct causal identities,
not over observation occurrences. -/
def correctedEvidence (observations : List ActionObservation) :
    GradedActionEvidence operatorCount :=
  ((observations.map ActionObservation.innovationId).toFinset).sum
    evidenceOfInnovation

/-- The provenance-correct distribution over every aligned representative for
one query.  Representatives are retained as a distribution of actions; only
their exact causal innovation identities are deduplicated. -/
def alignedRepresentativeEvidence
    (observations : List ActionObservation) (query : ActionQuery) :
    GradedActionEvidence operatorCount :=
  correctedEvidence (observations.filter fun observation =>
    observation.query = query)

theorem correctedEvidence_perm {left right : List ActionObservation}
    (hperm : left.Perm right) :
    correctedEvidence left = correctedEvidence right := by
  unfold correctedEvidence
  have hmap := hperm.map ActionObservation.innovationId
  have hfinset :
      (left.map ActionObservation.innovationId).toFinset =
        (right.map ActionObservation.innovationId).toFinset := by
    ext identity
    simp only [List.mem_toFinset]
    exact hmap.mem_iff
  rw [hfinset]

/-- Enumeration order of the aligned bounded class is irrelevant. -/
theorem alignedRepresentativeEvidence_perm
    {left right : List ActionObservation} (hperm : left.Perm right)
    (query : ActionQuery) :
    alignedRepresentativeEvidence left query =
      alignedRepresentativeEvidence right query := by
  apply correctedEvidence_perm
  exact hperm.filter _

/-- Exact duplicate removal is semantics-preserving. -/
theorem correctedEvidence_duplicate (observation : ActionObservation)
    (rest : List ActionObservation) :
    correctedEvidence (observation :: observation :: rest) =
      correctedEvidence (observation :: rest) := by
  simp [correctedEvidence]

/-- Repeating an exact representative observation cannot change its bounded
class distribution. -/
theorem alignedRepresentativeEvidence_duplicate
    (observation : ActionObservation) (rest : List ActionObservation)
    (query : ActionQuery) :
    alignedRepresentativeEvidence (observation :: observation :: rest) query =
      alignedRepresentativeEvidence (observation :: rest) query := by
  simp only [alignedRepresentativeEvidence, List.filter_cons]
  split <;> simp [correctedEvidence]

/-- Different manifestations with one causal root/action/verdict collapse to
one precision contribution even when paths and surface programs differ. -/
theorem correctedEvidence_common_root
    (first second : ActionObservation)
    (hid : first.innovationId = second.innovationId) :
    correctedEvidence [first, second] = correctedEvidence [first] := by
  simp [correctedEvidence, hid]

/-- Independent causal roots with otherwise equal observations add two
categorical counts. -/
theorem independent_positive_discoveries_add
    (query : ActionQuery) (coordinate : AlignmentCoordinate)
    (action : OperatorAction) :
    let first : ActionObservation :=
      ⟨query, coordinate, [], action, .provablyTotal, 10, 10⟩
    let second : ActionObservation :=
      ⟨query, coordinate, [], action, .provablyTotal, 20, 20⟩
    (correctedEvidence [first, second]).positive.counts action = 2 := by
  simp [correctedEvidence, evidenceOfInnovation,
    ActionObservation.innovationId, GradedActionEvidence.ofVerdict,
    GradedActionEvidence.oneHot, MultiEvidence.zero]

/-- A refutation contributes negative, not positive, action evidence. -/
theorem refutation_is_negative_evidence
    (query : ActionQuery) (coordinate : AlignmentCoordinate)
    (action : OperatorAction) :
    let observation : ActionObservation :=
      ⟨query, coordinate, [], action, .provablyPartial, 3, 3⟩
    (correctedEvidence [observation]).positive.counts action = 0 ∧
      (correctedEvidence [observation]).negative.counts action = 1 := by
  simp [correctedEvidence, evidenceOfInnovation,
    ActionObservation.innovationId, GradedActionEvidence.ofVerdict,
    GradedActionEvidence.oneHot, MultiEvidence.zero]

/-- Resource exhaustion remains a third, graded observation and cannot become
a failure count. -/
theorem undetermined_is_not_failure
    (query : ActionQuery) (coordinate : AlignmentCoordinate)
    (action : OperatorAction) :
    let observation : ActionObservation :=
      ⟨query, coordinate, [], action, .undeterminedAtBudget, 3, 3⟩
    (correctedEvidence [observation]).negative.counts action = 0 ∧
      (correctedEvidence [observation]).undetermined.counts action = 1 := by
  simp [correctedEvidence, evidenceOfInnovation,
    ActionObservation.innovationId, GradedActionEvidence.ofVerdict,
    GradedActionEvidence.oneHot, MultiEvidence.zero]

/-- Repeated DAG occurrences are the same causal observation when only their
occurrence path differs. -/
theorem shared_dag_occurrences_assimilated_once
    (query : ActionQuery) (action : OperatorAction) (sourceRoot : Nat) :
    let firstCoordinate : AlignmentCoordinate := ⟨0, [0], .value, true⟩
    let secondCoordinate : AlignmentCoordinate := ⟨0, [1], .value, true⟩
    let first : ActionObservation :=
      ⟨query, firstCoordinate, [0], action, .provablyTotal, sourceRoot, sourceRoot⟩
    let second : ActionObservation :=
      ⟨query, secondCoordinate, [0], action, .provablyTotal, sourceRoot, sourceRoot⟩
    correctedEvidence [first, second] = correctedEvidence [first] := by
  simp [correctedEvidence, ActionObservation.innovationId]

/-! ## Lineage-manifest authentication of causal source classes -/

/-- A finite manifest may attach an executable source-class identifier to
each lineage.  The certificate requires every common-ancestor pair to share a
class.  It is deliberately conservative: unrelated sources may also share a
class, which can lose evidence but can never inflate precision. -/
structure SourceClassCertificate {World Lineage : Type*}
    (graph : LineageDAG Nat World Lineage) where
  classOf : Nat → Nat
  commonAncestor_same : ∀ {left right},
    (∃ common,
      graph.AncestorOrSelf common left ∧ graph.AncestorOrSelf common right) →
      classOf left = classOf right

/-- Construct an observation whose causal class is supplied by an
authenticated lineage-manifest certificate. -/
def observationOfManifest {World Lineage : Type*}
    {graph : LineageDAG Nat World Lineage}
    (certificate : SourceClassCertificate graph)
    (query : ActionQuery) (coordinate : AlignmentCoordinate)
    (structuralSource : List Nat) (action : OperatorAction)
    (verdict : TotalityVerdict) (source : Nat) : ActionObservation :=
  ⟨query, coordinate, structuralSource, action, verdict, source,
    certificate.classOf source⟩

/-- Manifest descendants with a common causal ancestor cannot become two
innovation identities merely by being emitted on different lineage rows. -/
theorem common_ancestor_observations_same_innovation
    {World Lineage : Type*} {graph : LineageDAG Nat World Lineage}
    (certificate : SourceClassCertificate graph)
    {left right : Nat}
    (hcommon : ∃ common,
      graph.AncestorOrSelf common left ∧ graph.AncestorOrSelf common right)
    (query : ActionQuery) (leftCoordinate rightCoordinate : AlignmentCoordinate)
    (leftSource rightSource : List Nat) (action : OperatorAction)
    (verdict : TotalityVerdict) :
    (observationOfManifest certificate query leftCoordinate leftSource action
        verdict left).innovationId =
      (observationOfManifest certificate query rightCoordinate rightSource action
        verdict right).innovationId := by
  simp only [observationOfManifest, ActionObservation.innovationId]
  rw [certificate.commonAncestor_same hcommon]

/-- The preceding identity feeds the overlap-corrected accumulator, so two
manifest rows descending from a common source contribute once. -/
theorem common_ancestor_observations_assimilated_once
    {World Lineage : Type*} {graph : LineageDAG Nat World Lineage}
    (certificate : SourceClassCertificate graph)
    {left right : Nat}
    (hcommon : ∃ common,
      graph.AncestorOrSelf common left ∧ graph.AncestorOrSelf common right)
    (query : ActionQuery) (leftCoordinate rightCoordinate : AlignmentCoordinate)
    (leftSource rightSource : List Nat) (action : OperatorAction)
    (verdict : TotalityVerdict) :
    correctedEvidence
        [observationOfManifest certificate query leftCoordinate leftSource action
          verdict left,
         observationOfManifest certificate query rightCoordinate rightSource action
          verdict right] =
      correctedEvidence
        [observationOfManifest certificate query leftCoordinate leftSource action
          verdict left] := by
  apply correctedEvidence_common_root
  exact common_ancestor_observations_same_innovation certificate hcommon
    query leftCoordinate rightCoordinate leftSource rightSource action verdict

/-- Direct reuse of `CommonAncestorIndependence`: actual ancestry forbids the
legacy source-disjoint certificate used by `EvidenceBridge`. -/
theorem manifest_ancestor_forbids_source_disjoint
    {Source World Lineage : Type*} [DecidableEq Source] [Fintype Source]
    (graph : LineageDAG Source World Lineage)
    {earlier later : Source} (hancestor : graph.AncestorOf earlier later)
    (laterAction earlierAction : OperatorAction)
    (laterQuery earlierQuery : ActionQuery) :
    ¬ (packetFromLineageDAG graph earlierAction earlierQuery earlier).SourceDisjoint
      (packetFromLineageDAG graph laterAction laterQuery later) :=
  ancestor_not_sourceDisjoint graph hancestor
    laterAction earlierAction laterQuery earlierQuery

/-- Direct reuse of `EvidenceBridge`: genuinely graph-independent action
observations receive its existing additive-revision license. -/
theorem manifest_independence_licenses_action_revision
    {Source World Lineage : Type*} [DecidableEq Source] [Fintype Source]
    (graph : LineageDAG Source World Lineage)
    (left right : Source) (leftAction rightAction : OperatorAction)
    (leftQuery rightQuery : ActionQuery)
    (h : graph.GraphIndependent left right) :
    AdditiveRevisionLicense
      (packetFromLineageDAG graph leftAction leftQuery left)
      (packetFromLineageDAG graph rightAction rightQuery right) :=
  graphIndependent_licenses_additiveRevision graph left right
    leftAction rightAction leftQuery rightQuery h

/-! ## Existing causal-ledger transport, instantiated -/

@[ext]
structure DecidedActionEvidence (k : Nat) where
  positive : MultiEvidence k
  negative : MultiEvidence k

namespace DecidedActionEvidence

def zero : DecidedActionEvidence k := ⟨MultiEvidence.zero, MultiEvidence.zero⟩
def add (left right : DecidedActionEvidence k) : DecidedActionEvidence k :=
  ⟨left.positive + right.positive, left.negative + right.negative⟩

instance : Zero (DecidedActionEvidence k) := ⟨zero⟩
instance : Add (DecidedActionEvidence k) := ⟨add⟩
instance : AddCommMonoid (DecidedActionEvidence k) where
  zero := zero
  add := add
  add_assoc := by intro a b c; ext i <;> exact Nat.add_assoc _ _ _
  zero_add := by intro a; ext i <;> exact Nat.zero_add _
  add_zero := by intro a; ext i <;> exact Nat.add_zero _
  add_comm := by intro a b; ext i <;> exact Nat.add_comm _ _
  nsmul := nsmulRec

end DecidedActionEvidence

/-- Meaningful evidence-frame transport that forgets only the explicitly
undetermined channel. -/
def decidedTransport :
    GradedActionEvidence k →+ DecidedActionEvidence k where
  toFun evidence := ⟨evidence.positive, evidence.negative⟩
  map_zero' := rfl
  map_add' := by intro left right; rfl

/-- This is the existing `mapEvidence_assimilate` theorem instantiated on the
action-evidence carrier; no parallel assimilation semantics is introduced. -/
theorem decidedTransport_commutes_with_assimilation
    (ledger : CausalInnovationLedger ActionInnovationId
      (GradedActionEvidence operatorCount))
    (packet : InnovationPacket ActionInnovationId
      (GradedActionEvidence operatorCount)) :
    CausalInnovationLedger.mapEvidence decidedTransport
        (CausalInnovationLedger.assimilate ledger packet) =
      CausalInnovationLedger.assimilate
        (CausalInnovationLedger.mapEvidence decidedTransport ledger)
        (packet.mapEvidence decidedTransport) := by
  exact CausalInnovationLedger.mapEvidence_assimilate
    decidedTransport ledger packet

/-! ## Why bounded equivalence cannot choose one action -/

/-- The established one-probe-equivalent programs have different postfix
continuations after the common first token.  Hence a bounded e-class cannot
soundly be assigned one representative-invariant action. -/
theorem bounded_equivalent_programs_different_actions :
    EmitsPrefix orgE1Signature 20 probeId oneProbePrefix ∧
      EmitsPrefix orgE1Signature 20 probeZeroAfterZero oneProbePrefix ∧
      (rpnTokens probeId).drop 1 = [] ∧
      (rpnTokens probeZeroAfterZero).drop 1 = [10, 0, 8] := by
  exact ⟨probeId_emits_one_prefix, probeZeroAfterZero_emits_one_prefix,
    by simp [probeId, Org.X, rpnTokens],
    by simp [probeZeroAfterZero, Org.cond, Org.X, Org.z, rpnTokens]⟩

theorem no_representative_invariant_next_action :
    ¬ ∀ program,
      EmitsPrefix orgE1Signature 20 program oneProbePrefix →
      (rpnTokens program).drop 1 = (rpnTokens probeId).drop 1 := by
  intro hinvariant
  have h := hinvariant probeZeroAfterZero probeZeroAfterZero_emits_one_prefix
  rw [show (rpnTokens probeZeroAfterZero).drop 1 = [10, 0, 8] by
      simp [probeZeroAfterZero, Org.cond, Org.X, Org.z, rpnTokens],
    show (rpnTokens probeId).drop 1 = [] by
      simp [probeId, Org.X, rpnTokens]] at h
  cases h

#print axioms correctedEvidence_perm
#print axioms alignedRepresentativeEvidence_perm
#print axioms alignedRepresentativeEvidence_duplicate
#print axioms correctedEvidence_duplicate
#print axioms correctedEvidence_common_root
#print axioms independent_positive_discoveries_add
#print axioms refutation_is_negative_evidence
#print axioms undetermined_is_not_failure
#print axioms shared_dag_occurrences_assimilated_once
#print axioms common_ancestor_observations_assimilated_once
#print axioms manifest_ancestor_forbids_source_disjoint
#print axioms manifest_independence_licenses_action_revision
#print axioms decidedTransport_commutes_with_assimilation
#print axioms bounded_equivalent_programs_different_actions
#print axioms no_representative_invariant_next_action

end Mettapedia.GSLT.LanguageDef.GauthierAlignmentEvidence
