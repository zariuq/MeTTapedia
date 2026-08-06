/-
# Executable Grade-B action-evidence pipeline

This is the reference composition of the preceding layers.  It authenticates
wire DAGs through the established parser, replays their prefixes, chooses one
most-specific legal alignment per historical program, constructs
provenance-correct graded observations, deduplicates causal innovations, and
returns the exact checker-masked categorical distribution.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.ActionEvidencePCBridge

namespace Mettapedia.GSLT.LanguageDef.GauthierGradeBActionEvidence

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierSkeletonMask
open Mettapedia.GSLT.LanguageDef.GauthierProgramDAG
open Mettapedia.GSLT.LanguageDef.GauthierPartialPostfixAlignment
open Mettapedia.GSLT.LanguageDef.GauthierAlignmentEvidence
open Mettapedia.GSLT.LanguageDef.GauthierActionEvidencePCBridge
open Mettapedia.PLN.Bridges.PredictiveCoding
open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

/-- One historical artifact row awaiting authentication.  `sourceLineage`
retains the exact row lineage for audit; its causal source class is derived
only from the separately supplied provenance-manifest certificate. -/
structure HistoricalProgram where
  sourceOrdinal : Nat
  dag : WireProgramDAG
  verdict : TotalityVerdict
  sourceLineage : Nat

/-- Turn an accepted wire artifact into the proof-carrying reference expected
by the alignment layer.  Parser authentication and the explicit budget check
both fail closed. -/
def authenticateReference? (maxLen : Nat) (history : HistoricalProgram) :
    Option (AuthenticatedReference orgMemoSignature maxLen) :=
  match hunfold : unfoldWire? orgMemoSignature history.dag with
  | none => none
  | some program =>
      if hbudget : (rpnTokens program).length ≤ maxLen then
        some
          { sourceOrdinal := history.sourceOrdinal
            program
            wellFormed := unfoldWire_wellFormed hunfold
            withinBudget := hbudget }
      else none

/-- Build one observation from the selected aligned candidate.  Alignment
must expose a real tree coordinate and the action must belong to the finite
operator vocabulary; otherwise the row is rejected. -/
def observationForHistory {World Lineage : Type*}
    {graph : LineageDAG Nat World Lineage}
    (certificate : SourceClassCertificate graph)
    (maxLen : Nat) (query : ActionQuery)
    (currentForest : List Prog) (currentState : MaskState)
    (history : HistoricalProgram) : Option ActionObservation := do
  let reference ← authenticateReference? maxLen history
  let candidate ← chooseMostSpecific
    (candidatesForReference orgMemoSignature currentForest currentState reference)
  let coordinate ← candidate.alignment.coordinates.head?
  let actionNat := candidate.action.toNat
  if haction : actionNat < operatorCount then
    pure
      { query
        alignmentCoordinate := coordinate
        structuralSource := rpnTokens reference.program
        action := ⟨actionNat, haction⟩
        verdict := history.verdict
        sourceLineage := history.sourceLineage
        sourceRoot := certificate.classOf history.sourceLineage }
  else none

/-- Complete result of one legal partial-decoder evidence query. -/
structure GradeBStepResult where
  query : ActionQuery
  state : MaskState
  legalTokens : List PyToken
  observations : List ActionObservation
  evidence : GradedActionEvidence operatorCount
  actionDistribution : List ExactActionProbability

/-- **Executable Grade-B reference implementation.** -/
def gradeBStep? {World Lineage : Type*}
    {graph : LineageDAG Nat World Lineage}
    (certificate : SourceClassCertificate graph)
    (maxLen : Nat) (targetQuery : Nat)
    (decoderPrefix : List Nat) (history : List HistoricalProgram) :
    Option GradeBStepResult := do
  let state ← run orgMemoSignature (decoderPrefix.map Int.ofNat) (initial maxLen)
  let currentForest ← prefixForest? orgMemoSignature decoderPrefix
  let query : ActionQuery := ⟨targetQuery, decoderPrefix⟩
  let observations := history.filterMap
    (observationForHistory certificate maxLen query currentForest state)
  let evidence := alignedRepresentativeEvidence observations query
  pure
    { query
      state
      legalTokens := Mettapedia.GSLT.LanguageDef.GauthierSkeletonMask.legalTokens
        orgMemoSignature state
      observations
      evidence
      actionDistribution := exactMaskedActionDistribution evidence state }

/-- A failed decoder prefix cannot acquire action evidence. -/
theorem invalid_prefix_fails_closed {World Lineage : Type*}
    {graph : LineageDAG Nat World Lineage}
    (certificate : SourceClassCertificate graph)
    (maxLen targetQuery : Nat)
    (history : List HistoricalProgram) :
    gradeBStep? certificate maxLen targetQuery [99] history = none := by
  have houtside : (99 : Int) ∉
      Mettapedia.GSLT.LanguageDef.GauthierSkeletonMask.legalTokens
        orgMemoSignature (initial maxLen) := by
    simp only [legalTokens, List.mem_append, not_or]
    constructor
    · simp [initial]
    · intro hmem
      obtain ⟨id, hid, hid99⟩ := List.mem_map.mp hmem
      have hidRange : id < orgMemoSignature.length := by
        exact List.mem_range.mp (List.mem_filter.mp hid).1
      have hlength : orgMemoSignature.length = operatorCount := by rfl
      rw [hlength, operatorCount_eq] at hidRange
      norm_num at hid99
      omega
  simp [gradeBStep?, run, step?, houtside]

/-- Unknown historical operators fail authentication before alignment. -/
theorem unknown_history_fails_authentication (maxLen : Nat)
    (history : HistoricalProgram) (hdag : history.dag = unknownOperator) :
    authenticateReference? maxLen history = none := by
  rcases history with ⟨sourceOrdinal, dag, verdict, sourceLineage⟩
  dsimp only at hdag ⊢
  subst dag
  rw [authenticateReference?]
  simp [unfoldWire?, unknownOperator_rejected]

/-- The shared-subtree wire fixture is accepted by the complete reference
boundary, not merely by an isolated Boolean predicate. -/
def sharedPositiveHistory : HistoricalProgram :=
  { sourceOrdinal := 0
    dag := sharedZeroAdd
    verdict := .provablyTotal
    sourceLineage := 10 }

/-- Minimal certified provenance surface for the executable canary.  The
constant class is conservative: it can discard independence but cannot
manufacture it.  Production callers supply their authenticated manifest
certificate instead. -/
def canaryLineageDAG : LineageDAG Nat Unit Unit where
  node source :=
    { world := ()
      lineage := ()
      generation := source
      parents := ∅ }
  parentEarlier := by intro parent child hparent; simp at hparent
  parentSameWorld := by intro parent child hparent; simp at hparent
  parentSameLineage := by intro parent child hparent; simp at hparent

def canarySourceClassCertificate : SourceClassCertificate canaryLineageDAG where
  classOf _ := 0
  commonAncestor_same := by intros; rfl

theorem sharedPositiveHistory_authenticates :
    (authenticateReference? 8 sharedPositiveHistory).isSome := by
  unfold authenticateReference?
  split
  · rename_i heq
    rw [sharedPositiveHistory, sharedZeroAdd_unfolds] at heq
    contradiction
  · rename_i program heq
    rw [sharedPositiveHistory, sharedZeroAdd_unfolds] at heq
    have hprogram : program = .node 3 [.node 0 [], .node 0 []] := by
      exact (Option.some.inj heq).symm
    subst program
    simp [rpnTokens]

/-- Concrete end-to-end canary evaluated and pinned by the fixture exporter. -/
def sharedPositiveStep : Option GradeBStepResult :=
  gradeBStep? canarySourceClassCertificate 8 42 [0] [sharedPositiveHistory]

#print axioms invalid_prefix_fails_closed
#print axioms unknown_history_fails_authentication
#print axioms sharedPositiveHistory_authenticates

end Mettapedia.GSLT.LanguageDef.GauthierGradeBActionEvidence
