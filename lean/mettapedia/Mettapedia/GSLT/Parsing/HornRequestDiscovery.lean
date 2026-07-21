import Mettapedia.GSLT.Parsing.HornPlan
import Mettapedia.GSLT.Parsing.HornSemanticEnumeration

/-!
# Fail-closed discovery of specialization requests

A finite candidate generator may deliberately overproduce.  This module
filters those candidates through the checked Horn specializer, proves that
the surviving requests compile as one presentation, and lifts a coverage
witness for the candidate universe to the exact `RequestsExhaustive`
obligation consumed by `HornPlan`.
-/

namespace Mettapedia.GSLT.Parsing.HornRequestDiscovery

open HornCertificate HornSpecialization HornPlan
open GuardCorrespondence PackedForest GroundedChart BackendCorrespondence

def discoveredRequests (program : Program) (parseRelation : String)
    (candidates : List LinearRequest) : List LinearRequest :=
  candidates.filter fun request =>
    (compileRequest program parseRelation request).isSome

def discoveredRules (program : Program) (parseRelation : String)
    (candidates : List LinearRequest) : List NormalizedRule :=
  candidates.filterMap (compileRequest program parseRelation)

theorem mem_discoveredRules_iff (program : Program) (parseRelation : String)
    (candidates : List LinearRequest) (normalized : NormalizedRule) :
    normalized ∈ discoveredRules program parseRelation candidates ↔
      ∃ request ∈ candidates,
        compileRequest program parseRelation request = some normalized := by
  simp [discoveredRules]

theorem mem_discoveredRequests_iff (program : Program) (parseRelation : String)
    (candidates : List LinearRequest) (request : LinearRequest) :
    request ∈ discoveredRequests program parseRelation candidates ↔
      request ∈ candidates ∧
        (compileRequest program parseRelation request).isSome = true := by
  simp [discoveredRequests]

theorem compileRequests_discovered (program : Program) (parseRelation : String)
    (candidates : List LinearRequest) :
    compileRequests program parseRelation
        (discoveredRequests program parseRelation candidates) =
      some (discoveredRules program parseRelation candidates) := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates inductionHypothesis =>
      change compileRequests program parseRelation
          ((candidate :: candidates).filter fun request =>
            (compileRequest program parseRelation request).isSome) =
        some ((candidate :: candidates).filterMap
          (compileRequest program parseRelation))
      change compileRequests program parseRelation
          (candidates.filter fun request =>
            (compileRequest program parseRelation request).isSome) =
        some (candidates.filterMap (compileRequest program parseRelation)) at inductionHypothesis
      cases accepted : compileRequest program parseRelation candidate with
      | none =>
          simp [accepted, inductionHypothesis]
      | some rule =>
          simp [accepted, compileRequests, inductionHypothesis]

/-- The generator's finite candidate universe covers the semantic request
domain.  Candidates may be malformed or redundant; `eligible` is required
only for candidates that pass the checked compiler. -/
structure CandidatesCover (program : Program) (parseRelation : String)
    (admitted : LinearRequest → Prop) (candidates : List LinearRequest) : Prop where
  eligible : ∀ request, request ∈ candidates →
    (compileRequest program parseRelation request).isSome = true → admitted request
  covers : ∀ request rule,
    admitted request → RequestCompiles program parseRelation request rule →
    ∃ candidate ∈ candidates,
      RequestCompiles program parseRelation candidate rule

theorem discoveredRequests_exhaustive
    {program : Program} {parseRelation : String}
    {admitted : LinearRequest → Prop} {candidates : List LinearRequest}
    (coverage : CandidatesCover program parseRelation admitted candidates) :
    RequestsExhaustive program parseRelation admitted
      (discoveredRequests program parseRelation candidates) := by
  constructor
  · intro request member
    obtain ⟨candidateMember, accepted⟩ :=
      (mem_discoveredRequests_iff program parseRelation candidates request).mp
        member
    exact coverage.eligible request candidateMember accepted
  · intro request rule admittedRequest requestCompiled
    obtain ⟨candidate, candidateMember, candidateCompiled⟩ :=
      coverage.covers request rule admittedRequest requestCompiled
    have accepted := compileRequest_complete program parseRelation candidate rule
      candidateCompiled
    refine ⟨candidate, ?_, candidateCompiled⟩
    exact (mem_discoveredRequests_iff program parseRelation candidates candidate).2
      ⟨candidateMember, by simp [accepted]⟩

theorem discoveredRules_exact
    (program : Program) (parseRelation : String)
    (admitted : LinearRequest → Prop) (candidates : List LinearRequest)
    (coverage : CandidatesCover program parseRelation admitted candidates)
    (rule : NormalizedRule) :
    rule ∈ discoveredRules program parseRelation candidates ↔
      ∃ request, admitted request ∧
        RequestCompiles program parseRelation request rule := by
  exact compileRequests_exact_of_exhaustive program parseRelation admitted
    (discoveredRequests program parseRelation candidates)
    (discoveredRules program parseRelation candidates)
    (compileRequests_discovered program parseRelation candidates)
    (discoveredRequests_exhaustive coverage) rule

def discoveredPresentation (program : Program) (parseRelation : String)
    (start : CompilerCorrespondence.Category)
    (candidates : List LinearRequest) :
    NormalizedPresentation :=
  { start := start
    rules := discoveredRules program parseRelation candidates }

theorem compileDiscoveredPresentation_accepts
    (program : Program) (parseRelation : String)
    (start : CompilerCorrespondence.Category)
    (candidates : List LinearRequest) :
    compilePresentation program parseRelation start
        (discoveredRequests program parseRelation candidates) =
      some (discoveredPresentation program parseRelation start candidates) := by
  simp [compilePresentation, discoveredPresentation,
    compileRequests_discovered]

theorem discoveredPlan_chart_result_set_agreement
    (program : Program) (parseRelation : String)
    (start : CompilerCorrespondence.Category)
    (candidates : List LinearRequest)
    (input : List CompilerCorrespondence.Codepoint) :
    packedResults
        (chartForest
          (GuardCorrespondence.compile
            (discoveredPresentation program parseRelation start candidates))
          input)
        (discoveredPresentation program parseRelation start candidates) input =
      GuardCorrespondence.sourceResults
        (discoveredPresentation program parseRelation start candidates) input := by
  exact (acceptedPlan_chart_result_set_agreement program parseRelation start
    (discoveredRequests program parseRelation candidates)
    (discoveredPresentation program parseRelation start candidates)
    (compileDiscoveredPresentation_accepts program parseRelation start candidates)
    input).2

theorem discoveredPlan_backend_result_set_agreement
    (program : Program) (parseRelation : String)
    (start : CompilerCorrespondence.Category)
    (candidates : List LinearRequest)
    (input : List CompilerCorrespondence.Codepoint)
    (backend : Forest)
    (covers : ForestCovers
      (rootReachableForest
        (chartForest
          (GuardCorrespondence.compile
            (discoveredPresentation program parseRelation start candidates))
          input))
      backend) :
    packedResults backend
        (discoveredPresentation program parseRelation start candidates) input =
      GuardCorrespondence.sourceResults
        (discoveredPresentation program parseRelation start candidates) input := by
  exact (acceptedPlan_backend_result_set_agreement program parseRelation start
    (discoveredRequests program parseRelation candidates)
    (discoveredPresentation program parseRelation start candidates) input backend
    (compileDiscoveredPresentation_accepts program parseRelation start candidates)
    covers).2

/-! ## Executable positive and negative controls -/

def controlCandidates : List LinearRequest :=
  [controlRequest, mutatedRequest]

theorem controlDiscovery_keeps_only_checked_request :
    discoveredRequests exampleProgram "parse" controlCandidates =
      [controlRequest] := by
  decide

theorem controlDiscovery_keeps_only_checked_rule :
    discoveredRules exampleProgram "parse" controlCandidates =
      [controlRule] := by
  decide

theorem controlDiscoveredPresentation_is_controlPresentation :
    discoveredPresentation exampleProgram "parse" "g0" controlCandidates =
      HornPlan.controlPresentation := by
  decide

theorem controlTree_mem_discovered_chart :
    HornPlan.controlTree ∈
      packedResults
        (chartForest
          (GuardCorrespondence.compile
            (discoveredPresentation exampleProgram "parse" "g0"
              controlCandidates))
          [97])
        (discoveredPresentation exampleProgram "parse" "g0" controlCandidates)
        [97] := by
  rw [discoveredPlan_chart_result_set_agreement]
  simpa [controlDiscoveredPresentation_is_controlPresentation] using
    HornPlan.controlTree_mem_sourceResults

def controlAdmittedRequest (request : LinearRequest) : Prop :=
  request = controlRequest

theorem controlCandidates_cover :
    CandidatesCover exampleProgram "parse" controlAdmittedRequest
      controlCandidates := by
  constructor
  · intro request member accepted
    simp [controlCandidates] at member
    rcases member with rfl | rfl
    · rfl
    · have rejected :
          compileRequest exampleProgram "parse" mutatedRequest = none := by
        decide
      simp [rejected] at accepted
  · intro request rule admittedRequest requestCompiled
    subst request
    exact ⟨controlRequest, by simp [controlCandidates], requestCompiled⟩

theorem controlDiscoveredRules_are_exact (rule : NormalizedRule) :
    rule ∈ discoveredRules exampleProgram "parse" controlCandidates ↔
      ∃ request, controlAdmittedRequest request ∧
        RequestCompiles exampleProgram "parse" request rule :=
  discoveredRules_exact exampleProgram "parse" controlAdmittedRequest
    controlCandidates controlCandidates_cover rule

end Mettapedia.GSLT.Parsing.HornRequestDiscovery
