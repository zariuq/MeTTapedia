import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.StaticDeploymentAnalysis

/-!
# Static deployment-analysis conformance examples

The positive example has one funded COMM and reaches quiescence at the exact
analysis bound.  The negative bound example refuses to certify that same live
term at depth zero.  A literal quoted drop is separately checked as inert,
matching the concrete runtime rather than silently importing a stronger
paper-level resolver.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

namespace StaticDeploymentAnalysisExamples

open StaticCallTree

def surface : RawCostName := .signature ["pay"]
def spend : RawCostSig := ["coin"]
def done : RawCostTerm := .signed .nil ["done"]
def payload : RawCostTerm := .signed .nil ["payload"]

def oneComm : RawCostTerm :=
  RawCostTerm.fromComponents
    [.signed
      (.par
        (.recv surface done)
        (.send surface payload))
      spend,
     .purse surface [spend]]

theorem oneComm_wellFormed : oneComm.wellFormed = true := by decide

/-- One step is sufficient to analyze every branch through quiescence. -/
theorem oneComm_analyzed :
    (analyzeDeployment? 1 oneComm).isSome = true := by decide

/-- The independent concrete frontier reports exactly the selected purse-head
occurrence that the static call tree accumulates. -/
theorem oneComm_exact_frontier_demand :
    (runtimeCostCandidatesFromConfig
      ((initialTraceComponents oneComm).map RawTraceComponent.term)).map
        RawRuntimeStep.fundingDemand = [[(surface, spend)]] := by
  decide

/-- A live frontier at the depth bound is incomplete, never quiescent. -/
theorem oneComm_zero_bound_incomplete :
    (analyzeDeployment? 0 oneComm).isSome = false := by decide

def hiddenComm : RawCostTerm := .drop (.quote oneComm)

theorem hiddenComm_wellFormed : hiddenComm.wellFormed = true := by decide

/-- Literal dequotation is inert in the concrete runtime, so the quoted COMM
has an empty frontier and a complete zero-depth analysis. -/
theorem hiddenComm_frontier_empty : runtimeCostCandidatesFromConfig
    ((initialTraceComponents hiddenComm).map RawTraceComponent.term) = [] := by
  decide

theorem hiddenComm_zero_demand_analyzed :
    (analyzeDeployment? 0 hiddenComm).isSome = true := by decide

def malformed : RawCostTerm := .signed .nil []

/-- Malformed cost syntax is rejected before call-tree analysis. -/
theorem malformed_rejected :
    (analyzeDeployment? 1 malformed).isSome = false := by decide

/-- Every successfully analyzed term is accepted against the conservative
envelope computed from all of its branches. -/
theorem oneComm_has_accepted_envelope :
    ∃ deployment reservation,
      analyzeDeployment? 1 oneComm = some deployment ∧
      checkDeployment 1 oneComm deployment.conservativeDemand =
        .accepted deployment reservation := by
  have analyzedSome : (analyzeDeployment? 1 oneComm).isSome := by
    simpa using oneComm_analyzed
  obtain ⟨deployment, analyzed⟩ :=
    Option.isSome_iff_exists.mp analyzedSome
  obtain ⟨reservation, accepted⟩ :=
    checkDeployment_accepts_conservativeDemand analyzed
  exact ⟨deployment, reservation, analyzed, accepted⟩

/-- An insufficient analysis depth remains distinct from resource rejection. -/
theorem zero_bound_analysis_incomplete (supply : Multiset RawFundingCell) :
    checkDeployment 0 oneComm supply = .analysisIncomplete := by
  apply (checkDeployment_analysisIncomplete_iff 0 oneComm supply).2
  cases analyzed : analyzeDeployment? 0 oneComm with
  | none => exact analyzed
  | some deployment =>
      have incomplete := oneComm_zero_bound_incomplete
      simp [analyzed] at incomplete

end StaticDeploymentAnalysisExamples

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
