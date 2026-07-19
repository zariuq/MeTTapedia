import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.BudgetedRuntime
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Path
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ScopedSyntax

/-!
# Whole-prefix refinement for budgeted cost-rho execution

The two-budget executor returns only an operational record.  This module
recovers the exact occurrence-bearing `CostPath` that record executed.  In
particular, exhaustive search failure certifies declarative quiescence, while
search exhaustion carries no negative conclusion.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- Evidence that a budgeted operational prefix is exactly one declarative
`CostPath`, including its occurrence provenance and event identifiers. -/
structure BudgetedPrefixPathWitness
    (fuel searchBudget eventId : Nat)
    (components : List RawTraceComponent) (reverseReceipt : RawReceipt) where
  finalId : Nat
  finalComponents : List RawTraceComponent
  path : CostPath eventId components finalId finalComponents
  residual_eq :
    (runBudgetedCausalPrefix fuel searchBudget eventId components
      reverseReceipt).residual = tracedResidual finalComponents
  receipt_eq :
    (runBudgetedCausalPrefix fuel searchBudget eventId components
      reverseReceipt).receipt = reverseReceipt.reverse ++ path.rawEmission
  depth_le : path.depth ≤ fuel
  remainingSearchBudget_le :
    (runBudgetedCausalPrefix fuel searchBudget eventId components
      reverseReceipt).remainingSearchBudget ≤ searchBudget
  quiescent_frontier_empty :
    (runBudgetedCausalPrefix fuel searchBudget eventId components
      reverseReceipt).status = .quiescent →
      runtimeCostCandidatesFromConfig
        (finalComponents.map RawTraceComponent.term) = []
  fuelExhausted_depth_eq :
    (runBudgetedCausalPrefix fuel searchBudget eventId components
      reverseReceipt).status = .fuelExhausted →
      path.depth = fuel

/-- Propositional form of whole-prefix path refinement, exposing the actual
final state and occurrence-bearing path as existential witnesses. -/
def BudgetedPrefixPathRefines
    (fuel searchBudget eventId : Nat)
    (components : List RawTraceComponent) (reverseReceipt : RawReceipt) : Prop :=
  ∃ (finalId : Nat) (finalComponents : List RawTraceComponent)
      (path : CostPath eventId components finalId finalComponents),
    (runBudgetedCausalPrefix fuel searchBudget eventId components
      reverseReceipt).residual = tracedResidual finalComponents ∧
    (runBudgetedCausalPrefix fuel searchBudget eventId components
      reverseReceipt).receipt = reverseReceipt.reverse ++ path.rawEmission ∧
    path.depth ≤ fuel ∧
    (runBudgetedCausalPrefix fuel searchBudget eventId components
      reverseReceipt).remainingSearchBudget ≤ searchBudget ∧
    ((runBudgetedCausalPrefix fuel searchBudget eventId components
      reverseReceipt).status = .quiescent →
        runtimeCostCandidatesFromConfig
          (finalComponents.map RawTraceComponent.term) = []) ∧
    ((runBudgetedCausalPrefix fuel searchBudget eventId components
      reverseReceipt).status = .fuelExhausted → path.depth = fuel)

/-- Whole-prefix refinement: every operational firing selected by the
two-budget runner is witnessed by the independent declarative runtime
relation. -/
def budgetedPrefixPathWitness :
    ∀ (fuel searchBudget eventId : Nat)
      (components : List RawTraceComponent) (reverseReceipt : RawReceipt),
      TraceComponentsWellFormed components →
      TraceComponentsBefore eventId components →
      BudgetedPrefixPathWitness fuel searchBudget eventId components
        reverseReceipt := by
  intro fuel
  induction fuel with
  | zero =>
      intro searchBudget eventId components reverseReceipt supported bounded
      exact
        { finalId := eventId
          finalComponents := components
          path := .done supported bounded
          residual_eq := rfl
          receipt_eq := by simp [runBudgetedCausalPrefix, CostPath.rawEmission]
          depth_le := by simp [CostPath.depth]
          remainingSearchBudget_le := by simp [runBudgetedCausalPrefix]
          quiescent_frontier_empty := by
            simp [runBudgetedCausalPrefix]
          fuelExhausted_depth_eq := by
            simp [runBudgetedCausalPrefix, CostPath.depth] }
  | succ fuel ih =>
      intro searchBudget eventId components reverseReceipt supported bounded
      cases search_eq : budgetedFirstRuntimeCandidate searchBudget
          (components.map RawTraceComponent.term) with
      | mk decision remaining =>
          cases decision with
          | searchExhausted =>
              exact
                { finalId := eventId
                  finalComponents := components
                  path := .done supported bounded
                  residual_eq := by
                    simp [runBudgetedCausalPrefix, search_eq]
                  receipt_eq := by
                    simp [runBudgetedCausalPrefix, search_eq,
                      CostPath.rawEmission]
                  depth_le := by simp [CostPath.depth]
                  remainingSearchBudget_le := by
                    simpa [runBudgetedCausalPrefix, search_eq] using
                      budgetedFirstRuntimeCandidate_remaining_le searchBudget
                        (components.map RawTraceComponent.term)
                  quiescent_frontier_empty := by
                    simp [runBudgetedCausalPrefix, search_eq]
                  fuelExhausted_depth_eq := by
                    simp [runBudgetedCausalPrefix, search_eq] }
          | noCandidate =>
              have frontier_empty :
                  runtimeCostCandidatesFromConfig
                    (components.map RawTraceComponent.term) = [] :=
                budgetedFirstRuntimeCandidate_noCandidate search_eq
              exact
                { finalId := eventId
                  finalComponents := components
                  path := .done supported bounded
                  residual_eq := by
                    simp [runBudgetedCausalPrefix, search_eq]
                  receipt_eq := by
                    simp [runBudgetedCausalPrefix, search_eq,
                      CostPath.rawEmission]
                  depth_le := by simp [CostPath.depth]
                  remainingSearchBudget_le := by
                    simpa [runBudgetedCausalPrefix, search_eq] using
                      budgetedFirstRuntimeCandidate_remaining_le searchBudget
                        (components.map RawTraceComponent.term)
                  quiescent_frontier_empty := by
                    intro _
                    exact frontier_empty
                  fuelExhausted_depth_eq := by
                    simp [runBudgetedCausalPrefix, search_eq] }
          | found step =>
              have enabled : step ∈ runtimeCostCandidatesFromConfig
                  (components.map RawTraceComponent.term) :=
                budgetedFirstRuntimeCandidate_found_sound search_eq
              have nextSupported : TraceComponentsWellFormed
                  (applyTracedStep components step eventId) :=
                applyTracedStep_wellFormed supported enabled eventId
              have nextBounded : TraceComponentsBefore (eventId + 1)
                  (applyTracedStep components step eventId) :=
                applyTracedStep_before bounded step
              let event := eventFor components step eventId
              let next := applyTracedStep components step eventId
              have tail := ih remaining (eventId + 1) next
                (event :: reverseReceipt) nextSupported nextBounded
              exact
                { finalId := tail.finalId
                  finalComponents := tail.finalComponents
                  path := .fire supported bounded step enabled tail.path
                  residual_eq := by
                    simpa [runBudgetedCausalPrefix, search_eq, event, next]
                      using tail.residual_eq
                  receipt_eq := by
                    simpa [runBudgetedCausalPrefix, search_eq, event, next,
                      CostPath.rawEmission, List.reverse_cons,
                      List.append_assoc] using tail.receipt_eq
                  depth_le := by
                    have tail_depth_le := tail.depth_le
                    simp only [CostPath.depth]
                    omega
                  remainingSearchBudget_le := by
                    have search_le : remaining ≤ searchBudget := by
                      simpa [search_eq] using
                        budgetedFirstRuntimeCandidate_remaining_le searchBudget
                          (components.map RawTraceComponent.term)
                    have tail_le := tail.remainingSearchBudget_le
                    simpa [runBudgetedCausalPrefix, search_eq, event, next] using
                      Nat.le_trans tail_le search_le
                  quiescent_frontier_empty := by
                    simpa [runBudgetedCausalPrefix, search_eq, event, next] using
                      tail.quiescent_frontier_empty
                  fuelExhausted_depth_eq := by
                    intro exhausted
                    have tail_exhausted :
                        (runBudgetedCausalPrefix fuel remaining (eventId + 1)
                          next (event :: reverseReceipt)).status =
                            .fuelExhausted := by
                      simpa [runBudgetedCausalPrefix, search_eq, event, next]
                        using exhausted
                    have depth_eq := tail.fuelExhausted_depth_eq tail_exhausted
                    simp only [CostPath.depth]
                    omega }

/-- Whole-prefix refinement theorem for the two-budget executor. -/
theorem BudgetedPrefixPathRefinement
    (fuel searchBudget eventId : Nat)
    (components : List RawTraceComponent) (reverseReceipt : RawReceipt)
    (supported : TraceComponentsWellFormed components)
    (bounded : TraceComponentsBefore eventId components) :
    BudgetedPrefixPathRefines fuel searchBudget eventId components
      reverseReceipt := by
  let witness := budgetedPrefixPathWitness fuel searchBudget eventId components
    reverseReceipt supported bounded
  exact ⟨witness.finalId, witness.finalComponents, witness.path,
    witness.residual_eq, witness.receipt_eq, witness.depth_le,
    witness.remainingSearchBudget_le, witness.quiescent_frontier_empty,
    witness.fuelExhausted_depth_eq⟩

/-- An admitted source term starts with empty provenance and its budgeted
execution refines an actual cost path. -/
def boundedBudgetedCausalPrefix_pathWitness
    {fuel searchBudget : Nat} {term : RawCostTerm}
    (supported : term.supported = true) :
    BudgetedPrefixPathWitness fuel searchBudget 0
      (initialTraceComponents term) [] :=
  budgetedPrefixPathWitness fuel searchBudget 0
    (initialTraceComponents term) []
    (initialTraceComponents_wellFormed
      ((RawCostTerm.supported_iff term).mp supported).1)
    (initialTraceComponents_before term)

/-- Publicly admitted sources satisfy whole-prefix path refinement. -/
theorem boundedBudgetedCausalPrefix_pathRefinement
    {fuel searchBudget : Nat} {term : RawCostTerm}
    (supported : term.supported = true) :
    BudgetedPrefixPathRefines fuel searchBudget 0
      (initialTraceComponents term) [] :=
  BudgetedPrefixPathRefinement fuel searchBudget 0
    (initialTraceComponents term) []
    (initialTraceComponents_wellFormed
      ((RawCostTerm.supported_iff term).mp supported).1)
    (initialTraceComponents_before term)

/-- The public wrapper returns the same refined execution when its raw source
passes the grammar check. -/
theorem boundedBudgetedCausalPrefix_eq_refined_run
    {fuel searchBudget : Nat} {term : RawCostTerm}
    (supported : term.supported = true) :
    boundedBudgetedCausalPrefix fuel searchBudget term =
      some (runBudgetedCausalPrefix fuel searchBudget 0
        (initialTraceComponents term) []) := by
  simp [boundedBudgetedCausalPrefix, initialTraceComponents, supported]

/-- Direct public-wrapper corollary: a successful grammar check returns a
prefix whose residual, receipt, statuses, and budgets are witnessed by one
actual occurrence-bearing `CostPath`. -/
theorem boundedBudgetedCausalPrefix_refinesPath
    {fuel searchBudget : Nat} {term : RawCostTerm}
    (supported : term.supported = true) :
    ∃ (result : BudgetedCausalPrefix) (finalId : Nat)
        (finalComponents : List RawTraceComponent)
        (path : CostPath 0 (initialTraceComponents term)
          finalId finalComponents),
      boundedBudgetedCausalPrefix fuel searchBudget term = some result ∧
      result.residual = tracedResidual finalComponents ∧
      result.receipt = path.rawEmission ∧
      path.depth ≤ fuel ∧
      result.remainingSearchBudget ≤ searchBudget ∧
      (result.status = .quiescent →
        runtimeCostCandidatesFromConfig
          (finalComponents.map RawTraceComponent.term) = []) ∧
      (result.status = .fuelExhausted → path.depth = fuel) := by
  let witness := boundedBudgetedCausalPrefix_pathWitness
    (fuel := fuel) (searchBudget := searchBudget) supported
  let result := runBudgetedCausalPrefix fuel searchBudget 0
    (initialTraceComponents term) []
  refine ⟨result, witness.finalId, witness.finalComponents, witness.path,
    boundedBudgetedCausalPrefix_eq_refined_run supported,
    witness.residual_eq, ?_, witness.depth_le,
    witness.remainingSearchBudget_le, witness.quiescent_frontier_empty,
    witness.fuelExhausted_depth_eq⟩
  simpa [result] using witness.receipt_eq

/-- The path recovered from a public execution emits a valid causal receipt. -/
theorem boundedBudgetedCausalPrefix_receipt_valid
    {fuel searchBudget : Nat} {term : RawCostTerm}
    (supported : term.supported = true) :
    let witness := boundedBudgetedCausalPrefix_pathWitness
      (fuel := fuel) (searchBudget := searchBudget) supported
    witness.path.emission.Valid := by
  dsimp
  exact CostPath.emitted_receipt_valid _

/-- The operational order of the recovered public receipt linearizes its
consumption-derived causal order. -/
theorem boundedBudgetedCausalPrefix_emission_linearizes
    {fuel searchBudget : Nat} {term : RawCostTerm}
    (supported : term.supported = true) :
    let witness := boundedBudgetedCausalPrefix_pathWitness
      (fuel := fuel) (searchBudget := searchBudget) supported
    ∀ {earlier later : Fin witness.path.emission.length},
      ((witness.path.emission.toReceipt
        witness.path.emitted_receipt_valid).CausalLE earlier later) →
      earlier ≤ later := by
  dsimp
  intro earlier later causal
  exact CostPath.emission_linearizes _ causal

/-! ## Status-separation examples -/

private def refinementExampleSurface : RawCostName := .signature ["pay"]
private def refinementExampleSpend : RawCostSig := ["coin"]
private def refinementExampleDone : RawCostTerm := .signed .nil ["done"]
private def refinementExamplePayload : RawCostTerm := .signed .nil ["payload"]

private def refinementExampleTerm : RawCostTerm :=
  RawCostTerm.fromComponents
    [.signed
      (.par
        (.recv refinementExampleSurface refinementExampleDone)
        (.send refinementExampleSurface refinementExamplePayload))
      refinementExampleSpend,
     .purse refinementExampleSurface [refinementExampleSpend]]

private theorem refinementExampleTerm_supported :
    refinementExampleTerm.supported = true := by decide

/-- Sufficient firing and search allowance yields an actual one-event path. -/
example :
    (boundedBudgetedCausalPrefix_pathWitness
      (fuel := 1) (searchBudget := 3)
      refinementExampleTerm_supported).path.depth = 1 := by
  decide

/-- Exhaustive candidate failure, unlike bounded exhaustion, certifies a
quiescent empty path. -/
example :
    let result := runBudgetedCausalPrefix 1 0 0 [] []
    result.status = .quiescent ∧
      runtimeCostCandidatesFromConfig [] = [] := by
  decide

/-- Zero firing allowance reports fuel exhaustion even though an eager
semantic successor exists. -/
example :
    let initial := initialTraceComponents refinementExampleTerm
    let result := runBudgetedCausalPrefix 0 3 0 initial []
    result.status = .fuelExhausted ∧
      runtimeCostCandidatesFromConfig
        (initial.map RawTraceComponent.term) ≠ [] := by
  decide

/-- Zero search allowance reports search exhaustion and makes no negative
claim: the independent eager candidate relation is nonempty. -/
example :
    let initial := initialTraceComponents refinementExampleTerm
    let result := runBudgetedCausalPrefix 1 0 0 initial []
    result.status = .searchExhausted ∧
      runtimeCostCandidatesFromConfig
        (initial.map RawTraceComponent.term) ≠ [] := by
  decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
