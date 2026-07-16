import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.BudgetedPreconditions

/-!
# Versioned two-budget cost-rho differential boundary

This wire boundary exposes reduction fuel and candidate-search work
independently, including an explicit search-exhausted result.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

namespace CostWire

def budgetedCausalPrefixSchema : String :=
  "cetta.cost-rho.causal-prefix.v2"

structure BudgetedPrefixRequest where
  schema : String
  fuel : Nat
  searchFuel : Nat
  term : CostWire
  deriving Repr, Lean.ToJson, Lean.FromJson

inductive BudgetedPrefixOutcome where
  | schemaMismatch
  | malformedWire
  | malformedTerm
  | result : CostWire → BudgetedPrefixOutcome
  deriving Repr, Lean.ToJson, Lean.FromJson

def encodeBudgetedPrefixStatus : BudgetedPrefixStatus → CostWire
  | .quiescent => .symbol "quiescent"
  | .fuelExhausted => .symbol "fuel-exhausted"
  | .searchExhausted => .symbol "search-exhausted"

def encodeBudgetedPrefix (result : BudgetedCausalPrefix) : CostWire :=
  .node "causal-prefix"
    [encodeBudgetedPrefixStatus result.status,
     encodeReceipt result.receipt,
     encodeTerm result.residual]

def evaluateBudgetedPrefix
    (request : BudgetedPrefixRequest) : BudgetedPrefixOutcome :=
  if request.schema != budgetedCausalPrefixSchema then .schemaMismatch
  else
    match decodeTerm request.term with
    | none => .malformedWire
    | some term =>
        match boundedBudgetedCausalPrefix request.fuel request.searchFuel term with
        | none => .malformedTerm
        | some execution => .result (encodeBudgetedPrefix execution)

/-- Decode and expose the exact runtime-bridge preconditions checked for a
theorem-covered differential case. -/
def budgetedPrefixPreconditions
    (request : BudgetedPrefixRequest) : Option RuntimePreconditionChecks :=
  if request.schema != budgetedCausalPrefixSchema then none
  else (decodeTerm request.term).map runtimePreconditionChecks

theorem evaluateBudgetedPrefix_of_decoded
    {request : BudgetedPrefixRequest} {term : RawCostTerm}
    {execution : BudgetedCausalPrefix}
    (schemaOk : request.schema = budgetedCausalPrefixSchema)
    (decoded : decodeTerm request.term = some term)
    (executed : boundedBudgetedCausalPrefix request.fuel request.searchFuel term =
      some execution) :
    evaluateBudgetedPrefix request =
      .result (encodeBudgetedPrefix execution) := by
  simp [evaluateBudgetedPrefix, schemaOk, decoded, executed]

theorem evaluateBudgetedPrefix_encodeTerm_exists
    (fuel searchFuel : Nat) (term : RawCostTerm)
    (supported : term.wellFormed = true) :
    ∃ execution,
      boundedBudgetedCausalPrefix fuel searchFuel term = some execution ∧
      evaluateBudgetedPrefix
          { schema := budgetedCausalPrefixSchema
            fuel
            searchFuel
            term := encodeTerm term } =
        .result (encodeBudgetedPrefix execution) := by
  let initial : List RawTraceComponent :=
    term.normalizeConfig.map fun component =>
      { term := component, producer := none }
  let execution := runBudgetedCausalPrefix fuel searchFuel 0 initial []
  refine ⟨execution, ?_, ?_⟩
  · simp [boundedBudgetedCausalPrefix, supported, execution, initial]
  · apply evaluateBudgetedPrefix_of_decoded (request :=
      { schema := budgetedCausalPrefixSchema
        fuel
        searchFuel
        term := encodeTerm term })
    · rfl
    · exact decodeTerm_encodeTerm term
    · simp [boundedBudgetedCausalPrefix, supported, execution, initial]

end CostWire

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
