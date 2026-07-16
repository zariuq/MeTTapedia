import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.Encoding

/-!
# Executable cost-rho conformance boundary

The request and outcome types below are the versioned JSON boundary used by
bounded differential tests.  Evaluation first decodes the wire term and then
runs the independent raw-syntax causal-prefix machine.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

namespace CostWire

/-- Version tag for the executable causal-prefix exchange format. -/
def causalPrefixSchema : String := "cetta.cost-rho.causal-prefix.v1"

/-- One bounded request at the CeTTa/Lean conformance boundary. -/
structure PrefixRequest where
  schema : String
  fuel : Nat
  term : CostWire
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- Explicit outcomes keep schema, wire-shape, and cost-grammar failures
distinct from successful quiescent or fuel-exhausted prefixes. -/
inductive PrefixOutcome where
  | schemaMismatch
  | malformedWire
  | malformedTerm
  | result : CostWire → PrefixOutcome
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- Decode and execute one bounded request through the independent raw model. -/
def evaluatePrefix (request : PrefixRequest) : PrefixOutcome :=
  if request.schema != causalPrefixSchema then .schemaMismatch
  else
    match decodeTerm request.term with
    | none => .malformedWire
    | some term =>
        match boundedCausalPrefix request.fuel term with
        | none => .malformedTerm
        | some execution => .result (encodePrefix execution)

theorem evaluatePrefix_of_decoded
    {request : PrefixRequest} {term : RawCostTerm} {execution : RawCausalPrefix}
    (schema_ok : request.schema = causalPrefixSchema)
    (decoded : decodeTerm request.term = some term)
    (executed : boundedCausalPrefix request.fuel term = some execution) :
    evaluatePrefix request = .result (encodePrefix execution) := by
  simp [evaluatePrefix, schema_ok, decoded, executed]

/-- Every well-formed raw term has a successful bounded JSON-boundary result;
the prefix status itself still distinguishes quiescence from fuel exhaustion. -/
theorem evaluatePrefix_encodeTerm_exists (fuel : Nat) (term : RawCostTerm)
    (supported : term.wellFormed = true) :
    ∃ execution,
      boundedCausalPrefix fuel term = some execution ∧
      evaluatePrefix
          { schema := causalPrefixSchema
            fuel
            term := encodeTerm term } =
        .result (encodePrefix execution) := by
  let initial : List RawTraceComponent :=
    term.normalizeConfig.map fun component =>
      { term := component, producer := none }
  let execution := runCausalPrefix fuel 0 initial []
  refine ⟨execution, ?_, ?_⟩
  · simp [boundedCausalPrefix, supported, execution, initial]
  · apply evaluatePrefix_of_decoded (request :=
      { schema := causalPrefixSchema, fuel, term := encodeTerm term })
    · rfl
    · exact decodeTerm_encodeTerm term
    · simp [boundedCausalPrefix, supported, execution, initial]

end CostWire

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
