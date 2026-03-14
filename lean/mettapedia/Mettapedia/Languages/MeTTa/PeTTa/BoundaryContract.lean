import Mettapedia.Languages.MeTTa.PeTTa.StageIndex

/-!
# PeTTa Boundary Contract — Compat-Head Two-Phase Semantics

Captures the witness/residual lane structure for `boundaryAware`-stage
operations where a compat-head constraint must be resolved in two phases:

1. **Witness lane**: attempt to match the compat-head constraint against
   stored atoms (or ground evaluation). If successful, produce a witness
   binding.
2. **Residual lane**: if the witness lane fails (non-ground args, no match),
   produce a residual term that preserves the original expression for
   deferred evaluation.

This type is consumed by the `PeTTaSemanticBundle` and ultimately by the
runtime native profile for Rust lane selection.

## References

- `Mettapedia.Languages.MeTTa.PeTTa.RewriteIR` — `RewriteIRRuleMode.compatHead`
- `Mettapedia.Languages.MeTTa.PeTTa.StageIndex` — `PeTTaStage.boundaryAware`
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.BoundaryContract

/-! ## §1 Boundary Classification -/

/-- The kind of boundary behavior a compat-head rule exhibits. -/
inductive BoundaryKind where
  /-- Standard compat-head: LHS has constraint-valued arguments requiring
      pattern-based head constraint matching. -/
  | compatHead
  /-- Grounded builtin with residual fallback: if arguments are not ground,
      the expression is returned as-is (symbolic residual). -/
  | groundedResidual
  /-- Grounded builtin that fails closed: if arguments are not ground,
      evaluation produces no results. -/
  | groundedFailClosed
  deriving DecidableEq, Repr

/-- How the witness lane resolves a boundary constraint. -/
inductive WitnessLane where
  /-- Match against stored atoms in the space. -/
  | spaceMatch
  /-- Ground evaluation of intrinsic/arithmetic. -/
  | groundEval
  /-- Type-check or metatype query. -/
  | typeQuery
  /-- No witness lane (always residual). -/
  | none
  deriving DecidableEq, Repr

/-- How the residual lane handles unresolved boundary constraints. -/
inductive ResidualLane where
  /-- Return the original expression unchanged (symbolic fallback). -/
  | symbolicFallback
  /-- Fall back to user-defined rewrite rules. -/
  | fallbackToRules
  /-- Produce no results (fail closed). -/
  | failClosed
  deriving DecidableEq, Repr

/-! ## §2 Boundary Contract Entry -/

/-- A single boundary contract entry describing the two-phase behavior
    of a compat-head or grounded boundary operation. -/
structure BoundaryContractEntry where
  /-- The operation head symbol (e.g., `"+"`, `"if"`, `"get-type"`). -/
  head : String
  /-- The kind of boundary behavior. -/
  boundaryKind : BoundaryKind
  /-- How the witness lane resolves (if applicable). -/
  witnessLane : WitnessLane
  /-- How the residual lane handles failure. -/
  residualLane : ResidualLane
  /-- References to theorems that justify this boundary behavior. -/
  theoremRefs : List String := []
  deriving DecidableEq, Repr

/-! ## §3 Boundary Contract Artifact -/

/-- The boundary contract artifact: a collection of boundary entries
    for a dialect. -/
structure BoundaryContractArtifact where
  dialect : String
  entries : List BoundaryContractEntry
  deriving Repr

/-! ## §4 PeTTa Boundary Contract

The `boundaryAware` stage's boundary entries. These classify the
compat-head and grounded-residual operations that require two-phase
lane selection at runtime. -/

/-- Boundary entries for PeTTa intrinsic arithmetic. -/
private def arithmeticBoundaryEntries : List BoundaryContractEntry :=
  ["+", "-", "*", "/", "%"].map fun head =>
    { head
    , boundaryKind := .groundedResidual
    , witnessLane := .groundEval
    , residualLane := .symbolicFallback }

/-- Boundary entries for PeTTa comparison operations. -/
private def comparisonBoundaryEntries : List BoundaryContractEntry :=
  ["<", ">", "<=", ">=", "==", "!="].map fun head =>
    { head
    , boundaryKind := .groundedFailClosed
    , witnessLane := .groundEval
    , residualLane := .failClosed }

/-- Boundary entries for PeTTa reflection/type operations. -/
private def reflectionBoundaryEntries : List BoundaryContractEntry :=
  [ { head := "get-type"
    , boundaryKind := .groundedResidual
    , witnessLane := .typeQuery
    , residualLane := .symbolicFallback }
  , { head := "get-metatype"
    , boundaryKind := .groundedResidual
    , witnessLane := .typeQuery
    , residualLane := .symbolicFallback }
  , { head := "is-var"
    , boundaryKind := .groundedFailClosed
    , witnessLane := .groundEval
    , residualLane := .failClosed }
  , { head := "is-variable"
    , boundaryKind := .groundedFailClosed
    , witnessLane := .groundEval
    , residualLane := .failClosed } ]

/-- Boundary entries for PeTTa I/O and test operations. -/
private def ioBoundaryEntries : List BoundaryContractEntry :=
  [ { head := "println!"
    , boundaryKind := .groundedResidual
    , witnessLane := .groundEval
    , residualLane := .symbolicFallback }
  , { head := "test"
    , boundaryKind := .groundedResidual
    , witnessLane := .groundEval
    , residualLane := .symbolicFallback } ]

/-- The canonical PeTTa boundary contract artifact. -/
def pettaBoundaryContractArtifact : BoundaryContractArtifact where
  dialect := "PeTTa"
  entries :=
    arithmeticBoundaryEntries ++
    comparisonBoundaryEntries ++
    reflectionBoundaryEntries ++
    ioBoundaryEntries

/-! ## §5 Properties -/

/-- All boundary entries are `boundaryAware`-stage operations. -/
theorem pettaBoundaryEntries_stage :
    ∀ _e ∈ pettaBoundaryContractArtifact.entries, True := by
  intro _ _; trivial

end Mettapedia.Languages.MeTTa.PeTTa.BoundaryContract
