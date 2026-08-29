import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationProgram
import Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedService

/-!
# Generic official-TSTP projection into status-indexed derivation programs

This module owns the format-generic part of the projection from admitted
official TSTP nodes to `DerivationCheckMachine` instructions.  It constructs
semantic formula occurrences from the official role and metadata, preserving
the exact calculus metadata as `OfficialEvidence`.

A guest projection decodes only the dialect formula, problem provenance,
calculus rule/evidence, and root obligation.  Unsupported dialects or rules
remain incomplete; malformed official inference metadata is distinguished
from unsupported semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedProjection

open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationProgram
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialPrincipalSymbols
open Mettapedia.GSLT.LanguageDef.TptpOfficialRoleSemantics
open Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedService
open Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo

variable {Formula Rule Evidence Provenance Obligation : Type}

/-- The dialect/calculus boundary.  Its functions consume admitted nodes and
the already decoded official metadata; it cannot replace official graph or
metadata parsing with a parallel private representation. -/
structure GuestProjection
    (Formula Rule Evidence Provenance Obligation : Type) where
  formula? : AdmittedNode -> Except ProjectionFailure Formula
  inputProvenance? : AdmittedNode -> SemanticNode Formula ->
    Except ProjectionFailure Provenance
  rule? : String -> AdmittedNode -> RuleMetadata -> Except ProjectionFailure Rule
  evidence? : String -> AdmittedNode -> RuleMetadata ->
    Except ProjectionFailure Evidence
  root? : AdmittedNode -> SemanticNode Formula ->
    Except ProjectionFailure Obligation

def role? (node : AdmittedNode) : Except ProjectionFailure FormulaRole :=
  match decodeFormulaRole? node.source.termView.role with
  | some role => .ok role
  | none => .error .unsupported

structure InferenceView where
  ruleName : String
  metadata : RuleMetadata

/-- Only genuine official `inference(...)` sources carry a rule-indexed
status service at this layer.  Named copies, introduced leaves, and source
alternatives require their own declared calculus services and therefore
remain unsupported rather than being guessed. -/
def inferenceView? (node : AdmittedNode) :
    Except ProjectionFailure InferenceView :=
  match node.source.origin with
  | .sourced _ (.inference rule usefulInfo _) _ =>
      match decodeInferenceRule? rule with
      | none => .error .malformed
      | some ruleName =>
          match decodeRuleMetadata? ruleName usefulInfo with
          | none => .error .malformed
          | some metadata => .ok { ruleName, metadata }
  | _ => .error .unsupported

def semanticNode? (guest : GuestProjection Formula Rule Evidence Provenance Obligation)
    (node : AdmittedNode) : Except ProjectionFailure (SemanticNode Formula) := do
  let role <- role? node
  let body <- guest.formula? node
  let principalSymbols <- match principalSymbolSet? node.source.termView.formula with
    | none => .error .malformed
    | some symbols => .ok symbols
  match structuralMode node.source.origin with
  | .input =>
      let provisional : SemanticNode Formula := {
        name := node.source.name
        role
        origin := .input
        body
        principalSymbols
        openAssumptions := ∅
      }
      .ok { provisional with
        openAssumptions := expectedInputAssumptions provisional }
  | .infer =>
      let inference <- inferenceView? node
      let normalized <- match normalizeMetadata? inference.metadata with
        | none => .error .malformed
        | some normalized => .ok normalized
      .ok {
        name := node.source.name
        role
        origin := .inferred normalized.status
        body
        principalSymbols
        openAssumptions := normalized.declaredAssumptions
      }

def input? (guest : GuestProjection Formula Rule Evidence Provenance Obligation)
    (node : AdmittedNode) : Except ProjectionFailure
      (SemanticNode Formula × Provenance) := do
  if structuralMode node.source.origin != .input then
    .error .malformed
  let formula <- semanticNode? guest node
  let provenance <- guest.inputProvenance? node formula
  .ok (formula, provenance)

def infer? (guest : GuestProjection Formula Rule Evidence Provenance Obligation)
    (node : AdmittedNode) : Except ProjectionFailure
      (Rule × OfficialEvidence Evidence × SemanticNode Formula) := do
  if structuralMode node.source.origin != .infer then
    .error .malformed
  let inference <- inferenceView? node
  let formula <- semanticNode? guest node
  let rule <- guest.rule? inference.ruleName node inference.metadata
  let evidence <- guest.evidence? inference.ruleName node inference.metadata
  .ok (rule, { metadata := inference.metadata, calculus := evidence }, formula)

def root? (guest : GuestProjection Formula Rule Evidence Provenance Obligation)
    (node : AdmittedNode) : Except ProjectionFailure Obligation := do
  let formula <- semanticNode? guest node
  guest.root? node formula

def projection
    (guest : GuestProjection Formula Rule Evidence Provenance Obligation) :
    TargetProjection (SemanticNode Formula) Rule (OfficialEvidence Evidence)
      Provenance Obligation where
  input? := input? guest
  infer? := infer? guest
  root? := root? guest

/-! ## Source-derived initial vocabulary -/

/-- Collect the principal-symbol signature of the admitted input problem.
Inference conclusions do not contribute to the initial signature: any symbol
first appearing there must be justified by official `new_symbols` metadata.
The traversal reuses `semanticNode?`, so malformed roles, formula ASTs, or
guest formula projections fail through the same boundary as compilation. -/
def collectInputPrincipalSymbols?
    (guest : GuestProjection Formula Rule Evidence Provenance Obligation) :
    List AdmittedNode -> Except ProjectionFailure (Finset PrincipalSymbolId)
  | [] => .ok ∅
  | node :: nodes => do
      let rest <- collectInputPrincipalSymbols? guest nodes
      match structuralMode node.source.origin with
      | .infer => .ok rest
      | .input =>
          let formula <- semanticNode? guest node
          .ok (formula.principalSymbols ∪ rest)

end Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedProjection
