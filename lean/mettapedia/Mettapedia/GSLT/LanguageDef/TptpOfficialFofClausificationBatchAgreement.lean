import Mettapedia.GSLT.LanguageDef.TptpOfficialRoleSemantics
import Mettapedia.GSLT.LanguageDef.TptpOfficialFofClausificationPipelineAgreement
import Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchGenerationAgreement

/-!
# Source-linked official FOF clausification batches

This module joins the official semantic document to formula-level
clausification without copying document metadata into the CNF carrier.  The
official source retains formula name, role, annotations, occurrence and span.
The generated batch carries only a decoded occurrence key, an explicit
clausification polarity, the two fresh-symbol ledgers and ordered local clause
identities.

The source link and the batch input are deliberately separate structures.
Consequently batch generation cannot inspect or rewrite a formula name,
annotation or source span; it receives only the semantic data needed for the
clausification arrow.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialFofClausificationBatchAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

namespace Official

abbrev AnnotatedInputView := TptpOfficialSemanticCarrier.AnnotatedInputView
abbrev DerivationNodeView := TptpOfficialDerivationSyntax.DerivationNodeView
abbrev FormulaRole := TptpOfficialRoleSemantics.FormulaRole
abbrev PipelineInput := TptpOfficialFofClausificationPipelineAgreement.PreparedInput

end Official


namespace Batch

abbrev SourceOccurrence :=
  TptpFofClausificationBatchLanguageDef.SourceOccurrence

end Batch


private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

/-! ## Exact bridge from official occurrence identities -/

def decodeSourceOccurrence? : Pattern → Option Batch.SourceOccurrence
  | .apply "tptp-semantic:occurrence-id" [
      .apply "tptp-semantic:source-digest" [.apply digest []],
      .apply indexLexeme []] =>
      some ⟨digest, indexLexeme⟩
  | _ => none

def encodeOfficialOccurrence (occurrence : Batch.SourceOccurrence) : Pattern :=
  a "tptp-semantic:occurrence-id" [
    a "tptp-semantic:source-digest" [a occurrence.sourceDigest],
    a occurrence.indexLexeme]

theorem decode_encodeOfficialOccurrence (occurrence : Batch.SourceOccurrence) :
    decodeSourceOccurrence? (encodeOfficialOccurrence occurrence) =
      some occurrence := by
  rfl

theorem encodeOfficialOccurrence_injective :
    Function.Injective encodeOfficialOccurrence := by
  intro left right equality
  have decoded := congrArg decodeSourceOccurrence? equality
  simpa only [decode_encodeOfficialOccurrence, Option.some.injEq] using decoded

/-! ## Role policy -/

/-- Polarity controls formula negation, not theorem status.  A conjecture is
negated before refutation; a `negated_conjecture` has already crossed that
boundary.  Type and interpretation records are not FOF clauses, and the
literal `unknown` role fails closed.  Assumption discharge remains a later
derivation-DAG obligation. -/
def rolePolarity? : Official.FormulaRole → Option Bool
  | .conjecture => some false
  | .type
  | .interpretation
  | .finiteInterpretationDomain
  | .finiteInterpretationFunctors
  | .finiteInterpretationPredicates
  | .unknown => none
  | _ => some true

/-! ## Source link and metadata-free batch input -/

structure PreparedSource where
  sourceInput : Official.AnnotatedInputView
  sourceNode : Official.DerivationNodeView
  sourceNodeExact :
    TptpOfficialDerivationSyntax.decodeDerivationNode? sourceInput =
      some sourceNode
  fofDialect : sourceNode.dialect = .fof
  occurrence : Batch.SourceOccurrence
  occurrenceExact :
    decodeSourceOccurrence? sourceNode.occurrence = some occurrence
  role : Official.FormulaRole
  roleExact :
    TptpOfficialRoleSemantics.decodeFormulaRole? sourceNode.role = some role
  polarity : Bool
  polarityExact : rolePolarity? role = some polarity
  pipeline : Official.PipelineInput
  pipelineFormulaExact : pipeline.official = sourceNode.formula

/-- This is the complete input visible to batch generation.  Official name,
role, annotation and span are intentionally absent. -/
structure BatchInput where
  occurrence : Batch.SourceOccurrence
  polarity : Bool
  pipeline : Official.PipelineInput
  namingFrontier : Nat

def PreparedSource.toBatchInput (source : PreparedSource)
    (namingFrontier : Nat) : BatchInput := {
  occurrence := source.occurrence
  polarity := source.polarity
  pipeline := source.pipeline
  namingFrontier
}

noncomputable def BatchInput.nnfFormula (input : BatchInput) :=
  TptpOfficialFofClausificationPipelineAgreement.nnfFormula
    input.pipeline input.polarity

noncomputable def BatchInput.skolemOutput (input : BatchInput) :=
  TptpFofClausificationPipelineAgreement.skolemOutput input.nnfFormula

noncomputable def BatchInput.namingEvidence (input : BatchInput) :=
  TptpFofClausificationPipelineAgreement.namingEvidence input.nnfFormula

noncomputable def BatchInput.namedOutput (input : BatchInput) :=
  TptpFofDefinitionalPipelineAgreement.namedOutput input.namingEvidence
    input.namingFrontier

noncomputable def BatchInput.definitionQuantifierFree (input : BatchInput) :=
  TptpFofDefinitionalPipelineAgreement.definitionQuantifierFree
    input.namingEvidence input.namingFrontier

noncomputable def BatchInput.encodedRequest (input : BatchInput) : Pattern :=
  TptpFofClausificationBatchGenerationLanguageDef.request
    (TptpFofClausificationBatchLanguageDef.encodeOccurrence input.occurrence)
    (TptpFofClausificationBatchLanguageDef.encodePolarity input.polarity)
    (TptpFofSkolemLanguageDef.encodeOutput input.skolemOutput
      input.namingEvidence.existentialFree)
    (TptpFofDefinitionalCnfLanguageDef.encodeCnfOutput input.namedOutput
      input.definitionQuantifierFree)

noncomputable def BatchInput.encodedOutput (input : BatchInput) : Pattern :=
  TptpFofClausificationBatchLanguageDef.encodeOutput input.occurrence
    input.polarity input.skolemOutput input.namingEvidence.existentialFree
    input.namedOutput input.definitionQuantifierFree

noncomputable def BatchInput.derivation (input : BatchInput) :
    TptpFofClausificationBatchGenerationAgreement.Derivation
      input.encodedRequest input.encodedOutput :=
  TptpFofClausificationBatchGenerationAgreement.outputDerivation
    input.occurrence input.polarity input.skolemOutput
    input.namingEvidence.existentialFree input.namedOutput
    input.definitionQuantifierFree

/-- The eighth authored arrow, from the final definitional CNF payload to one
source-indexed batch, has an exact singleton result. -/
theorem BatchInput.rewriteAt_exact (input : BatchInput) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofClausificationBatchGenerationLanguageDef.language
      input.derivation.height input.encodedRequest = [input.encodedOutput] := by
  exact input.derivation.rewriteAt_exact _ (by rfl)

theorem BatchInput.no_invention (input : BatchInput) (candidate : Pattern)
    (membership : candidate ∈ rewriteAt
      (engineBasePremises RelationEnv.empty)
      TptpFofClausificationBatchGenerationLanguageDef.language
      input.derivation.height input.encodedRequest) :
    candidate = input.encodedOutput :=
  input.derivation.no_invention _ (by rfl) membership

/-- The source-linked batch has exactly the same independent satisfiability
statement as the seven formula-level stages. -/
theorem PreparedSource.polarizedSatisfiable_iff_batchCnfSatisfiable
    (source : PreparedSource) (namingFrontier : Nat) :
    TptpOfficialFofClausificationPipelineAgreement.PolarizedResolvedSatisfiable
        source.pipeline.resolved source.polarity ↔
      TptpFofDefinitionalCnfSemantics.Satisfiable
        (source.toBatchInput namingFrontier).namedOutput := by
  exact
    TptpOfficialFofClausificationPipelineAgreement.polarizedResolvedSatisfiable_iff_pipelineCnfSatisfiable
      source.pipeline source.polarity namingFrontier

/-! ## Positive and negative controls -/

namespace Canary

def occurrence : Batch.SourceOccurrence := ⟨"sha256-source", "0"⟩

noncomputable def sourceNode (role : Pattern) : Official.DerivationNodeView := {
  occurrence := encodeOfficialOccurrence occurrence
  dialect := .fof
  name := a "formula-name"
  role
  formula :=
    TptpOfficialFofClausificationPipelineAgreement.Canary.truthInput.official
  annotation := .absent
  span := a "source-span"
}

noncomputable def sourceInput (role : Pattern) : Official.AnnotatedInputView :=
  TptpOfficialDerivationSyntax.encodeDerivationNode (sourceNode role)

noncomputable def preparedAxiom : PreparedSource where
  sourceInput := sourceInput (TptpOfficialRoleSemantics.Canary.role "axiom")
  sourceNode := sourceNode (TptpOfficialRoleSemantics.Canary.role "axiom")
  sourceNodeExact := by
    exact TptpOfficialDerivationSyntax.decode_encode_derivation_node _ trivial
  fofDialect := rfl
  occurrence := occurrence
  occurrenceExact := rfl
  role := .axiom
  roleExact := rfl
  polarity := true
  polarityExact := rfl
  pipeline :=
    TptpOfficialFofClausificationPipelineAgreement.Canary.truthInput
  pipelineFormulaExact := rfl

noncomputable def preparedConjecture : PreparedSource where
  sourceInput := sourceInput
    (TptpOfficialRoleSemantics.Canary.role "conjecture")
  sourceNode := sourceNode
    (TptpOfficialRoleSemantics.Canary.role "conjecture")
  sourceNodeExact := by
    exact TptpOfficialDerivationSyntax.decode_encode_derivation_node _ trivial
  fofDialect := rfl
  occurrence := occurrence
  occurrenceExact := rfl
  role := .conjecture
  roleExact := rfl
  polarity := false
  polarityExact := rfl
  pipeline :=
    TptpOfficialFofClausificationPipelineAgreement.Canary.truthInput
  pipelineFormulaExact := rfl

theorem axiom_is_positive : rolePolarity? .axiom = some true := by rfl

theorem conjecture_is_negated : rolePolarity? .conjecture = some false := by rfl

theorem negated_conjecture_is_already_positive :
    rolePolarity? .negatedConjecture = some true := by rfl

theorem unknown_role_fails_closed : rolePolarity? .unknown = none := by rfl

theorem malformed_occurrence_fails_closed :
    decodeSourceOccurrence?
      (a "tptp-semantic:occurrence-id" [a "missing-digest", a "0"]) =
        none := by
  rfl

theorem role_policy_changes_the_batch_polarity :
    TptpFofClausificationBatchLanguageDef.encodePolarity
        (preparedAxiom.toBatchInput 0).polarity ≠
      TptpFofClausificationBatchLanguageDef.encodePolarity
        (preparedConjecture.toBatchInput 0).polarity := by
  exact TptpFofClausificationBatchLanguageDef.Canary.polarity_is_load_bearing

end Canary

#print axioms decode_encodeOfficialOccurrence
#print axioms encodeOfficialOccurrence_injective
#print axioms BatchInput.rewriteAt_exact
#print axioms BatchInput.no_invention
#print axioms PreparedSource.polarizedSatisfiable_iff_batchCnfSatisfiable
#print axioms Canary.role_policy_changes_the_batch_polarity
#print axioms Canary.malformed_occurrence_fails_closed

end Mettapedia.GSLT.LanguageDef.TptpOfficialFofClausificationBatchAgreement
