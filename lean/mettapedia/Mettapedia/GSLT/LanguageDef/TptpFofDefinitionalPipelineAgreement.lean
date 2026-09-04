import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfGenerationSemanticAgreement

/-!
# Exact composition of authored definitional naming and CNF generation

This module retains the two authored operational derivations and identifies
their shared boundary with one typed named output.  The final theorem combines
their exact singleton executions with the independent satisfiability theorem;
it does not replace either stage with a direct semantic calculation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalPipelineAgreement

open LO FirstOrder
open scoped LO.FirstOrder
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open TptpFofDefinitionalNamingSemantics
open TptpFofDefinitionalNamingLanguageDef
open TptpFofDefinitionalCnfGenerationLanguageDef

abbrev NamingDerivation :=
  TptpFofDefinitionalNamingAgreement.Derivation

abbrev CnfDerivation :=
  TptpFofDefinitionalCnfGenerationAgreement.Derivation

noncomputable def namedOutput {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) : Output evidence.opened.depth :=
  nameFrom evidence.opened.formula evidence.opened.quantifierFree frontier

noncomputable def definitionQuantifierFree {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) :
    ∀ definition ∈ (namedOutput evidence frontier).definitions,
      QuantifierFree definition.source :=
  nameFrom_definition_sources_quantifierFree evidence.opened.formula
    evidence.opened.quantifierFree frontier

noncomputable def ledgerAlignment {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) :
    TptpFofDefinitionalCnfGenerationSemanticAgreement.Semantic.LedgerAlignment
      evidence.opened.depth
      (namedOutput evidence frontier).definitions
      (namedOutput evidence frontier).introduced :=
  TptpFofDefinitionalCnfGenerationSemanticAgreement.Semantic.nameFrom_ledgerAlignment
    evidence.opened.formula evidence.opened.quantifierFree frontier

noncomputable def namingRequestPattern {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) : Pattern :=
  openRequest
    (TptpResolvedFofLanguageDef.encodeNatIndex depth)
    (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
    (TptpFofSkolemLanguageDef.encodeFormula source evidence.existentialFree)

noncomputable def namedPattern {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) : Pattern :=
  TptpFofDefinitionalCnfLanguageDef.encodeNamedOutput
    (namedOutput evidence frontier)
    (definitionQuantifierFree evidence frontier)

noncomputable def namingReceiptPattern {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) : Pattern :=
  openResult
    (TptpResolvedFofLanguageDef.encodeNatIndex depth)
    (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
    (TptpFofSkolemLanguageDef.encodeFormula source evidence.existentialFree)
    (namedPattern evidence frontier)

noncomputable def cnfPattern {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) : Pattern :=
  TptpFofDefinitionalCnfLanguageDef.encodeCnfOutput
    (namedOutput evidence frontier)
    (definitionQuantifierFree evidence frontier)

noncomputable def cnfRequestPattern {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) : Pattern :=
  generateRequest (namedPattern evidence frontier)

noncomputable def cnfReceiptPattern {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) : Pattern :=
  generateResult (namedPattern evidence frontier) (cnfPattern evidence frontier)

/-- The two operational arrows, sharing the exact encoded named output rather
than merely agreeing on a final example. -/
structure PipelineDerivation {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) where
  naming : NamingDerivation
    (namingRequestPattern evidence frontier)
    (namingReceiptPattern evidence frontier)
  cnf : CnfDerivation
    (cnfRequestPattern evidence frontier)
    (cnfReceiptPattern evidence frontier)

noncomputable def pipelineDerivation {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) : PipelineDerivation evidence frontier where
  naming := by
    simpa [namingRequestPattern, namingReceiptPattern, namedPattern,
      namedOutput, definitionQuantifierFree,
      TptpFofDefinitionalCnfLanguageDef.encodeNameFrom] using
      TptpFofDefinitionalNamingSemanticAgreement.Operational.universalDerivation
        evidence frontier
  cnf := by
    exact
      TptpFofDefinitionalCnfGenerationSemanticAgreement.Semantic.generateDerivation
        (namedOutput evidence frontier) (ledgerAlignment evidence frontier)
        (definitionQuantifierFree evidence frontier)

/-- Both authored stages execute to one exact target, in order, with the named
payload of the first stage definitionally identical to the input of the second. -/
theorem rewriteAt_pipeline_exact {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) :
    (rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalNamingLanguageDef.language
        (pipelineDerivation evidence frontier).naming.height
        (namingRequestPattern evidence frontier) =
      [namingReceiptPattern evidence frontier]) ∧
    (rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalCnfGenerationLanguageDef.language
        (pipelineDerivation evidence frontier).cnf.height
        (cnfRequestPattern evidence frontier) =
      [cnfReceiptPattern evidence frontier]) := by
  constructor
  · exact
      TptpFofDefinitionalNamingAgreement.Derivation.rewriteAt_exact
        (pipelineDerivation evidence frontier).naming _ (Nat.le_refl _)
  · exact
      TptpFofDefinitionalCnfGenerationAgreement.Derivation.rewriteAt_exact
        (pipelineDerivation evidence frontier).cnf _ (Nat.le_refl _)

theorem naming_no_invention {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) (invented : Pattern)
    (membership : invented ∈ rewriteAt
      (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalNamingLanguageDef.language
      (pipelineDerivation evidence frontier).naming.height
      (namingRequestPattern evidence frontier)) :
    invented = namingReceiptPattern evidence frontier :=
  TptpFofDefinitionalNamingAgreement.Derivation.no_invention
    (pipelineDerivation evidence frontier).naming _ (Nat.le_refl _) membership

theorem cnf_no_invention {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) (invented : Pattern)
    (membership : invented ∈ rewriteAt
      (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language
      (pipelineDerivation evidence frontier).cnf.height
      (cnfRequestPattern evidence frontier)) :
    invented = cnfReceiptPattern evidence frontier :=
  TptpFofDefinitionalCnfGenerationAgreement.Derivation.no_invention
    (pipelineDerivation evidence frontier).cnf _ (Nat.le_refl _) membership

/-- The operationally generated CNF is the independently proved
equisatisfiable output for the original universally closed source. -/
theorem sourceSatisfiable_iff_pipelineCnfSatisfiable {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) :
    SourceSatisfiable source ↔
      TptpFofDefinitionalCnfSemantics.Satisfiable
        (namedOutput evidence frontier) :=
  TptpFofDefinitionalCnfSemantics.universallyClosedSourceSatisfiable_iff_cnfSatisfiable
    source evidence.opened evidence.openUniversals?_exact frontier

namespace Canary

open TptpFofDefinitionalNamingSemanticAgreement.Operational.Canary

theorem universal_pipeline_has_exactly_one_result_per_stage :
    (rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalNamingLanguageDef.language
        (pipelineDerivation universalEvidence 7).naming.height
        (namingRequestPattern universalEvidence 7)).length = 1 ∧
    (rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalCnfGenerationLanguageDef.language
        (pipelineDerivation universalEvidence 7).cnf.height
        (cnfRequestPattern universalEvidence 7)).length = 1 := by
  rw [(rewriteAt_pipeline_exact universalEvidence 7).1,
    (rewriteAt_pipeline_exact universalEvidence 7).2]
  simp

/-- An unmatched introduction cannot cross the shared boundary by pretending
to be an output of naming. -/
theorem extra_introduced_row_is_rejected
    (root id arity : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
      (clausesRequest root TptpFofDefinitionalCnfLanguageDef.definitionsNil
        (TptpFofDefinitionalCnfLanguageDef.introducedCons
          (TptpFofDefinitionalCnfLanguageDef.introducedPredicate id arity)
          TptpFofDefinitionalCnfLanguageDef.introducedNil)) = [] :=
  TptpFofDefinitionalCnfGenerationAgreement.mismatched_empty_ledgers_have_no_reduct
    root id arity fuel

end Canary

#print axioms rewriteAt_pipeline_exact
#print axioms naming_no_invention
#print axioms cnf_no_invention
#print axioms sourceSatisfiable_iff_pipelineCnfSatisfiable
#print axioms Canary.extra_introduced_row_is_rejected

end Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalPipelineAgreement
