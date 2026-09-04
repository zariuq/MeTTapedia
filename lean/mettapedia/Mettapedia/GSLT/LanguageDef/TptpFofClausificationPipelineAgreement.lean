import Mettapedia.GSLT.LanguageDef.TptpFofPrenexNormalizationLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemanticAgreement
import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalPipelineAgreement

/-!
# Exact authored FOF clausification pipeline

This module composes four independently specified authored transformations:
prenex normalization, Skolemization, definitional naming, and definitional CNF
generation.  The composition retains every operational derivation and proves
the typed boundaries between adjacent stages.  In particular, it constructs
the all-only prefix evidence required by naming from the actual Skolem
traversal; it does not assume that an existential-free result is automatically
in the image of the naming stage.

The input here is canonical closed NNF.  Official TPTP syntax, role changes,
formula identities, and provenance belong to the surrounding document-level
transformation and are not invented by this formula-level pipeline.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofClausificationPipelineAgreement

open LO FirstOrder
open scoped LO.FirstOrder
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-! ## Typed Skolem-to-naming boundary -/

/-- The actual Skolem traversal of a prenex object has exactly the universal
prefix shape required by definitional naming.  Existentials are removed and
universals remain binders. -/
noncomputable def skolemizePrenex_universalPrefix
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> TptpFofSkolemizationSemantics.Term targetDepth) :
    (form : TptpFofPrenexSemantics.PrenexForm sourceDepth) -> (frontier : Nat) ->
      TptpFofDefinitionalNamingSemantics.UniversalPrefix
        (TptpFofSkolemizationSemantics.skolemizeFrom environment form.toFormula frontier).formula
  | .matrix formula free, frontier =>
      .matrix
        (TptpFofDefinitionalNamingSemantics.skolemizeFrom_quantifierFree
          environment formula free frontier)
  | .all body, frontier => by
      simpa [TptpFofPrenexSemantics.PrenexForm.toFormula,
        TptpFofSkolemizationSemantics.skolemizeFrom] using
          TptpFofDefinitionalNamingSemantics.UniversalPrefix.all
            (skolemizePrenex_universalPrefix
              (TptpFofSkolemizationSemantics.underUniversal environment)
              body frontier)
  | .ex body, frontier => by
      simpa [TptpFofPrenexSemantics.PrenexForm.toFormula,
        TptpFofSkolemizationSemantics.skolemizeFrom] using
          skolemizePrenex_universalPrefix
            (TptpFofSkolemizationSemantics.underExistential environment frontier)
            body (frontier + 1)

theorem skolemizePrenex_openUniversals_exact
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> TptpFofSkolemizationSemantics.Term targetDepth)
    (form : TptpFofPrenexSemantics.PrenexForm sourceDepth) (frontier : Nat) :
    TptpFofDefinitionalNamingSemantics.openUniversals?
        (TptpFofSkolemizationSemantics.skolemizeFrom environment form.toFormula frontier).formula =
      some (skolemizePrenex_universalPrefix environment form frontier).opened :=
  TptpFofDefinitionalNamingSemantics.UniversalPrefix.openUniversals?_exact
    (skolemizePrenex_universalPrefix environment form frontier)

/-! ## Canonical closed pipeline -/

abbrev SourceFormula := TptpFofPrenexSemantics.Formula 0

noncomputable def prenexForm (source : SourceFormula) : TptpFofPrenexSemantics.PrenexForm 0 :=
  TptpFofPrenexSemantics.prenex source

noncomputable def skolemOutput (source : SourceFormula) : TptpFofSkolemizationSemantics.Output 0 :=
  TptpFofSkolemizationSemantics.skolemizeFrom Fin.elim0 (prenexForm source).toFormula 0

noncomputable def namingEvidence (source : SourceFormula) :
    TptpFofDefinitionalNamingSemantics.UniversalPrefix (skolemOutput source).formula :=
  skolemizePrenex_universalPrefix Fin.elim0 (prenexForm source) 0

noncomputable def prenexRequestPattern (source : SourceFormula) : Pattern :=
  TptpFofPrenexNormalizationLanguageDef.prenexRequest
    (TptpFofNnfLanguageDef.encodeFormula source)

noncomputable def prenexReceiptPattern (source : SourceFormula) : Pattern :=
  TptpFofPrenexNormalizationLanguageDef.prenexResult
    (TptpFofNnfLanguageDef.encodeFormula source)
    (TptpFofPrenexLanguageDef.encodePrenex (prenexForm source))

noncomputable def skolemRequestPattern (source : SourceFormula) : Pattern :=
  TptpFofSkolemizationLanguageDef.formRequest
    (TptpFofSkolemTermAgreement.Semantic.environmentPattern
      (Fin.elim0 : Fin 0 -> TptpFofSkolemizationSemantics.Term 0))
    (TptpResolvedFofLanguageDef.encodeNatIndex 0)
    (TptpResolvedFofLanguageDef.encodeNatIndex 0)
    (TptpFofPrenexLanguageDef.encodePrenex (prenexForm source))

noncomputable def skolemReceiptPattern (source : SourceFormula) : Pattern :=
  TptpFofSkolemizationSemanticAgreement.semanticResultPattern
    (Fin.elim0 : Fin 0 -> TptpFofSkolemizationSemantics.Term 0) (prenexForm source) 0

/-- The four real authored derivations.  No stage is replaced by its semantic
reference function inside this evidence object. -/
structure PipelineDerivation (source : SourceFormula)
    (namingFrontier : Nat) where
  prenex : TptpFofPrenexNormalizationLanguageDef.Derivation
    (prenexRequestPattern source) (prenexReceiptPattern source)
  skolem : TptpFofSkolemizationAgreement.Derivation
    (skolemRequestPattern source) (skolemReceiptPattern source)
  definitional : TptpFofDefinitionalPipelineAgreement.PipelineDerivation
    (namingEvidence source) namingFrontier

noncomputable def pipelineDerivation (source : SourceFormula)
    (namingFrontier : Nat) : PipelineDerivation source namingFrontier where
  prenex := TptpFofPrenexNormalizationLanguageDef.prenexDerivation source
  skolem := TptpFofSkolemizationSemanticAgreement.formDerivation
    (Fin.elim0 : Fin 0 -> TptpFofSkolemizationSemantics.Term 0) (prenexForm source) 0
  definitional := TptpFofDefinitionalPipelineAgreement.pipelineDerivation
    (namingEvidence source) namingFrontier

/-- The encoded prenex object produced by the first stage is literally the
prenex payload consumed by the second stage. -/
theorem prenex_skolem_payload_exact (source : SourceFormula) :
    TptpFofPrenexLanguageDef.encodePrenex (TptpFofPrenexSemantics.prenex source) =
      TptpFofPrenexLanguageDef.encodePrenex (prenexForm source) := rfl

/-- The formula payload produced by Skolemization is exactly the source
formula encoded for naming.  Proof arguments to the encoder cannot change the
wire pattern. -/
theorem skolem_naming_formula_payload_exact (source : SourceFormula) :
    TptpFofSkolemLanguageDef.encodeFormula (skolemOutput source).formula
        (TptpFofSkolemizationSemantics.skolemizeFrom_existentialFree
          (Fin.elim0 : Fin 0 -> TptpFofSkolemizationSemantics.Term 0)
          (prenexForm source).toFormula 0) =
      TptpFofSkolemLanguageDef.encodeFormula (skolemOutput source).formula
        (namingEvidence source).existentialFree := by
  rfl

/-- At depth zero, the Skolem stage's closed-form satisfiability judgment and
the naming stage's universally-closed source judgment are equivalent.  This
is stated explicitly because the two stages deliberately use different
definitions rather than sharing a convenient alias. -/
theorem skolemSatisfiable_iff_namingSourceSatisfiable
    (formula : TptpFofSkolemizationSemantics.Formula 0) :
    TptpFofSkolemizationSemantics.Satisfiable formula ↔
      TptpFofDefinitionalNamingSemantics.SourceSatisfiable formula := by
  constructor
  · rintro ⟨Domain, domainNonempty, model, satisfied⟩
    refine ⟨Domain, domainNonempty, model, fun values => ?_⟩
    simpa only [Subsingleton.elim values ![]] using satisfied
  · rintro ⟨Domain, domainNonempty, model, satisfied⟩
    exact ⟨Domain, domainNonempty, model, satisfied ![]⟩

/-- All four authored stages have exact singleton outcomes. -/
theorem rewriteAt_pipeline_exact (source : SourceFormula)
    (namingFrontier : Nat) :
    (rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofPrenexNormalizationLanguageDef.language
        (pipelineDerivation source namingFrontier).prenex.height
        (prenexRequestPattern source) = [prenexReceiptPattern source]) ∧
    (rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofSkolemizationLanguageDef.language
        (pipelineDerivation source namingFrontier).skolem.height
        (skolemRequestPattern source) = [skolemReceiptPattern source]) ∧
    (rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalNamingLanguageDef.language
        (pipelineDerivation source namingFrontier).definitional.naming.height
        (TptpFofDefinitionalPipelineAgreement.namingRequestPattern
          (namingEvidence source) namingFrontier) =
      [TptpFofDefinitionalPipelineAgreement.namingReceiptPattern
        (namingEvidence source) namingFrontier]) ∧
    (rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalCnfGenerationLanguageDef.language
        (pipelineDerivation source namingFrontier).definitional.cnf.height
        (TptpFofDefinitionalPipelineAgreement.cnfRequestPattern
          (namingEvidence source) namingFrontier) =
      [TptpFofDefinitionalPipelineAgreement.cnfReceiptPattern
        (namingEvidence source) namingFrontier]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact TptpFofPrenexNormalizationLanguageDef.prenex_rewriteAt_exact source _ (Nat.le_refl _)
  · exact TptpFofSkolemizationSemanticAgreement.rewriteAt_skolemizeFrom_exact
      (Fin.elim0 : Fin 0 -> TptpFofSkolemizationSemantics.Term 0) (prenexForm source) 0
  · exact (TptpFofDefinitionalPipelineAgreement.rewriteAt_pipeline_exact
      (namingEvidence source) namingFrontier).1
  · exact (TptpFofDefinitionalPipelineAgreement.rewriteAt_pipeline_exact
      (namingEvidence source) namingFrontier).2

/-- The final generated CNF is independently proved equisatisfiable with the
original closed NNF source. -/
theorem sourceSatisfiable_iff_pipelineCnfSatisfiable
    (source : SourceFormula) (namingFrontier : Nat) :
    TptpFofSkolemizationSemantics.SourceSatisfiable source ↔
      TptpFofDefinitionalCnfSemantics.Satisfiable
        (TptpFofDefinitionalPipelineAgreement.namedOutput (namingEvidence source) namingFrontier) := by
  have skolemToNaming :
      TptpFofSkolemizationSemantics.Satisfiable
          (TptpFofSkolemizationSemantics.prenexSkolemize source).formula ↔
        TptpFofDefinitionalNamingSemantics.SourceSatisfiable
          (skolemOutput source).formula := by
    simpa [skolemOutput, prenexForm,
      TptpFofSkolemizationSemantics.prenexSkolemize,
      TptpFofSkolemizationSemantics.skolemize,
      TptpFofPrenexSemantics.normalize] using
      skolemSatisfiable_iff_namingSourceSatisfiable
        (skolemOutput source).formula
  exact
    (TptpFofSkolemizationSemantics.sourceSatisfiable_iff_prenexSkolemSatisfiable source).trans
      (skolemToNaming.trans
        (TptpFofDefinitionalPipelineAgreement.sourceSatisfiable_iff_pipelineCnfSatisfiable
          (namingEvidence source) namingFrontier))

namespace Canary

abbrev source : SourceFormula := TptpFofPrenexSemantics.Canary.source

theorem source_requires_prenex_normalization :
    ¬ TptpFofPrenexSemantics.Prenex source :=
  TptpFofPrenexSemantics.Canary.source_not_prenex

theorem composed_source_has_four_exact_singleton_stages :
    (rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofPrenexNormalizationLanguageDef.language
        (pipelineDerivation source 0).prenex.height
        (prenexRequestPattern source)).length = 1 ∧
    (rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofSkolemizationLanguageDef.language
        (pipelineDerivation source 0).skolem.height
        (skolemRequestPattern source)).length = 1 ∧
    (rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalNamingLanguageDef.language
        (pipelineDerivation source 0).definitional.naming.height
        (TptpFofDefinitionalPipelineAgreement.namingRequestPattern (namingEvidence source) 0)).length = 1 ∧
    (rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalCnfGenerationLanguageDef.language
        (pipelineDerivation source 0).definitional.cnf.height
        (TptpFofDefinitionalPipelineAgreement.cnfRequestPattern (namingEvidence source) 0)).length = 1 := by
  rw [(rewriteAt_pipeline_exact source 0).1,
    (rewriteAt_pipeline_exact source 0).2.1,
    (rewriteAt_pipeline_exact source 0).2.2.1,
    (rewriteAt_pipeline_exact source 0).2.2.2]
  simp

/-- Skipping Skolemization is observably invalid: the source contains an
existential and therefore cannot cross the naming boundary directly. -/
theorem unskolemized_source_is_rejected_by_naming :
    TptpFofDefinitionalNamingSemantics.openUniversals?
      (.ex (.verum : TptpFofDefinitionalNamingSemantics.Source.Formula 1)) = none := by
  rfl

end Canary

#print axioms skolemizePrenex_openUniversals_exact
#print axioms prenex_skolem_payload_exact
#print axioms skolem_naming_formula_payload_exact
#print axioms skolemSatisfiable_iff_namingSourceSatisfiable
#print axioms rewriteAt_pipeline_exact
#print axioms sourceSatisfiable_iff_pipelineCnfSatisfiable
#print axioms Canary.source_requires_prenex_normalization
#print axioms Canary.composed_source_has_four_exact_singleton_stages

end Mettapedia.GSLT.LanguageDef.TptpFofClausificationPipelineAgreement
