import Mettapedia.GSLT.LanguageDef.TptpNamedFofToNnfAgreement
import Mettapedia.GSLT.LanguageDef.TptpFofClausificationPipelineAgreement

/-!
# Official TPTP FOF through authored clausification

This module connects the official grammar-shaped FOF carrier to the complete
formula-level clausification pipeline.  A prepared input contains independent
evidence that the official decoder accepts the source and that binder
resolution succeeds.  From that evidence we retain seven actual authored
LanguageDef executions:

* official FOF AST to named FOF;
* named FOF to binder-resolved FOF;
* binder-resolved FOF to canonical NNF;
* prenex normalization;
* Skolemization;
* definitional naming; and
* definitional CNF generation.

The semantic theorem begins at the binder-resolved formula because source
metadata and TPTP's document-level role policy are separate concerns.  Free
variables are not silently reinterpreted here: a source enters this pipeline
only when the existing closed binder resolver succeeds.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialFofClausificationPipelineAgreement

open LO FirstOrder
open scoped LO.FirstOrder
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

abbrev NamedFormula := TptpFofBinderResolution.NamedFormula
abbrev ResolvedFormula := TptpFofNormalizationSemantics.Formula 0
abbrev NnfFormula := TptpFofPrenexSemantics.Formula 0

/-- An official FOF source together with independently computed semantic
decoding and binder-resolution evidence. -/
structure PreparedInput where
  official : Pattern
  named : NamedFormula
  resolved : ResolvedFormula
  decoded : TptpOfficialFofElaboration.decodeFormula? official = some named
  resolved_exact :
    TptpFofBinderResolution.resolveClosedFormula? named = some resolved

def nnfFormula (input : PreparedInput) (polarity : Bool) : NnfFormula :=
  TptpFofNormalizationSemantics.normalize polarity input.resolved

noncomputable def officialRequest (input : PreparedInput) : Pattern :=
  TptpOfficialFofToNamedFormulaLanguageDef.request
    "tptp-fof-elab:formula" input.official

noncomputable def namedPattern (input : PreparedInput) : Pattern :=
  TptpNamedFofLanguageDef.encodeFormula input.named

noncomputable def resolverRequest (input : PreparedInput) : Pattern :=
  TptpNamedFofToResolvedLanguageDef.resolveClosed (namedPattern input)

noncomputable def resolvedPattern (input : PreparedInput) : Pattern :=
  TptpResolvedFofLanguageDef.encodeFormula input.resolved

noncomputable def nnfRequest (input : PreparedInput) (polarity : Bool) : Pattern :=
  TptpFofNormalizationLanguageDef.request polarity (resolvedPattern input)

noncomputable def nnfPattern (input : PreparedInput) (polarity : Bool) : Pattern :=
  TptpFofNnfLanguageDef.encodeFormula (nnfFormula input polarity)

/-! ## Operational evidence retained at every boundary -/

/-- Exact execution evidence for one authored LanguageDef at one finite
contextual depth. -/
structure ExactDerivation (base : BasePremiseEvaluator)
    (language : LanguageDef) (source target : Pattern) where
  height : Nat
  exact : rewriteAt base language height source = [target]

theorem ExactDerivation.stepAt {base : BasePremiseEvaluator}
    {language : LanguageDef} {source target : Pattern}
    (derivation : ExactDerivation base language source target) :
    StepAt base language derivation.height source target := by
  apply mem_rewriteAt_iff_stepAt.mp
  rw [derivation.exact]
  simp

noncomputable def exactDerivationOfStable
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {source target : Pattern}
    (stable : exists requiredFuel, forall fuel, requiredFuel <= fuel ->
      rewriteAt base language fuel source = [target]) :
    ExactDerivation base language source target where
  height := Classical.choose stable
  exact := Classical.choose_spec stable (Classical.choose stable) (Nat.le_refl _)

/-- All seven authored executions.  The last four stages reuse the exact
formula-level composition rather than rebuilding parallel evidence. -/
structure PipelineDerivation (input : PreparedInput) (polarity : Bool)
    (namingFrontier : Nat) where
  official : ExactDerivation
    (engineBasePremises RelationEnv.empty)
    TptpOfficialFofToNamedFormulaLanguageDef.language
    (officialRequest input) (namedPattern input)
  resolver : ExactDerivation
    (engineBasePremises TptpNamedFofToResolvedLanguageDef.relations)
    TptpNamedFofToResolvedLanguageDef.language
    (resolverRequest input) (resolvedPattern input)
  nnf : ExactDerivation
    (engineBasePremises RelationEnv.empty)
    TptpFofNormalizationLanguageDef.language
    (nnfRequest input polarity) (nnfPattern input polarity)
  clausification :
    TptpFofClausificationPipelineAgreement.PipelineDerivation
      (nnfFormula input polarity) namingFrontier

noncomputable def pipelineDerivation (input : PreparedInput)
    (polarity : Bool) (namingFrontier : Nat) :
    PipelineDerivation input polarity namingFrontier where
  official := exactDerivationOfStable
    (TptpNamedFofToNnfAgreement.official_ast_to_nnf_exact
      input.official input.named input.resolved input.decoded input.resolved_exact
      polarity (TptpFofNormalizationLanguageDef.semanticHeight input.resolved)
      (Nat.le_refl _)).1
  resolver := exactDerivationOfStable
    (TptpNamedFofToNnfAgreement.official_ast_to_nnf_exact
      input.official input.named input.resolved input.decoded input.resolved_exact
      polarity (TptpFofNormalizationLanguageDef.semanticHeight input.resolved)
      (Nat.le_refl _)).2.1
  nnf := {
    height := TptpFofNormalizationLanguageDef.semanticHeight input.resolved
    exact := by
      simpa only [nnfRequest, resolvedPattern, nnfPattern, nnfFormula,
        TptpFofNormalizationSemantics.normalizePositive] using
        (TptpNamedFofToNnfAgreement.official_ast_to_nnf_exact
          input.official input.named input.resolved input.decoded
          input.resolved_exact polarity
          (TptpFofNormalizationLanguageDef.semanticHeight input.resolved)
          (Nat.le_refl _)).2.2
  }
  clausification :=
    TptpFofClausificationPipelineAgreement.pipelineDerivation
      (nnfFormula input polarity) namingFrontier

theorem official_named_payload_exact (input : PreparedInput) :
    namedPattern input = TptpNamedFofLanguageDef.encodeFormula input.named := rfl

theorem resolver_nnf_payload_exact (input : PreparedInput) :
    resolvedPattern input =
      TptpResolvedFofLanguageDef.encodeFormula input.resolved := rfl

theorem nnf_clausification_payload_exact (input : PreparedInput)
    (polarity : Bool) :
    nnfPattern input polarity =
      TptpFofNnfLanguageDef.encodeFormula (nnfFormula input polarity) := rfl

/-- Exact singleton execution for every authored stage from the official FOF
AST through definitional CNF. -/
theorem rewriteAt_pipeline_exact (input : PreparedInput)
    (polarity : Bool) (namingFrontier : Nat) :
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofToNamedFormulaLanguageDef.language
      (pipelineDerivation input polarity namingFrontier).official.height
      (officialRequest input) = [namedPattern input]) /\
    (rewriteAt
      (engineBasePremises TptpNamedFofToResolvedLanguageDef.relations)
      TptpNamedFofToResolvedLanguageDef.language
      (pipelineDerivation input polarity namingFrontier).resolver.height
      (resolverRequest input) = [resolvedPattern input]) /\
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofNormalizationLanguageDef.language
      (pipelineDerivation input polarity namingFrontier).nnf.height
      (nnfRequest input polarity) = [nnfPattern input polarity]) /\
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofPrenexNormalizationLanguageDef.language
      (pipelineDerivation input polarity namingFrontier).clausification.prenex.height
      (TptpFofClausificationPipelineAgreement.prenexRequestPattern
        (nnfFormula input polarity)) =
      [TptpFofClausificationPipelineAgreement.prenexReceiptPattern
        (nnfFormula input polarity)]) /\
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofSkolemizationLanguageDef.language
      (pipelineDerivation input polarity namingFrontier).clausification.skolem.height
      (TptpFofClausificationPipelineAgreement.skolemRequestPattern
        (nnfFormula input polarity)) =
      [TptpFofClausificationPipelineAgreement.skolemReceiptPattern
        (nnfFormula input polarity)]) /\
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalNamingLanguageDef.language
      (pipelineDerivation input polarity namingFrontier).clausification.definitional.naming.height
      (TptpFofDefinitionalPipelineAgreement.namingRequestPattern
        (TptpFofClausificationPipelineAgreement.namingEvidence
          (nnfFormula input polarity))
        namingFrontier) =
      [TptpFofDefinitionalPipelineAgreement.namingReceiptPattern
        (TptpFofClausificationPipelineAgreement.namingEvidence
          (nnfFormula input polarity))
        namingFrontier]) /\
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language
      (pipelineDerivation input polarity namingFrontier).clausification.definitional.cnf.height
      (TptpFofDefinitionalPipelineAgreement.cnfRequestPattern
        (TptpFofClausificationPipelineAgreement.namingEvidence
          (nnfFormula input polarity))
        namingFrontier) =
      [TptpFofDefinitionalPipelineAgreement.cnfReceiptPattern
        (TptpFofClausificationPipelineAgreement.namingEvidence
          (nnfFormula input polarity))
        namingFrontier]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (pipelineDerivation input polarity namingFrontier).official.exact
  · exact (pipelineDerivation input polarity namingFrontier).resolver.exact
  · exact (pipelineDerivation input polarity namingFrontier).nnf.exact
  · exact (TptpFofClausificationPipelineAgreement.rewriteAt_pipeline_exact
      (nnfFormula input polarity) namingFrontier).1
  · exact (TptpFofClausificationPipelineAgreement.rewriteAt_pipeline_exact
      (nnfFormula input polarity) namingFrontier).2.1
  · exact (TptpFofClausificationPipelineAgreement.rewriteAt_pipeline_exact
      (nnfFormula input polarity) namingFrontier).2.2.1
  · exact (TptpFofClausificationPipelineAgreement.rewriteAt_pipeline_exact
      (nnfFormula input polarity) namingFrontier).2.2.2

/-! ## End-to-end semantic statement -/

def PolarizedResolvedSatisfiable (formula : ResolvedFormula)
    (polarity : Bool) : Prop :=
  exists (Domain : Type) (_ : Nonempty Domain)
    (model : TptpFofNormalizationSemantics.Model Domain),
    if polarity then TptpFofNormalizationSemantics.eval model ![] formula
    else Not (TptpFofNormalizationSemantics.eval model ![] formula)

abbrev ResolvedSatisfiable (formula : ResolvedFormula) : Prop :=
  PolarizedResolvedSatisfiable formula true

theorem polarizedResolvedSatisfiable_iff_nnfSourceSatisfiable
    (formula : ResolvedFormula) (polarity : Bool) :
    PolarizedResolvedSatisfiable formula polarity <->
      TptpFofSkolemizationSemantics.SourceSatisfiable
        (TptpFofNormalizationSemantics.normalize polarity formula) := by
  constructor
  · rintro ⟨Domain, domainNonempty, model, satisfied⟩
    refine ⟨Domain, domainNonempty, model, ?_⟩
    exact (TptpFofNormalizationSemantics.eval_normalize_iff
      model ![] polarity formula).mpr satisfied
  · rintro ⟨Domain, domainNonempty, model, satisfied⟩
    refine ⟨Domain, domainNonempty, model, ?_⟩
    exact (TptpFofNormalizationSemantics.eval_normalize_iff
      model ![] polarity formula).mp satisfied

theorem resolvedSatisfiable_iff_nnfSourceSatisfiable
    (formula : ResolvedFormula) :
    ResolvedSatisfiable formula <->
      TptpFofSkolemizationSemantics.SourceSatisfiable
        (TptpFofNormalizationSemantics.normalizePositive formula) := by
  simpa only [ResolvedSatisfiable, PolarizedResolvedSatisfiable,
    TptpFofNormalizationSemantics.normalizePositive] using
    polarizedResolvedSatisfiable_iff_nnfSourceSatisfiable formula true

/-- Positive premises and negated conjectures share one explicit polarity-
indexed theorem. -/
theorem polarizedResolvedSatisfiable_iff_pipelineCnfSatisfiable
    (input : PreparedInput) (polarity : Bool) (namingFrontier : Nat) :
    PolarizedResolvedSatisfiable input.resolved polarity <->
      TptpFofDefinitionalCnfSemantics.Satisfiable
        (TptpFofDefinitionalPipelineAgreement.namedOutput
          (TptpFofClausificationPipelineAgreement.namingEvidence
            (nnfFormula input polarity)) namingFrontier) :=
  (polarizedResolvedSatisfiable_iff_nnfSourceSatisfiable
      input.resolved polarity).trans
    (TptpFofClausificationPipelineAgreement.sourceSatisfiable_iff_pipelineCnfSatisfiable
      (nnfFormula input polarity) namingFrontier)

/-- A successfully decoded and binder-resolved official FOF source is
equisatisfiable with the final definitional CNF produced by the seven authored
LanguageDef executions. -/
theorem resolvedSatisfiable_iff_pipelineCnfSatisfiable
    (input : PreparedInput) (namingFrontier : Nat) :
    ResolvedSatisfiable input.resolved <->
      TptpFofDefinitionalCnfSemantics.Satisfiable
        (TptpFofDefinitionalPipelineAgreement.namedOutput
          (TptpFofClausificationPipelineAgreement.namingEvidence
            (nnfFormula input true)) namingFrontier) :=
  polarizedResolvedSatisfiable_iff_pipelineCnfSatisfiable
    input true namingFrontier

namespace Canary

noncomputable def truthInput : PreparedInput where
  official := TptpOfficialFofElaboration.Canary.definedNullaryFormula "$true"
  named := .verum
  resolved := .verum
  decoded := TptpOfficialFofElaboration.Canary.defined_true_is_verum
  resolved_exact := rfl

/-- Polarity is operationally and semantically load-bearing: the same official
truth formula enters positive clausification as truth and conjecture-negation
clausification as falsity. -/
theorem truth_polarities_are_distinct :
    nnfFormula truthInput true = (.verum : NnfFormula) /\
      nnfFormula truthInput false = (.falsum : NnfFormula) := by
  exact ⟨rfl, rfl⟩

noncomputable def shadowingInput : PreparedInput where
  official := TptpOfficialFofElaboration.Canary.shadowingFormula
  named := TptpOfficialFofElaboration.Canary.shadowingNamed
  resolved := .all (.ex (.equal (.bvar 0) (.bvar 0)))
  decoded := TptpOfficialFofElaboration.Canary.official_shadowing_elaborates_exactly
  resolved_exact := by
    have composed :=
      TptpOfficialFofElaboration.Canary.official_shadowing_resolves_exactly
    rw [TptpOfficialFofElaboration.Canary.official_shadowing_elaborates_exactly]
      at composed
    exact composed

theorem official_shadowing_has_seven_exact_singleton_stages :
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofToNamedFormulaLanguageDef.language
      (pipelineDerivation shadowingInput true 0).official.height
      (officialRequest shadowingInput)).length = 1 /\
    (rewriteAt
      (engineBasePremises TptpNamedFofToResolvedLanguageDef.relations)
      TptpNamedFofToResolvedLanguageDef.language
      (pipelineDerivation shadowingInput true 0).resolver.height
      (resolverRequest shadowingInput)).length = 1 /\
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofNormalizationLanguageDef.language
      (pipelineDerivation shadowingInput true 0).nnf.height
      (nnfRequest shadowingInput true)).length = 1 /\
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofPrenexNormalizationLanguageDef.language
      (pipelineDerivation shadowingInput true 0).clausification.prenex.height
      (TptpFofClausificationPipelineAgreement.prenexRequestPattern
        (nnfFormula shadowingInput true))).length = 1 /\
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofSkolemizationLanguageDef.language
      (pipelineDerivation shadowingInput true 0).clausification.skolem.height
      (TptpFofClausificationPipelineAgreement.skolemRequestPattern
        (nnfFormula shadowingInput true))).length = 1 /\
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalNamingLanguageDef.language
      (pipelineDerivation shadowingInput true 0).clausification.definitional.naming.height
      (TptpFofDefinitionalPipelineAgreement.namingRequestPattern
        (TptpFofClausificationPipelineAgreement.namingEvidence
          (nnfFormula shadowingInput true)) 0)).length = 1 /\
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language
      (pipelineDerivation shadowingInput true 0).clausification.definitional.cnf.height
      (TptpFofDefinitionalPipelineAgreement.cnfRequestPattern
        (TptpFofClausificationPipelineAgreement.namingEvidence
          (nnfFormula shadowingInput true)) 0)).length = 1 := by
  rw [(rewriteAt_pipeline_exact shadowingInput true 0).1,
    (rewriteAt_pipeline_exact shadowingInput true 0).2.1,
    (rewriteAt_pipeline_exact shadowingInput true 0).2.2.1,
    (rewriteAt_pipeline_exact shadowingInput true 0).2.2.2.1,
    (rewriteAt_pipeline_exact shadowingInput true 0).2.2.2.2.1,
    (rewriteAt_pipeline_exact shadowingInput true 0).2.2.2.2.2.1,
    (rewriteAt_pipeline_exact shadowingInput true 0).2.2.2.2.2.2]
  simp

/-- The composed API does not reinterpret an unbound variable. -/
theorem free_variable_still_fails_before_normalization :
    TptpFofBinderResolution.resolveClosedFormula?
      (.equal (.variable "X") (.variable "X")) = none :=
  TptpFofBinderResolution.Canary.free_variable_is_rejected

end Canary

#print axioms ExactDerivation.stepAt
#print axioms official_named_payload_exact
#print axioms resolver_nnf_payload_exact
#print axioms nnf_clausification_payload_exact
#print axioms rewriteAt_pipeline_exact
#print axioms polarizedResolvedSatisfiable_iff_nnfSourceSatisfiable
#print axioms resolvedSatisfiable_iff_nnfSourceSatisfiable
#print axioms polarizedResolvedSatisfiable_iff_pipelineCnfSatisfiable
#print axioms resolvedSatisfiable_iff_pipelineCnfSatisfiable
#print axioms Canary.truth_polarities_are_distinct
#print axioms Canary.official_shadowing_has_seven_exact_singleton_stages
#print axioms Canary.free_variable_still_fails_before_normalization

end Mettapedia.GSLT.LanguageDef.TptpOfficialFofClausificationPipelineAgreement
