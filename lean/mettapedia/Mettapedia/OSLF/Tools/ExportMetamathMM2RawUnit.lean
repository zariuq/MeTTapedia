import Mettapedia.Languages.Metamath.MM2SourceActionExecution
import Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory
import Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch
import Mettapedia.Languages.Metamath.MM2NormalLabelLookup
import Mettapedia.Languages.Metamath.MM2NormalLabelLookupAgreement
import Mettapedia.Languages.Metamath.MM2SourceConstantDeclaration
import Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
import Mettapedia.Languages.Metamath.MM2SourceScopeExecution
import Mettapedia.Languages.Metamath.MM2SourceFloatingDeclaration
import Mettapedia.Languages.Metamath.MM2SourceDVDeclaration
import Mettapedia.Languages.Metamath.MM2SourceEssentialDeclaration
import Mettapedia.Languages.Metamath.MM2SourceAssertionPlan
import Mettapedia.Languages.Metamath.MM2SourceAssertionExecution
import Mettapedia.Languages.Metamath.MM2CompressedProofExecution
import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
import Mettapedia.Languages.Metamath.MM2Transformation
import Mettapedia.Languages.Metamath.MM2VerifierProgram
import Mettapedia.Languages.Metamath.MM2TwoTransformProgram
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenUTF8
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenExecution
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenRuleScopedExecution

/-!
# Export one raw Metamath unit fixture through the two MM2 transformations

This executable keeps the source and verifier transformations separate.  It
first converts raw Metamath bytes into structurally admitted, proof-neutral
source-event data.  It then composes that data with the generic verifier
generated from the authored Metamath and MM2 presentations and renders the
result as ordinary MM2.
-/

namespace Mettapedia.OSLF.Tools.ExportMetamathMM2RawUnit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory
open Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2NormalLabelLookup
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceConstantDeclaration
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
open Mettapedia.Languages.Metamath.MM2SourceScopeExecution
open Mettapedia.Languages.Metamath.MM2SourceFloatingDeclaration
open Mettapedia.Languages.Metamath.MM2SourceDVDeclaration
open Mettapedia.Languages.Metamath.MM2SourceEssentialDeclaration
open Mettapedia.Languages.Metamath.MM2SourceAssertionPlan
open Mettapedia.Languages.Metamath.MM2SourceAssertionExecution
open Mettapedia.Languages.Metamath.MM2SourceFormulaValidation
open Mettapedia.Languages.Metamath.MM2SourceDVOccurrenceLookup
open Mettapedia.Languages.Metamath.MM2SourceDVPairPlan
open Mettapedia.Languages.Metamath.MM2SourceVariableTypecodeLookup
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
open Mettapedia.Languages.Metamath.SourceGSLTOperations
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenExecution
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenRuleScopedExecution

/-- The executable projection of `transformNormalVerifierSlice`.  The target's
proof fields are erased here; the following equality keeps this projection
definitionally tied to the semantic transformation. -/
def baseVerifierProgram (source : MetamathVerifierGSLT) : List Atom :=
  Mettapedia.Languages.Metamath.MM2VerifierProgram.baseVerifierProgram source

theorem baseVerifierProgram_eq_transform (source : MetamathVerifierGSLT)
    (target : MM2Target) :
    baseVerifierProgram source =
      (transformNormalVerifierSlice source target).program := by
  rfl

/-- Fixed-profile compressed source-rule extension selected by the supplied
operation spine.  These source-level activation, loading, and finishing rules
are verifier-owned and must be reinstalled by the ordinary source reload
protocol; compact header/body rows remain dynamic source data. -/
def compressedVerifierSourceRulesForOperation : SourceOperation → List Atom
  := Mettapedia.Languages.Metamath.MM2VerifierProgram.compressedVerifierSourceRulesForOperation

/-- Fixed verifier-owned compressed runtime inventory selected by the supplied
operation spine.  These linked rows are data for the ordered rule loader; they
are not executable source actions. -/
def compressedVerifierRuntimeRowsForOperation : SourceOperation → List Atom
  := Mettapedia.Languages.Metamath.MM2VerifierProgram.compressedVerifierRuntimeRowsForOperation

/-- The compressed source-rule branch is selected from the actual supplied
operation list.  This is an operation-spine profile selection, not a claim
that the present fixed rule inventory has been synthesized from arbitrary
source operational equations. -/
def compressedVerifierSourceExtension
    (source : MetamathVerifierGSLT) : List Atom :=
  Mettapedia.Languages.Metamath.MM2VerifierProgram.compressedVerifierSourceExtension
    source

/-- The corresponding fixed verifier-owned runtime rows. -/
def compressedVerifierRuntimeExtension
    (source : MetamathVerifierGSLT) : List Atom :=
  Mettapedia.Languages.Metamath.MM2VerifierProgram.compressedVerifierRuntimeExtension
    source

def verifierProgram (source : MetamathVerifierGSLT) : List Atom :=
  Mettapedia.Languages.Metamath.MM2VerifierProgram.verifierProgram source

theorem verifierProgram_eq_transform_extension
    (source : MetamathVerifierGSLT) (target : MM2Target) :
    verifierProgram source =
      (transformNormalVerifierSlice source target).program ++
        sourceActionVerifierExtensionProgramWith
          normalProofMachineRuleInventory
          (normalLabelLookupSourceRules ++
            compressedVerifierSourceExtension source) ++
          normalLabelLookupStaticRows ++
          compressedVerifierRuntimeExtension source := by
  simpa only [verifierProgram, compressedVerifierSourceExtension,
    compressedVerifierRuntimeExtension] using
      (Mettapedia.Languages.Metamath.MM2VerifierProgram.verifierProgram_eq_transform_extension
        source target)

/-- The single database- and proof-independent verifier program.  Both normal
and compressed machinery is present before source data is composed with it;
no statement, proof payload, pathname, or fixture identity selects a verifier
variant. -/
def genericVerifierProgram (source : MetamathVerifierGSLT) : List Atom :=
  Mettapedia.Languages.Metamath.MM2VerifierProgram.genericVerifierProgram source

/-- The database- and proof-dependent output of the source-data
transformation.  It contains only passive rows: the canonical ordered event
stream, proof syntax derived without checking a proof, source-state action
plans, their finite successor relations, and occurrence-indexed action kinds.

Keeping this value separate from `genericVerifierProgram` is the executable
two-transform boundary.  Either output can be rendered and parsed as an
ordinary MM2 program before the two atom lists are concatenated. -/
def usesNativeSourceStatement : RawStatement → Bool
  := Mettapedia.Languages.Metamath.MM2TwoTransformProgram.usesNativeSourceStatement

def usesNativeSourceOperation (plan : StatementActionPlan) : Bool :=
  Mettapedia.Languages.Metamath.MM2TwoTransformProgram.usesNativeSourceOperation
    plan

@[simp] theorem usesNativeSourceStatement_closeScope
    (span :
      Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan) :
    usesNativeSourceStatement (.closeScope span) = true := by
  exact
    Mettapedia.Languages.Metamath.MM2TwoTransformProgram.usesNativeSourceStatement_closeScope
      span

def residualSourceActionPlans {owner : Atom}
    {statements : List RawStatement}
    (actions : AdmittedSourceActionPlans owner statements) :
    List StatementActionPlan :=
  Mettapedia.Languages.Metamath.MM2TwoTransformProgram.residualSourceActionPlans
    actions

def residualSourceActionRows {owner : Atom}
    {statements : List RawStatement}
    (actions : AdmittedSourceActionPlans owner statements) : List Atom :=
  Mettapedia.Languages.Metamath.MM2TwoTransformProgram.residualSourceActionRows
    actions

def residualSourceActionKindRows {owner : Atom}
    {statements : List RawStatement}
    (actions : AdmittedSourceActionPlans owner statements) : List Atom :=
  Mettapedia.Languages.Metamath.MM2TwoTransformProgram.residualSourceActionKindRows
    actions

/-- Source data starts with canonical empty permanent-object, active-variable,
active-hypothesis, and active-distinct ledgers.  Native declaration and scope
rules extend or restore them only after finite validation reaches explicit
frontiers.  Plans for operations not yet executed natively remain on the
existing source-derived action path. -/
def sourceDataProgram {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) : List Atom :=
  Mettapedia.Languages.Metamath.MM2TwoTransformProgram.sourceDataProgram
    input actions

def composeProgram (source : MetamathVerifierGSLT) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) : List Atom :=
  Mettapedia.Languages.Metamath.MM2TwoTransformProgram.composeProgram
    source input actions

/-- The executable composition is literally the concatenation of the two
independently renderable transformation outputs. -/
@[simp] theorem composeProgram_eq_two_outputs
    (source : MetamathVerifierGSLT) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    composeProgram source input actions =
      genericVerifierProgram source ++ sourceDataProgram input actions := by
  rfl

/-- Composition cannot use the statement list or either proof representation to
choose verifier code: the only source-dependent prefix is the transformation
of the supplied verifier GSLT itself. -/
theorem composeProgram_eq_generic (source : MetamathVerifierGSLT)
    {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    composeProgram source input actions =
      let dvPlans := admitSourceDVPairPlans actions
      let assertionCandidates := admitSourceAssertionCandidatesFromActions actions
      (genericVerifierProgram source ++
        deferCompressedHeaderControls (deferProofControls input.initialRows) ++
          objectInventoryRows owner [] ++ activeVariableRows owner [] ++
            variableTypecodeLedgerRows owner [] ++
              emptyScopedActivityRows owner ++
                dvOccurrenceRows owner [] ++ dvPlans.rows ++
                  dvPlans.witnessRows ++
            AdmittedSourceAssertionCandidates.rows assertionCandidates ++
            nativeAssertionPublicationRows owner assertionCandidates.candidates ++
            essentialCandidateRows owner actions.plans ++
            residualSourceActionRows actions ++
              residualSourceActionKindRows actions) := by
  simpa only [composeProgram, genericVerifierProgram,
    residualSourceActionRows, residualSourceActionKindRows] using
      (Mettapedia.Languages.Metamath.MM2TwoTransformProgram.composeProgram_eq_generic
        source input actions)

/-- A successfully rendered verifier output is parsed by the generated MM2
ParserPack and enters the rule-scoped execution GSLT only through OSLF. -/
theorem genericVerifierProgram_successful_render_ruleScoped_pipeline
    (source : MetamathVerifierGSLT) {rendered : String}
    (renderedExact :
      renderProgram? (genericVerifierProgram source) = some rendered) :
    ∃ parsed :
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan.PlannedProgram
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics.stringScalars
            rendered),
      parsed.atoms = genericVerifierProgram source ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT.theory).satisfies
          (.request parsed.tree)
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT.exactOutcomeNativeType
            (.program parsed.atoms)).pred ∧
      initialSupport parsed.toParsedProgram =
        (genericVerifierProgram source).eraseDups ∧
      ∀ (policy : UnsupportedExecPolicy) (target : List Atom),
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (ruleScopedNativeListExecGSLT policy)).satisfies
            (initialSupport parsed.toParsedProgram)
            (ruleScopedExactTargetNativeType policy target).pred ↔
          cRuleScopedSourceWorkQueueStep policy
            (initialSupport parsed.toParsedProgram) = some target :=
  successful_render_ruleScoped_full_pipeline renderedExact

/-- A successfully rendered source-data output crosses the same generated
parser, executable elaboration GSLT, OSLF, and rule-scoped MM2 execution
boundary independently of the verifier output. -/
theorem sourceDataProgram_successful_render_ruleScoped_pipeline
    {owner : Atom} (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements)
    {rendered : String}
    (renderedExact : renderProgram? (sourceDataProgram input actions) =
      some rendered) :
    ∃ parsed :
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan.PlannedProgram
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics.stringScalars
            rendered),
      parsed.atoms = sourceDataProgram input actions ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT.theory).satisfies
          (.request parsed.tree)
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT.exactOutcomeNativeType
            (.program parsed.atoms)).pred ∧
      initialSupport parsed.toParsedProgram =
        (sourceDataProgram input actions).eraseDups ∧
      ∀ (policy : UnsupportedExecPolicy) (target : List Atom),
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (ruleScopedNativeListExecGSLT policy)).satisfies
            (initialSupport parsed.toParsedProgram)
            (ruleScopedExactTargetNativeType policy target).pred ↔
          cRuleScopedSourceWorkQueueStep policy
            (initialSupport parsed.toParsedProgram) = some target :=
  successful_render_ruleScoped_full_pipeline renderedExact

#print axioms genericVerifierProgram_successful_render_ruleScoped_pipeline
#print axioms sourceDataProgram_successful_render_ruleScoped_pipeline

/-- Every successfully rendered two-transform output is accepted by the
maximal-token ParserPack generated from its authored language and elaborates
back to the exact composed atom occurrences. -/
theorem composeProgram_successful_render_has_maximal_parser_square
    (source : MetamathVerifierGSLT) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements)
    {rendered : String}
    (renderedExact :
      renderProgram? (composeProgram source input actions) = some rendered) :
    ∃ parsed :
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics.ParsedProgram
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics.stringScalars
            rendered),
      parsed.atoms = composeProgram source input actions :=
  Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics.successful_render_has_exact_parser_square
    renderedExact

#print axioms composeProgram_successful_render_has_maximal_parser_square

/-- Every successfully rendered two-transform output is admitted from its
actual UTF-8 bytes by the maximal-token ParserPack and lowers to the exact
composed atom occurrences. -/
theorem composeProgram_successful_render_has_maximal_byte_parser_square
    (source : MetamathVerifierGSLT) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements)
    {rendered : String}
    (renderedExact :
      renderProgram? (composeProgram source input actions) = some rendered) :
    ∃ parsed :
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenUTF8.ByteParsedProgram
          rendered.toUTF8,
      parsed.atoms = composeProgram source input actions :=
  Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenUTF8.successful_render_has_exact_byte_parser_square
    renderedExact

#print axioms composeProgram_successful_render_has_maximal_byte_parser_square

/-- Every successfully rendered two-transform output enters the existing
reflective MM2 execution GSLT through the exact atoms recovered by generated
parsing and the finite source-derived CST plan. -/
theorem composeProgram_successful_render_execution_commutes
    (source : MetamathVerifierGSLT) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements)
    {rendered : String}
    (renderedExact :
      renderProgram? (composeProgram source input actions) = some rendered) :
    ∃ parsed :
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan.PlannedProgram
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics.stringScalars
            rendered),
      parsed.atoms = composeProgram source input actions ∧
      initialSupport parsed.toParsedProgram =
        (composeProgram source input actions).eraseDups ∧
      ∀ (policy : UnsupportedExecPolicy) (target : List Atom),
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveNativeListExecGSLT policy)).satisfies
            (initialSupport parsed.toParsedProgram)
            (reflectiveNativeListExactTargetNativeType policy target).pred ↔
          ReflectiveComputable.cReflectiveSourceWorkQueueStep
            policy
              (initialSupport parsed.toParsedProgram) = some target :=
  Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenExecution.successful_render_execution_commutes
    renderedExact

#print axioms composeProgram_successful_render_execution_commutes

/-- Raw Metamath transformation, MM2 rendering, generated parsing, executable
CST elaboration, and the existing MM2 work-queue GSLT form one source-bound
pipeline. -/
theorem composeProgram_successful_render_full_pipeline
    (source : MetamathVerifierGSLT) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements)
    {rendered : String}
    (renderedExact :
      renderProgram? (composeProgram source input actions) = some rendered) :
    ∃ parsed :
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan.PlannedProgram
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics.stringScalars
            rendered),
      parsed.atoms = composeProgram source input actions ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT.theory).satisfies
          (.request parsed.tree)
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT.exactOutcomeNativeType
            (.program parsed.atoms)).pred ∧
      initialSupport parsed.toParsedProgram =
        (composeProgram source input actions).eraseDups ∧
      ∀ (policy : UnsupportedExecPolicy) (target : List Atom),
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (reflectiveNativeListExecGSLT policy)).satisfies
            (initialSupport parsed.toParsedProgram)
            (reflectiveNativeListExactTargetNativeType policy target).pred ↔
          ReflectiveComputable.cReflectiveSourceWorkQueueStep
            policy (initialSupport parsed.toParsedProgram) = some target :=
  Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenExecution.successful_render_full_pipeline
    renderedExact

#print axioms composeProgram_successful_render_full_pipeline

/-- The actual two-transform output traverses generated parsing and executable
CST elaboration before entering the rule-scoped MM2 work queue.  This is the
execution boundary used by output-local binders in generated verifier rules. -/
theorem composeProgram_successful_render_ruleScoped_full_pipeline
    (source : MetamathVerifierGSLT) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements)
    {rendered : String}
    (renderedExact :
      renderProgram? (composeProgram source input actions) = some rendered) :
    ∃ parsed :
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan.PlannedProgram
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics.stringScalars
            rendered),
      parsed.atoms = composeProgram source input actions ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT.theory).satisfies
          (.request parsed.tree)
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT.exactOutcomeNativeType
            (.program parsed.atoms)).pred ∧
      initialSupport parsed.toParsedProgram =
        (composeProgram source input actions).eraseDups ∧
      ∀ (policy : UnsupportedExecPolicy) (target : List Atom),
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (ruleScopedNativeListExecGSLT policy)).satisfies
            (initialSupport parsed.toParsedProgram)
            (ruleScopedExactTargetNativeType policy target).pred ↔
          cRuleScopedSourceWorkQueueStep policy
            (initialSupport parsed.toParsedProgram) = some target :=
  successful_render_ruleScoped_full_pipeline renderedExact

#print axioms composeProgram_successful_render_ruleScoped_full_pipeline

/-- Every bounded execution of the rendered two-transform output carries the
exact rule-scoped GSLT path and executed-step count. -/
theorem composeProgram_successful_render_ruleScoped_bounded_pipeline
    (source : MetamathVerifierGSLT) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements)
    {rendered : String}
    (renderedExact :
      renderProgram? (composeProgram source input actions) = some rendered)
    (policy : UnsupportedExecPolicy) (fuel : Nat) :
    ∃ parsed :
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan.PlannedProgram
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics.stringScalars
            rendered),
      parsed.atoms = composeProgram source input actions ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT.theory).satisfies
          (.request parsed.tree)
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT.exactOutcomeNativeType
            (.program parsed.atoms)).pred ∧
      initialSupport parsed.toParsedProgram =
        (composeProgram source input actions).eraseDups ∧
      ∃ path : (ruleScopedNativeListExecGSLT policy).RewritePath
          (initialSupport parsed.toParsedProgram)
          (cRuleScopedSourceWorkQueueRunN policy fuel
            (initialSupport parsed.toParsedProgram)).1,
        path.length =
          (cRuleScopedSourceWorkQueueRunN policy fuel
            (initialSupport parsed.toParsedProgram)).2 :=
  successful_render_ruleScoped_bounded_pipeline renderedExact policy fuel

#print axioms composeProgram_successful_render_ruleScoped_bounded_pipeline

/-- Every bounded execution of a successfully rendered two-transform output
also carries a proof-relevant trace through the exact native types generated
by applying OSLF to the rule-scoped execution GSLT. -/
theorem composeProgram_successful_render_ruleScoped_native_type_trace
    (source : MetamathVerifierGSLT) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements)
    {rendered : String}
    (renderedExact :
      renderProgram? (composeProgram source input actions) = some rendered)
    (policy : UnsupportedExecPolicy) (fuel : Nat) :
    ∃ parsed :
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan.PlannedProgram
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics.stringScalars
            rendered),
      parsed.atoms = composeProgram source input actions ∧
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT.theory).satisfies
          (.request parsed.tree)
          (Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT.exactOutcomeNativeType
            (.program parsed.atoms)).pred ∧
      initialSupport parsed.toParsedProgram =
        (composeProgram source input actions).eraseDups ∧
      Nonempty (RuleScopedNativeTypeTrace policy fuel
        (initialSupport parsed.toParsedProgram)
        (cRuleScopedSourceWorkQueueRunN policy fuel
          (initialSupport parsed.toParsedProgram)).1) :=
  successful_render_ruleScoped_native_type_trace_pipeline renderedExact policy
    fuel

#print axioms composeProgram_successful_render_ruleScoped_native_type_trace

/-! ## Directly authored declaration controls -/

private def authoredSpan (start stop : Nat) :
    Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan :=
  { fileId := "authored.mm2", start, stop }

private def authoredName (name : String) (start stop : Nat) :
    Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition.LocatedName :=
  { span := authoredSpan start stop, name }

private def authoredOwner : Atom := .symbol "authored-declaration-control"

private def authoredDuplicateStatement : RawStatement :=
  .constDecl (authoredSpan 0 2)
    [authoredName "a" 3 4, authoredName "b" 5 6,
      authoredName "a" 7 8]
    (authoredSpan 9 11)

private def authoredOccupiedName : LocatedName :=
  authoredName "occupied" 20 28

private def authoredOccupiedEntry : ObjectOccurrence :=
  { kind := .constant, occurrence := authoredOccupiedName }

private def authoredLateOccupiedStatement : RawStatement :=
  .constDecl (authoredSpan 0 2)
    [authoredName "fresh" 3 8, authoredName "occupied" 9 17]
    (authoredSpan 18 20)

private def authoredDuplicateVariableStatement : RawStatement :=
  .varDecl (authoredSpan 0 2)
    [authoredName "x" 3 4, authoredName "x" 5 6]
    (authoredSpan 7 9)

private def authoredActiveVariable : LocatedName :=
  authoredName "x" 20 21

private def authoredActiveVariableEntry : ObjectOccurrence :=
  { kind := .variable, occurrence := authoredActiveVariable }

private def authoredLateActiveVariableStatement : RawStatement :=
  .varDecl (authoredSpan 0 2)
    [authoredName "fresh" 3 8, authoredName "x" 9 10]
    (authoredSpan 11 13)

private def authoredFloatingTypecode : LocatedName :=
  authoredName "wff" 40 43

private def authoredHistoricalTypecode : LocatedName :=
  authoredName "class" 44 49

private def authoredFloatingVariable : LocatedName :=
  authoredName "x" 50 51

private def authoredFloatingTypecodeEntry : ObjectOccurrence :=
  { kind := .constant, occurrence := authoredFloatingTypecode }

private def authoredHistoricalTypecodeEntry : ObjectOccurrence :=
  { kind := .constant, occurrence := authoredHistoricalTypecode }

private def authoredFloatingVariableEntry : ObjectOccurrence :=
  { kind := .variable, occurrence := authoredFloatingVariable }

private def authoredFloatingStatement : RawStatement :=
  .floating (authoredSpan 0 2) (authoredName "wx" 3 5)
    (authoredName "wff" 6 9) (authoredName "x" 10 11)
    (authoredSpan 12 14)

private def authoredEssentialLabel : LocatedName :=
  authoredName "ex" 60 62

private def authoredEssentialStatement : RawStatement :=
  .essential (authoredSpan 0 2) authoredEssentialLabel
    authoredFloatingTypecode [authoredFloatingVariable]
    (authoredSpan 12 14)

private def authoredEssentialFormula :
    Mettapedia.Languages.Metamath.InferenceEncoding.ConstantHeadedFormula :=
  { typecode := "wff", body := [.var "x"] }

private def authoredWrongEssentialFormula :
    Mettapedia.Languages.Metamath.InferenceEncoding.ConstantHeadedFormula :=
  { typecode := "wff", body := [.const "x"] }

private def authoredEssentialEntry : ObjectOccurrence :=
  { kind := .label, occurrence := authoredEssentialLabel }

private def authoredPriorVariableTypecode : VariableTypecodeOccurrence :=
  { statementPosition := 17
    label := authoredName "oldx" 52 56
    typecode := authoredHistoricalTypecode
    variableName := authoredFloatingVariable }

private def authoredCloseScopeStatement : RawStatement :=
  .closeScope (authoredSpan 30 32)

private def authoredRootCheckpoint : ScopeCheckpoint :=
  { activeVariableFrontier := objectRootKey
    activeHypothesisFrontier := objectRootKey
    activeDistinctFrontier := objectRootKey
    dvOccurrenceFrontier := natAtom 0 }

private def authoredNestedEnvironment : Atom :=
  sourceEnvironmentAtom authoredOwner
    (listAtom id [scopeCheckpointAtom authoredRootCheckpoint]) 0 0

private def authoredInitialScopedRows : List Atom :=
  emptyScopedActivityRows authoredOwner ++ dvOccurrenceRows authoredOwner []

private def directlyAuthoredDeclarationProgram
    (statement : RawStatement) (inventory : List ObjectOccurrence) : List Atom :=
  genericVerifierProgram authoredMetamathVerifierGSLT ++
    [sourceCurrentAtom authoredOwner 0 1 statement,
      sourceInitialEnvironmentAtom authoredOwner] ++
      objectInventoryRows authoredOwner inventory ++
      activeVariableRows authoredOwner [] ++
      variableTypecodeLedgerRows authoredOwner [] ++
      authoredInitialScopedRows

def authoredDuplicateConstantProgram : List Atom :=
  directlyAuthoredDeclarationProgram authoredDuplicateStatement []

def authoredLateOccupiedConstantProgram : List Atom :=
  directlyAuthoredDeclarationProgram authoredLateOccupiedStatement
    [authoredOccupiedEntry]

def authoredDuplicateVariableProgram : List Atom :=
  directlyAuthoredDeclarationProgram authoredDuplicateVariableStatement []

def authoredLateActiveVariableProgram : List Atom :=
  genericVerifierProgram authoredMetamathVerifierGSLT ++
    [sourceCurrentAtom authoredOwner 0 1 authoredLateActiveVariableStatement,
      sourceInitialEnvironmentAtom authoredOwner] ++
      objectInventoryRows authoredOwner [authoredActiveVariableEntry] ++
      activeVariableRows authoredOwner [authoredActiveVariable] ++
      variableTypecodeLedgerRows authoredOwner [] ++
      authoredInitialScopedRows

def authoredFreshFloatingProgram : List Atom :=
  genericVerifierProgram authoredMetamathVerifierGSLT ++
    [sourceCurrentAtom authoredOwner 0 1 authoredFloatingStatement,
      sourceInitialEnvironmentAtom authoredOwner] ++
      objectInventoryRows authoredOwner
        [authoredFloatingTypecodeEntry, authoredFloatingVariableEntry] ++
      activeVariableRows authoredOwner [authoredFloatingVariable] ++
      variableTypecodeLedgerRows authoredOwner [] ++
      authoredInitialScopedRows

def authoredConflictingFloatingProgram : List Atom :=
  genericVerifierProgram authoredMetamathVerifierGSLT ++
    [sourceCurrentAtom authoredOwner 0 1 authoredFloatingStatement,
      sourceInitialEnvironmentAtom authoredOwner] ++
      objectInventoryRows authoredOwner
        [authoredFloatingTypecodeEntry, authoredHistoricalTypecodeEntry,
          authoredFloatingVariableEntry] ++
      activeVariableRows authoredOwner [authoredFloatingVariable] ++
      variableTypecodeLedgerRows authoredOwner
        [authoredPriorVariableTypecode] ++
      authoredInitialScopedRows

def authoredNestedConstantProgram : List Atom :=
  genericVerifierProgram authoredMetamathVerifierGSLT ++
    [sourceCurrentAtom authoredOwner 0 1 authoredDuplicateStatement,
      authoredNestedEnvironment] ++
      objectInventoryRows authoredOwner [] ++
      activeVariableRows authoredOwner [] ++
      variableTypecodeLedgerRows authoredOwner [] ++
      authoredInitialScopedRows

def authoredScopeUnderflowProgram : List Atom :=
  genericVerifierProgram authoredMetamathVerifierGSLT ++
    [sourceCurrentAtom authoredOwner 0 1 authoredCloseScopeStatement,
      sourceInitialEnvironmentAtom authoredOwner] ++
      objectInventoryRows authoredOwner [] ++
      activeVariableRows authoredOwner [] ++
      variableTypecodeLedgerRows authoredOwner [] ++
      authoredInitialScopedRows

private def directlyAuthoredEssentialProgram
    (candidateFormula :
      Mettapedia.Languages.Metamath.InferenceEncoding.ConstantHeadedFormula)
    (inventory : List ObjectOccurrence) : List Atom :=
  genericVerifierProgram authoredMetamathVerifierGSLT ++
    [sourceCurrentAtom authoredOwner 0 1 authoredEssentialStatement,
      sourceInitialEnvironmentAtom authoredOwner,
      essentialCandidateAtom authoredOwner 0 1 authoredEssentialStatement
        authoredEssentialLabel (formulaAtom candidateFormula)] ++
      objectInventoryRows authoredOwner inventory ++
      activeVariableRows authoredOwner [authoredFloatingVariable] ++
      variableTypecodeLedgerRows authoredOwner [] ++
      authoredInitialScopedRows

def authoredFreshEssentialProgram : List Atom :=
  directlyAuthoredEssentialProgram authoredEssentialFormula
    [authoredFloatingTypecodeEntry, authoredFloatingVariableEntry]

def authoredWrongFormulaEssentialProgram : List Atom :=
  directlyAuthoredEssentialProgram authoredWrongEssentialFormula
    [authoredFloatingTypecodeEntry, authoredFloatingVariableEntry]

def authoredOccupiedEssentialProgram : List Atom :=
  directlyAuthoredEssentialProgram authoredEssentialFormula
    [authoredFloatingTypecodeEntry, authoredFloatingVariableEntry,
      authoredEssentialEntry]

def exportAuthoredDeclarationControl (mode outputPath : String) : IO UInt32 := do
  let program <- match mode with
    | "constant-duplicate" => pure authoredDuplicateConstantProgram
    | "constant-occupied" => pure authoredLateOccupiedConstantProgram
    | "variable-duplicate" => pure authoredDuplicateVariableProgram
    | "variable-active" => pure authoredLateActiveVariableProgram
    | "floating-fresh" => pure authoredFreshFloatingProgram
    | "floating-conflict" => pure authoredConflictingFloatingProgram
    | "constant-nested" => pure authoredNestedConstantProgram
    | "scope-underflow" => pure authoredScopeUnderflowProgram
    | "essential-fresh" => pure authoredFreshEssentialProgram
    | "essential-wrong-formula" => pure authoredWrongFormulaEssentialProgram
    | "essential-occupied" => pure authoredOccupiedEssentialProgram
    | _ =>
        IO.eprintln "unknown authored declaration control"
        return 2
  match renderProgram? program with
  | none =>
      IO.eprintln "the authored declaration control is outside ordinary MM2"
      return 1
  | some rendered =>
      IO.FS.writeFile outputPath rendered
      IO.println
        s!"MM2AuthoredDeclarationControl mode={mode} programAtoms={program.length} outputBytes={rendered.toUTF8.size}"
      return 0

inductive ExportDestination where
  | combined (outputPath : String)
  | split (verifierOutputPath sourceDataOutputPath : String)

def run (arguments : List String) : IO UInt32 := do
  let (sourcePath, destination) <- match arguments with
    | [sourcePath, outputPath] =>
        pure (sourcePath, ExportDestination.combined outputPath)
    | [sourcePath, verifierOutputPath, sourceDataOutputPath] =>
        pure (sourcePath,
          ExportDestination.split verifierOutputPath sourceDataOutputPath)
    | _ =>
        IO.eprintln
          "usage: ExportMetamathMM2RawUnit <source.mm> <output.mm2>\n       ExportMetamathMM2RawUnit <source.mm> <verifier.mm2> <source-data.mm2>"
        return 2

  let sourceBytes <- IO.FS.readBinFile sourcePath
  let logicalRoot := "unit.mm"
  let files : FileMap := fun path =>
    if path = logicalRoot then some sourceBytes else none
  let owner := stringAtom "metamath-test-unit"

  match transformRawSource owner files bookSpecPolicy logicalRoot with
  | .error _ =>
      IO.eprintln "raw Metamath source transformation rejected the fixture"
      return 1
  | .ok artifact =>
      match admitSourceEventInput owner artifact.rows with
      | .error _ =>
          IO.eprintln "MM2 source-event admission rejected transformed rows"
          return 1
      | .ok input =>
          match admitSourceActionPlans owner input.statements with
          | .rejected _ =>
              IO.eprintln "MM2 source-action planning rejected transformed rows"
              return 1
          | .ok plannedActions =>
              match admitSourceActionPlanRows plannedActions
                  plannedActions.bundleRows with
              | .error _ =>
                  IO.eprintln
                    "MM2 source-action bundle admission rejected derived rows"
                  return 1
              | .ok actions =>
                  let verifier :=
                    genericVerifierProgram authoredMetamathVerifierGSLT
                  let sourceData := sourceDataProgram input actions
                  let program := verifier ++ sourceData
                  match destination with
                  | .combined outputPath =>
                      match renderProgram? program with
                      | none =>
                          IO.eprintln
                            "the composed transformation outputs are outside ordinary MM2"
                          return 1
                      | some rendered =>
                          IO.FS.writeFile outputPath rendered
                          IO.println
                            s!"MM2RawUnitExport statements={artifact.statements.length} obligations={artifact.obligations.length} initialRows={input.initialRows.length} actionPlans={actions.plans.length} actionRows={actions.rows.length} verifierAtoms={verifier.length} sourceDataAtoms={sourceData.length} programAtoms={program.length} outputBytes={rendered.toUTF8.size}"
                          return 0
                  | .split verifierOutputPath sourceDataOutputPath =>
                      match renderProgram? verifier, renderProgram? sourceData with
                      | some renderedVerifier, some renderedSourceData =>
                          IO.FS.writeFile verifierOutputPath renderedVerifier
                          IO.FS.writeFile sourceDataOutputPath renderedSourceData
                          IO.println
                            s!"MM2RawUnitSplitExport statements={artifact.statements.length} obligations={artifact.obligations.length} initialRows={input.initialRows.length} actionPlans={actions.plans.length} actionRows={actions.rows.length} verifierAtoms={verifier.length} sourceDataAtoms={sourceData.length} verifierBytes={renderedVerifier.toUTF8.size} sourceDataBytes={renderedSourceData.toUTF8.size}"
                          return 0
                      | _, _ =>
                          IO.eprintln
                            "one transformation output is outside ordinary MM2"
                          return 1

end Mettapedia.OSLF.Tools.ExportMetamathMM2RawUnit

def exportMetamathMM2RawUnitMain (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportMetamathMM2RawUnit.run arguments

/-- Environment-facing entry used by the bounded conformance gate.  Keeping
the entry named avoids inheriting an unrelated root `main` from the raw-source
parser library. -/
def exportMetamathMM2RawUnitFromEnvironment : IO UInt32 := do
  match (← IO.getEnv "METTAPEDIA_MM2_RAW_SOURCE"),
      (← IO.getEnv "METTAPEDIA_MM2_RAW_OUTPUT"),
      (← IO.getEnv "METTAPEDIA_MM2_VERIFIER_OUTPUT"),
      (← IO.getEnv "METTAPEDIA_MM2_SOURCE_DATA_OUTPUT") with
  | some sourcePath, some outputPath, none, none =>
      exportMetamathMM2RawUnitMain [sourcePath, outputPath]
  | some sourcePath, none, some verifierOutputPath, some sourceDataOutputPath =>
      exportMetamathMM2RawUnitMain
        [sourcePath, verifierOutputPath, sourceDataOutputPath]
  | _, _, _, _ =>
      IO.eprintln
        "set METTAPEDIA_MM2_RAW_SOURCE with either METTAPEDIA_MM2_RAW_OUTPUT or both METTAPEDIA_MM2_VERIFIER_OUTPUT and METTAPEDIA_MM2_SOURCE_DATA_OUTPUT"
      return 2

def exportAuthoredDeclarationControlFromEnvironment : IO UInt32 := do
  match (← IO.getEnv "METTAPEDIA_MM2_AUTHORED_DECLARATION_MODE"),
      (← IO.getEnv "METTAPEDIA_MM2_AUTHORED_DECLARATION_OUTPUT") with
  | some mode, some outputPath =>
      Mettapedia.OSLF.Tools.ExportMetamathMM2RawUnit.exportAuthoredDeclarationControl
        mode outputPath
  | _, _ =>
      IO.eprintln
        "set METTAPEDIA_MM2_AUTHORED_DECLARATION_MODE and METTAPEDIA_MM2_AUTHORED_DECLARATION_OUTPUT"
      return 2
