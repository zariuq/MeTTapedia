import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTypedOperational
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSelectedAdequacy

/-!
# Semantic composite for the typed PeTTa call-guard compiler

This module closes the source-to-typed semantic triangle before any lowering.
The left summand of the single validated source-indexed calculus has exactly
the cold compiler paths, normal forms, and terminal observations.  Its right
summand is the same generated calculus whose arbitrary proof trees satisfy the
independently defined displayed meaning.

The two authorities remain separate: object execution cannot enter proof
search, and proof derivability cannot manufacture an object transition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSemanticComposite

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTypedOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedModel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedDerivationSoundness
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSelectedAdequacy

/-- The object component of the one validated typed theory. -/
def flatObjectTheory : GSLT :=
  languageGSLTUsing relationEnv generated.1.toLanguageDef reductionLaws

/-- One flat-object step is exactly one step of the authenticated cold
presentation, globally on raw patterns. -/
theorem flatObject_step_iff_coldPresentation (source target : Pattern) :
    flatObjectTheory.Step source target ↔
      compileLanguagePresentationGSLT.Step source target := by
  change
    (languageGSLTUsing relationEnv generated.1.toLanguageDef reductionLaws).Step
        source target ↔
      (languageGSLTUsing relationEnv language languageReductionLaws).Step
        source target
  exact
    (languageGSLTUsing_step relationEnv generated.1.toLanguageDef
      reductionLaws source target).trans
      ((flat_langReduces_iff_cold relationEnv source target).trans
        (languageGSLTUsing_step relationEnv language languageReductionLaws
          source target).symm)

/-- Exact step agreement maps every flat-object path to a cold path. -/
private theorem flatObject_multiStep_to_cold :
    ∀ {source target : Pattern},
      flatObjectTheory.MultiStep source target →
        compileLanguagePresentationGSLT.MultiStep source target
  | _, _, .refl term =>
      @GSLT.MultiStep.refl compileLanguagePresentationGSLT term
  | _, _, .step reduction rest =>
      .step ((flatObject_step_iff_coldPresentation _ _).1 reduction)
        (flatObject_multiStep_to_cold rest)

/-- Conversely, exact step agreement maps every cold path into the flat
object language. -/
private theorem cold_multiStep_to_flatObject :
    ∀ {source target : Pattern},
      compileLanguagePresentationGSLT.MultiStep source target →
        flatObjectTheory.MultiStep source target
  | _, _, .refl term => @GSLT.MultiStep.refl flatObjectTheory term
  | _, _, .step reduction rest =>
      .step ((flatObject_step_iff_coldPresentation _ _).2 reduction)
        (cold_multiStep_to_flatObject rest)

/-- Exact step agreement lifts compositionally to every finite object path. -/
theorem flatObject_multiStep_iff_coldPresentation
    (source target : Pattern) :
    flatObjectTheory.MultiStep source target ↔
      compileLanguagePresentationGSLT.MultiStep source target :=
  ⟨flatObject_multiStep_to_cold, cold_multiStep_to_flatObject⟩

/-- Normality is also unchanged by the generated object signature. -/
theorem flatObject_normal_iff_coldPresentation (source : Pattern) :
    flatObjectTheory.IsNormalForm source ↔
      compileLanguagePresentationGSLT.IsNormalForm source := by
  constructor
  · intro normal ⟨target, step⟩
    exact normal ⟨target,
      (flatObject_step_iff_coldPresentation source target).2 step⟩
  · intro normal ⟨target, step⟩
    exact normal ⟨target,
      (flatObject_step_iff_coldPresentation source target).1 step⟩

/-- The full typed theory has exactly the cold object's finite paths between
object endpoints.  The proof-search summand cannot occur in the middle. -/
theorem typedObject_multiStep_iff_coldPresentation
    (source target : Pattern) :
    typedCompilerTheory.MultiStep
        (inLanguage source) (inLanguage target) ↔
      compileLanguagePresentationGSLT.MultiStep source target := by
  calc
    typedCompilerTheory.MultiStep
          (inLanguage source) (inLanguage target) ↔
        flatObjectTheory.MultiStep source target := by
          exact combinedGSLTUsing_language_multiStep relationEnv generated
            reductionLaws source target
    _ ↔ compileLanguagePresentationGSLT.MultiStep source target :=
      flatObject_multiStep_iff_coldPresentation source target

/-- Canonical finite paths in the qualified typed theory reconstruct exactly
one path of the independent cold control machine and a canonical target. -/
theorem typedObject_multiStep_iff_compileLanguageMultiStep
    (source : CompileLanguageControl) (wire : Pattern) :
    typedCompilerTheory.MultiStep
        (inLanguage (encodeCompileLanguageControl source))
        (inLanguage wire) ↔
      ∃ target,
        compileLanguageGSLT.MultiStep source target ∧
          wire = encodeCompileLanguageControl target :=
  (typedObject_multiStep_iff_coldPresentation
    (encodeCompileLanguageControl source) wire).trans
      (language_multiStep_iff_compileLanguageMultiStep source wire)

/-- A canonical object state is normal in the complete typed theory exactly
when the independent cold control is halted. -/
theorem typedObject_normal_iff_halted (source : CompileLanguageControl) :
    typedCompilerTheory.IsNormalForm
        (inLanguage (encodeCompileLanguageControl source)) ↔
      ∃ result, source = .halted result := by
  calc
    typedCompilerTheory.IsNormalForm
          (inLanguage (encodeCompileLanguageControl source)) ↔
        flatObjectTheory.IsNormalForm
          (encodeCompileLanguageControl source) := by
            exact combinedGSLTUsing_language_normalForm relationEnv generated
              reductionLaws (encodeCompileLanguageControl source)
    _ ↔ compileLanguagePresentationGSLT.IsNormalForm
          (encodeCompileLanguageControl source) :=
      flatObject_normal_iff_coldPresentation _
    _ ↔ ∃ result, source = .halted result :=
      language_normal_iff_halted source

/-- The typed source reaches the exact independently specified cold
compilation result. -/
theorem typedObject_total_exact (owned : OwnedSnapshot) (head : String)
    (arity : Nat) :
    typedCompilerTheory.MultiStep
      (inLanguage (encodeCompileLanguageControl
        (compileLanguageStart owned head arity)))
      (inLanguage (encodeCompileLanguageControl
        (.halted (compileGuards owned head arity)))) :=
  (typedObject_multiStep_iff_coldPresentation _ _).2
    (language_total_exact owned head arity)

/-- No typed object path from the canonical start can invent a different
terminal compilation result. -/
theorem typedObject_halted_result_unique (owned : OwnedSnapshot)
    (head : String) (arity : Nat) (result : CompilationResult)
    (steps : typedCompilerTheory.MultiStep
      (inLanguage (encodeCompileLanguageControl
        (compileLanguageStart owned head arity)))
      (inLanguage (encodeCompileLanguageControl (.halted result)))) :
    result = compileGuards owned head arity :=
  language_halted_result_unique owned head arity result
    ((typedObject_multiStep_iff_coldPresentation _ _).1 steps)

/-- When cold compilation returns a current family, the typed path and the
independent SWI-style successful-declaration observation agree exactly as an
ordered list. -/
theorem typedObject_compiled_execution_exact (owned : OwnedSnapshot)
    (call : Call) (family : CompiledGuardFamily)
    (wellFormed : owned.snapshot.WellFormed)
    (compiled : compileGuards owned call.function
      call.sourceArguments.length = .compiled family) :
    typedCompilerTheory.MultiStep
        (inLanguage (encodeCompileLanguageControl
          (compileLanguageStart owned call.function
            call.sourceArguments.length)))
        (inLanguage (encodeCompileLanguageControl (.halted (.compiled family))))
      ∧
    executeCompilation owned call (.compiled family) =
      .executed (successfulDeclarations ⟨owned.snapshot, call⟩) := by
  have path := typedObject_total_exact owned call.function
    call.sourceArguments.length
  rw [compiled] at path
  have valid := compileGuards_family_valid owned call.function
    call.sourceArguments.length family wellFormed compiled
  have coordinates := compileGuards_coordinates compiled
  have requestMatches : family.MatchesCall call :=
    ⟨coordinates.2.2.1, coordinates.2.2.2⟩
  exact ⟨path,
    executeCompilation_eq_successfulDeclarations owned call family
      valid requestMatches⟩

/-- Unsupported relevant declarations remain an explicit fallback result;
typing attachment cannot silently turn them into an empty successful family. -/
theorem typedObject_outsideFragment_exact (owned : OwnedSnapshot)
    (call : Call)
    (outside : compileGuards owned call.function
      call.sourceArguments.length = .outsideFragment) :
    typedCompilerTheory.MultiStep
        (inLanguage (encodeCompileLanguageControl
          (compileLanguageStart owned call.function
            call.sourceArguments.length)))
        (inLanguage (encodeCompileLanguageControl
          (.halted .outsideFragment)))
      ∧
    executeCompilation owned call .outsideFragment =
      .fallback .outsideFragment := by
  have path := typedObject_total_exact owned call.function
    call.sourceArguments.length
  rw [outside] at path
  exact ⟨path, rfl⟩

/-- Independent source observation for one compiled call.  The cold compiler
decides only whether the supported fragment applies; successful declarations
remain the separately defined SWI-style semantic observation. -/
def sourceCallGuardObservation (owned : OwnedSnapshot) (call : Call) :
    GuardExecution :=
  match compileGuards owned call.function call.sourceArguments.length with
  | .compiled _ =>
      .executed (successfulDeclarations ⟨owned.snapshot, call⟩)
  | .outsideFragment => .fallback .outsideFragment

/-- The typed source path and the GuardPlan executor compose to the exact
independent call observation for every well-formed source snapshot. -/
theorem typedObject_call_execution_exact (owned : OwnedSnapshot)
    (call : Call) (wellFormed : owned.snapshot.WellFormed) :
    typedCompilerTheory.MultiStep
        (inLanguage (encodeCompileLanguageControl
          (compileLanguageStart owned call.function
            call.sourceArguments.length)))
        (inLanguage (encodeCompileLanguageControl
          (.halted (compileGuards owned call.function
            call.sourceArguments.length))))
      ∧
    executeCompilation owned call
        (compileGuards owned call.function call.sourceArguments.length) =
      sourceCallGuardObservation owned call := by
  refine ⟨typedObject_total_exact owned call.function
    call.sourceArguments.length, ?_⟩
  cases compiled : compileGuards owned call.function
      call.sourceArguments.length with
  | outsideFragment =>
      simp [sourceCallGuardObservation, compiled, executeCompilation]
  | compiled family =>
      have valid := compileGuards_family_valid owned call.function
        call.sourceArguments.length family wellFormed compiled
      have coordinates := compileGuards_coordinates compiled
      have requestMatches : family.MatchesCall call :=
        ⟨coordinates.2.2.1, coordinates.2.2.2⟩
      simpa [sourceCallGuardObservation, compiled] using
        executeCompilation_eq_successfulDeclarations owned call family
          valid requestMatches

/-- No finite object execution can turn into a proof obligation. -/
theorem typedObject_cannot_reach_proof (pattern : Pattern)
    (state : GoalState) :
    ¬ typedCompilerTheory.MultiStep
      (inLanguage pattern) (inCalculus state) := by
  change ¬ (GSLT.disjointSum flatObjectTheory
    (proofSearchGSLT generated)).MultiStep
      (inLanguage pattern) (inCalculus state)
  exact no_left_multiStep_to_right flatObjectTheory
    (proofSearchGSLT generated) pattern state

/-- No generated proof search can manufacture an object execution state. -/
theorem typedProof_cannot_reach_object (state : GoalState)
    (pattern : Pattern) :
    ¬ typedCompilerTheory.MultiStep
      (inCalculus state) (inLanguage pattern) := by
  change ¬ (GSLT.disjointSum flatObjectTheory
    (proofSearchGSLT generated)).MultiStep
      (inCalculus state) (inLanguage pattern)
  exact no_right_multiStep_to_left flatObjectTheory
    (proofSearchGSLT generated) state pattern

/-! ## Named source-to-typed composite -/

/-- The complete semantic evidence available before lowering.  Every field
refers to the same validated source-indexed calculus `generated`: object
execution is exact and terminal, proof derivations have independent displayed
meaning, the selected image is covered, and the two operational summands are
disjoint. -/
structure SourceToTypedSemanticComposite (owned : OwnedSnapshot)
    (head : String) (arity : Nat) : Type where
  objectTotal : typedCompilerTheory.MultiStep
    (inLanguage (encodeCompileLanguageControl
      (compileLanguageStart owned head arity)))
    (inLanguage (encodeCompileLanguageControl
      (.halted (compileGuards owned head arity))))
  terminalNormal : typedCompilerTheory.IsNormalForm
    (inLanguage (encodeCompileLanguageControl
      (.halted (compileGuards owned head arity))))
  terminalUnique : ∀ result,
    typedCompilerTheory.MultiStep
      (inLanguage (encodeCompileLanguageControl
        (compileLanguageStart owned head arity)))
      (inLanguage (encodeCompileLanguageControl (.halted result))) →
    result = compileGuards owned head arity
  proofSound : ∀ (model : CarrierModel) {goal : Pattern},
    Derivation generated goal → JudgmentMeaning model goal
  selectedCoverage : ∀ endpoint : RootEndpoint,
    Nonempty (GeneratedEndpointRepresentation endpoint)
  demandCoverage : CoversEveryRootEndpoint demand
  summandsDisjoint : ∀ (pattern : Pattern) (state : GoalState),
    ¬ typedCompilerTheory.Step (inLanguage pattern) (inCalculus state) ∧
      ¬ typedCompilerTheory.Step (inCalculus state) (inLanguage pattern)
  summandPathsDisjoint : ∀ (pattern : Pattern) (state : GoalState),
    ¬ typedCompilerTheory.MultiStep
        (inLanguage pattern) (inCalculus state) ∧
      ¬ typedCompilerTheory.MultiStep
        (inCalculus state) (inLanguage pattern)

/-- The qualified source-to-typed composite, assembled from independently
proved operational, semantic, and selected-image arrows. -/
def sourceToTypedSemanticComposite (owned : OwnedSnapshot)
    (head : String) (arity : Nat) :
    SourceToTypedSemanticComposite owned head arity where
  objectTotal := typedObject_total_exact owned head arity
  terminalNormal :=
    (typedObject_normal_iff_halted
      (.halted (compileGuards owned head arity))).2
      ⟨compileGuards owned head arity, rfl⟩
  terminalUnique := fun result steps =>
    typedObject_halted_result_unique owned head arity result steps
  proofSound := fun model _ derivation =>
    generated_derivation_sound model derivation
  selectedCoverage := generatedEndpoint_representable
  demandCoverage := fullDemand_coversEveryRootEndpoint
  summandsDisjoint := typedCompilerTheory_no_crossing
  summandPathsDisjoint := fun pattern state =>
    ⟨typedObject_cannot_reach_proof pattern state,
      typedProof_cannot_reach_object state pattern⟩

/-- Call-indexed crown joining the typed operational route to the independent
source observation. -/
structure SourceToTypedCallSemanticComposite (owned : OwnedSnapshot)
    (call : Call) : Type where
  semantic : SourceToTypedSemanticComposite owned call.function
    call.sourceArguments.length
  observationExact :
    executeCompilation owned call
        (compileGuards owned call.function call.sourceArguments.length) =
      sourceCallGuardObservation owned call

/-- Complete source-to-typed semantic composite for one well-formed call. -/
def sourceToTypedCallSemanticComposite (owned : OwnedSnapshot) (call : Call)
    (wellFormed : owned.snapshot.WellFormed) :
    SourceToTypedCallSemanticComposite owned call where
  semantic := sourceToTypedSemanticComposite owned call.function
    call.sourceArguments.length
  observationExact :=
    (typedObject_call_execution_exact owned call wellFormed).2

#print axioms flatObject_multiStep_iff_coldPresentation
#print axioms typedObject_multiStep_iff_compileLanguageMultiStep
#print axioms typedObject_normal_iff_halted
#print axioms typedObject_total_exact
#print axioms typedObject_halted_result_unique
#print axioms typedObject_compiled_execution_exact
#print axioms typedObject_outsideFragment_exact
#print axioms typedObject_call_execution_exact
#print axioms typedObject_cannot_reach_proof
#print axioms typedProof_cannot_reach_object
#print axioms sourceToTypedSemanticComposite
#print axioms sourceToTypedCallSemanticComposite

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSemanticComposite
