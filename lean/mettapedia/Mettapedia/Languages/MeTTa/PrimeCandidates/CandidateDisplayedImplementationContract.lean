import Mettapedia.Languages.MeTTa.PrimeCandidates.CandidateAbstractImplementationModel
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDisplayedCrown

/-!
# Displayed gradual capabilities in the abstract candidate implementation model

The abstract implementation contract already requires exact fallback codecs,
proof-relevant receipts, observation agreement, and revision-current NIK
activation.  The displayed gradual crown already proves that whole programs
and native parallel schedules live over unchanged raw computations.  This
module closes the precise join between those results.

There is no new runner here.  Complete program plans instantiate the exact
source-codec boundary.  Displayed rho states are fed to the existing worldwise
implementation model.  Current exact evidence therefore realizes its native
schedule, while suspended, refuted, or stale evidence realizes the exact raw
branch.  Staleness of the implementation admission is a second independent
axis: it prevents activation and leaves that raw input available through the
model's exact fallback codec.

The contested-world control is the implementation-level non-collapse law.
Two distinct raw communication indices compile as two ordered occurrences;
maximal-native selection inside either fibre cannot become branch selection.
-/

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.CandidateDisplayedImplementationContract

open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability
open Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability.State
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDisplayedCrown
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeParallelGradualGuarantee
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeParallelNIKAdmission
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeParallelNondeterministicWorlds
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeProgramElaboration
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeProgramGradualGuarantee
open Mettapedia.Languages.MeTTa.PrimeCandidates.CandidateAbstractImplementationModel
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-! ## Complete program plans at the exact fallback boundary -/

/-- Raw planning is an exact representation of complete authored programs.
Decoding reads the retained source field; the planner's proof establishes that
its internal rows erase to the same source. -/
def programPlanCodec : ExactCodec SourceProgram where
  Representation := ProgramPlan
  encode := prepareProgram rawPolicy
  decode := ProgramPlan.source
  decode_encode := fun _ => rfl

@[simp] theorem programPlanCodec_decode_encode (source : SourceProgram) :
    programPlanCodec.decode (programPlanCodec.encode source) = source :=
  programPlanCodec.decode_encode source

/-- Every displayed exact program package decodes to the raw program indexing
its fibre. -/
theorem ProgramEvidence.codec_adequate {source : SourceProgram}
    (evidence : ProgramEvidence source) :
    programPlanCodec.decode evidence.plan = source :=
  evidence.source_eq

/-- Source-preserving promotion remains exact at the representation boundary,
independently of whether the candidate evidence matches. -/
theorem programPromotion_codec_adequate {source : SourceProgram}
    (location : SourceLocation) (typing : NativeGradualQuotation.TypingEvidence)
    (evidence : ProgramEvidence source) :
    programPlanCodec.decode
        ((programPromotionMap location typing).mapExact evidence).plan =
      source :=
  ((programPromotionMap location typing).mapExact evidence).source_eq

/-- The representation decoder observes no source change under island
promotion. -/
theorem decode_promoteProgramAt (plan : ProgramPlan)
    (location : SourceLocation)
    (typing : NativeGradualQuotation.TypingEvidence) :
    programPlanCodec.decode (promoteProgramAt plan location typing) =
      programPlanCodec.decode plan :=
  promoteProgramAt_source plan location typing

/-! ## Displayed rho states as implementation traces -/

/-- One gradual capability state becomes one source-world occurrence for the
already-established worldwise implementation model. -/
def stateTrace {Ground : Type} {source : CostConfig Ground}
    {raw : RawBranchWorld source}
    (state : State (parallelFibre Ground source) raw) :
    ExecutionTrace (ambiguousWorldObject Ground source) :=
  ⟨PUnit.unit, PUnit.unit, [worldOfState state]⟩

/-- Current implementation realizes exactly the strongest world justified by
the displayed state. -/
@[simp] theorem compile_stateTrace {Ground : Type}
    {source : CostConfig Ground} {raw : RawBranchWorld source}
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (state : State (parallelFibre Ground source) raw) :
    ((CandidateAbstractImplementationModel.Worldwise.model Ground dependencies
        revision source).compileTrace
      (CandidateAbstractImplementationModel.Worldwise.active Ground dependencies
        revision source)
      (stateTrace state)).2.2 =
      [realize (worldOfState state)] :=
  rfl

/-- Exact fallback recovers the complete displayed source-world occurrence,
not merely its target or scheduled result. -/
theorem fallback_stateTrace {Ground : Type}
    {source : CostConfig Ground} {raw : RawBranchWorld source}
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (state : State (parallelFibre Ground source) raw) :
    let model := CandidateAbstractImplementationModel.Worldwise.model Ground
      dependencies revision source
    let prepared := model.prepare (stateTrace state)
    model.rawCodec.decode prepared.fallback = stateTrace state := by
  exact (CandidateAbstractImplementationModel.Worldwise.model Ground dependencies
    revision source).prepare (stateTrace state) |>.fallback_adequate

/-- Compilation preserves the visible target of the raw branch indexing the
gradual state. -/
theorem compile_stateTrace_target {Ground : Type}
    {source : CostConfig Ground} {raw : RawBranchWorld source}
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (state : State (parallelFibre Ground source) raw) :
    (((CandidateAbstractImplementationModel.Worldwise.model Ground dependencies
        revision source).compileTrace
      (CandidateAbstractImplementationModel.Worldwise.active Ground dependencies
        revision source)
      (stateTrace state)).2.2.map RealizedWorld.target) =
      [raw.2.1] := by
  rw [compile_stateTrace]
  exact congrArg (fun target => [target])
    (realized_worldOfState_target state)

/-- Evidence staleness and implementation staleness are independent, and both
fail open.  The former returns the displayed world to its raw branch; the
latter prevents NIK activation; the exact fallback codec remains available. -/
theorem stale_evidence_and_model_preserve_raw
    {Ground : Type} {source : CostConfig Ground}
    {raw : RawBranchWorld source}
    (dependencies : DependencySystem)
    (revision candidateRevision : dependencies.Revision)
    (modelStale :
      (CandidateAbstractImplementationModel.Worldwise.model Ground dependencies
        revision source).StaleAt candidateRevision)
    {EvidenceRevision : Type} [DecidableEq EvidenceRevision]
    {cached current : EvidenceRevision} (evidenceStale : cached ≠ current)
    (state : State (parallelFibre Ground source) raw) :
    let model := CandidateAbstractImplementationModel.Worldwise.model Ground
      dependencies revision source
    let staleState := state.activateAt cached current
    let prepared := model.prepare (stateTrace staleState)
    (¬ model.admission.Active candidateRevision) ∧
      worldOfState staleState = .raw raw ∧
      model.rawCodec.decode prepared.fallback = stateTrace staleState := by
  dsimp only
  constructor
  · exact
      (CandidateAbstractImplementationModel.Worldwise.model Ground dependencies
        revision source).stale_prevents_activation modelStale
  · constructor
    · exact stale_state_realizes_raw evidenceStale state
    · exact
        (CandidateAbstractImplementationModel.Worldwise.model Ground dependencies
          revision source).prepare
            (stateTrace (state.activateAt cached current)) |>.fallback_adequate

/-! ## Separated positive control -/

namespace SeparatedCanary

open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDisplayedCrown.Examples.Separated
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteractionFamilyFibration.Examples
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteractionFibration.Examples
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeParallelNIKAdmission.Examples.Separated

/-- Current exact evidence compiles to the established certified one-wave
schedule without an interior checker. -/
theorem current_exact_compiles_scheduled
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    ((CandidateAbstractImplementationModel.Worldwise.model Ground dependencies
        revision source).compileTrace
      (CandidateAbstractImplementationModel.Worldwise.active Ground dependencies
        revision source)
      (stateTrace pairState)).2.2 =
      [RealizedWorld.scheduled (compileFamilyExecution pairExecution)] :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Stale exact evidence compiles as the original raw rho branch at a current
implementation revision. -/
theorem stale_exact_compiles_raw
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    ((CandidateAbstractImplementationModel.Worldwise.model Ground dependencies
        revision source).compileTrace
      (CandidateAbstractImplementationModel.Worldwise.active Ground dependencies
        revision source)
      (stateTrace (pairState.activateAt false true))).2.2 =
      [RealizedWorld.raw (rawOfCertified pairExecution)] := by
  rw [activateAt_stale (by decide : false ≠ true)]
  rfl

end SeparatedCanary

/-! ## Contested non-collapse control -/

namespace ContestedCanary

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDisplayedCrown.Examples.Contested
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteractionParallelWorlds.Examples.Contested

def aliceState :
    State (parallelFibre ExampleGround contestedSource) aliceRaw :=
  .suspended

def competitorState :
    State (parallelFibre ExampleGround contestedSource) competitorRaw :=
  .suspended

def contestedTrace :
    ExecutionTrace (ambiguousWorldObject ExampleGround contestedSource) :=
  ⟨PUnit.unit, PUnit.unit,
    [worldOfState aliceState, worldOfState competitorState]⟩

/-- The abstract implementation maps both contested occurrences in source
order and retains their distinct targets.  Native realization selects neither
communication branch. -/
theorem current_implementation_preserves_contested_occurrences
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    let output :=
      ((CandidateAbstractImplementationModel.Worldwise.model ExampleGround
          dependencies revision contestedSource).compileTrace
        (CandidateAbstractImplementationModel.Worldwise.active ExampleGround
          dependencies revision contestedSource)
        contestedTrace).2.2
    output.length = 2 ∧
      output.map RealizedWorld.target =
        [aliceRaw.2.1, competitorRaw.2.1] ∧
      aliceRaw.2.1 ≠ competitorRaw.2.1 := by
  dsimp only [contestedTrace, aliceState, competitorState, stateTrace,
    CandidateAbstractImplementationModel.Worldwise.model,
    CandidateAbstractImplementationModel.Worldwise.active,
    AdmittedExecutionModel.compileTrace,
    NativeParallelNondeterministicWorlds.admittedAt, observedRealization,
    realizationRefinement, ExecutionTrace.map, realizeWorlds, worldOfState,
    realize, RealizedWorld.target]
  exact ⟨rfl, rfl, branchWorld_targets_differ⟩

end ContestedCanary

#print axioms programPlanCodec_decode_encode
#print axioms programPromotion_codec_adequate
#print axioms compile_stateTrace
#print axioms fallback_stateTrace
#print axioms compile_stateTrace_target
#print axioms stale_evidence_and_model_preserve_raw
#print axioms SeparatedCanary.current_exact_compiles_scheduled
#print axioms SeparatedCanary.stale_exact_compiles_raw
#print axioms ContestedCanary.current_implementation_preserves_contested_occurrences

end Mettapedia.Languages.MeTTa.PrimeCandidates.CandidateDisplayedImplementationContract
