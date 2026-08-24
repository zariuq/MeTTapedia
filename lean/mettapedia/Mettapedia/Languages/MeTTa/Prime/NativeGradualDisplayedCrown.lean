import Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentGuarantee
import Mettapedia.Languages.MeTTa.Prime.NativeIndexedFamilyGradualTransport
import Mettapedia.Languages.MeTTa.Prime.NativeConversionPathGradualTransport

/-!
# The displayed gradual crown for native Prime capabilities

Prime's gradual domains share one construction rather than one universal
runner.  An unchanged raw computation is the base point of a displayed
fibre; exact native structure, suspended evidence, and local blame live over
that same point.  Existing dependent term formation, interaction,
indexed-family construction, and conversion paths already have this form.

This module places the two operational outliers in the same structure.

* A complete authored program is the raw point.  A source-preserving program
  plan is exact evidence over that point, and island promotion is an exact map
  whose raw action is identity.
* A proof-relevant rho branch is the raw point.  A certified finite-family
  schedule is exact evidence over that particular branch.  Suspension,
  invalidated blame, or stale evidence realizes the raw branch; exact evidence
  realizes the certified world.

The raw index is the non-collapse boundary.  In particular, two competing
rho communications inhabit different points of the fibre, so adding native
parallel evidence cannot select, merge, or serialize them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NativeGradualDisplayedCrown

open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability
open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State
open Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentGuarantee
open Mettapedia.Languages.MeTTa.Prime.NativeGradualQuotation
open Mettapedia.Languages.MeTTa.Prime.NativeProgramElaboration
open Mettapedia.Languages.MeTTa.Prime.NativeProgramGradualGuarantee
open Mettapedia.Languages.MeTTa.Prime.NativeParallelGradualGuarantee
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKAdmission
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-! ## Complete authored programs as a displayed gradual capability -/

/-- Exact evidence over a complete source program is a proof-carrying plan
whose erasure names that exact source.  The equality is retained explicitly
so evidence can be reindexed after a source-preserving plan transformation. -/
structure ProgramEvidence (source : SourceProgram) where
  plan : ProgramPlan
  source_eq : plan.source = source

/-- The raw carrier is the complete authored program, not a selected island.
Exact evidence may change the plan but cannot change that carrier. -/
def programFibre : Fibre where
  Raw := SourceProgram
  Exact := ProgramEvidence

/-- Every existing proof-carrying plan inhabits the fibre over its own complete
authored source. -/
def ProgramEvidence.ofPlan (plan : ProgramPlan) :
    (programFibre.Exact plan.source) :=
  ⟨plan, rfl⟩

/-- Promote one island inside exact program evidence.  The program-level
source theorem supplies the reindexing proof; no parser, checker, or runner is
invoked by this construction. -/
def ProgramEvidence.promote {source : SourceProgram}
    (location : SourceLocation) (typing : TypingEvidence)
    (evidence : ProgramEvidence source) : ProgramEvidence source where
  plan := promoteProgramAt evidence.plan location typing
  source_eq :=
    (promoteProgramAt_source evidence.plan location typing).trans
      evidence.source_eq

/-- Island promotion is an exact constructional map with identity raw action. -/
def programPromotionMap (location : SourceLocation)
    (typing : TypingEvidence) : ExactMap programFibre programFibre where
  mapRaw := id
  mapExact := ProgramEvidence.promote location typing

@[simp] theorem programPromotionMap_raw (location : SourceLocation)
    (typing : TypingEvidence) (source : SourceProgram) :
    (programPromotionMap location typing).mapRaw source = source :=
  rfl

/-- Program promotion earns the generic safe-transport laws.  Exact evidence
is constructed directly; unsupported blame is invalidated rather than
transported to a different plan. -/
def programPromotionSafeTransportLaws (location : SourceLocation)
    (typing : TypingEvidence) :
    SafeTransportLaws (programPromotionMap location typing) :=
  safeTransportLaws _

/-- Revision activation and whole-program island promotion commute because
both are operations on evidence over the same unchanged source. -/
theorem programPromotion_revision_commutes
    (location : SourceLocation) (typing : TypingEvidence)
    {source : SourceProgram} {Revision : Type} [DecidableEq Revision]
    (cached current : Revision) (state : State programFibre source) :
    mapSafe (programPromotionMap location typing)
        (state.activateAt cached current) =
      (mapSafe (programPromotionMap location typing) state).activateAt
        cached current :=
  mapSafe_activateAt _ cached current state

/-! ### A real positive and cross-candidate negative -/

/-- A one-command complete program containing the established suspended
receipt occurrence. -/
def receiptProgramSource : SourceProgram :=
  [(1, .eval receiptSource)]

def receiptProgramPlan : ProgramPlan where
  source := receiptProgramSource
  planned := [(1, .eval receiptCheckedPattern)]
  erases := rfl

def receiptProgramEvidence : ProgramEvidence receiptProgramSource :=
  ProgramEvidence.ofPlan receiptProgramPlan

/-- A small observation used only to expose the operational preparation mode
of the unique command. -/
def singletonEvalKind? (program : ProgramPlan) : Option PreparationMode :=
  match program.planned with
  | [(_, .eval planned)] => some planned.kind
  | _ => none

/-- Matching intrinsic evidence promotes the selected checked occurrence
inside the complete-program fibre. -/
theorem receipt_program_exact_promotion :
    singletonEvalKind?
        ((programPromotionMap receiptLocation receiptEvidence).mapExact
          receiptProgramEvidence).plan =
      some .eager := by
  rfl

/-- Negative control: a valid universe typing package cannot be used to
promote the receipt occurrence.  The complete program remains exact evidence,
but the selected island remains suspended. -/
theorem universe_program_evidence_does_not_cross_promote :
    singletonEvalKind?
        ((programPromotionMap receiptLocation universeEvidence).mapExact
          receiptProgramEvidence).plan =
      some .checked := by
  change some
      (promoteAt receiptLocation universeEvidence receiptCheckedPattern).kind =
    some .checked
  rw [universe_evidence_cannot_promote_receipt]
  rfl

/-! ## Certified rho schedules as a displayed gradual capability -/

/-- Exact parallel evidence is indexed by its complete proof-relevant raw rho
branch.  The target and certified execution remain explicit, while `erases`
prevents evidence for one branch from being attached to another. -/
structure ParallelEvidence (Ground : Type) (source : CostConfig Ground)
    (raw : RawBranchWorld source) where
  target : CostConfig Ground
  execution : AnyCertifiedFamilyExecution Ground source target
  erases : rawOfCertified execution = raw

/-- Native parallel scheduling is displayed over already-authorized rho
branches. -/
def parallelFibre (Ground : Type) (source : CostConfig Ground) : Fibre where
  Raw := RawBranchWorld source
  Exact := ParallelEvidence Ground source

/-- A certified execution is exact evidence over its own proof-relevant raw
erasure. -/
def ParallelEvidence.ofCertified {Ground : Type}
    {source target : CostConfig Ground}
    (execution : AnyCertifiedFamilyExecution Ground source target) :
    (parallelFibre Ground source).Exact (rawOfCertified execution) :=
  ⟨target, execution, rfl⟩

/-- Interpret one displayed evidence state as its strongest justified world.
Suspension and blame retain raw execution.  Exact evidence selects only the
schedule stored over that same raw branch. -/
def worldOfState {Ground : Type} {source : CostConfig Ground}
    {raw : RawBranchWorld source} :
    State (parallelFibre Ground source) raw -> ExecutionWorld Ground source
  | .suspended => .raw raw
  | .exact evidence => .parallel evidence.execution
  | .refuted _ => .raw raw

/-- Every gradual state has exactly the raw branch indexing its fibre. -/
@[simp] theorem rawProjection_worldOfState {Ground : Type}
    {source : CostConfig Ground} {raw : RawBranchWorld source}
    (state : State (parallelFibre Ground source) raw) :
    rawProjection (worldOfState state) = raw := by
  cases state with
  | suspended => rfl
  | exact evidence => exact evidence.erases
  | refuted blame => rfl

/-- Native scheduling and its subsequent realization preserve the visible
target of the indexed raw rho branch. -/
theorem realized_worldOfState_target {Ground : Type}
    {source : CostConfig Ground} {raw : RawBranchWorld source}
    (state : State (parallelFibre Ground source) raw) :
    (realize (worldOfState state)).target = raw.2.1 := by
  rw [realize_target]
  cases state with
  | suspended => rfl
  | refuted blame => rfl
  | exact evidence =>
      have sameTarget := congrArg
        (fun branch : RawBranchWorld source => branch.2.1)
        evidence.erases
      change evidence.target = raw.2.1
      simpa only [rawOfCertified_target] using sameTarget

/-- Interpreting a gradual state always refines its indexed raw branch. -/
def rawRefinesWorldOfState {Ground : Type} {source : CostConfig Ground}
    {raw : RawBranchWorld source}
    (state : State (parallelFibre Ground source) raw) :
    WorldRefines (.raw raw) (worldOfState state) := by
  cases state with
  | suspended => exact .refl (.raw raw)
  | refuted blame => exact .refl (.raw raw)
  | exact evidence =>
      rcases evidence with ⟨target, execution, rfl⟩
      exact .certify execution

/-- Stale scheduling evidence returns to the exact raw branch rather than
refuting or serializing it. -/
theorem stale_state_realizes_raw {Ground : Type}
    {source : CostConfig Ground} {raw : RawBranchWorld source}
    {Revision : Type} [DecidableEq Revision]
    {cached current : Revision} (stale : cached ≠ current)
    (state : State (parallelFibre Ground source) raw) :
    worldOfState (state.activateAt cached current) = .raw raw := by
  rw [activateAt_stale stale]
  rfl

/-! ### Separated positive and contested negative -/

namespace Examples.Separated

open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKAdmission.Examples.Separated
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds.Examples.Separated
open Mettapedia.Languages.MeTTa.Prime.NativeParallelGradualGuarantee.Examples.Separated

def pairEvidence :
    (parallelFibre Ground source).Exact (rawOfCertified pairExecution) :=
  ParallelEvidence.ofCertified pairExecution

def pairState :
    State (parallelFibre Ground source) (rawOfCertified pairExecution) :=
  .exact pairEvidence

def pairSuspended :
    State (parallelFibre Ground source) (rawOfCertified pairExecution) :=
  .suspended

/-- Exact evidence realizes the established one-wave certified world. -/
@[simp] theorem pair_exact_world : worldOfState pairState = world :=
  rfl

/-- The same raw index without current evidence is the ordinary rho branch. -/
theorem pair_suspended_world : worldOfState pairSuspended = rawPairWorld := by
  change ExecutionWorld.raw (rawOfCertified pairExecution) = rawPairWorld
  simpa [world, deopt, rawProjection] using deopt_world_eq_rawPairWorld

/-- A revision change removes only native scheduling evidence. -/
theorem pair_stale_returns_raw (cached current : Bool)
    (stale : cached ≠ current) :
    worldOfState (pairState.activateAt cached current) = rawPairWorld := by
  rw [stale_state_realizes_raw stale]
  exact pair_suspended_world

end Examples.Separated

namespace Examples.Contested

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionParallelWorlds.Examples.Contested
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds.Examples.Contested

def aliceRaw : RawBranchWorld contestedSource := aliceWorld PUnit.unit

def competitorRaw : RawBranchWorld contestedSource :=
  competitorWorld PUnit.unit

/-- The two legal communications are distinct raw indices, not two precision
states over one branch. -/
theorem aliceRaw_ne_competitorRaw : aliceRaw ≠ competitorRaw := by
  intro same
  apply branchWorld_targets_differ
  exact congrArg (fun branch : RawBranchWorld contestedSource => branch.2.1)
    same

/-- Negative control: suspension retains both contested alternatives as
distinct worlds.  The shared gradual fibre supplies no branch-selection
operation. -/
theorem suspended_contested_worlds_remain_distinct :
    worldOfState
        (State.suspended :
          State (parallelFibre ExampleGround contestedSource) aliceRaw) ≠
      worldOfState
        (State.suspended :
          State (parallelFibre ExampleGround contestedSource) competitorRaw) := by
  intro same
  apply aliceRaw_ne_competitorRaw
  exact ExecutionWorld.raw.inj same

end Examples.Contested

#print axioms programPromotion_revision_commutes
#print axioms receipt_program_exact_promotion
#print axioms universe_program_evidence_does_not_cross_promote
#print axioms rawProjection_worldOfState
#print axioms realized_worldOfState_target
#print axioms rawRefinesWorldOfState
#print axioms stale_state_realizes_raw
#print axioms Examples.Separated.pair_stale_returns_raw
#print axioms Examples.Contested.suspended_contested_worlds_remain_distinct

end Mettapedia.Languages.MeTTa.Prime.NativeGradualDisplayedCrown
