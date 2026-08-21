import Mettapedia.Languages.MeTTa.Prime.PrimeMotivationProgramPackages
import Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationAdmission

/-!
# A scoped gradual guarantee for authored Prime programs

This guarantee is deliberately about the current program planner and
interaction seam.  It does not add unknown terms to kernel conversion.

Replacing selected planned islands with intrinsically typed islands leaves
the complete authored program unchanged.  Consequently every observation or
raw reduction defined on that source program is preserved.  Type conflicts
and exact licenses retain the existing seam laws: `conflict_persists` and
`license_rigid`.  The program layer only transports those laws through one
source-preserving island substitution.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeProgramGradualGuarantee

open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
open Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core
open Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Seam
open Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan
open Mettapedia.Languages.MeTTa.Prime.NativeGradualQuotation
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionSeam
open Mettapedia.Languages.MeTTa.Prime.NativeProgramElaboration
open Mettapedia.Languages.MeTTa.Prime.NativeTypedQuotation
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationAdmission

/-! ## One program-level island substitution -/

/-- Apply a source-preserving island transformation to every planned command.
The transform may inspect exact locations and therefore still replace only a
single selected occurrence. -/
def mapPlannedRows (transform : PlannedPattern → PlannedPattern) :
    PlannedRows → PlannedRows
  | [] => []
  | row :: rows =>
      (row.1, row.2.map transform) :: mapPlannedRows transform rows

theorem eraseCommand_map_of_preserves
    (transform : PlannedPattern → PlannedPattern)
    (preserves : ∀ planned, (transform planned).erase = planned.erase)
    (command : PlannedCommand) :
    eraseCommand (command.map transform) = eraseCommand command := by
  unfold eraseCommand
  rw [ProgramCommand.map_map]
  congr 1
  funext planned
  exact preserves planned

theorem eraseRows_mapPlannedRows
    (transform : PlannedPattern → PlannedPattern)
    (preserves : ∀ planned, (transform planned).erase = planned.erase)
    (rows : PlannedRows) :
    eraseRows (mapPlannedRows transform rows) = eraseRows rows := by
  induction rows with
  | nil => rfl
  | cons row rows inductionHypothesis =>
      rcases row with ⟨line, command⟩
      simp only [mapPlannedRows, eraseRows, List.map_cons]
      rw [eraseCommand_map_of_preserves transform preserves command]
      exact congrArg (List.cons (line, eraseCommand command))
        inductionHypothesis

/-- Lift one source-preserving island transformation to a new proof-carrying
program plan.  The source field is definitionally shared. -/
def refineProgramIslands (program : ProgramPlan)
    (transform : PlannedPattern → PlannedPattern)
    (preserves : ∀ planned, (transform planned).erase = planned.erase) :
    ProgramPlan where
  source := program.source
  planned := mapPlannedRows transform program.planned
  erases := by
    rw [eraseRows_mapPlannedRows transform preserves, program.erases]

/-- Promote exactly the requested location to intrinsic evidence, but only
when the evidence was produced for that occurrence's retained native
candidate.  A location match alone is not authority: evidence for another
candidate leaves the plan unchanged.  Raw execution always retains the
island's original source. -/
def promoteAt (location : SourceLocation) (evidence : TypingEvidence)
    (planned : PlannedPattern) : PlannedPattern :=
  if planned.location = location then
    if evidence.source = planned.plan.nativeCandidate then
      { planned with
        plan := .typed planned.erase evidence
        failure? := none }
    else planned
  else planned

theorem promoteAt_preserves_source (location : SourceLocation)
    (evidence : TypingEvidence) (planned : PlannedPattern) :
    (promoteAt location evidence planned).erase = planned.erase := by
  by_cases selected : planned.location = location
  · by_cases candidateEq : evidence.source = planned.plan.nativeCandidate
    · simp [promoteAt, selected, candidateEq, PlannedPattern.erase,
        IslandPlan.erase]
    · simp [promoteAt, selected, candidateEq]
  · simp [promoteAt, selected]

theorem promoteAt_other (location : SourceLocation)
    (evidence : TypingEvidence) (planned : PlannedPattern)
    (different : planned.location ≠ location) :
    promoteAt location evidence planned = planned := by
  simp [promoteAt, different]

theorem promoteAt_selected_is_typed (location : SourceLocation)
    (evidence : TypingEvidence) (planned : PlannedPattern)
    (selected : planned.location = location)
    (candidateEq : evidence.source = planned.plan.nativeCandidate) :
    (promoteAt location evidence planned).kind = .eager := by
  simp [promoteAt, selected, candidateEq, PlannedPattern.kind,
    IslandPlan.kind]

/-- Negative control: valid intrinsic evidence for a different native
candidate cannot type the selected occurrence. -/
theorem promoteAt_candidate_mismatch_is_ignored (location : SourceLocation)
    (evidence : TypingEvidence) (planned : PlannedPattern)
    (selected : planned.location = location)
    (mismatch : evidence.source ≠ planned.plan.nativeCandidate) :
    promoteAt location evidence planned = planned := by
  simp [promoteAt, selected, mismatch]

def promoteProgramAt (program : ProgramPlan)
    (location : SourceLocation) (evidence : TypingEvidence) : ProgramPlan :=
  refineProgramIslands program (promoteAt location evidence)
    (promoteAt_preserves_source location evidence)

@[simp] theorem promoteProgramAt_source (program : ProgramPlan)
    (location : SourceLocation) (evidence : TypingEvidence) :
    (promoteProgramAt program location evidence).source = program.source := rfl

/-- Every raw observation is invariant under successful island promotion. -/
theorem promoteAt_preserves_raw_observation (program : ProgramPlan)
    (location : SourceLocation) (evidence : TypingEvidence)
    (observeRaw : SourceProgram → Observation) :
    observeRaw
        (eraseRows (promoteProgramAt program location evidence).planned) =
      observeRaw (eraseRows program.planned) := by
  rw [(promoteProgramAt program location evidence).erases, program.erases]
  rw [promoteProgramAt_source]

/-- In particular, promotion cannot remove an unrelated source reduction.
The reduction relation is arbitrary because both executable plan erasures are
the exact authored program. -/
theorem promoteAt_cannot_remove_raw_reduction (program : ProgramPlan)
    (location : SourceLocation) (evidence : TypingEvidence)
    (RawReduces : SourceProgram → SourceProgram → Prop)
    (target : SourceProgram)
    (step : RawReduces (eraseRows program.planned) target) :
    RawReduces
      (eraseRows (promoteProgramAt program location evidence).planned)
      target := by
  rw [(promoteProgramAt program location evidence).erases]
  rw [promoteProgramAt_source]
  rw [← program.erases]
  exact step

/-! ## The existing gradual seam, lifted through substitution -/

/-- A witnessed type conflict survives precision refinement while an island
is promoted; source preservation and conflict persistence are one result. -/
theorem promoteAt_preserves_source_and_conflict
    (program : ProgramPlan) (location : SourceLocation)
    (evidence : TypingEvidence)
    {actual actual' expected expected' : Ty}
    (actualRefines : Refines actual' actual)
    (expectedRefines : Refines expected' expected)
    (conflict : consistent? actual expected = false) :
    (promoteProgramAt program location evidence).source = program.source ∧
      consistent? actual' expected' = false :=
  ⟨rfl, interaction_conflict_persists actualRefines expectedRefines conflict⟩

/-- Exact type indices remain rigid across the same program substitution.
This is `license_rigid`, not a second program-specific gradual law. -/
theorem promoteAt_preserves_source_and_exact_indices
    (program : ProgramPlan) (location : SourceLocation)
    (evidence : TypingEvidence) (license : OptLicense)
    {actual' expected' : Ty}
    (actualRefines : Refines actual' license.actual)
    (expectedRefines : Refines expected' license.expected) :
    (promoteProgramAt program location evidence).source = program.source ∧
      actual' = license.actual ∧ expected' = license.expected := by
  exact ⟨rfl, license_rigid license actualRefines expectedRefines⟩

/-! ## Demand-time named failure and exact-key cache scope -/

/-- A suspended rejected island has no eager diagnostic before demand; demand
then caches the existing structured child-path blame. -/
theorem rejected_island_failure_is_demanded :
    (checkedPlan rejectedKey).run id = rejectedSource ∧
      (rejectedSuspended.demandCheck typingChecker (0 : Nat)).1 =
        .cachedStableFault rejectedSuspended.origin rejectedBlame :=
  ⟨rejected_blame_does_not_gate_raw_execution,
    rejected_demand_caches_structured_blame⟩

/-- Equal complete typing keys imply equality of every cache coordinate. -/
theorem typingKey_eq_coordinates {left right : TypingKey}
    (same : left = right) :
    left.occurrence = right.occurrence ∧
      left.revision = right.revision ∧
      left.dialect = right.dialect ∧
      left.expected = right.expected ∧
      left.authority = right.authority := by
  subst right
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A revision change makes exact-key cache sharing impossible. -/
theorem typingKey_ne_of_revision_ne {left right : TypingKey}
    (changed : left.revision ≠ right.revision) : left ≠ right := by
  intro same
  exact changed (congrArg CheckKey.revision same)

/-- The existing exact sharing scheme therefore cannot reuse evidence or
blame across a changed revision. -/
theorem no_exact_cache_share_across_revision {left right : TypingKey}
    (changed : left.revision ≠ right.revision) :
    left ≠ right := by
  exact typingKey_ne_of_revision_ne changed

/-! ## Optional acceleration remains downstream of source preservation -/

theorem preparation_may_authorize_fast_path {Source : Type}
    (spec : OptimizationSpec Source) (source : Source)
    (authority : ExactAuthority spec.kind source)
    (shape : spec.ShapeEvidence source)
    (recognized : spec.recognize source = some shape) :
    prepare spec source (some authority) = .optimized authority shape := by
  simp [prepare, recognized]

/-! ## Occurrence-faithful promotion controls -/

def receiptLocation : SourceLocation := ⟨0, 1, 0⟩

def receiptCheckedPattern : PlannedPattern where
  location := receiptLocation
  source := receiptSource
  plan := .checked receiptSource receiptKey
  failure? := none

/-- Positive control: matching evidence promotes the exact checked
occurrence. -/
theorem receipt_matching_evidence_promotes :
    (promoteAt receiptLocation receiptEvidence receiptCheckedPattern).kind =
      .eager := by
  apply promoteAt_selected_is_typed
  · rfl
  · rfl

def universeSource : RuntimePattern :=
  metta% petta "(native:u0)"

def universeTyping : ClosedTyping := by
  exact native% petta "(native:u0)"

def universeEvidence : TypingEvidence :=
  ⟨universeSource, universeTyping, rfl⟩

/-- Negative control: an independently valid universe typing package cannot
be attached to the selected receipt occurrence. -/
theorem universe_evidence_cannot_promote_receipt :
    promoteAt receiptLocation universeEvidence receiptCheckedPattern =
      receiptCheckedPattern := by
  apply promoteAt_candidate_mismatch_is_ignored
  · rfl
  · simp [universeEvidence, universeSource, receiptCheckedPattern, receiptKey,
      receiptSource, NativeGradualQuotation.key, IslandPlan.nativeCandidate]

#print axioms eraseRows_mapPlannedRows
#print axioms promoteProgramAt_source
#print axioms promoteAt_cannot_remove_raw_reduction
#print axioms promoteAt_preserves_source_and_conflict
#print axioms promoteAt_preserves_source_and_exact_indices
#print axioms rejected_island_failure_is_demanded
#print axioms no_exact_cache_share_across_revision
#print axioms preparation_may_authorize_fast_path
#print axioms receipt_matching_evidence_promotes
#print axioms universe_evidence_cannot_promote_receipt

end Mettapedia.Languages.MeTTa.Prime.NativeProgramGradualGuarantee
