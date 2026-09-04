import Mettapedia.GSLT.Core.SemanticTransport
import Mettapedia.GSLT.Dynamics.ContextualEffectValuation
import Mettapedia.GSLT.Dynamics.DependentInteractionChoice
import Mettapedia.GSLT.Dynamics.ObserverSemanticTransport
import Mettapedia.TypeTheory.DisplayedEvidence

/-!
# Evidence-indexed branching with a path-expanding realization

This module is one cross-layer canary rather than a language definition.  It
connects a genuinely varying family of exact evidence, occurrence-retaining
dependent choice, contextual event history, observer-relative erasure,
work/span valuation, and a non-identity operational realization.

Two source alternatives have the same visible answer.  Their exact evidence
fibres differ, their occurrence identities remain distinct, and their target
paths have different lengths.  A constant denotation is nevertheless
conserved by both systems and forms a commuting denotation square.  Thus
semantic adequacy for the selected meaning does not authorize erasure of
evidence, occurrence, history, or cost.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization

open Mettapedia.Algebra
open Mettapedia.Cybernetics
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Core.InteractionEvent.InteractionPresentation
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ContextualEffectValuation
open Mettapedia.GSLT.Dynamics.DependentInteractionChoice
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory.DisplayedEvidence

/-! ## Source and target dynamics -/

/-- A branching source with two completed occurrences. -/
inductive SourceTerm where
  | entry
  | leftDone
  | rightDone
deriving DecidableEq, Repr

/-- The two primitive source branches retain distinct endpoints. -/
inductive SourceStep : SourceTerm → SourceTerm → Prop where
  | left : SourceStep .entry .leftDone
  | right : SourceStep .entry .rightDone

/-- The source branching system. -/
def sourceSystem : GSLT where
  Term := SourceTerm
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := SourceStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- The target exposes one administrative state on the left branch. -/
inductive TargetTerm where
  | entry
  | leftPrepared
  | leftDone
  | rightDone
deriving DecidableEq, Repr

/-- The left source step expands to two target steps; the right remains one. -/
inductive TargetStep : TargetTerm → TargetTerm → Prop where
  | prepareLeft : TargetStep .entry .leftPrepared
  | finishLeft : TargetStep .leftPrepared .leftDone
  | finishRight : TargetStep .entry .rightDone

/-- The target system with an explicit administrative transition. -/
def targetSystem : GSLT where
  Term := TargetTerm
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := TargetStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Direct mapping of source states to their target representatives. -/
def mapTerm : SourceTerm → TargetTerm
  | .entry => .entry
  | .leftDone => .leftDone
  | .rightDone => .rightDone

def leftTargetPath :
    ExecutionPath targetSystem TargetTerm.entry TargetTerm.leftDone :=
  .cons ⟨TargetStep.prepareLeft⟩
    (.cons ⟨TargetStep.finishLeft⟩ (.refl TargetTerm.leftDone))

def rightTargetPath :
    ExecutionPath targetSystem TargetTerm.entry TargetTerm.rightDone :=
  .cons ⟨TargetStep.finishRight⟩ (.refl TargetTerm.rightDone)

/-- The target path depends on source and target data, never on the proof of a
proposition-valued source step.  Occurrence evidence remains in the separate
Type-valued interaction layer below. -/
def realizeStepPath : (source target : SourceTerm) →
    SourceStep source target →
      ExecutionPath targetSystem (mapTerm source) (mapTerm target)
  | .entry, .entry, step => False.elim (by cases step)
  | .entry, .leftDone, _step => leftTargetPath
  | .entry, .rightDone, _step => rightTargetPath
  | .leftDone, .entry, step => False.elim (by cases step)
  | .leftDone, .leftDone, step => False.elim (by cases step)
  | .leftDone, .rightDone, step => False.elim (by cases step)
  | .rightDone, .entry, step => False.elim (by cases step)
  | .rightDone, .leftDone, step => False.elim (by cases step)
  | .rightDone, .rightDone, step => False.elim (by cases step)

/-- A genuine path-valued realization: one source transition is expanded. -/
def realization : OperationalRealization sourceSystem targetSystem where
  mapTerm := mapTerm
  mapEquiv := fun equal => congrArg mapTerm equal
  mapStep := realizeStepPath _ _

/-- A proposition-valued semantic step cannot secretly select a target path
by proof identity.  Occurrence-sensitive selection therefore belongs in the
separate Type-valued interaction interface. -/
theorem realization_step_proof_irrelevant
    {source target : SourceTerm}
    (first second : sourceSystem.Step source target) :
    realization.mapStep first = realization.mapStep second := by
  have equal : first = second := Subsingleton.elim _ _
  subst second
  rfl

def leftSourcePath :
    ExecutionPath sourceSystem SourceTerm.entry SourceTerm.leftDone :=
  .cons ⟨SourceStep.left⟩ (.refl SourceTerm.leftDone)

def rightSourcePath :
    ExecutionPath sourceSystem SourceTerm.entry SourceTerm.rightDone :=
  .cons ⟨SourceStep.right⟩ (.refl SourceTerm.rightDone)

@[simp] theorem realization_left_path :
    realization.mapRoute leftSourcePath = leftTargetPath :=
  rfl

@[simp] theorem realization_right_path :
    realization.mapRoute rightSourcePath = rightTargetPath :=
  rfl

/-- Positive control: the realization genuinely expands one source step. -/
theorem realization_expands_left :
    leftSourcePath.length = 1 ∧
      (realization.mapRoute leftSourcePath).length = 2 :=
  ⟨rfl, rfl⟩

/-- Negative control: path expansion is not uniform across alternatives. -/
theorem realized_path_lengths_distinct :
    (realization.mapRoute leftSourcePath).length ≠
      (realization.mapRoute rightSourcePath).length := by
  decide

/-! ## Independent denotation and visible observation -/

/-- The selected denotation deliberately ignores administrative and branch
identity. -/
def sourceDenotation : SemanticInvariant sourceSystem Unit where
  denote := fun _ => ()
  equation := fun _ => rfl
  rewrite := fun _ => rfl

def targetDenotation : SemanticInvariant targetSystem Unit where
  denote := fun _ => ()
  equation := fun _ => rfl
  rewrite := fun _ => rfl

/-- The path-expanding realization preserves the independently selected
meaning. -/
def denotationSquare : DenotationSquare realization sourceDenotation
    targetDenotation id where
  commutes := fun _ => rfl

/-- A coarse source observer sees only whether execution has completed. -/
def sourceCompletion : Observer SourceTerm Bool where
  observe
    | .entry => false
    | .leftDone => true
    | .rightDone => true

/-- The corresponding target observer treats the administrative state as
incomplete. -/
def targetCompletion : Observer TargetTerm Bool where
  observe
    | .entry => false
    | .leftPrepared => false
    | .leftDone => true
    | .rightDone => true

/-- The operational realization preserves the selected completion view. -/
def completionRepresentation :
    ObserverPreservingMap SourceTerm TargetTerm Bool
      sourceCompletion targetCompletion where
  transform := mapTerm
  preserves := by
    intro term
    cases term <;> rfl

/-- The selected observer identifies the two completed alternatives. -/
theorem alternatives_have_same_visible_completion :
    sourceCompletion.observe .leftDone =
      sourceCompletion.observe .rightDone :=
  rfl

/-! ## Occurrence-indexed dependent evidence -/

/-- Occurrence sites remain distinct even when a later observer identifies
their answers. -/
inductive BranchSite where
  | left
  | right
deriving DecidableEq, Repr

/-- Evidence that a particular occurrence is one of the two source steps. -/
inductive BranchEvent : BranchSite → SourceTerm → SourceTerm → Type where
  | left : BranchEvent .left .entry .leftDone
  | right : BranchEvent .right .entry .rightDone

def interaction : InteractionPresentation sourceSystem where
  Site := BranchSite
  Event := BranchEvent
  sound := by
    intro site source target event
    cases event with
    | left => exact SourceStep.left
    | right => exact SourceStep.right

def leftEvent : interaction.Enabled .entry where
  site := .left
  target := .leftDone
  evidence := .left

def rightEvent : interaction.Enabled .entry where
  site := .right
  target := .rightDone
  evidence := .right

/-- Exact evidence varies with the operational endpoint.  The left fibre is
a singleton; the right fibre has two inhabitants. -/
def exactFamily : Family where
  Raw := SourceTerm
  Exact
    | .entry => PEmpty
    | .leftDone => PUnit
    | .rightDone => Bool

abbrev Result (target : SourceTerm) :=
  Status exactFamily Unit target

def leftStatus : Result .leftDone :=
  .established PUnit.unit

def rightStatus : Result .rightDone :=
  .established false

/-- The continuation is genuinely indexed by the selected occurrence target. -/
def continuation :
    (event : interaction.Enabled .entry) → List (Result event.target)
  | ⟨.left, .leftDone, .left⟩ => [leftStatus]
  | ⟨.right, .rightDone, .right⟩ => [rightStatus]

def leftOutcome : Outcome interaction .entry Result :=
  ⟨leftEvent, leftStatus⟩

def rightOutcome : Outcome interaction .entry Result :=
  ⟨rightEvent, rightStatus⟩

/-- Ordered dependent choice retains both event identity and indexed exact
evidence. -/
def outcomes : List (Outcome interaction .entry Result) :=
  chooseDependent (theory := sourceSystem) (presentation := interaction)
    (source := SourceTerm.entry) listEffect.{0} Result
      [leftEvent, rightEvent] continuation

theorem outcomes_exact : outcomes = [leftOutcome, rightOutcome] :=
  rfl

/-- The result family is genuinely varying across the two completed
branches, not a constant simple type with different notation. -/
theorem completed_exact_fibres_not_equivalent :
    ¬ Nonempty
      (exactFamily.Exact .leftDone ≃ exactFamily.Exact .rightDone) := by
  rintro ⟨equivalence⟩
  have preimagesEqual : equivalence.symm false = equivalence.symm true := by
    cases equivalence.symm false
    cases equivalence.symm true
    rfl
  have falseEqualsTrue : false = true := by
    simpa using congrArg equivalence.toFun preimagesEqual
  exact Bool.false_ne_true falseEqualsTrue

/-- Forget every branch, occurrence, and evidence distinction. -/
def visibleOutcome (_outcome : Outcome interaction .entry Result) : Unit := ()

theorem outcomes_have_same_visible_answers :
    outcomes.map visibleOutcome = [(), ()] :=
  rfl

/-! ## Contextual history and realization-derived work/span -/

/-- Contextual execution retains the occurrence sites as deferred intents. -/
def evidenceProgram :
    Program Unit (Outcome interaction .entry Result) BranchSite :=
  .choose
    (.intent .left (.pure leftOutcome))
    (.intent .right (.pure rightOutcome))

def visibleProgram : Program Unit Unit BranchSite :=
  Program.map visibleOutcome evidenceProgram

/-- Erasing dependent evidence and occurrences from answers does not erase
the authentic effect history. -/
theorem visible_erasure_preserves_history :
    sharedHistory visibleProgram () = sharedHistory evidenceProgram () := by
  exact sharedHistory_map visibleOutcome evidenceProgram ()

theorem evidenceProgram_history :
    sharedHistory evidenceProgram () =
      [EffectEvent.choose, EffectEvent.intent .left,
        EffectEvent.intent .right] :=
  rfl

/-- Convert one enabled event into its singleton source execution. -/
def eventPath (event : interaction.Enabled .entry) :
    ExecutionPath sourceSystem .entry event.target :=
  .cons ⟨event.step⟩ (.refl event.target)

/-- Work/span is read from the path produced by the operational realization,
not inferred from the visible endpoint. -/
def realizedEventCost (event : interaction.Enabled .entry) : WorkSpan :=
  let length := (realization.mapRoute (eventPath event)).length
  ⟨length, length⟩

def realizedOutcomeCost
    (outcome : Outcome interaction .entry Result) : WorkSpan :=
  realizedEventCost outcome.1

@[simp] theorem left_realized_cost :
    realizedOutcomeCost leftOutcome = ⟨2, 2⟩ :=
  rfl

@[simp] theorem right_realized_cost :
    realizedOutcomeCost rightOutcome = ⟨1, 1⟩ :=
  rfl

/-- Parallel valuation retains total work while exposing the shorter critical
path. -/
theorem outcomes_parallel_workSpan :
    parallelReceipt realizedOutcomeCost outcomes = ⟨3, 2⟩ :=
  rfl

/-! The contextual event history admits more than one lawful WorkSpan
valuation.  This models schedule selection after authentic events have been
retained. -/

def sequentialWorkSpanPartialMonoid : PartialMonoid WorkSpan where
  unit := 0
  op := fun first second => some (WorkSpan.sequential first second)
  unit_op := by
    intro value
    rw [WorkSpan.sequential_zero_left]
  op_unit := by
    intro value
    rw [WorkSpan.sequential_zero_right]
  op_assoc := by
    intro first second third
    simp only [Option.bind_some]
    rw [WorkSpan.sequential_assoc]

def parallelWorkSpanPartialMonoid : PartialMonoid WorkSpan where
  unit := 0
  op := fun first second => some (WorkSpan.parallel first second)
  unit_op := by
    intro value
    rw [WorkSpan.parallel_zero_left]
  op_unit := by
    intro value
    rw [WorkSpan.parallel_zero_right]
  op_assoc := by
    intro first second third
    simp only [Option.bind_some]
    rw [WorkSpan.parallel_assoc]

/-- Value the occurrence-intent events by their realized target paths.
Administrative bookkeeping events themselves receive zero cost. -/
def historyEventCost : EffectEvent Unit BranchSite → WorkSpan
  | .choose => 0
  | .read => 0
  | .write _ => 0
  | .intent .left => realizedEventCost leftEvent
  | .intent .right => realizedEventCost rightEvent

def sequentialWorkSpanValuation :
    Valuation (EffectEvent Unit BranchSite) where
  Grade := WorkSpan
  algebra := sequentialWorkSpanPartialMonoid
  grade := fun event => some (historyEventCost event)

def parallelWorkSpanValuation :
    Valuation (EffectEvent Unit BranchSite) where
  Grade := WorkSpan
  algebra := parallelWorkSpanPartialMonoid
  grade := fun event => some (historyEventCost event)

theorem evidenceProgram_sequential_workSpan :
    sharedGrade sequentialWorkSpanValuation evidenceProgram () =
      some ⟨3, 3⟩ :=
  rfl

theorem evidenceProgram_parallel_workSpan :
    sharedGrade parallelWorkSpanValuation evidenceProgram () =
      some ⟨3, 2⟩ :=
  rfl

/-- The same history has equal total work and a schedule-dependent span. -/
theorem schedule_valuations_are_distinct :
    sharedGrade sequentialWorkSpanValuation evidenceProgram () ≠
      sharedGrade parallelWorkSpanValuation evidenceProgram () := by
  intro equal
  rw [evidenceProgram_sequential_workSpan,
    evidenceProgram_parallel_workSpan] at equal
  have costs : (⟨3, 3⟩ : WorkSpan) = ⟨3, 2⟩ := Option.some.inj equal
  have spans := congrArg WorkSpan.span costs
  norm_num at spans

/-- Erasing dependent answer evidence changes neither selected valuation. -/
theorem visible_erasure_preserves_workSpan :
    sharedGrade sequentialWorkSpanValuation visibleProgram () =
        sharedGrade sequentialWorkSpanValuation evidenceProgram () ∧
      sharedGrade parallelWorkSpanValuation visibleProgram () =
        sharedGrade parallelWorkSpanValuation evidenceProgram () := by
  exact
    ⟨sharedGrade_map sequentialWorkSpanValuation visibleOutcome
        evidenceProgram (),
      sharedGrade_map parallelWorkSpanValuation visibleOutcome
        evidenceProgram ()⟩

/-- The common visible answer cannot reconstruct realization-derived cost. -/
theorem realized_cost_not_visible_determined :
    ¬ Factors visibleOutcome realizedOutcomeCost := by
  let fibre : NonTrivialFiber visibleOutcome realizedOutcomeCost :=
    { left := leftOutcome
      right := rightOutcome
      sameShadow := rfl
      differentValue := by decide }
  exact fibre.not_factors

/-! ## Verification boundary -/

/-- One bundled statement of the positive vertical path.  Each conjunct is
proved independently above; the conjunction adds no new authority. -/
theorem semantic_vertical_canary :
    realization.mapRoute leftSourcePath = leftTargetPath ∧
      realization.mapRoute rightSourcePath = rightTargetPath ∧
      outcomes = [leftOutcome, rightOutcome] ∧
      sourceCompletion.observe .leftDone =
        sourceCompletion.observe .rightDone ∧
      parallelReceipt realizedOutcomeCost outcomes = ⟨3, 2⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms realization_expands_left
#print axioms realized_path_lengths_distinct
#print axioms realization_step_proof_irrelevant
#print axioms denotationSquare
#print axioms completed_exact_fibres_not_equivalent
#print axioms visible_erasure_preserves_history
#print axioms outcomes_parallel_workSpan
#print axioms evidenceProgram_sequential_workSpan
#print axioms evidenceProgram_parallel_workSpan
#print axioms schedule_valuations_are_distinct
#print axioms visible_erasure_preserves_workSpan
#print axioms realized_cost_not_visible_determined
#print axioms semantic_vertical_canary

end Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization
