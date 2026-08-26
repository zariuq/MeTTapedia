import Mettapedia.Cybernetics.HierarchicalComplexity.Composition
import Mettapedia.Enactive.MetasystemTransition
import Mettapedia.Order.RankedStep

/-!
# Task generations and hierarchical levels

Bennett's child relation is a transitive refinement relation.  Its existing
length-indexed `Task.Generation` therefore records a chosen witness path, not
an intrinsic order: a strict refinement may be witnessed directly or through
intermediate tasks.

The Model of Hierarchical Complexity needs more structure.  A level
presentation chooses a unit-step subrelation of Bennett refinement and proves
that each such step raises a natural-number rank by exactly one.  Its paths
map back to Bennett generations, have endpoint-determined lengths, and supply
the equal-order premise required by Commons's HC2 when children occur at the
same depth below a common task.

References:

- M. T. Bennett, *Is Complexity an Illusion?* (2024), for the transitive
  child-task relation and task generations.
- M. L. Commons and A. Pekker, *Presenting the Formal Theory of Hierarchical
  Complexity* (2008), for the equal-order coordination condition HC2 and the
  no-gaps condition C2.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive

open Mettapedia.Order

universe uWorld uIndex uState uWitness

namespace Task

variable {World : Type uWorld} {layer : AbstractionLayer World}

namespace Generation

/-- Removing the first Bennett child edge exposes a generation one step
shorter. -/
theorem tail {steps : Nat} {source target : Task layer}
    (generation : Generation (steps + 1) source target) :
    ∃ middle, source.IsChild middle ∧ Generation steps middle target := by
  cases generation with
  | step child rest => exact ⟨_, child, rest⟩

/-- Some task pair is connected by a Bennett generation of the given witness
length. -/
def RealizesLength (steps : Nat) : Prop :=
  ∃ source target : Task layer, Generation steps source target

/-- Bennett generation paths have no gaps as witness lengths: a realized path
of length `n + 1` contains a realized suffix of length `n`.  This does not yet
make path length an intrinsic order of its endpoints. -/
theorem realizesLength_pred {steps : Nat}
    (realized : RealizesLength (layer := layer) (steps + 1)) :
    RealizesLength (layer := layer) steps := by
  obtain ⟨source, target, generation⟩ := realized
  obtain ⟨middle, _, tail⟩ := generation.tail
  exact ⟨middle, target, tail⟩

end Generation

/-! ## The extra structure needed for intrinsic levels -/

/-- A unit-ranked subrelation of Bennett task refinement.  `Step` is selected
structure: the broad transitive `IsChild` relation is not assumed to consist
only of immediate level changes. -/
structure LevelPresentation (layer : AbstractionLayer World) where
  toRankedStep : RankedStep (Task layer)
  step_isChild : ∀ {source target}, toRankedStep.Step source target →
    source.IsChild target

namespace LevelPresentation

variable (presentation : LevelPresentation layer)

/-- The chosen unit-step relation. -/
abbrev Step : Task layer → Task layer → Prop :=
  presentation.toRankedStep.Step

/-- The intrinsic task order supplied by the presentation. -/
abbrev order : Task layer → Nat :=
  presentation.toRankedStep.rank

/-- Exact paths through the chosen unit-step relation. -/
abbrev Generation (steps : Nat) (source target : Task layer) : Prop :=
  presentation.toRankedStep.Path steps source target

/-- Every level path is in particular a Bennett generation, after forgetting
which child refinements were selected as unit steps. -/
theorem toTaskGeneration {steps : Nat} {source target : Task layer}
    (generation : presentation.Generation steps source target) :
    Task.Generation steps source target := by
  induction generation with
  | refl => exact Task.Generation.refl _
  | step edge rest inductionHypothesis =>
      exact Task.Generation.step
        (presentation.step_isChild edge) inductionHypothesis

/-- Intrinsic order difference along a level path is exactly its length. -/
theorem order_target_eq_order_source_add
    {steps : Nat} {source target : Task layer}
    (generation : presentation.Generation steps source target) :
    presentation.order target = presentation.order source + steps :=
  RankedStep.Path.rank_target_eq_rank_source_add
    (system := presentation.toRankedStep) generation

/-- The length of a level path is determined by its endpoints. -/
theorem generation_length_unique {firstSteps secondSteps : Nat}
    {source target : Task layer}
    (first : presentation.Generation firstSteps source target)
    (second : presentation.Generation secondSteps source target) :
    firstSteps = secondSteps :=
  RankedStep.Path.length_unique
    (system := presentation.toRankedStep) first second

/-- A task family is homogeneous exactly when its members have the same
intrinsic order.  This is the task-side premise corresponding to Commons's
HC2 equal-order condition. -/
def Homogeneous {Index : Type uIndex} (tasks : Index → Task layer) : Prop :=
  ∀ first second,
    presentation.order (tasks first) = presentation.order (tasks second)

/-- Tasks lying at the same exact level depth below one common target are
homogeneous.  Thus HC2 is earned from a graded common-target presentation,
not from the broad child relation alone. -/
theorem homogeneous_sources_of_common_target
    {Index : Type uIndex} [Nonempty Index]
    {steps : Nat} (tasks : Index → Task layer) (target : Task layer)
    (generation : ∀ index,
      presentation.Generation steps (tasks index) target) :
    presentation.Homogeneous tasks := by
  intro first second
  have firstRank :=
    (presentation.order_target_eq_order_source_add (generation first))
  have secondRank :=
    (presentation.order_target_eq_order_source_add (generation second))
  omega

end LevelPresentation

/-! ## Why Bennett's broad relation is not itself a unit-level relation -/

/-- Any two composable strict child refinements create a shortcut by
transitivity.  Consequently no rank can make every Bennett `IsChild` edge an
exact one-level increase. -/
theorem no_unit_rank_for_all_isChild
    {first middle last : Task layer}
    (first_middle : first.IsChild middle)
    (middle_last : middle.IsChild last) :
    ¬ ∃ rank : Task layer → Nat,
      ∀ {source target}, source.IsChild target →
        rank target = rank source + 1 := by
  rintro ⟨rank, everyChildRaisesOne⟩
  have firstLast : first.IsChild last := first_middle.trans middle_last
  have firstMiddleRank := everyChildRaisesOne first_middle
  have middleLastRank := everyChildRaisesOne middle_last
  have firstLastRank := everyChildRaisesOne firstLast
  omega

end Task

/-! ## Metasystem transitions earn levels only through unit-step evidence -/

namespace MetasystemTransition

/-- A metasystem task semantics whose admitted changes are chosen unit-level
steps.  This strengthens the existing `TaskInterpretation`, which requires
only the broader Bennett child relation. -/
structure LevelInterpretation
    {State : Type uState}
    (metasystem : Metasystem.{uState, uWitness} State)
    {World : Type uWorld} (layer : AbstractionLayer World)
    (levels : Task.LevelPresentation layer) where
  task : Mettapedia.Cybernetics.Constraint State → Task layer
  change_isStep : ∀ {source target}, metasystem.Change source target →
    levels.Step (task source) (task target)

namespace LevelInterpretation

variable {State : Type uState}
  {metasystem : Metasystem.{uState, uWitness} State}
  {World : Type uWorld} {layer : AbstractionLayer World}
  {levels : Task.LevelPresentation layer}

/-- Forgetting the chosen unit levels recovers the existing metasystem task
interpretation. -/
def toTaskInterpretation
    (interpretation : LevelInterpretation metasystem layer levels) :
    TaskInterpretation metasystem layer where
  task := interpretation.task
  change_isChild := fun evidence =>
    levels.step_isChild (interpretation.change_isStep evidence)

/-- A realized metasystem transition is a one-level generation when its
change evidence inhabits the selected unit-step relation. -/
def generation
    (interpretation : LevelInterpretation metasystem layer levels)
    (transition : metasystem.Transition) :
    levels.Generation 1
      (interpretation.task transition.source)
      (interpretation.task transition.target) :=
  RankedStep.Path.step
    (interpretation.change_isStep transition.evidence)
    (RankedStep.Path.refl (interpretation.task transition.target))

/-- Under that stronger interpretation, a metasystem transition raises the
intrinsic task order by exactly one. -/
theorem order_target_eq_order_source_add_one
    (interpretation : LevelInterpretation metasystem layer levels)
    (transition : metasystem.Transition) :
    levels.order (interpretation.task transition.target) =
      levels.order (interpretation.task transition.source) + 1 := by
  simpa using levels.order_target_eq_order_source_add
    (interpretation.generation transition)

/-- Erasing the level witness recovers the existing one-step Bennett
generation theorem. -/
theorem toTaskGeneration
    (interpretation : LevelInterpretation metasystem layer levels)
    (transition : metasystem.Transition) :
    Task.Generation 1
      (interpretation.task transition.source)
      (interpretation.task transition.target) :=
  levels.toTaskGeneration (interpretation.generation transition)

end LevelInterpretation

end MetasystemTransition

/-! ## A concrete three-task witness -/

namespace HierarchicalComplexityBridgeCanary

open NoAbstraction

/-- The unconstrained, realizable aspect. -/
def emptyAspect : Aspect (AbstractionLayer.full Bool) where
  facts := ∅
  facts_subset_vocabulary := by simp [AbstractionLayer.full]
  realized := ⟨false, by simp⟩

theorem emptyAspect_ne_trueAspect : emptyAspect ≠ trueAspect := by
  intro equal
  have member : trueOnly ∈ emptyAspect.facts := by
    rw [equal]
    simp [trueAspect]
  change trueOnly ∈ (∅ : Set (Fact Bool)) at member
  simp at member

theorem emptyAspect_ne_redundantTrueAspect :
    emptyAspect ≠ redundantTrueAspect := by
  intro equal
  have member : redundantTop ∈ emptyAspect.facts := by
    rw [equal]
    simp [redundantTrueAspect]
  change redundantTop ∈ (∅ : Set (Fact Bool)) at member
  simp at member

def taskZero : Task (AbstractionLayer.full Bool) where
  inputs := {emptyAspect}
  correctOutputs := ∅
  correctOutputs_subset := by simp

def taskOne : Task (AbstractionLayer.full Bool) where
  inputs := {emptyAspect, trueAspect}
  correctOutputs := ∅
  correctOutputs_subset := by simp

def taskTwo : Task (AbstractionLayer.full Bool) where
  inputs := {emptyAspect, trueAspect, redundantTrueAspect}
  correctOutputs := ∅
  correctOutputs_subset := by simp

theorem taskZero_isChild_taskOne : taskZero.IsChild taskOne := by
  constructor
  · change taskZero.inputs ⊂ taskOne.inputs
    rw [Set.ssubset_iff_subset_ne]
    constructor
    · intro aspect member
      have aspectEqual : aspect = emptyAspect := by
        simpa [taskZero] using member
      subst aspect
      simp [taskOne]
    · intro equal
      have member : trueAspect ∈ taskZero.inputs := by
        rw [equal]
        simp [taskOne]
      have aspectsEqual : trueAspect = emptyAspect := by
        simpa [taskZero] using member
      exact emptyAspect_ne_trueAspect aspectsEqual.symm
  · simp [taskZero, taskOne]

theorem taskOne_isChild_taskTwo : taskOne.IsChild taskTwo := by
  constructor
  · change taskOne.inputs ⊂ taskTwo.inputs
    rw [Set.ssubset_iff_subset_ne]
    constructor
    · intro aspect member
      have aspectCases : aspect = emptyAspect ∨ aspect = trueAspect := by
        simpa [taskOne] using member
      rcases aspectCases with rfl | rfl <;> simp [taskTwo]
    · intro equal
      have member : redundantTrueAspect ∈ taskOne.inputs := by
        rw [equal]
        simp [taskTwo]
      have true_ne_redundant : trueAspect ≠ redundantTrueAspect :=
        PrimeGeneration.Canary.trueAspect_ne_redundantTrueAspect
      have aspectCases :
          redundantTrueAspect = emptyAspect ∨
            redundantTrueAspect = trueAspect := by
        simpa [taskOne] using member
      rcases aspectCases with redundant_empty | redundant_true
      · exact emptyAspect_ne_redundantTrueAspect redundant_empty.symm
      · exact true_ne_redundant redundant_true.symm
  · simp [taskOne, taskTwo]

theorem taskZero_isChild_taskTwo : taskZero.IsChild taskTwo :=
  taskZero_isChild_taskOne.trans taskOne_isChild_taskTwo

/-- The broad Bennett relation admits a direct witness for the endpoint
refinement. -/
def directGeneration : Task.Generation 1 taskZero taskTwo :=
  Task.Generation.step taskZero_isChild_taskTwo
    (Task.Generation.refl taskTwo)

/-- The same endpoint refinement also admits a two-step witness through the
intermediate task. -/
def mediatedGeneration : Task.Generation 2 taskZero taskTwo := by
  simpa using (Task.Generation.step taskZero_isChild_taskOne
    (Task.Generation.step taskOne_isChild_taskTwo
      (Task.Generation.refl taskTwo)))

/-- Bennett generation length is not an intrinsic endpoint order. -/
theorem same_endpoints_have_different_generation_lengths :
    Task.Generation 1 taskZero taskTwo ∧
      Task.Generation 2 taskZero taskTwo :=
  ⟨directGeneration, mediatedGeneration⟩

/-- This realized three-task refinement instantiates the general obstruction
to treating every Bennett child edge as one MHC level. -/
theorem broad_child_relation_has_no_unit_rank :
    ¬ ∃ rank : Task (AbstractionLayer.full Bool) → Nat,
      ∀ {source target}, source.IsChild target →
        rank target = rank source + 1 :=
  Task.no_unit_rank_for_all_isChild
    taskZero_isChild_taskOne taskOne_isChild_taskTwo

/-- The two selected unit refinements; the transitive shortcut is deliberately
not a constructor. -/
inductive UnitStep :
    Task (AbstractionLayer.full Bool) →
      Task (AbstractionLayer.full Bool) → Prop where
  | zero_one : UnitStep taskZero taskOne
  | one_two : UnitStep taskOne taskTwo

noncomputable def taskOrder
    (task : Task (AbstractionLayer.full Bool)) : Nat := by
  classical
  exact if task = taskZero then 0
    else if task = taskOne then 1
    else if task = taskTwo then 2
    else 0

theorem taskZero_ne_taskOne : taskZero ≠ taskOne := by
  intro equal
  have child := taskZero_isChild_taskOne
  rw [equal] at child
  exact Task.not_isChild_self taskOne child

theorem taskOne_ne_taskTwo : taskOne ≠ taskTwo := by
  intro equal
  have child := taskOne_isChild_taskTwo
  rw [equal] at child
  exact Task.not_isChild_self taskTwo child

theorem taskZero_ne_taskTwo : taskZero ≠ taskTwo := by
  intro equal
  have child := taskZero_isChild_taskTwo
  rw [equal] at child
  exact Task.not_isChild_self taskTwo child

@[simp] theorem taskOrder_taskZero : taskOrder taskZero = 0 := by
  classical
  simp [taskOrder]

@[simp] theorem taskOrder_taskOne : taskOrder taskOne = 1 := by
  classical
  simp [taskOrder, Ne.symm taskZero_ne_taskOne]

@[simp] theorem taskOrder_taskTwo : taskOrder taskTwo = 2 := by
  classical
  simp [taskOrder, Ne.symm taskZero_ne_taskTwo,
    Ne.symm taskOne_ne_taskTwo]

/-- A genuine task-level presentation selecting only adjacent levels. -/
noncomputable def levelPresentation :
    Task.LevelPresentation (AbstractionLayer.full Bool) where
  toRankedStep :=
    { Step := UnitStep
      rank := taskOrder
      step_rank := by
        intro source target step
        cases step <;> simp }
  step_isChild := by
    intro source target step
    cases step with
    | zero_one => exact taskZero_isChild_taskOne
    | one_two => exact taskOne_isChild_taskTwo

/-- The selected adjacent refinements form an intrinsic two-level path. -/
noncomputable def levelGeneration :
    levelPresentation.Generation 2 taskZero taskTwo := by
  exact RankedStep.Path.step .zero_one
    (RankedStep.Path.step .one_two (RankedStep.Path.refl taskTwo))

theorem levelGeneration_has_intrinsic_length
    {steps : Nat}
    (other : levelPresentation.Generation steps taskZero taskTwo) :
    steps = 2 :=
  levelPresentation.generation_length_unique other levelGeneration

/-- Forgetting unit-level structure recovers the mediated Bennett generation,
not a parallel task semantics. -/
theorem levelGeneration_to_Bennett :
    Task.Generation 2 taskZero taskTwo :=
  levelPresentation.toTaskGeneration levelGeneration

end HierarchicalComplexityBridgeCanary

end Mettapedia.Enactive

#print axioms Mettapedia.Enactive.Task.Generation.realizesLength_pred
#print axioms Mettapedia.Enactive.Task.LevelPresentation.homogeneous_sources_of_common_target
#print axioms Mettapedia.Enactive.Task.no_unit_rank_for_all_isChild
#print axioms Mettapedia.Enactive.MetasystemTransition.LevelInterpretation.order_target_eq_order_source_add_one
#print axioms Mettapedia.Enactive.HierarchicalComplexityBridgeCanary.broad_child_relation_has_no_unit_rank
#print axioms Mettapedia.Enactive.HierarchicalComplexityBridgeCanary.levelGeneration_has_intrinsic_length
