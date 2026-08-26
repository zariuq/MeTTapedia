import Mettapedia.Languages.MeTTa.MeTTaZeroQuiescence
import Mettapedia.Languages.MeTTa.MeTTaZeroWorkClosure
import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.LanguageDef.CertificateGSLTRecurrentTraceAuthority

/-!
# An experimental inductive/coinductive control layer for MeTTa Zero

This module tests a possible successor to the current one-step Zero candidate.
It is deliberately named `ZeroUV`: the name records the experiment rather than
claiming that its operator basis is already canonical.

The semantic boundary has three parts.

* `productiveGSLT` re-enters the untotalized `interpretedResults` relation.
  Empty production is a normal form; a genuine self-loop remains a step.
* `Enumeration` supplies only an occurrence-preserving physical enumeration of
  that bag.  The generic inference-control theory then provides resumable,
  language-visible frontiers and authored controllers.
* finite descent and recurrent progress certificates remain distinct evidence
  disciplines.  A scheduler is never smuggled into the one-step relation.

The canaries cover finite chaining, productive looping, duplicate occurrences,
order-varying controllers with the same completed answer bag, and checked
Buechi recurrence with a rejecting near miss.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaZeroUV

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.ClosureCriteria
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaZeroQuiescence
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The untotalized, work-closed transition relation -/

/-- A productive ZeroUV transition is exactly one occurrence returned by the
untotalized query-derived evaluator. -/
def ProductiveStep (model : Model) (space : model.Space)
    (source target : Pattern) : Prop :=
  target ∈ interpretedResults model space source

/-- Re-entry changes only the carrier of the one-step relation: results are
again terms, rather than terminal answer envelopes. -/
def productiveGSLT (model : Model) (space : model.Space) : GSLT where
  Term := Pattern
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := ProductiveStep model space
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

@[simp] theorem productiveGSLT_step_iff (model : Model)
    (space : model.Space) (source target : Pattern) :
    (productiveGSLT model space).Step source target ↔
      target ∈ interpretedResults model space source :=
  Iff.rfl

/-- Normal form is exactly kernel quiescence.  No report tag or comparison
against the inert singleton is involved. -/
theorem productiveGSLT_normalForm_iff_quiescent (model : Model)
    (space : model.Space) (subject : Pattern) :
    (productiveGSLT model space).IsNormalForm subject ↔
      Quiescent model space subject := by
  constructor
  · intro normal
    unfold Quiescent
    by_contra productive
    obtain ⟨target, member⟩ := Multiset.exists_mem_of_ne_zero productive
    exact normal ⟨target, member⟩
  · intro quiescent
    rintro ⟨target, step⟩
    unfold Quiescent at quiescent
    change target ∈ interpretedResults model space subject at step
    exact (Multiset.eq_zero_iff_forall_notMem.mp quiescent target) step

/-! ## Occurrence-preserving physical enumerations -/

/-- A physical traversal may choose a list order, but it must enumerate the
kernel multiset exactly.  This is the only realization-specific input needed
by the generic controller machine. -/
structure Enumeration (model : Model) (space : model.Space) where
  successors : Pattern → List Pattern
  exact : ∀ subject,
    (successors subject : Multiset Pattern) =
      interpretedResults model space subject

namespace Enumeration

variable {model : Model} {space : model.Space}

/-- The executable branching system emits a value precisely at quiescence and
otherwise exposes every productive result occurrence as new work. -/
def system (enumeration : Enumeration model space) :
    BranchingSystem Pattern Pattern where
  emit subject :=
    if enumeration.successors subject = [] then some subject else none
  successors := enumeration.successors

theorem successors_mem_iff_step (enumeration : Enumeration model space)
    (source target : Pattern) :
    target ∈ enumeration.successors source ↔
      (productiveGSLT model space).Step source target := by
  change target ∈ enumeration.successors source ↔
    target ∈ interpretedResults model space source
  rw [← enumeration.exact source]
  simp

theorem successors_nil_iff_quiescent
    (enumeration : Enumeration model space) (subject : Pattern) :
    enumeration.successors subject = [] ↔
      Quiescent model space subject := by
  rw [← Multiset.coe_eq_zero]
  exact ⟨fun equal => (enumeration.exact subject).symm.trans equal,
    fun quiescent => (enumeration.exact subject).trans quiescent⟩

theorem emit_eq_some_iff_quiescent
    (enumeration : Enumeration model space) (subject : Pattern) :
    (system enumeration).emit subject = some subject ↔
      Quiescent model space subject := by
  constructor
  · intro emitted
    by_cases empty : enumeration.successors subject = []
    · exact (successors_nil_iff_quiescent enumeration subject).mp empty
    · simp [system, empty] at emitted
  · intro quiescent
    have empty :=
      (successors_nil_iff_quiescent enumeration subject).mpr quiescent
    simp [system, empty]

theorem emit_eq_none_of_productive
    (enumeration : Enumeration model space) {subject : Pattern}
    (productive : Productive model space subject) :
    (system enumeration).emit subject = none := by
  simp only [system]
  rw [if_neg]
  intro empty
  exact productive <| by
    rw [← enumeration.exact subject, Multiset.coe_eq_zero]
    exact empty

/-- Every generated child is authorized by the untotalized ZeroUV GSLT. -/
theorem successor_step (enumeration : Enumeration model space)
    {source target : Pattern}
    (member : target ∈ (system enumeration).successors source) :
    (productiveGSLT model space).Step source target :=
  (successors_mem_iff_step enumeration source target).mp member

private theorem multistep_tail {theory : GSLT}
    {first middle last : theory.Term}
    (path : theory.MultiStep first middle)
    (lastStep : theory.Step middle last) :
    theory.MultiStep first last := by
  induction path with
  | refl _ => exact .step lastStep (.refl _)
  | step firstStep rest inductionHypothesis =>
      exact .step firstStep (inductionHypothesis lastStep)

/-- A generated work item is reachable through genuine productive ZeroUV
steps.  Scheduling can change its position in the frontier, not its semantic
origin. -/
theorem generated_multistep (enumeration : Enumeration model space)
    {root subject : Pattern}
    (generated : Generated (system enumeration) [root] subject) :
    (productiveGSLT model space).MultiStep root subject := by
  induction generated with
  | root member =>
      simp only [List.mem_singleton] at member
      rw [member]
      exact .refl _
  | successor generated member inductionHypothesis =>
      exact multistep_tail inductionHypothesis
        (successor_step enumeration member)

/-- Every public emission from every authored controller is both reachable
from the requested root and exactly quiescent.  A controller may select work;
it cannot forge an edge or report a productive state as complete. -/
theorem controlled_emission_reachable_quiescent
    (enumeration : Enumeration model space)
    {Memory : Type*}
    (controller : Controller Pattern Pattern Memory)
    (root : Pattern) (fuel : Nat)
    {event : Emission Pattern Pattern}
    (member : event ∈
      (Snapshot.run (system enumeration) controller fuel
        (Snapshot.initial controller [root])).search.events) :
    (productiveGSLT model space).MultiStep root event.value ∧
      Quiescent model space event.value := by
  have initialSound :
      (Snapshot.initial controller [root]).search.Sound
        (system enumeration) [root] := by
    exact Mettapedia.GSLT.Core.BranchingTemporal.initial_sound
      (system enumeration) [root]
  have runSound := Snapshot.sound_run (system enumeration) controller
    initialSound fuel
  obtain ⟨generated, emitted⟩ := runSound.2 event member
  have empty : enumeration.successors event.origin = [] := by
    by_contra nonempty
    simp [system, nonempty] at emitted
  have originEq : event.origin = event.value := by
    simpa [system, empty] using emitted
  rw [← originEq]
  exact ⟨generated_multistep enumeration generated,
    (successors_nil_iff_quiescent enumeration event.origin).mp empty⟩

end Enumeration

/-! ## Finite canaries -/

namespace FiniteCanary

def a : Pattern := .apply "zerouv-a" []
def b : Pattern := .apply "zerouv-b" []
def c : Pattern := .apply "zerouv-c" []

def chainGround (subject : Pattern) : Multiset Pattern :=
  if subject = a then {b}
  else if subject = b then {c}
  else 0

def chainModel : Model := structuralModel chainGround
def chainSpace : Multiset Pattern := 0

@[simp] theorem chainResultsA :
    interpretedResults chainModel chainSpace a = {b} := by
  simp [chainModel, chainSpace, chainGround, structuralModel,
    interpretedResults, equationResults, queryAll, query]

@[simp] theorem chainResultsB :
    interpretedResults chainModel chainSpace b = {c} := by
  simp [chainModel, chainSpace, chainGround, structuralModel,
    interpretedResults, equationResults, queryAll, query, a, b, c]

@[simp] theorem chainResultsC :
    interpretedResults chainModel chainSpace c = 0 := by
  simp [chainModel, chainSpace, chainGround, structuralModel,
    interpretedResults, equationResults, queryAll, query, a, b, c]

def chainEnumeration : Enumeration chainModel chainSpace where
  successors subject :=
    if subject = a then [b]
    else if subject = b then [c]
    else []
  exact subject := by
    by_cases subjectA : subject = a
    · subst subject
      simp [chainResultsA]
    · by_cases subjectB : subject = b
      · subst subject
        simp [chainResultsB, subjectA]
      · simp [chainModel, chainSpace, chainGround, structuralModel,
          interpretedResults, equationResults, queryAll, query,
          subjectA, subjectB]

def chainSystem : BranchingSystem Pattern Pattern := chainEnumeration.system

def breadthController : Controller Pattern Pattern Unit :=
  Controller.fixed Scheduler.breadthFirst

/-- The productive relation itself composes; no answer-envelope wrapper blocks
the second link. -/
theorem chain_reaches_c :
    (productiveGSLT chainModel chainSpace).MultiStep a c := by
  apply GSLT.MultiStep.step (u := b)
  · exact (show b ∈ interpretedResults chainModel chainSpace a by simp)
  · apply GSLT.MultiStep.step (u := c)
    · exact (show c ∈ interpretedResults chainModel chainSpace b by simp)
    · exact .refl _

/-- Unlike the answer-envelope GSLT, the untotalized productive relation has
an internally composable pair of steps. -/
theorem productiveZero_has_composable_steps :
    HasComposableSteps (productiveGSLT chainModel chainSpace) :=
  ⟨
    { source := a
      middle := b
      target := c
      first := show b ∈ interpretedResults chainModel chainSpace a by simp
      second := show c ∈ interpretedResults chainModel chainSpace b by simp }⟩

/-- The carrier choice is semantically consequential: terminal answer
envelopes forbid internal chaining, while direct re-entry restores it without
choosing a scheduler. -/
theorem bareZero_and_productiveZero_are_separated :
    (¬ HasComposableSteps (evaluationGSLT chainModel)) ∧
      HasComposableSteps (productiveGSLT chainModel chainSpace) :=
  ⟨bareZero_has_no_composable_steps chainModel,
    productiveZero_has_composable_steps⟩

/-- The generic controller consumes the two productive links, emits the
quiescent result, and has no residual frontier. -/
theorem chain_run_completes :
    (Snapshot.run chainSystem breadthController 3
      (Snapshot.initial breadthController [a])).search.frontier = [] := by
  decide

theorem chain_run_emits_terminal :
    (Snapshot.run chainSystem breadthController 3
      (Snapshot.initial breadthController [a])).search.events.map
        Emission.value = [c] := by
  decide

/-! ### Productive loops do not masquerade as completion -/

def loop : Pattern := .apply "zerouv-loop" []

def loopModel : Model :=
  structuralModel fun subject => if subject = loop then {loop} else 0

def loopSpace : Multiset Pattern := 0

def loopEnumeration : Enumeration loopModel loopSpace where
  successors subject := if subject = loop then [loop] else []
  exact subject := by
    by_cases equal : subject = loop
    · subst subject
      simp [loopModel, loopSpace, structuralModel, interpretedResults,
        equationResults, queryAll, query]
    · simp [loopModel, loopSpace, structuralModel, interpretedResults,
        equationResults, queryAll, query, equal]

def loopSystem : BranchingSystem Pattern Pattern := loopEnumeration.system

/-- Any finite observation of the productive self-loop retains residual work
and emits no false terminal value. -/
theorem productive_loop_remains_pending :
    let result := Snapshot.run loopSystem breadthController 5
      (Snapshot.initial breadthController [loop])
    result.search.frontier = [loop] ∧ result.search.events = [] := by
  decide

/-! ### Duplicate occurrences and controller-dependent order -/

def root : Pattern := .apply "zerouv-root" []
def left : Pattern := .apply "zerouv-left" []
def right : Pattern := .apply "zerouv-right" []

def branchGround (subject : Pattern) : Multiset Pattern :=
  if subject = root then {left, right} else 0

def branchModel : Model := structuralModel branchGround
def branchSpace : Multiset Pattern := 0

@[simp] theorem branchResultsRoot :
    interpretedResults branchModel branchSpace root = {left, right} := by
  simp [branchModel, branchSpace, branchGround, structuralModel,
    interpretedResults, equationResults, queryAll, query]

def branchEnumeration : Enumeration branchModel branchSpace where
  successors subject := if subject = root then [left, right] else []
  exact subject := by
    by_cases equal : subject = root
    · subst subject
      rw [branchResultsRoot]
      rfl
    · simp [branchModel, branchSpace, branchGround, structuralModel,
        interpretedResults, equationResults, queryAll, query, equal]

def branchSystem : BranchingSystem Pattern Pattern := branchEnumeration.system

def reverseController : Controller Pattern Pattern Unit :=
  Controller.fixed Scheduler.reverseBreadthFirst

theorem branch_breadth_stream :
    (Snapshot.run branchSystem breadthController 3
      (Snapshot.initial breadthController [root])).search.events.map
        Emission.value = [left, right] := by
  decide

theorem branch_reverse_stream :
    (Snapshot.run branchSystem reverseController 3
      (Snapshot.initial reverseController [root])).search.events.map
        Emission.value = [right, left] := by
  decide

/-- Controller order is observable in the receipt while the completed answer
bag remains the same. -/
theorem branch_streams_differ_bags_agree :
    (Snapshot.run branchSystem breadthController 3
      (Snapshot.initial breadthController [root])).search.events.map
        Emission.value ≠
      (Snapshot.run branchSystem reverseController 3
        (Snapshot.initial reverseController [root])).search.events.map
          Emission.value ∧
    eventBag
        (Snapshot.run branchSystem breadthController 3
          (Snapshot.initial breadthController [root])).search.events =
      eventBag
        (Snapshot.run branchSystem reverseController 3
          (Snapshot.initial reverseController [root])).search.events := by
  decide

def duplicateAnswer : Pattern := .apply "zerouv-duplicate" []

def duplicateModel : Model := structuralModel fun subject =>
  if subject = root then {duplicateAnswer, duplicateAnswer} else 0

def duplicateSpace : Multiset Pattern := 0

@[simp] theorem duplicateResultsRoot :
    interpretedResults duplicateModel duplicateSpace root =
      {duplicateAnswer, duplicateAnswer} := by
  simp [duplicateModel, duplicateSpace, structuralModel,
    interpretedResults, equationResults, queryAll, query]

def duplicateEnumeration : Enumeration duplicateModel duplicateSpace where
  successors subject :=
    if subject = root then [duplicateAnswer, duplicateAnswer] else []
  exact subject := by
    by_cases equal : subject = root
    · subst subject
      rw [duplicateResultsRoot]
      rfl
    · simp [duplicateModel, duplicateSpace, structuralModel,
        interpretedResults, equationResults, queryAll, query, equal]

def duplicateSystem : BranchingSystem Pattern Pattern :=
  duplicateEnumeration.system

theorem duplicate_occurrences_survive_control :
    (Snapshot.run duplicateSystem breadthController 3
      (Snapshot.initial breadthController [root])).search.events.map
        Emission.value = [duplicateAnswer, duplicateAnswer] := by
  decide

end FiniteCanary

/-! ## Recurrent ZeroUV canary -/

namespace RecurrentCanary

def encode : Bool → Pattern
  | false => .apply "zerouv-off" []
  | true => .apply "zerouv-on" []

def toggleGround (subject : Pattern) : Multiset Pattern :=
  if subject = encode false then {encode true}
  else if subject = encode true then {encode false}
  else 0

def toggleModel : Model := structuralModel toggleGround
def toggleSpace : Multiset Pattern := 0

def ToggleStep (source target : Bool) : Prop :=
  encode target ∈ interpretedResults toggleModel toggleSpace (encode source)

@[reducible] def toggleTheory : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := ToggleStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

inductive ToggleEvidence where
  | up
  | down
deriving Repr, DecidableEq

def checkToggleEdge (claim : StepClaim toggleTheory)
    (evidence : ToggleEvidence) : Bool :=
  match claim.source, claim.target, evidence with
  | false, true, .up => true
  | true, false, .down => true
  | _, _, _ => false

theorem toggle_up : ToggleStep false true := by
  change encode true ∈
    interpretedResults toggleModel toggleSpace (encode false)
  simp [toggleModel, toggleSpace, toggleGround, structuralModel,
    interpretedResults, equationResults, queryAll, query]

theorem toggle_down : ToggleStep true false := by
  change encode false ∈
    interpretedResults toggleModel toggleSpace (encode true)
  simp [toggleModel, toggleSpace, toggleGround, structuralModel,
    interpretedResults, equationResults, queryAll, query, encode]

theorem checkToggleEdge_sound {claim : StepClaim toggleTheory}
    {evidence : ToggleEvidence}
    (accepted : checkToggleEdge claim evidence = true) : claim.Meaning := by
  rcases claim with ⟨source, target⟩
  cases source <;> cases target <;> cases evidence <;>
    simp [checkToggleEdge] at accepted
  · exact toggle_up
  · exact toggle_down

def toggleStepAuthority : StepAuthority String toggleTheory where
  id := "zerouv-toggle-step-v1"
  Certificate := ToggleEvidence
  check := checkToggleEdge
  sound := checkToggleEdge_sound

def alternatingAction (state : Bool) :
    TraceLink toggleTheory ToggleEvidence :=
  match state with
  | false => ⟨true, .up⟩
  | true => ⟨false, .down⟩

def alternatingController :
    MemorylessController Bool (TraceLink toggleTheory ToggleEvidence) where
  active := fun _ => true
  action := alternatingAction
  next := not

def acceptsOn : Bool → Bool := id

def recurrenceClaim : RecurrentTraceClaim toggleTheory ToggleEvidence :=
  ⟨false, alternatingController⟩

def recurrenceMeasure : ProgressMeasure Bool where
  rank
    | false => 1
    | true => 0

def recurrenceAuthority :=
  recurrentTraceAuthority "zerouv-toggle-recurrence-v1"
    toggleStepAuthority acceptsOn

def alternatingSystem :=
  auditedLabeledSystem toggleStepAuthority acceptsOn

theorem recurrenceMeasure_valid :
    recurrenceMeasure.Valid alternatingSystem alternatingController false := by
  constructor
  · constructor
    · rfl
    · intro state _
      cases state <;>
        simp [alternatingSystem, auditedLabeledSystem,
          alternatingController, alternatingAction, checkToggleEdge,
          toggleStepAuthority]
  · intro state _
    cases state <;>
      simp [alternatingSystem, auditedLabeledSystem, alternatingController,
        recurrenceMeasure, acceptsOn, checkToggleEdge, toggleStepAuthority]

theorem recurrenceMeasure_accepted :
    recurrenceAuthority.check recurrenceClaim recurrenceMeasure = true := by
  exact (ProgressMeasure.check_eq_true_iff alternatingSystem
    alternatingController recurrenceMeasure false).2 recurrenceMeasure_valid

/-- Finite checked evidence entails a genuine infinite ZeroUV-derived
execution with infinitely many visits to the `on` state. -/
theorem recurrenceClaim_meaning :
    recurrenceClaim.Meaning acceptsOn :=
  recurrenceAuthority.sound recurrenceMeasure_accepted

def acceptsNothing (_ : Bool) : Bool := false

/-- Changing only the objective to one with no accepting state invalidates
the recurrence claim, although every selected local transition remains legal. -/
theorem recurrenceClaim_not_meaning_without_acceptance :
    ¬ recurrenceClaim.Meaning acceptsNothing := by
  intro recurrent
  let execution := alternatingController.canonicalExecution false
  obtain ⟨visit, _, accepted⟩ := (recurrent execution).2 0
  simp [acceptsNothing] at accepted

end RecurrentCanary

#print axioms productiveGSLT_normalForm_iff_quiescent
#print axioms Enumeration.successor_step
#print axioms Enumeration.controlled_emission_reachable_quiescent
#print axioms FiniteCanary.chain_reaches_c
#print axioms FiniteCanary.bareZero_and_productiveZero_are_separated
#print axioms FiniteCanary.productive_loop_remains_pending
#print axioms FiniteCanary.branch_streams_differ_bags_agree
#print axioms FiniteCanary.duplicate_occurrences_survive_control
#print axioms RecurrentCanary.recurrenceClaim_meaning
#print axioms RecurrentCanary.recurrenceClaim_not_meaning_without_acceptance

end Mettapedia.Languages.MeTTa.MeTTaZeroUV
