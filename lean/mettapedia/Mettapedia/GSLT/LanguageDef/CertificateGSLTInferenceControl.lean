import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.LanguageDef.CertificateGSLTBuchiAuthority
import Mettapedia.GSLT.LanguageDef.CertificateGSLTFiniteTraceAuthority

/-!
# Proof-carrying inference control

A proof-search controller should be more than a recommendation to an
executor.  Each selected action in this module carries three independently
checked pieces of information:

* the exact successor-list occurrence to execute;
* the target state claimed for that occurrence;
* local evidence accepted by the admitted GSLT step authority.

A finite progress measure may then certify a global Büchi objective.  The
central result, `checked_progress_is_executable_plan`, states that accepted
global evidence supplies both an executable occurrence trace and a genuine
GSLT rewrite path at every finite prefix, as well as the infinitary objective.
The checker therefore validates a proof-carrying plan; it does not trust the
producer that found the plan.

This is a finite-state Büchi result.  It does not claim completeness for
arbitrary objectives, parity games, unbounded controller memory, or physical
runtime scheduling.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.InferenceControl

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

universe uAuthority uCertificate

/-- One proof-carrying control action.  `index` identifies a transition
occurrence even when multiple successor positions contain equal targets. -/
structure OccurrenceLink (theory : GSLT)
    (StepCertificate : Type uCertificate) where
  index : Nat
  target : theory.Term
  evidence : StepCertificate

/-- A locally audited occurrence system.  The definition validates the
selected occurrence, and the step authority independently validates its
semantic edge. -/
def auditedOccurrenceSystem
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (definition : GSLTBranchingPresentation theory Unit)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term → Bool) :
    LabeledSystem theory.Term
      (OccurrenceLink theory stepAuthority.Certificate) where
  step := fun source action target =>
    decide ((definition.successors source)[action.index]? =
      some action.target) &&
    decide (action.target = target) &&
    stepAuthority.check ⟨source, action.target⟩ action.evidence
  accepting := accepting

theorem auditedOccurrenceSystem_step_eq_true_iff
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (definition : GSLTBranchingPresentation theory Unit)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term → Bool)
    (source target : theory.Term)
    (action : OccurrenceLink theory stepAuthority.Certificate) :
    (auditedOccurrenceSystem definition stepAuthority accepting).step
        source action target = true ↔
      (definition.successors source)[action.index]? = some action.target ∧
        action.target = target ∧
        stepAuthority.check ⟨source, action.target⟩ action.evidence = true := by
  simp only [auditedOccurrenceSystem, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨occurrence, targetEquality⟩, evidence⟩
    exact ⟨occurrence, targetEquality, evidence⟩
  · rintro ⟨occurrence, targetEquality, evidence⟩
    exact ⟨⟨occurrence, targetEquality⟩, evidence⟩

/-- Every accepted controller transition is a real edge of the admitted
GSLT, not merely a well-indexed physical successor. -/
theorem auditedOccurrenceSystem_step_sound
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (definition : GSLTBranchingPresentation theory Unit)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term → Bool)
    {source target : theory.Term}
    {action : OccurrenceLink theory stepAuthority.Certificate}
    (accepted :
      (auditedOccurrenceSystem definition stepAuthority accepting).step
        source action target = true) :
    theory.Step source target := by
  obtain ⟨_, targetEquality, evidenceAccepted⟩ :=
    (auditedOccurrenceSystem_step_eq_true_iff definition stepAuthority
      accepting source target action).mp accepted
  rw [← targetEquality]
  exact stepAuthority.sound evidenceAccepted

/-! ## Executing the selected occurrence indices -/

/-- Replay a list of successor positions in an exact branching definition. -/
def follow {theory : GSLT}
    (definition : GSLTBranchingPresentation theory Unit) :
    theory.Term → List Nat → Option theory.Term
  | state, [] => some state
  | state, index :: rest =>
      (definition.successors state)[index]? >>= fun target =>
        follow definition target rest

theorem follow_append {theory : GSLT}
    (definition : GSLTBranchingPresentation theory Unit)
    (state : theory.Term) (first second : List Nat) :
    follow definition state (first ++ second) =
      (follow definition state first).bind fun middle =>
        follow definition middle second := by
  induction first generalizing state with
  | nil => simp [follow]
  | cons index rest inductionHypothesis =>
      simp only [List.cons_append, follow]
      cases lookup : (definition.successors state)[index]? with
      | none => simp
      | some target => simpa using inductionHypothesis target

namespace ControlledExecution

/-- Exact successor positions selected along a finite prefix of one canonical
controller execution. -/
def occurrenceTrace {theory : GSLT} {StepCertificate : Type uCertificate}
    {controller :
      MemorylessController theory.Term
        (OccurrenceLink theory StepCertificate)} {root : theory.Term}
    (execution : ControlledExecution controller root) : Nat → List Nat
  | 0 => []
  | length + 1 =>
      occurrenceTrace execution length ++
        [(controller.action (execution.state length)).index]

theorem active_of_locallyValid
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    {definition : GSLTBranchingPresentation theory Unit}
    {stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory}
    {accepting : theory.Term → Bool}
    {controller : MemorylessController theory.Term
      (OccurrenceLink theory stepAuthority.Certificate)}
    {root : theory.Term}
    (localValidity : controller.LocallyValid
      (auditedOccurrenceSystem definition stepAuthority accepting) root)
    (execution : ControlledExecution controller root) :
    ∀ index, controller.active (execution.state index) = true := by
  intro index
  induction index with
  | zero => simpa [execution.starts] using localValidity.1
  | succ index inductionHypothesis =>
      rw [execution.follows index]
      exact (localValidity.2 (execution.state index) inductionHypothesis).2

/-- The proof-carrying controller is an executable plan: its selected indices
replay to exactly the states in every controlled execution. -/
theorem follow_occurrenceTrace
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    {definition : GSLTBranchingPresentation theory Unit}
    {stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory}
    {accepting : theory.Term → Bool}
    {controller : MemorylessController theory.Term
      (OccurrenceLink theory stepAuthority.Certificate)}
    {root : theory.Term}
    (localValidity : controller.LocallyValid
      (auditedOccurrenceSystem definition stepAuthority accepting) root)
    (execution : ControlledExecution controller root) :
    ∀ length,
      follow definition root (occurrenceTrace execution length) =
        some (execution.state length) := by
  intro length
  induction length with
  | zero => simp [occurrenceTrace, follow, execution.starts]
  | succ length inductionHypothesis =>
      have active := active_of_locallyValid localValidity execution length
      have selected :=
        (localValidity.2 (execution.state length) active).1
      have audited :=
        (auditedOccurrenceSystem_step_eq_true_iff definition stepAuthority
          accepting _ _ _).mp selected
      have lookupNext :
          (definition.successors (execution.state length))[(controller.action
            (execution.state length)).index]? =
            some (controller.next (execution.state length)) := by
        simpa [audited.2.1] using audited.1
      rw [occurrenceTrace, follow_append, inductionHypothesis]
      simp only [Option.bind_some]
      rw [execution.follows length]
      simp [follow, lookupNext]

end ControlledExecution

private theorem multistep_tail {theory : GSLT}
    {first middle last : theory.Term}
    (path : theory.MultiStep first middle)
    (lastStep : theory.Step middle last) :
    theory.MultiStep first last := by
  induction path with
  | refl _ => exact .step lastStep (.refl _)
  | step firstStep rest inductionHypothesis =>
      exact .step firstStep (inductionHypothesis lastStep)

/-- Every finite prefix selected by a locally valid controller is also a
genuine finite GSLT derivation. -/
theorem controlledExecution_multistep
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    {definition : GSLTBranchingPresentation theory Unit}
    {stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory}
    {accepting : theory.Term → Bool}
    {controller : MemorylessController theory.Term
      (OccurrenceLink theory stepAuthority.Certificate)}
    {root : theory.Term}
    (localValidity : controller.LocallyValid
      (auditedOccurrenceSystem definition stepAuthority accepting) root)
    (execution : ControlledExecution controller root) :
    ∀ length, theory.MultiStep root (execution.state length) := by
  intro length
  induction length with
  | zero => simpa [execution.starts] using GSLT.MultiStep.refl root
  | succ length inductionHypothesis =>
      apply multistep_tail inductionHypothesis
      have active :=
        ControlledExecution.active_of_locallyValid localValidity execution length
      have selected :=
        (localValidity.2 (execution.state length) active).1
      have genuine := auditedOccurrenceSystem_step_sound definition
        stepAuthority accepting selected
      rw [execution.follows length]
      exact genuine

/-! ## Proof-as-plan statement and objective completeness -/

/-- A controller is an executable Büchi proof-plan when every finite prefix
both replays by exact transition occurrence and denotes a GSLT path, while its
infinite executions satisfy the stated recurrence objective. -/
def IsExecutableBuchiPlan
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (definition : GSLTBranchingPresentation theory Unit)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term → Bool)
    (controller : MemorylessController theory.Term
      (OccurrenceLink theory stepAuthority.Certificate))
    (root : theory.Term) : Prop :=
  (∀ execution : ControlledExecution controller root,
      ∀ length,
        follow definition root
            (ControlledExecution.occurrenceTrace execution length) =
              some (execution.state length) ∧
          theory.MultiStep root (execution.state length)) ∧
    controller.BuchiWinning
      (auditedOccurrenceSystem definition stepAuthority accepting) root

/-- A valid finite progress measure is simultaneously a proof of the global
objective and an executable occurrence-level plan. -/
theorem valid_progress_is_executable_plan
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (definition : GSLTBranchingPresentation theory Unit)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term → Bool)
    (controller : MemorylessController theory.Term
      (OccurrenceLink theory stepAuthority.Certificate))
    (measure : ProgressMeasure theory.Term) (root : theory.Term)
    (valid : measure.Valid
      (auditedOccurrenceSystem definition stepAuthority accepting)
      controller root) :
    IsExecutableBuchiPlan definition stepAuthority accepting controller root := by
  constructor
  · intro execution length
    exact ⟨ControlledExecution.follow_occurrenceTrace valid.1 execution length,
      controlledExecution_multistep valid.1 execution length⟩
  · exact ProgressMeasure.buchi_sound valid

/-- The executable checker, rather than the certificate producer, establishes
the proof-as-plan result. -/
theorem checked_progress_is_executable_plan
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [Fintype theory.Term] [DecidableEq theory.Term]
    (definition : GSLTBranchingPresentation theory Unit)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term → Bool)
    (controller : MemorylessController theory.Term
      (OccurrenceLink theory stepAuthority.Certificate))
    (measure : ProgressMeasure theory.Term) (root : theory.Term)
    (accepted : measure.check
      (auditedOccurrenceSystem definition stepAuthority accepting)
      controller root = true) :
    IsExecutableBuchiPlan definition stepAuthority accepting controller root := by
  apply valid_progress_is_executable_plan definition stepAuthority accepting
    controller measure root
  exact (ProgressMeasure.check_eq_true_iff
    (auditedOccurrenceSystem definition stepAuthority accepting)
    controller measure root).mp accepted

/-- Certificate-existence completeness is exact for uniform Büchi recurrence
over the declared active region.  Root-only recurrence is intentionally not
substituted for this stronger objective. -/
theorem progress_certificate_exists_iff_uniformBuchi
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [Fintype theory.Term] [DecidableEq theory.Term]
    (definition : GSLTBranchingPresentation theory Unit)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term → Bool)
    (controller : MemorylessController theory.Term
      (OccurrenceLink theory stepAuthority.Certificate))
    (root : theory.Term) :
    (∃ measure : ProgressMeasure theory.Term,
        measure.check
          (auditedOccurrenceSystem definition stepAuthority accepting)
          controller root = true) ↔
      controller.UniformBuchiWinning
        (auditedOccurrenceSystem definition stepAuthority accepting) root := by
  rw [← ProgressMeasure.exists_valid_iff_uniformBuchi]
  constructor
  · rintro ⟨measure, accepted⟩
    exact ⟨measure, (ProgressMeasure.check_eq_true_iff _ _ _ _).mp accepted⟩
  · rintro ⟨measure, valid⟩
    exact ⟨measure, (ProgressMeasure.check_eq_true_iff _ _ _ _).mpr valid⟩

/-! ## Positive and negative executable witnesses -/

namespace Examples

@[reducible] def toggleTheory : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => target = !source
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def toggleSuccessors : Bool → List Bool
  | false => [true]
  | true => [false]

def togglePresentation : GSLTBranchingPresentation toggleTheory Unit where
  emit _ := none
  successors := toggleSuccessors
  step_iff_mem := by
    intro source target
    cases source <;> cases target <;>
      simp [toggleSuccessors, toggleTheory, GSLT.Step]

def toggleStepAuthority : StepAuthority String toggleTheory where
  id := "toggle-occurrence-step-v1"
  Certificate := Unit
  check := fun claim _ => decide (claim.target = !claim.source)
  sound := by
    intro claim certificate accepted
    change claim.target = !claim.source
    exact of_decide_eq_true accepted

def acceptsTrue : Bool → Bool := id

def goodAction (state : Bool) :
    OccurrenceLink toggleTheory Unit :=
  ⟨0, !state, ()⟩

def goodController :
    MemorylessController Bool (OccurrenceLink toggleTheory Unit) where
  active _ := true
  action := goodAction
  next state := !state

def goodMeasure : ProgressMeasure Bool where
  rank
    | false => 1
    | true => 0

theorem goodMeasure_valid : goodMeasure.Valid
    (auditedOccurrenceSystem togglePresentation toggleStepAuthority acceptsTrue)
    goodController false := by
  constructor
  · constructor
    · rfl
    · intro state _
      cases state <;> exact ⟨rfl, rfl⟩
  · intro state _
    cases state <;>
      simp [auditedOccurrenceSystem, acceptsTrue, goodController, goodMeasure]

/-- The checked controller is a recurrent executable plan. -/
example : goodMeasure.check
    (auditedOccurrenceSystem togglePresentation toggleStepAuthority acceptsTrue)
    goodController false = true := by
  exact (ProgressMeasure.check_eq_true_iff _ _ _ _).mpr goodMeasure_valid

/-- Its first four control choices replay as four exact successor indices. -/
example :
    let execution := goodController.canonicalExecution false
    ControlledExecution.occurrenceTrace (theory := toggleTheory)
      execution 4 = [0, 0, 0, 0] := by
  decide

/-- A locally valid proof action with a nonexistent occurrence index is
rejected even though its target and semantic edge evidence are otherwise
correct. -/
def badIndexController :
    MemorylessController Bool (OccurrenceLink toggleTheory Unit) where
  active _ := true
  action state := ⟨1, !state, ()⟩
  next state := !state

theorem badIndexController_not_locallyValid :
    ¬ badIndexController.LocallyValid
      (auditedOccurrenceSystem togglePresentation toggleStepAuthority acceptsTrue)
      false := by
  intro valid
  have selected := (valid.2 false rfl).1
  simp [auditedOccurrenceSystem, togglePresentation, toggleSuccessors,
    badIndexController, toggleStepAuthority] at selected

example : goodMeasure.check
    (auditedOccurrenceSystem togglePresentation toggleStepAuthority acceptsTrue)
    badIndexController false = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have valid := (ProgressMeasure.check_eq_true_iff _ _ _ _).mp accepted
  exact badIndexController_not_locallyValid valid.1

end Examples

#print axioms auditedOccurrenceSystem_step_sound
#print axioms ControlledExecution.follow_occurrenceTrace
#print axioms controlledExecution_multistep
#print axioms checked_progress_is_executable_plan
#print axioms progress_certificate_exists_iff_uniformBuchi

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.InferenceControl
