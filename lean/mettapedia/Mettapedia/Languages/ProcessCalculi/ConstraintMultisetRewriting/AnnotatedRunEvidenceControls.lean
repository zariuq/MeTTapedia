import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidenceBridges
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidenceEquivariance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAttemptOutcomesControls

/-!
# Controls for evidence-rich histories

The controls distinguish three claims that are easy to conflate:

* evidence fields are retained by the rich history but erased by the thin
  firing projection;
* a failed attempt changes no semantic state, while its physical charge stays
  observable;
* an environment input is not a failed attempt and cannot in general be
  erased from an execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidence.Controls

abbrev Thin := Nat
abbrev Prov := Provenance Nat Nat Nat
abbrev Rich := FiringEvidence Thin Nat Prov Nat Nat (List Nat)
abbrev Attempt := AttemptRecord (List Nat) Nat Nat Nat
abbrev Env := EnvironmentEvent Nat Nat Nat
abbrev RichEvent := Event Rich Attempt Env

def firstWorld : Rich where
  firing := 2
  witness := 11
  provenance := ⟨4, 5, some 6⟩
  world := 7
  round := 0
  queryEvidence := [1, 3]

def secondWorld : Rich := { firstWorld with world := 8 }

def forget (event : Rich) : Thin := event.firing

def worldOf (event : Rich) : Nat := event.world

def refusal : Attempt where
  outcome := .refused
  nonfiring := by decide
  answers := [4, 5]
  task := 9
  world := 7
  round := 0
  charge := 13

def input : Env := .input 10 3
def outputFour : Env := .output 4 80
def outputFourAgain : Env := .output 4 81
def outputFive : Env := .output 5 90

def step (firing before after : Nat) : Prop := after = before + firing

def environmentStep : Env → Nat → Nat → Prop
  | .input _ payload, before, after => after = before + payload
  | .output _ _, before, after => after = before

theorem step_functional : Functional step := by
  intro firing before first second left right
  exact left.trans right.symm

theorem environmentStep_functional : Functional environmentStep := by
  intro event before first second left right
  cases event <;> simp only [environmentStep] at left right <;>
    exact left.trans right.symm

def observed : List RichEvent :=
  [.fired firstWorld, .attempted refusal, .environment input]

theorem observed_run : Run forget step environmentStep 0 observed 5 := by
  apply Run.firing (middle := 2)
  · rfl
  apply Run.attempted
  apply Run.environment (middle := 5)
  · rfl
  exact .nil 5

theorem erasing_attempts_keeps_the_scripted_run :
    CoreRun step environmentStep 0 (coreWord forget observed) 5 :=
  observed_run.eraseAttempts

def noEnvironment : List RichEvent := [.fired firstWorld, .attempted refusal]

theorem noEnvironment_run : Run forget step environmentStep 0 noEnvironment 2 := by
  apply Run.firing (middle := 2)
  · rfl
  apply Run.attempted
  exact .nil 2

theorem noEnvironment_word : NoEnvironment noEnvironment :=
  .firing firstWorld (.attempted refusal .nil)

theorem forgetting_evidence_gives_the_old_run :
    FiringRun step 0 (firingWord forget noEnvironment) 2 :=
  noEnvironment_run.forget_noEnvironment noEnvironment_word

theorem failed_attempt_cost_survives : attemptCharge noEnvironment = 13 := rfl

theorem failed_attempt_cost_is_erased_from_the_firing_word :
    eraseHistory forget (FreeMonoid.ofList noEnvironment) = FreeMonoid.ofList [2] ∧
      attemptCharge noEnvironment = 13 := by
  constructor
  · rw [eraseHistory_ofList]
    rfl
  · rfl

theorem search_worlds_are_real_history_data : firstWorld ≠ secondWorld := by
  intro same
  have worlds := congrArg FiringEvidence.world same
  change 7 = 8 at worlds
  omega

theorem thin_history_forgets_the_search_world :
    eraseHistory (Attempt := Attempt) (Environment := Env) forget
        (FreeMonoid.of (.fired firstWorld)) =
      eraseHistory (Attempt := Attempt) (Environment := Env) forget
        (FreeMonoid.of (.fired secondWorld)) := by
  simp [forget, firstWorld, secondWorld]

theorem thin_firing_is_fiber_stable :
    FiberStable forget (fun event : Rich => event.firing) := by
  intro first second same
  exact same

theorem search_world_is_not_fiber_stable : ¬ FiberStable forget worldOf := by
  intro stable
  have same := stable firstWorld secondWorld rfl
  change 7 = 8 at same
  omega

theorem search_world_does_not_factor_through_the_thin_firing :
    ¬ FactorsThrough forget worldOf := by
  intro factors
  exact search_world_is_not_fiber_stable factors.fiberStable

def environmentOnly : List RichEvent := [.environment input]

theorem environment_input_is_an_actual_transition :
    Run forget step environmentStep 0 environmentOnly 3 :=
  .environment rfl (.nil 3)

theorem environment_input_cannot_be_erased_as_an_attempt :
    ¬ FiringRun step 0 [] 3 := by
  intro run
  cases run

theorem deterministic_replay (first second : Nat)
    (left : Run forget step environmentStep 0 observed first)
    (right : Run forget step environmentStep 0 observed second) : first = second :=
  Run.final_unique step_functional environmentStep_functional left right

theorem repeated_output_keys_are_applied_at_most_once :
    (Mettapedia.GSLT.Coordination.Deduplication.receiveAll
      Mettapedia.GSLT.Coordination.Deduplication.Receiver.empty
      (outputDeliveries [outputFour, outputFourAgain, outputFive])).applied.Nodup :=
  replayed_outputs_at_most_once _

open ContextualConjunctiveControls ContextualQueryAnswersControls
open ContextualSelectionViews.Controls (base)
open ConstraintMultisetRewriting.Controls (A)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def actualNoneRecord : AttemptRecord
    (Finset (Fin ContextualAttemptOutcomes.Controls.emptySearch.patterns.length → Nat)) Nat Nat Nat :=
  AnnotatedRunEvidenceBridges.attemptRecord queries locals captures
    ContextualAttemptOutcomes.Controls.completed_empty_search_reports_none (by decide) 17 23 0 5

@[simp] theorem actual_none_record_outcome : actualNoneRecord.outcome = .none := rfl

@[simp] theorem actual_none_record_charge : actualNoneRecord.charge = 5 := rfl

theorem recorded_none_is_not_a_firing : actualNoneRecord.outcome ≠ .fired :=
  actualNoneRecord.nonfiring

#print axioms erasing_attempts_keeps_the_scripted_run
#print axioms forgetting_evidence_gives_the_old_run
#print axioms deterministic_replay
#print axioms recorded_none_is_not_a_firing
#print axioms search_world_does_not_factor_through_the_thin_firing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidence.Controls
