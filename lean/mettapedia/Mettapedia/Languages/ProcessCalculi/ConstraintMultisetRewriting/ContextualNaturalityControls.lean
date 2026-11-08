import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPreparationExtensions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProducerRowControls

/-!
# Capture transport acts on real producer values without freshening schema locals

The capture interface is the actual producer's returned endpoint, not just
the initial caller family. A nonidentity binding changes its shared output;
the retained schema's private variable is untouched. Pure extensions reflect
asks, while that binding can make an earlier unsupported question true.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNaturalityControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualViewNaturality
open ContextualSelectionViews.Controls (base locals atom pair)
open ContextualProducerRowControls (after stored readTwice readRule)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : DecidableEq after.Names := after.equality

def producerName : after.Names := .inl (.inl (ScopedVar.at 8 0))
def boundValue : Term (signature base after.declarations) [] () := pair (atom _) (atom _)

def binding : Assignment after.declarations after.declarations := fun name => by
  by_cases same : name = producerName
  · subst name
    exact boundValue
  · exact generator after.declarations name

abbrev next := ContextualActivatedStep.target locals after.declarations
abbrev rawNext := ContextualActivatedStep.source locals after.declarations
def nextBound : Term (signature base next) [] () := pair (atom _) (atom _)

theorem actual_shared_output_transport_changes_the_capture_value :
    instantiate (activeLift locals binding)
      (ContextualStoredRows.viewAt locals after.declarations 20 (after.inventory.rows 99)) = nextBound := by
  rw [viewAt_transport locals binding]
  with_unfolding_all rfl

theorem the_retained_schema_local_is_not_the_producer_capture :
    (after.inventory.rows 7).map locals binding = after.inventory.rows 7 := by with_unfolding_all rfl

theorem actual_prepared_problem_transport :
    ContextualFrameUnifier.mapProblem (activeLift locals binding)
        (ContextualActivatedStep.problem locals after.declarations after.occupied (readTwice 99) readRule
          after.inventory.rows after.inventory.configuration) =
      ContextualActivatedStep.problem locals after.declarations after.occupied (readTwice 99)
        (readRule.map (instantiate (ContextualStoredRows.liftCaptures locals binding)))
        (fun occurrence => (after.inventory.rows occurrence).map locals binding)
        (ContextualTransportedActivation.configurationMap binding after.inventory.configuration) :=
  ContextualPreparationNaturality.problem_transport locals binding after.occupied (readTwice 99) readRule
    after.inventory.rows after.inventory.configuration

def emptySelection : Selection Nat := ⟨[], [], []⟩
def checkRule : RuleInstance (Term (signature base rawNext) [] ()) :=
  ⟨[], [], [], [.equal (generator rawNext (.inr producerName)) (pair (atom _) (atom _))], []⟩
def question : Check (Term (signature base next) [] ()) :=
  .equal (instantiate (ContextualSelectionViews.capturedTarget locals after.declarations) stored) nextBound
def prefixProblem := ContextualActivatedStep.problem locals after.declarations after.occupied emptySelection checkRule
  after.inventory.rows after.inventory.configuration

theorem no_question_binding_is_hidden_in_the_source_problem : prefixProblem = [] := rfl

theorem the_original_question_is_unentailed :
    ¬ ContextualGuardSemantics.Ask locals prefixProblem
      (ContextualGuardedStep.guardRows locals after.declarations after.inventory.rows)
      after.inventory.configuration.present question := by
  intro asked
  have same := asked (ScopedVar Nat ⊕ after.Names) next (generator next) (fun _ member => by cases member)
  change generator next (.inr producerName) = nextBound at same
  have heads := (Term.op.inj same).1
  cases heads

abbrev unused (_ : Unit) : MetaArity base := ([()], ())
def extension := ContextualGuardMatching.Extension.withLocals unused after.declarations

theorem the_pure_extension_of_the_actual_producer_frame_keeps_the_question_unentailed :
    ¬ ContextualGuardSemantics.Ask locals
      (ContextualActivatedStep.problem locals extension.declarations after.occupied emptySelection
        (checkRule.map (instantiate (ContextualStoredRows.liftCaptures locals extension.assignment)))
        (fun occurrence => (after.inventory.rows occurrence).map locals extension.assignment)
        (ContextualTransportedActivation.configurationMap extension.assignment after.inventory.configuration))
      (ContextualGuardedStep.guardRows locals extension.declarations
        (fun occurrence => (after.inventory.rows occurrence).map locals extension.assignment))
      after.inventory.configuration.present (question.map (instantiate (activeLift locals extension.assignment))) := by
  intro transported
  exact the_original_question_is_unentailed
    ((prepared_ask_extension_iff locals extension after.occupied emptySelection checkRule
      after.inventory.rows after.inventory.configuration question).mp transported)

theorem a_binding_can_make_the_question_true_without_reflecting_it :
    ContextualGuardSemantics.Ask locals
      (ContextualActivatedStep.problem locals after.declarations after.occupied emptySelection
        (checkRule.map (instantiate (ContextualStoredRows.liftCaptures locals binding)))
        (fun occurrence => (after.inventory.rows occurrence).map locals binding)
        (ContextualTransportedActivation.configurationMap binding after.inventory.configuration))
      (ContextualGuardedStep.guardRows locals after.declarations
        (fun occurrence => (after.inventory.rows occurrence).map locals binding))
      after.inventory.configuration.present (question.map (instantiate (activeLift locals binding))) ∧
      ¬ ContextualGuardSemantics.Ask locals prefixProblem
        (ContextualGuardedStep.guardRows locals after.declarations after.inventory.rows)
        after.inventory.configuration.present question := by
  refine ⟨?_, the_original_question_is_unentailed⟩
  have equal : instantiate (activeLift locals binding)
        (instantiate (ContextualSelectionViews.capturedTarget locals after.declarations) stored) =
      instantiate (activeLift locals binding) nextBound := by with_unfolding_all rfl
  intro Future future candidate _model
  exact congrArg (instantiate candidate) equal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNaturalityControls
