import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalFunctor
import Mettapedia.Languages.LambdaCalculus.NamePassingOperationalOccurrenceComparison
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenControls

/-!
# Actual communication trees, binder positions and complete path controls

An active beta below a supplied carrier is followed by a real fetch. Both
occurrences compose on the actual internal pullback and their compiled path
retains a binary then unary reaction. Target substitution changes both the
complete supplied program bodies and the communicated names. Two actual
parallel firings also demonstrate that endpoints cannot decode occurrences.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalControls

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open NamePassingOpenInterpretation NamePassingOperationalEvents
open Mettapedia.CategoryTheory


def beta : SourceEvent NamePassingOpenInterpretation.Controls.sourceScope := .beta NamePassingOpenInterpretation.Controls.body NamePassingOpenInterpretation.Controls.referenceName

theorem beta_target_readout :
    (mapEvent beta NamePassingOpenInterpretation.Controls.environment NamePassingOpenInterpretation.Controls.secondReturn).target = NamePassingOpenInterpretation.Controls.expectedBetaTarget :=
  (target_readout beta NamePassingOpenInterpretation.Controls.environment NamePassingOpenInterpretation.Controls.secondReturn).trans NamePassingOpenInterpretation.Controls.computed_beta_target

theorem complete_binary_receiver_readout :
    (mapEvent beta NamePassingOpenInterpretation.Controls.environment NamePassingOpenInterpretation.Controls.secondReturn).reaction =
      .restriction (.binary (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))
        (interpret NamePassingOpenInterpretation.Controls.body ((NamePassingOpenInterpretation.Controls.environment.substitute weakening).substitute weakening).lift
          (.var (.succ .zero)))) := rfl

theorem actual_beta_occurrence :
    StepModulo (interpret beta.source NamePassingOpenInterpretation.Controls.environment NamePassingOpenInterpretation.Controls.secondReturn) NamePassingOpenInterpretation.Controls.expectedBetaTarget := by
  rw [← beta_target_readout]
  exact (mapEvent beta NamePassingOpenInterpretation.Controls.environment NamePassingOpenInterpretation.Controls.secondReturn).sound

def identify : Sub sig NamePassingOpenInterpretation.Controls.targetScope NamePassingOpenInterpretation.Controls.targetScope
  | _, .zero => .var (.succ .zero)
  | _, .succ .zero => .var (.succ .zero)

/-- Identification affects the full receiver and its received program body,
not merely a may-return flag. -/
theorem identified_beta_complete_readout :
    (mapEvent beta NamePassingOpenInterpretation.Controls.environment NamePassingOpenInterpretation.Controls.secondReturn).substitute identify =
      mapEvent beta (NamePassingOpenInterpretation.Controls.environment.substitute identify) (bind identify NamePassingOpenInterpretation.Controls.secondReturn) :=
  event_substitution beta NamePassingOpenInterpretation.Controls.environment NamePassingOpenInterpretation.Controls.secondReturn identify

theorem identified_argument_and_return :
    (mapEvent beta (NamePassingOpenInterpretation.Controls.environment.substitute identify) (bind identify NamePassingOpenInterpretation.Controls.secondReturn)).reaction =
      .restriction (.binary (.var .zero) (.var (.succ (.succ .zero))) (.var (.succ (.succ .zero)))
        (interpret NamePassingOpenInterpretation.Controls.body
          (((NamePassingOpenInterpretation.Controls.environment.substitute identify).substitute weakening).substitute weakening).lift
          (.var (.succ .zero)))) := rfl

theorem identified_target_is_actual_substitution :
    (mapEvent beta (NamePassingOpenInterpretation.Controls.environment.substitute identify) (bind identify NamePassingOpenInterpretation.Controls.secondReturn)).target =
      bind identify NamePassingOpenInterpretation.Controls.expectedBetaTarget := by
  rw [← identified_beta_complete_readout]
  exact congrArg (bind identify) beta_target_readout

theorem exchanged_target_distinct :
    (mapEvent beta NamePassingOpenInterpretation.Controls.environment NamePassingOpenInterpretation.Controls.secondReturn).target ≠ NamePassingOpenInterpretation.Controls.exchangedBetaTarget := by
  rw [beta_target_readout]
  exact NamePassingOpenInterpretation.Controls.exchanged_names_have_different_readout

def boundReference : NamePassing.Presentation.Program (.nm :: NamePassingOpenInterpretation.Controls.sourceScope) :=
  NamePassing.Presentation.reference (.var .zero)

def firstOccurrence : SourceEvent NamePassingOpenInterpretation.Controls.sourceScope :=
  .carrier NamePassingOpenInterpretation.Controls.referenceName NamePassingOpenInterpretation.Controls.firstHole (.beta boundReference NamePassingOpenInterpretation.Controls.referenceName)

def lastOccurrence : SourceEvent NamePassingOpenInterpretation.Controls.sourceScope := .fetch NamePassingOpenInterpretation.Controls.referenceName NamePassingOpenInterpretation.Controls.firstHole

theorem successive_endpoints : firstOccurrence.target = lastOccurrence.source := rfl

def inputs : NamePassingOperationalFunctor.Inputs NamePassingOpenInterpretation.Controls.sourceScope NamePassingOpenInterpretation.Controls.targetScope :=
  ⟨NamePassingOpenInterpretation.Controls.environment, NamePassingOpenInterpretation.Controls.secondReturn⟩

def firstEvents : NamePassingOperationalFunctor.programs NamePassingOpenInterpretation.Controls.sourceScope ⟶ NamePassingOperationalFunctor.events NamePassingOpenInterpretation.Controls.sourceScope where
  app _ := TypeCat.ofHom (fun supplied => (supplied.1, firstOccurrence))
  naturality _ _ _ := rfl

def lastEvents : NamePassingOperationalFunctor.programs NamePassingOpenInterpretation.Controls.sourceScope ⟶ NamePassingOperationalFunctor.events NamePassingOpenInterpretation.Controls.sourceScope where
  app _ := TypeCat.ofHom (fun supplied => (supplied.1, lastOccurrence))
  naturality _ _ _ := rfl

def first : NamePassingOperationalFunctor.programs NamePassingOpenInterpretation.Controls.sourceScope ⟶ (NamePassingOperationalFunctor.internalCategory NamePassingOpenInterpretation.Controls.sourceScope).edge :=
  firstEvents ≫ InternalCategoryPathDiagram.edgeInclusion (NamePassingOperationalFunctor.graph NamePassingOpenInterpretation.Controls.sourceScope)

def last : NamePassingOperationalFunctor.programs NamePassingOpenInterpretation.Controls.sourceScope ⟶ (NamePassingOperationalFunctor.internalCategory NamePassingOpenInterpretation.Controls.sourceScope).edge :=
  lastEvents ≫ InternalCategoryPathDiagram.edgeInclusion (NamePassingOperationalFunctor.graph NamePassingOpenInterpretation.Controls.sourceScope)

theorem matching : first ≫ (NamePassingOperationalFunctor.internalCategory NamePassingOpenInterpretation.Controls.sourceScope).target =
    last ≫ (NamePassingOperationalFunctor.internalCategory NamePassingOpenInterpretation.Controls.sourceScope).source := by
  ext X supplied
  exact congrArg (fun term => (supplied.1, term)) successive_endpoints

def campaign : NamePassingOperationalFunctor.programs NamePassingOpenInterpretation.Controls.sourceScope ⟶ (NamePassingOperationalFunctor.internalCategory NamePassingOpenInterpretation.Controls.sourceScope).edge :=
  (NamePassingOperationalFunctor.internalCategory NamePassingOpenInterpretation.Controls.sourceScope).compose first last matching

abbrev stage : NamePassingOperationalFunctor.Base := Opposite.op ⟨NamePassingOpenInterpretation.Controls.targetScope⟩

inductive Kind where
  | unary | binary
  deriving DecidableEq

def reactionKind : {Δ : Ctx sig} → OperationalDiagram.Reaction Δ → Kind
  | _, .unary .. => .unary
  | _, .binary .. => .binary
  | _, .parallelLeft before _ => reactionKind before
  | _, .parallelRight _ before => reactionKind before
  | _, .restriction before => reactionKind before

def ledger {a : InternalCategoryPathDiagram.Vertex OperationalDiagram.graph stage} :
    {b : InternalCategoryPathDiagram.Vertex OperationalDiagram.graph stage} → InternalCategoryPathDiagram.Path OperationalDiagram.graph stage a b → List Kind
  | _, .nil => []
  | _, .cons before edge => ledger before ++ [reactionKind edge.1.reaction]

def readout (path : InternalCategoryDiagram.Arrow ((InternalCategoryPathDiagram.diagram OperationalDiagram.graph).obj stage)) :
    List Kind := ledger path.2.2

theorem compiled_two_step_ledger :
    readout ((NamePassingOperationalFunctor.internalFunctor NamePassingOpenInterpretation.Controls.sourceScope).edge.app stage
      (campaign.app stage (inputs, NamePassingOpenInterpretation.Controls.firstHole))) = [.binary, .unary] := by
  have actual := InternalCategoryDiagram.composeWith_apply
    (InternalCategoryPathDiagram.diagram (NamePassingOperationalFunctor.graph NamePassingOpenInterpretation.Controls.sourceScope)) first last matching stage (inputs, NamePassingOpenInterpretation.Controls.firstHole)
  change campaign.app stage (inputs, NamePassingOpenInterpretation.Controls.firstHole) = _ at actual
  rw [actual]
  rw [NamePassingOperationalFunctor.path_readout]
  rfl

theorem compiled_two_step_result :
    OperationalDiagram.internalCategory.target.app stage
      ((NamePassingOperationalFunctor.internalFunctor NamePassingOpenInterpretation.Controls.sourceScope).edge.app stage
        (campaign.app stage (inputs, NamePassingOpenInterpretation.Controls.firstHole))) = out1 (.var (.succ .zero)) (.var (.succ .zero)) := by
  have square := (NamePassingOperationalFunctor.internalFunctor NamePassingOpenInterpretation.Controls.sourceScope).target
  have read := congrArg (fun (arrow : (NamePassingOperationalFunctor.internalCategory NamePassingOpenInterpretation.Controls.sourceScope).edge ⟶
      OperationalDiagram.programs) => arrow.app stage (campaign.app stage (inputs, NamePassingOpenInterpretation.Controls.firstHole))) square
  change OperationalDiagram.internalCategory.target.app stage
    ((NamePassingOperationalFunctor.internalFunctor NamePassingOpenInterpretation.Controls.sourceScope).edge.app stage
      (campaign.app stage (inputs, NamePassingOpenInterpretation.Controls.firstHole))) =
    (NamePassingOperationalFunctor.internalFunctor NamePassingOpenInterpretation.Controls.sourceScope).vertex.app stage
      ((NamePassingOperationalFunctor.internalCategory NamePassingOpenInterpretation.Controls.sourceScope).target.app stage
        (campaign.app stage (inputs, NamePassingOpenInterpretation.Controls.firstHole))) at read
  rw [read]
  have endpoint := congrArg (fun (arrow : NamePassingOperationalFunctor.programs NamePassingOpenInterpretation.Controls.sourceScope ⟶
      (NamePassingOperationalFunctor.internalCategory NamePassingOpenInterpretation.Controls.sourceScope).vertex) => arrow.app stage (inputs, NamePassingOpenInterpretation.Controls.firstHole))
      ((NamePassingOperationalFunctor.internalCategory NamePassingOpenInterpretation.Controls.sourceScope).compose_target first last matching)
  change (NamePassingOperationalFunctor.internalCategory NamePassingOpenInterpretation.Controls.sourceScope).target.app stage
      (campaign.app stage (inputs, NamePassingOpenInterpretation.Controls.firstHole)) =
    (inputs, lastOccurrence.target) at endpoint
  exact (congrArg (fun supplied : (NamePassingOperationalFunctor.programs
      NamePassingOpenInterpretation.Controls.sourceScope).obj stage =>
        interpret supplied.2 supplied.1.environment supplied.1.result) endpoint).trans
    NamePassingOpenInterpretation.Controls.changed_program_return

def firing : OperationalDiagram.Reaction NamePassingOpenInterpretation.Controls.targetScope :=
  .unary NamePassingOpenInterpretation.Controls.firstReturn NamePassingOpenInterpretation.Controls.secondReturn (out1 (.var .zero) (.var .zero))

def leftFiring : TargetEvent NamePassingOpenInterpretation.Controls.targetScope :=
  (OperationalDiagram.Event.ofReaction firing).parallelLeft firing.source

def rightFiring : TargetEvent NamePassingOpenInterpretation.Controls.targetScope where
  source := leftFiring.source
  target := leftFiring.target
  reaction := .parallelRight firing.source firing
  source_readout := .refl _
  target_readout := .parComm _ _

theorem duplicate_firings_have_same_endpoints :
    leftFiring.source = rightFiring.source ∧ leftFiring.target = rightFiring.target := ⟨rfl, rfl⟩

theorem complete_firings_distinct : leftFiring ≠ rightFiring := by
  intro same
  have trees := congrArg OperationalDiagram.Event.reaction same
  cases trees

theorem both_complete_firings_are_actual :
    StepModulo leftFiring.source leftFiring.target ∧ StepModulo rightFiring.source rightFiring.target :=
  ⟨leftFiring.sound, rightFiring.sound⟩

theorem no_endpoint_firing_decoder :
    ¬ ∃ decode : Proc NamePassingOpenInterpretation.Controls.targetScope × Proc NamePassingOpenInterpretation.Controls.targetScope → TargetEvent NamePassingOpenInterpretation.Controls.targetScope,
      ∀ supplied, decode (supplied.source, supplied.target) = supplied := by
  rintro ⟨decode, correct⟩
  exact complete_firings_distinct ((correct leftFiring).symm.trans (correct rightFiring))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalControls
