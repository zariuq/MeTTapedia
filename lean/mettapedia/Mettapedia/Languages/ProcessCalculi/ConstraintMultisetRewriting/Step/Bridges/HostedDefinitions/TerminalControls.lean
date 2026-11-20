import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.TerminalAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ControlProtocol
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuleInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Data

/-!
# Literal terminal separation has a fixed-program boundary

A positive source run really ends with a native value's encoding. Adding an
equation at the done head makes that term reducible and violates the needed
literal separation premise. This is not an arbitrary-context equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.TerminalControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open RuleBuilder

def call : MClosed := activeC "start" []
def value : MClosed := encodeTm (TowerVectorsModel.zeroC : Tower.Tm 0)
def answer : MClosed := doneC value

def ordinary := equation (n := 0) (literal call) (literal answer)
def rows : List (ProgramBinders.Equation MSig [] ()) := [ordinary]

theorem separated : HeadSeparated rows activeTag doneTag where
  distinct := active_done_distinct
  lhs index := by
    fin_cases index
    rfl
  rhs index := by
    fin_cases index
    exact .inr rfl

theorem rewrites : ProgramBinders.Rewrites rows.get call answer := by
  have step := RuleInstances.template (rows := rows) (literal (n := 0) call) (literal answer)
    (List.mem_singleton_self ordinary) Fin.elim0
  simpa using step

theorem actual_source_answer : ∃ configuration,
    Runs untyped.discipline (BinderCore.program rows) (fun _ => csym "space")
      (BinderCore.start rows call) configuration ∧ HasAnswer rows configuration answer :=
  (answers_iff (D := untyped.discipline) rows separated (fun _ => csym "space") call answer
    (.inl (active_head _ _)) (done_head _)).mp (.single rewrites)

def extra := equation (n := 0) (literal answer) (literal call)
def extended : List (ProgramBinders.Equation MSig [] ()) := [ordinary, extra]

theorem arbitrary_added_equation_breaks_separation : ¬ HeadSeparated extended activeTag doneTag := by
  intro allowed
  have clash := allowed.lhs ⟨1, by decide⟩
  exact active_done_distinct (Option.some.inj clash).symm

theorem added_equation_rewrites_done : ProgramBinders.Rewrites extended.get answer call := by
  have step := RuleInstances.template (rows := extended) (literal (n := 0) answer) (literal call)
    (by simp [extended, extra]) Fin.elim0
  simpa using step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.TerminalControls
