import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ParallelRunExchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResidualRunClosingControls

/-!
# A local parallel exchange in a system without global closing

The existing tell-dropping transport has no profile-wide closing operation.
Two fresh resource-making events nevertheless have the required local square
and compose through the general complete-run construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.LocalClosingControls

open Mettapedia.Logic.LP
open AnnotatedRuns
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label)
open AnnotatedRuns.RoundControls (empty)

abbrev P := ResidualRunClosingControls.P
abbrev T := ResidualRunClosingControls.T

def maker (n : Nat) : AnnotatedRuns.Controls.Run := ⟨⟨[], [], [], [], [label n]⟩, [], ⟨[], [], [n]⟩⟩

theorem maker_valid (n : Nat) (state : Configuration (Term signature) Nat)
    (noKnowledge : state.equations = []) (fresh : n ∉ state.present) :
    (maker n).Valid A label state := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, ?_, ?_, by simp [maker]⟩,
    by simp [maker]⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [maker, Selection.commit, fresh]
  · refine ⟨Subst.id signature, ?_⟩
    intro equation member
    simp [Selection.problem, Selection.equations, maker, noKnowledge] at member

theorem first_admitted : P.Admits (s := empty) (maker 1) := maker_valid _ _ rfl (by decide)
theorem second_admitted : P.Admits (s := empty) (maker 2) := maker_valid _ _ rfl (by decide)

theorem after_first : P.Admits (s := P.result (maker 1) first_admitted)
    (T.residual (maker 1) first_admitted (maker 2)) :=
  maker_valid _ _ rfl (by decide)

theorem after_second : P.Admits (s := P.result (maker 2) second_admitted)
    (T.residual (maker 2) second_admitted (maker 1)) :=
  maker_valid _ _ rfl (by decide)

def left : P.Run empty := .cons (maker 1) first_admitted (.nil _)
def right : P.Run empty := .cons (maker 2) second_admitted (.nil _)

def crossing : T.Crossing left (maker 2) second_admitted := .cons after_second after_first (.nil _ _)

def localClosings : crossing.Closings := ⟨⟨⟨fun _ => Iff.rfl, by decide⟩⟩, PUnit.unit⟩

def head := crossing.exchangeWith localClosings

def connection : T.Iso head.residualRun.last (P.result head.residualFiring head.residualAdmitted) := by
  refine ⟨?_⟩
  obtain ⟨⟨same⟩⟩ := head.same_endpoint
  exact same

def plan : T.RunInterchangePlan left right := ⟨crossing, localClosings, connection, PUnit.unit⟩

def exchange : T.ParallelExchange left right := plan.exchange

theorem local_exchange_without_global_closing :
    Nonempty (T.RunInterchangePlan left right) ∧ IsEmpty T.Closing :=
  ⟨⟨plan⟩, ResidualRunClosingControls.no_closing_operation⟩

theorem native_resources_are_made : P.present (left.append exchange.afterLeft).last = {1, 2} := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.LocalClosingControls
