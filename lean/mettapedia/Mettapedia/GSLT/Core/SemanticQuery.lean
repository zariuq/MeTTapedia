import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Core.SemanticTransport

/-!
# Independent semantic query GSLTs

An atomic query has a common operational shape: a request retains the world
and query that determine its meaning, and one semantic step returns the
independently selected answer.  Concrete data structures may implement this
machine through a covered translation.

This construction does not choose what a world, query, or answer means.  Its
`observe` parameter is supplied by the surrounding mathematical theory.  It
only exposes that observation as an exact operational GSLT.
-/

namespace Mettapedia.GSLT.SemanticQuery

open Mettapedia.GSLT

set_option autoImplicit false

/-- A semantic query retains its determining world and query until it emits
the public answer. -/
inductive State (World Query Value : Type) where
  | request (world : World) (query : Query)
  | answer (value : Value)

/-- One atomic semantic observation. -/
inductive Step {World Query Value : Type}
    (observe : World → Query → Value) :
    State World Query Value → State World Query Value → Prop where
  | answer (world : World) (query : Query) :
      Step observe (.request world query) (.answer (observe world query))

/-- The independent operational theory of one semantic query. -/
def theory {World Query Value : Type} (observe : World → Query → Value) :
    GSLT where
  Term := State World Query Value
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step observe
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- The answer selected by a request, before or after its control step. -/
def observation {World Query Value : Type} (observe : World → Query → Value) :
    State World Query Value → Value
  | .request world query => observe world query
  | .answer value => value

theorem step_preserves_observation {World Query Value : Type}
    (observe : World → Query → Value) {source target : State World Query Value}
    (step : Step observe source target) :
    observation observe source = observation observe target := by
  cases step
  rfl

/-- The selected answer is a semantic invariant of query control. -/
def answerInvariant {World Query Value : Type}
    (observe : World → Query → Value) :
    Mettapedia.GSLT.SemanticInvariant (theory observe) Value where
  denote := observation observe
  equation := by
    intro source target equal
    cases equal
    rfl
  rewrite := step_preserves_observation observe

/-- The semantic query control machine realizes directly into the discrete
GSLT of its independently selected answers.  Its sole control step is
semantically silent: it reveals an answer without changing it. -/
def answerRealization {World Query Value : Type}
    (observe : World → Query → Value) :
    Mettapedia.GSLT.IndexedOperational.OperationalRealization
      (theory observe) (GSLT.discrete Value) :=
  (answerInvariant observe).toDiscreteRealization

@[simp] theorem answerRealization_mapTerm {World Query Value : Type}
    (observe : World → Query → Value)
    (state : State World Query Value) :
    (answerRealization observe).mapTerm state = observation observe state :=
  rfl

/-- Every semantic query step maps to a zero-length answer path. -/
theorem answerRealization_step_length {World Query Value : Type}
    (observe : World → Query → Value)
    {source target : State World Query Value}
    (step : Step observe source target) :
    ((answerRealization observe).mapStep step).length = 0 :=
  Mettapedia.GSLT.IndexedOperational.discreteExecutionPath_length _

/-- The exact one-step request path. -/
def path {World Query Value : Type} (observe : World → Query → Value)
    (world : World) (query : Query) :
    (theory observe).RewritePath (.request world query)
      (.answer (observe world query)) :=
  .cons (.answer world query) (.nil _)

theorem path_preserves_observation {World Query Value : Type}
    (observe : World → Query → Value) :
    {source target : State World Query Value} →
      (theory observe).RewritePath source target →
        observation observe source = observation observe target
  | _, _, .nil _ => rfl
  | _, _, .cons step rest =>
      (step_preserves_observation observe step).trans
        (path_preserves_observation observe rest)

/-- Answer states are normal forms. -/
theorem answer_normal {World Query Value : Type}
    (observe : World → Query → Value) (value : Value) :
    (theory observe).IsNormalForm (.answer value) := by
  rintro ⟨target, step⟩
  cases step

/-- Every reachable normal form is the independently selected answer. -/
theorem terminal_exact {World Query Value : Type}
    (observe : World → Query → Value) (world : World) (query : Query)
    (terminal : State World Query Value)
    (route : (theory observe).RewritePath (.request world query) terminal)
    (normal : (theory observe).IsNormalForm terminal) :
    terminal = .answer (observe world query) := by
  cases terminal with
  | request terminalWorld terminalQuery =>
      exact (normal ⟨.answer (observe terminalWorld terminalQuery),
        .answer terminalWorld terminalQuery⟩).elim
  | answer value =>
      have equal : observe world query = value := by
        change observation observe (.request world query) =
          observation observe (.answer value)
        exact path_preserves_observation observe route
      cases equal
      rfl

/-- No execution path can invent a different answer. -/
theorem cannot_answer_other {World Query Value : Type}
    (observe : World → Query → Value) (world : World) (query : Query)
    (other : Value) (different : other ≠ observe world query) :
    ¬ Nonempty ((theory observe).RewritePath
      (.request world query) (.answer other)) := by
  rintro ⟨route⟩
  have equal : observe world query = other := by
    change observation observe (.request world query) =
      observation observe (.answer other)
    exact path_preserves_observation observe route
  exact different equal.symm

#print axioms answerInvariant
#print axioms answerRealization
#print axioms answerRealization_step_length
#print axioms path
#print axioms terminal_exact
#print axioms cannot_answer_other

end Mettapedia.GSLT.SemanticQuery
