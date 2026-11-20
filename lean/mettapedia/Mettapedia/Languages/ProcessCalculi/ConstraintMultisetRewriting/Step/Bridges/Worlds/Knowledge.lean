import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.Firings

/-!
# Closed-row knowledge survives the subsequent actual firing run

A published row carries its publisher's knowledge along its fresh opening.
After an admitted import, every model at the end of a subsequent local firing
run still solves both the reader's original knowledge and the captured
publisher knowledge along their respective transports. This composes the
candidate's exact joint-information theorem with the step's existing run law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds

open RuleSyntax RuleSyntax.Worlds
open Hosting.Alternatives.Worlds (snapshot)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O]
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom)

/-- Solvability is preserved by this concrete rule step's runs. The proof
uses its literal result knowledge, not a property postulated of arbitrary
interface implementations. -/
theorem run_last_solvable (program : Program Tm) {state : State Tm O}
    (run : (step X O E program).toStep.Run state) (alive : X.Solvable state.knowledge) :
    X.Solvable run.last.knowledge := by
  induction run with
  | nil => exact alive
  | cons firing admitted rest ih => exact ih admitted.2.2.1

/-- A continuation following a real admitted firing has a model. Thus the
joint-information claim below is not licensed by an impossible final state. -/
theorem admitted_continuation_solvable {program : Program Tm} {state : State Tm O}
    (firing : Firing O E program state.frame) (admitted : firing.Admits X state)
    (rest : (step X O E program).toStep.Run (firing.result X state)) :
    X.Solvable rest.last.knowledge :=
  run_last_solvable X E program rest admitted.2.2.1

theorem imported_run_joint (program : Program Tm) (publisher reader : State Tm O)
    (atom : Tm publisher.frame) (member : snapshot publisher atom ∈ program)
    (ext : E.Ext reader.frame) (opening : Hom publisher.frame (E.target ext))
    (selection : Selection O) (seen : List (Finset O))
    (admitted : (⟨snapshot publisher atom, member, ext, opening, selection, seen⟩ :
      Firing O E program reader.frame).Admits X reader)
    (rest : (step X O E program).toStep.Run
      ((⟨snapshot publisher atom, member, ext, opening, selection, seen⟩ :
        Firing O E program reader.frame).result X reader))
    {b : Obj} (model : Hom rest.last.frame b) (solved : X.Models model rest.last.knowledge) :
    ∃ run : (step X O E program).toStep.Run reader,
      run.last = rest.last ∧ run.word.length = rest.word.length + 1 ∧
      X.Models (X.comp (X.comp model rest.toLast) (E.weaken ext)) reader.knowledge ∧
      X.Models (X.comp (X.comp model rest.toLast) opening) publisher.knowledge := by
  refine ⟨.cons _ admitted rest, rfl, rfl, ?_⟩
  exact import_knows publisher reader atom member ext opening selection seen _
    (rest.models_start model solved)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.imported_run_joint
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.admitted_continuation_solvable
