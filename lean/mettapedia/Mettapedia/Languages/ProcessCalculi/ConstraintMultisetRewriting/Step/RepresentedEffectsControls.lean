import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RepresentedEffects
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventEvaluationControls

/-!
# Closure for refused preparations is a real obligation

At the existing once-only tell program's occupied state, no candidate is
admitted. Its effect still prepares a second tell. A representation containing
only that occupied state is therefore closed under admitted execution but
cannot represent all prepared results. The result changes the actual store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RepresentedEffectsControls

open Presentation.Controls

abbrev P := Step.Evaluation.Controls.program
def occupied : Store := [(true, false)]

theorem prepared_refusal : P.Prepares (s := occupied) () ∧ ¬ P.Admits (s := occupied) () := by
  refine ⟨prepares occupied (), ?_⟩
  rintro ⟨_, permitted⟩
  exact permitted (List.mem_singleton_self _)

/-- The single represented state is closed under every admitted firing,
because this actual language profile refuses the repeated tell. -/
theorem admitted_closure (firing : Unit) (admitted : P.Admits (s := occupied) firing) :
    ∃ _represented : Unit, occupied = P.result firing admitted := by
  cases firing
  exact False.elim (prepared_refusal.2 admitted)

theorem cannot_represent_prepared_result :
    ¬ ∃ representation : P.effectCore.Representation Unit (fun _ => Unit),
      representation.state () = occupied := by
  rintro ⟨representation, initial⟩
  have prepared : P.effectCore.Prepares (representation.firing (s := ()) ()) :=
    prepares (representation.state ()) (representation.firing ())
  have result := representation.result_eq (s := ()) () prepared
  have representedTarget : representation.preparedResult () prepared = () := Subsingleton.elim _ _
  rw [representedTarget] at result
  change representation.state () = representation.state () ++ [(true, false)] at result
  rw [initial] at result
  have length := congrArg List.length result
  simp [occupied] at length

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RepresentedEffectsControls
