import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationClasses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationControls

/-!
# Equality-respecting readouts and a strictly finer code observation

The concrete two-firing program preserves its actual typed quotient value.
Adding raw code to the observer distinguishes its input from its result.
This invalidates an unqualified reuse of the old indistinguishability claim;
it does not say that adding observers destroys every existing concept.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Controls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open LogicOverTheStep.Distinctions

theorem typed_value_preserved :
    QTerm.mk setting.levels (start.state.label start.active).2 =
      QTerm.mk setting.levels program.output.2 := program.quotient

theorem code_observer_not_respectful :
    ¬ Respects (fun row : TotalTerm start.state.frame => row.2.code) := by
  intro respects
  exact raw_code_changed (respects _ _ program.output_equivalent)

def valueRead (row : TotalTerm start.state.frame) := QTerm.mk setting.levels row.2
def finerRead (row : TotalTerm start.state.frame) := (valueRead row, row.2.code)

theorem old_lens_agrees :
    ObserverConcepts.Indist (fun _ : Unit => valueRead) (start.state.label start.active) program.output :=
  fun _ => typed_value_preserved

theorem finer_lens_distinguishes :
    ¬ ObserverConcepts.Indist (fun _ : Unit => finerRead) (start.state.label start.active) program.output := by
  intro same
  exact raw_code_changed (congrArg Prod.snd (same ()))

theorem occurrence_observer_not_value_invariant :
    0 ∈ start.state.present ∧ 0 ∉ middle.state.present := occurrence_observer_changed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Controls.finer_lens_distinguishes
