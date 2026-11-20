import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationResultReadings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.DataViewModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationCut

/-!
# Soundness of actual principal-settled application runs

The invariant observes every present occurrence at every caller model. Frame
changes are composed along the real dependent run; each result hypothesis is
replaced by its derivation over the preceding source. Fresh output schemes do
not permit a change of the protected initial interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSemantics (Data Derives hypotheses)

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O]

def ValidFrom (judgmentTag arrowTag : Nat) (base : Data) (change : Subst rowSig) (s : Store O) : Prop :=
  ∀ (source : Subst rowSig) o, o ∈ s.present → ∀ value,
    (s.label o).ReadsAt X (b := PUnit.unit) source value →
      Derives judgmentTag arrowTag base (source.comp change) value

omit [DecidableEq O] in
theorem valid_initial (s : Store O) :
    ValidFrom judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) (Subst.id rowSig) s := by
  intro source o present value reading
  apply Derives.hypothesis
  apply (State.dataAt_model_reading_iff X (b := PUnit.unit) (c := PUnit.unit) s
    (Subst.id rowSig) (source.comp (Subst.id rowSig)) value).mpr
  refine ⟨o, present, ?_⟩
  change (s.label o).ReadsAt X (b := PUnit.unit) ((source.comp (Subst.id rowSig)).comp (Subst.id rowSig)) value
  simpa only [Subst.comp_id_right] using reading

theorem valid_step {s : Store O} (f : Attempt judgmentTag arrowTag O s)
    (admitted : (machine judgmentTag arrowTag O).Admits f) (base : Data) (change : Subst rowSig)
    (valid : ValidFrom judgmentTag arrowTag base change s) :
    ValidFrom judgmentTag arrowTag base (f.answer.comp change) f.result := by
  intro source o present value reading
  have localDerivation := result_reading_derivable f admitted source o present value reading
  have lifted : Derives judgmentTag arrowTag base ((source.comp f.answer).comp change) value := by
    apply Derives.cut judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) f.answer) base
      source ((source.comp f.answer).comp change) ?_ localDerivation
    intro premise assumed
    obtain ⟨old, inside, oldReading⟩ := (State.dataAt_model_reading_iff X
      (b := PUnit.unit) (c := PUnit.unit) s f.answer source premise).mp assumed
    exact valid (source.comp f.answer) old inside premise oldReading
  simpa only [Subst.comp_assoc] using lifted

theorem valid_run (base : Data) {s : Store O}
    (run : (machine judgmentTag arrowTag O).Run s) (change : Subst rowSig)
    (valid : ValidFrom judgmentTag arrowTag base change s) :
    ValidFrom judgmentTag arrowTag base (run.toLast.comp change) run.last := by
  induction run generalizing change with
  | nil s =>
    change ValidFrom judgmentTag arrowTag base ((Subst.id rowSig).comp change) s
    simpa only [Subst.comp_id_left] using valid
  | @cons s f admitted rest ih =>
    have next := valid_step f admitted base change valid
    have later := ih (f.answer.comp change) next
    change ValidFrom judgmentTag arrowTag base ((rest.toLast.comp f.answer).comp change) rest.last
    rw [Subst.comp_assoc]
    exact later

theorem run_reading_sound {s : Store O} (run : (machine judgmentTag arrowTag O).Run s)
    (source : Subst rowSig) (o : O) (present : o ∈ run.last.present) (value : Tm)
    (reading : (run.last.label o).ReadsAt X (b := PUnit.unit) source value) :
    Derives judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) (Subst.id rowSig))
      (source.comp run.toLast) value := by
  have valid := valid_run _ run (Subst.id rowSig) (valid_initial (judgmentTag := judgmentTag) (arrowTag := arrowTag) s)
  rw [Subst.comp_id_right] at valid
  exact valid source o present value reading

#print axioms valid_initial
#print axioms valid_step
#print axioms valid_run
#print axioms run_reading_sound

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
