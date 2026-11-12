import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualRunInterpretation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextResult

/-! # The contextual-helper consumer of the shared execution contract -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs

variable {S : Signature} {O : Type} [DecidableEq O]

abbrev ContextPlacement.nativePair {left right : State S O} (placed : ContextPlacement left right) :
    helperStep.toStep.effectCore.NativePair left right where
  state := placed.state
  leftMap := placed.leftMap
  rightMap := placed.rightMap
  knowledge := fun _ _ => Iff.rfl
  present := rfl

abbrev contextualRunInterpretation : ContextualRunInterpretation (helperTransport (S := S) (O := O)) where
  Place := ContextPlacement
  pair := ContextPlacement.nativePair
  candidate placed f := placed.leftFiring f
  advance placed f _ := placed.afterLeft f
  domain := fun {_ right} _ f => Disjoint f.selection.taken.toFinset right.present
  check := fun {_ right} placed f => (Frames.contextual S).Solvable placed.state.knowledge ∧ f.made ∉ right.present
  admission placed f allowed := placed.admitted_left_iff f allowed
  resultIso placed f _ _ allowed := placed.admitted_left_result_iso f allowed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
