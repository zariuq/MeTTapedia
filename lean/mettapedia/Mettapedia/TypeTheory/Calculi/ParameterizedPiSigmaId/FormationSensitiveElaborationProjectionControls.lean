import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationProjection

/-!
# Controls for exact type and success observations

These checks retain the actual producer and its inputs. They cover an open
variable, unchanged alignment, malformed target formation and exhausted fuel.
Producer success alone carries no context-formation or replay claim.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
namespace ProjectionControls

variable {Head : Type} {RootCode : Nat → Type}
  (R : Rules Head) (choices : Choices Head RootCode) [DecidableEq Head]

theorem variable_type {n : Nat} (context : Ctx Head n) (index : Fin n) :
    typeProjection R choices 1 context (.var index) = some (Ctx.lookup context index) := rfl

theorem variable_checked (head : Head) :
    (check R choices 2 (.snoc .nil (.head head)) (.var 0) (.head head)).isSome = true := by
  rw [check_success]
  simp [checkProjection,checkPresence,typeProjection,alignPresence,Ctx.lookup,rename]

theorem unchanged_alignment {n : Nat} (context : Ctx Head n) (term type : Tm Head n)
    (evidence : Code Head RootCode n) :
    (align R choices 1 context term type type evidence).isSome = true := by
  rw [align_success]
  simp [alignProjection,alignPresence]

theorem malformed_target_refused (head : Head) (evidence : Code Head RootCode 0) :
    (align R choices 2 .nil (.head head) (.head head) (.lam (.var 0)) evidence).isSome = false := by
  rw [align_success]
  simp [alignProjection,alignPresence,typeProjection]

theorem changed_variable_type_refused (head : Head) :
    (check R choices 3 (.snoc .nil (.head head)) (.var 0) (.lam (.var 0))).isSome = false := by
  rw [check_success]
  change (alignPresence R choices 2 (.snoc .nil (.head head))
    (.var 0) (.head head) (.lam (.var 0))).isSome = false
  simp [alignPresence,typeProjection]

theorem zero_fuel_refused {n : Nat} (context : Ctx Head n) (term type : Tm Head n) :
    (check R choices 0 context term type).isSome = false := by
  rw [check_success]
  rfl

theorem unannotated_abstraction_not_synthesized {n : Nat} (fuel : Nat)
    (context : Ctx Head n) (body : Tm Head (n+1)) :
    (synth R choices (fuel+1) context (.lam body)).map Inferred.type = none := by
  rw [synth_type]
  rfl

#print axioms variable_checked
#print axioms malformed_target_refused
#print axioms changed_variable_type_refused

end ProjectionControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
