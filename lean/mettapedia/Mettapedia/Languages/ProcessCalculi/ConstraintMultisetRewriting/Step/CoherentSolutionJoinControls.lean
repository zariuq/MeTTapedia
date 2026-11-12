import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoherentSolutionJoin

/-!
# Distinct frame codes may have the same action

The extra Boolean tag is invisible on terms. Solutions with either code are
distinct as raw morphisms and equal in the action quotient used by the
solution join. Uniqueness in that quotient does not assert raw-code equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.CoherentSolutionJoinControls

def frames : Frames (fun _ : Unit => Bool) (fun _ _ : Unit => Bool) where
  E := Eq
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act _ term := term
  id _ := false
  comp second first := xor second first
  act_id _ := rfl
  act_comp _ _ _ := rfl
  preserves := by intro _ _ _ _ _ same; exact same

def first : {mapping : Bool // frames.Models (a := ()) (b := ()) mapping []} :=
  ⟨false, Frames.models_nil _⟩

def second : {mapping : Bool // frames.Models (a := ()) (b := ()) mapping []} :=
  ⟨true, Frames.models_nil _⟩

theorem different_raw_solutions : first ≠ second := by
  intro equal
  have impossible := congrArg Subtype.val equal
  change false = true at impossible
  cases impossible

theorem identical_solution_classes :
    Quotient.mk (Frames.solutionSetoid (X := frames) (a := ()) [] ()) first =
      Quotient.mk (Frames.solutionSetoid (X := frames) (a := ()) [] ()) second :=
  Quotient.sound (fun _ => rfl)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.CoherentSolutionJoinControls
