import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FrameFamilies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceControls

/-! # Family-frame coexistence, faithful origins and the empty term fibre -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Frames.Families.Controls

open Coexistence.Controls (discreteFrames DiscreteHom no_common_native_frame)

abbrev terms := Term (fun _ : Bool => Bool)

def first : terms [false, true] := ⟨⟨false, false⟩, by simp⟩
def second : terms [false, true] := ⟨⟨true, false⟩, by simp⟩

theorem two_frames_have_family_extensions :
    Nonempty (Map DiscreteHom [false] [false, true]) ∧
      Nonempty (Map DiscreteHom [true] [false, true]) :=
  ⟨⟨left discreteFrames [false] [true]⟩, ⟨right discreteFrames [false] [true]⟩⟩

/-- The extension coexists without imposing a common original target. -/
theorem native_obstruction_is_not_an_axiom :
    (¬∃ target : Bool, Nonempty (DiscreteHom false target) ∧ Nonempty (DiscreteHom true target)) ∧
      Nonempty (Map DiscreteHom [false] [false, true]) ∧
        Nonempty (Map DiscreteHom [true] [false, true]) :=
  ⟨no_common_native_frame, two_frames_have_family_extensions⟩

theorem origins_remain_distinct : ¬(families discreteFrames).E first second := by
  intro same
  have impossible := related_frame_eq discreteFrames same
  cases impossible

theorem two_frame_knowledge_solvable : (families discreteFrames).Solvable (a := [false, true])
    [(first, first), (second, second)] := by
  refine ⟨[false, true], (families discreteFrames).id _, ?_⟩
  intro equation member
  rcases List.mem_cons.mp member with same | later
  · subst equation
    exact ((families discreteFrames).equivalence _).refl _
  · have same := List.mem_singleton.mp later
    subst equation
    exact ((families discreteFrames).equivalence _).refl _

theorem empty_family_has_no_phantom_term : ¬Nonempty (terms []) :=
  empty_term_fibre (Tm := fun _ : Bool => Bool)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Frames.Families.Controls
