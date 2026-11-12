import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ExecutionRectangleControls

/-!
# A selected composite need not admit every interleaving

Both local first steps are admitted. One candidate is restricted after a
tell, so exactly one order of the composed pair runs. All preparations remain
available, and every state has a solution. Neither joint solvability nor
permission of a chosen order licenses the other order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionRectangleAdmissionControls

open ExecutionGeometry
open ExecutionRectangleControls (grid)
open Presentation.Controls (Store frame)

def ordered : Step frame Nat Store (fun _ => Bool) :=
  Step.ofEffect ExecutionRectangleControls.P.effectCore
    (fun {state} label _ => label = false ∨ (true, false) ∉ state)

theorem ordered_initial (label : Bool) : ordered.Admits (s := ([] : Store)) label :=
  ⟨Presentation.Controls.prepares [] (), Or.inr (by simp)⟩

theorem ordered_allows_horizontal_after_tell :
    ordered.Admits (s := ([(true, false)] : Store)) false :=
  ⟨Presentation.Controls.prepares _ (), Or.inl rfl⟩

theorem ordered_refuses_vertical_after_tell :
    ¬ordered.Admits (s := ([(true, false)] : Store)) true := by
  rintro ⟨_, equal | fresh⟩
  · cases equal
  · exact fresh (List.mem_singleton_self _)

theorem selected_order_admitted :
    Rectangle.Admitted (ordered.effectCore.admittedSubquiver ordered.eventAdmission) (grid [] 1 1)
      (.vertical (.horizontal .nil)) :=
  .vertical (ordered_initial true)
    (.horizontal ordered_allows_horizontal_after_tell (.nil _))

theorem other_order_refused :
    ¬Rectangle.Admitted (ordered.effectCore.admittedSubquiver ordered.eventAdmission) (grid [] 1 1)
      (.horizontal (.vertical .nil)) := by
  intro permitted
  exact ordered_refuses_vertical_after_tell
    ((Rectangle.admitted_vertical_iff _ _).mp
      ((Rectangle.admitted_horizontal_iff _ _).mp permitted).2).1

theorem a_composite_run_exists :
    ∃! run : {r : ordered.Run (grid [] 1 1).entry // r.last = (grid [] 1 1).exit},
      ordered.preparedRunPath run =
        Rectangle.proposal (.vertical (.horizontal .nil)) (grid [] 1 1) :=
  (ordered.selected_shuffle_iff_unique_run _ _).mp selected_order_admitted

theorem all_interleavings_are_strictly_stronger :
    (∃ shuffle, Rectangle.Admitted (ordered.effectCore.admittedSubquiver ordered.eventAdmission)
      (grid [] 1 1) shuffle) ∧
    ¬Rectangle.AllPermitted (ordered.effectCore.admittedSubquiver ordered.eventAdmission) (grid [] 1 1) := by
  refine ⟨⟨_, selected_order_admitted⟩, ?_⟩
  intro all
  exact other_order_refused (Rectangle.admitted_of_all _ _ all)

theorem every_joint_state_solvable (state : Store) : frame.Solvable (a := ()) state :=
  ⟨(), (fun _ => false), by intro equation member; rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionRectangleAdmissionControls
