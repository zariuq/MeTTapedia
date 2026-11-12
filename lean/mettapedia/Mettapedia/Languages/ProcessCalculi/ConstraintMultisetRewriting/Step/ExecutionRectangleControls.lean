import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ExecutionRectangleEvents
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedPublicationsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Coexistence

/-!
# Store-changing rectangles and admission-sensitive composition

The existing Boolean-equation program supplies arbitrarily large rectangles.
All interleavings run under the permissive profile. The same preparations fail
to compose under duplicate refusal, even though either initial step is allowed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionRectangleControls

open ExecutionGeometry
open Presentation.Controls (Store frame)
open PublicationTransportControls (program permissive strict)

abbrev P := program permissive
abbrev Q := program strict

def after (start : Store) (count : Nat) : Store := start ++ List.replicate count (true, false)

theorem after_succ (start : Store) (count : Nat) :
    after start (count + 1) = after start count ++ [(true, false)] := by
  simp [after, List.replicate_succ', List.append_assoc]

def grid (start : Store) (width height : Nat) : Rectangle P.effectCore.PreparedObject width height where
  vertex i j := after start ((width - i.val) + (height - j.val))
  horizontal i j := {
    firing := false
    prepared := Presentation.Controls.prepares _ ()
    target_eq := by
      change after start ((width - (i.val + 1)) + (height - j.val)) ++ [(true, false)] =
        after start ((width - i.val) + (height - j.val))
      rw [← after_succ]
      congr 1
      have bounded := i.isLt
      omega }
  vertical i j := {
    firing := true
    prepared := Presentation.Controls.prepares _ ()
    target_eq := by
      change after start ((width - i.val) + (height - (j.val + 1))) ++ [(true, false)] =
        after start ((width - i.val) + (height - j.val))
      rw [← after_succ]
      congr 1
      have bounded := j.isLt
      omega }

theorem entry_grid (start : Store) (width height : Nat) : (grid start width height).entry = start := by
  simp [grid, Rectangle.entry, after]

theorem exit_grid (start : Store) (width height : Nat) :
    (grid start width height).exit = after start (width + height) := by
  simp [grid, Rectangle.exit]

theorem permissive_all (start : Store) (width height : Nat) :
    Rectangle.AllPermitted (P.effectCore.admittedSubquiver P.eventAdmission) (grid start width height) := by
  constructor
  · intro i j
    exact ⟨Presentation.Controls.prepares _ (), trivial⟩
  · intro i j
    exact ⟨Presentation.Controls.prepares _ (), trivial⟩

theorem arbitrary_interleavings_are_native_runs (start : Store) (width height : Nat)
    (shuffle : Shuffle width height) :
    ∃! run : {r : P.Run (grid start width height).entry // r.last = (grid start width height).exit},
      P.preparedRunPath run = Rectangle.proposal shuffle (grid start width height) :=
  (P.rectangle_admitted_iff_unique_runs (grid start width height)).mp
    (permissive_all start width height) shuffle

/-- The joint snapshots are the actual existing configuration tensor. -/
theorem grid_vertex_is_tensor (width height : Nat) (i : Fin (width + 1)) (j : Fin (height + 1)) :
    P.effectCore.configuration ((grid [] width height).vertex i j) =
      Coexistence.tensor
        (P.effectCore.configuration (after [] (width - i.val)))
        (P.effectCore.configuration (after [] (height - j.val))) := by
  change (⟨List.replicate ((width - i.val) + (height - j.val)) (true, false), ∅⟩ :
      Configuration Bool Nat) =
    ⟨List.replicate (width - i.val) (true, false) ++
      List.replicate (height - j.val) (true, false), ∅ ∪ ∅⟩
  rw [List.replicate_add, Finset.union_self]

theorem strict_initial_steps_admitted (label : Bool) : Q.Admits (s := ([] : Store)) label :=
  ⟨Presentation.Controls.prepares _ (), by simp [strict]⟩

theorem strict_rejects_second (label : Bool) :
    ¬Q.Admits (s := ([(true, false)] : Store)) label := by
  rintro ⟨_, allowed⟩
  exact allowed (List.mem_singleton_self _)

theorem strict_rectangle_not_admitted :
    ¬Rectangle.AllPermitted (Q.effectCore.admittedSubquiver Q.eventAdmission) (grid [] 1 1) := by
  intro all
  have second := all.horizontal (Fin.last 0) ⟨0, by decide⟩
  exact strict_rejects_second false second

theorem strict_horizontal_then_vertical_refused :
    ¬Rectangle.Admitted (Q.effectCore.admittedSubquiver Q.eventAdmission) (grid [] 1 1)
      (.horizontal (.vertical .nil)) := by
  intro admitted
  have later := (Rectangle.admitted_horizontal_iff _ _).mp admitted
  have second := (Rectangle.admitted_vertical_iff _ _).mp later.2
  exact strict_rejects_second true second.1

theorem strict_vertical_then_horizontal_refused :
    ¬Rectangle.Admitted (Q.effectCore.admittedSubquiver Q.eventAdmission) (grid [] 1 1)
      (.vertical (.horizontal .nil)) := by
  intro admitted
  have later := (Rectangle.admitted_vertical_iff _ _).mp admitted
  have second := (Rectangle.admitted_horizontal_iff _ _).mp later.2
  exact strict_rejects_second false second.1

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionRectangleControls
