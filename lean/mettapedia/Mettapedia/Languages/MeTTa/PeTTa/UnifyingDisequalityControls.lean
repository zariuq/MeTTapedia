import Mettapedia.Languages.MeTTa.PeTTa.UnifyingDisequality

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.UnifyingDisequality.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation (presentation)
open GSLTBindingPatterns ListView Unifying

private def x : Atom := .var "x"
private def seven : Atom := .grounded (.int 7)
private def eight : Atom := .grounded (.int 8)

def apartSeven : Disequality.Frame atomAction :=
  ⟨[(x, seven)], by
    intro pair member same
    obtain rfl := List.mem_singleton.mp member
    change x = seven at same
    exact (by decide : x ≠ seven) same⟩

theorem computed_seven :
    unifyBinding [] (quoted x) seven = .ok [("x", seven)] := by decide +kernel

theorem computed_eight :
    unifyBinding [] (quoted x) eight = .ok [("x", eight)] := by decide +kernel

theorem computed_answer_is_principal :
    atomAction.Principal (presentation [] ++ [(x, seven)]) (solved [("x", seven)]) :=
  quoted_principal idempotent_nil computed_seven

theorem computed_answer_changes_x : atomAction.apply (solved [("x", seven)]) x = seven := by
  rw [solved_apply]
  rfl

/-- The constructed answer has content; it is not the identity substitution. -/
theorem computed_answer_is_not_identity :
    ∃ term, atomAction.apply (solved [("x", seven)]) term ≠ atomAction.apply atomAction.identity term := by
  refine ⟨x, ?_⟩
  rw [computed_answer_changes_x, atomAction.apply_identity]
  decide +kernel

theorem retained_apart_refuses_seven :
    ¬ (Disequality.frames atomAction).Solvable (a := apartSeven) (presentation [] ++ [(x, seven)]) := by
  rw [quoted_frame_solvable apartSeven idempotent_nil computed_seven]
  intro separates
  apply separates (x, seven) (List.mem_singleton_self _)
  change atomAction.apply (solved [("x", seven)]) x = atomAction.apply (solved [("x", seven)]) seven
  rw [solved_apply, solved_apply]
  rfl

theorem retained_apart_allows_eight :
    (Disequality.frames atomAction).Solvable (a := apartSeven) (presentation [] ++ [(x, eight)]) := by
  apply (quoted_frame_solvable apartSeven idempotent_nil computed_eight).mpr
  intro pair member same
  obtain rfl := List.mem_singleton.mp member
  change atomAction.apply (solved [("x", eight)]) x = atomAction.apply (solved [("x", eight)]) seven at same
  rw [solved_apply, solved_apply] at same
  exact (by decide : eight ≠ seven) same

/-- A test against the equation-only frame would accept the forbidden binding. -/
theorem dropping_apart_changes_compatibility :
    atomAction.Consistent (presentation [] ++ [(x, seven)]) ∧
      ¬ (Disequality.frames atomAction).Solvable (a := apartSeven) (presentation [] ++ [(x, seven)]) := by
  refine ⟨⟨solved [("x", seven)], computed_answer_is_principal.sound⟩, retained_apart_refuses_seven⟩

end Mettapedia.Languages.MeTTa.PeTTa.UnifyingDisequality.Controls
