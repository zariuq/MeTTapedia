import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mettapedia.TypeTheory.ContextualKleisliAdjunction

/-!
# No terminal object in the occurrence-sensitive contextual Kleisli category

With singleton state and intent types, every existing contextual program has
a positive finite number of answer occurrences. Duplicating it with choice
doubles that actual observation. A terminal computation object would identify
every arrow into it with its duplicated-choice arrow, which is impossible.

Thus this Kleisli category lacks even the empty computation product. Its
proved adjunction does not by itself provide a computation universe with all
finite products. The obstruction does not assert failure of every binary
product, change the equality of programs, or select another effect model.
Ordinary value types still have their usual terminal singleton.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualKleisliProductBoundary

open CategoryTheory CategoryTheory.Limits
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open ContextualComputationKleisli (Object)

universe u

/-- Count the actual answer occurrences, with the singleton state resolved.
This is an observation of the existing syntax, not an alternative evaluator. -/
def answerCount {Answer : Type u} : Program Unit Answer Unit → Nat
  | .pure _ => 1
  | .choose left right => answerCount left + answerCount right
  | .read next => answerCount (next ())
  | .write _ next => answerCount next
  | .intent _ next => answerCount next

theorem answerCount_eq_length {Answer : Type u} (program : Program Unit Answer Unit)
    (branch : BranchTrace) :
    answerCount program = (runWorldsAt program () branch).length := by
  induction program generalizing branch with
  | pure _ => rfl
  | choose left right leftIH rightIH =>
      simp only [answerCount, runWorldsAt, List.length_append]
      exact congrArg₂ Nat.add (leftIH (false :: branch)) (rightIH (true :: branch))
  | read next nextIH => exact nextIH () branch
  | write state next nextIH => cases state; exact nextIH branch
  | intent request next nextIH =>
      simpa only [answerCount, runWorldsAt, List.length_map] using nextIH branch

theorem answerCount_pos {Answer : Type u} (program : Program Unit Answer Unit) :
    0 < answerCount program := by
  induction program with
  | pure _ => exact Nat.zero_lt_succ 0
  | choose left right leftIH _ =>
      exact Nat.lt_of_lt_of_le leftIH (Nat.le_add_right _ _)
  | read next nextIH => exact nextIH ()
  | write _ next nextIH => exact nextIH
  | intent _ next nextIH => exact nextIH

/-- The difference is visible in the actual handler, not only constructor tags. -/
theorem duplicate_choice_changes_occurrence_count {Answer : Type u}
    (program : Program Unit Answer Unit) (branch : BranchTrace) :
    (runWorldsAt (.choose program program) () branch).length ≠
      (runWorldsAt program () branch).length := by
  rw [← answerCount_eq_length, ← answerCount_eq_length]
  change answerCount program + answerCount program ≠ answerCount program
  have positive := answerCount_pos program
  omega

theorem ne_duplicate_choice {Answer : Type u} (program : Program Unit Answer Unit) :
    program ≠ .choose program program := by
  intro equality
  have counts := congrArg answerCount equality
  have positive := answerCount_pos program
  change answerCount program = answerCount program + answerCount program at counts
  omega

/-- Every alleged terminal target receives two observably distinct arrows
from the singleton value object. No inhabitant of the target is assumed. -/
theorem not_terminal (target : Object Unit Unit) : ¬ Nonempty (IsTerminal target) := by
  rintro ⟨terminal⟩
  let source : Object Unit Unit := ⟨Unit⟩
  let arrow : source ⟶ target := terminal.from source
  let doubled : source ⟶ target := ⟨fun input => .choose (arrow.toFun input) (arrow.toFun input)⟩
  have equal : arrow = doubled := terminal.hom_ext arrow doubled
  have programEqual := congrArg (fun current : source ⟶ target => current.toFun ()) equal
  exact ne_duplicate_choice (arrow.toFun ()) programEqual

theorem no_terminal_object :
    ¬ ∃ target : Object Unit Unit, Nonempty (IsTerminal target) := by
  rintro ⟨target, terminal⟩
  exact not_terminal target terminal

/-- Pure value maps still have a terminal singleton in the value category. -/
def valueUnit_terminal : IsTerminal (Unit : Type) :=
  IsTerminal.ofUniqueHom (fun _ => TypeCat.ofHom (fun _ => ())) (by
    intro source arrow
    ext value)

/-- The free functor does not turn that value terminal into a computation terminal. -/
theorem free_valueUnit_not_terminal :
    ¬ Nonempty (IsTerminal ((ContextualKleisliAdjunction.free Unit Unit).obj Unit)) :=
  not_terminal _

#print axioms answerCount_eq_length
#print axioms answerCount_pos
#print axioms duplicate_choice_changes_occurrence_count
#print axioms ne_duplicate_choice
#print axioms no_terminal_object
#print axioms valueUnit_terminal
#print axioms free_valueUnit_not_terminal

end Mettapedia.TypeTheory.ContextualKleisliProductBoundary
