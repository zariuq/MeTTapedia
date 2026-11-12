import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CellsHelper

/-!
# Local squares of placed contextual-helper candidates

Native independence has the exact joint-consistency and freshness domain.
Rebasing the opposite-side candidate after a placed step agrees with the
profile's residual, through the actual result transport. The canonical
declaration swap supplies a closing operation with its proved cube law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextPlacement

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {O : Type} [DecidableEq O]
  {left right : Helpers.State S O} (placed : ContextPlacement left right)

abbrev rightFiring (g : Helpers.Firing right) : Helpers.Firing placed.state := g.move placed.rightMap

theorem independent_pair_iff (f : Helpers.Firing left) (g : Helpers.Firing right)
    (first : helperStep.Admits f) (second : helperStep.Admits g) :
    helperTransport.Independent placed.state (placed.leftFiring f) (placed.rightFiring g) ↔
      (Frames.contextual S).Solvable placed.state.knowledge ∧
        f.made ∉ right.present ∧ g.made ∉ left.present ∧ f.made ≠ g.made := by
  rw [Helpers.independent_iff]
  have oldFirst := ((admits_iff f).mp first).2.1
  have oldSecond := ((admits_iff g).mp second).2.1
  have asksFirst := placed.inherits_left_guard f first
  have asksSecond := placed.inherits_right_guard g second
  change (_ ∧ f.made ∉ left.present ∪ right.present ∧ g.made ∉ left.present ∪ right.present ∧
    f.made ≠ g.made ∧ _ ∧ _) ↔ _
  simp only [Finset.mem_union, not_or]
  exact ⟨fun ⟨solved, freshFirst, freshSecond, distinct, _, _⟩ =>
      ⟨solved, freshFirst.2, freshSecond.1, distinct⟩,
    fun ⟨solved, freshFirst, freshSecond, distinct⟩ =>
      ⟨solved, ⟨oldFirst, freshFirst⟩, ⟨freshSecond, oldSecond⟩, distinct, asksFirst, asksSecond⟩⟩

abbrev oppositeBridge (f : Helpers.Firing left)
    (allowed : helperStep.Admits (s := placed.state) (placed.leftFiring f)) :=
  helperTransport.trans (placed.afterLeft f).swapIso
    (helperTransport.symm (placed.admitted_left_result_iso f allowed))

theorem opposite_candidate_is_residual (f : Helpers.Firing left) (g : Helpers.Firing right)
    (allowed : helperStep.Admits (s := placed.state) (placed.leftFiring f)) :
    helperTransport.move (placed.oppositeBridge f allowed) ((placed.afterLeft f).swap.leftFiring g) =
      helperTransport.residual (placed.leftFiring f) allowed (placed.rightFiring g) := by
  apply Firing.mk_congr _ _
  · change instantiate
      (Assignment.compose (generator (extend placed.frame f.helper).arity) (generator (extend placed.frame f.helper).arity))
      (instantiate (Assignment.compose (incl placed.frame f.helper) placed.rightMap) g.value) =
        instantiate (helperStep.along (placed.leftFiring f) allowed) (instantiate placed.rightMap g.value)
    rw [along_eq]
    simp only [Assignment.instantiate_compose, instantiate_identity]
  · rw [along_eq]
    change (Frames.contextual S).applyStore
      ((Frames.contextual S).comp ((Frames.contextual S).id (extend placed.frame f.helper))
        ((Frames.contextual S).id (extend placed.frame f.helper)))
      ((Frames.contextual S).applyStore
        ((Frames.contextual S).comp (incl placed.frame f.helper) placed.rightMap) g.guards) =
          (Frames.contextual S).applyStore (incl placed.frame f.helper)
            ((Frames.contextual S).applyStore placed.rightMap g.guards)
    rw [← Frames.applyStore_applyStore, Frames.applyStore_id, Frames.applyStore_id]
    exact (Frames.applyStore_applyStore (X := Frames.contextual S) placed.rightMap
      (incl placed.frame f.helper) g.guards).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextPlacement
