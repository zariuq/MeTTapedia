import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextResult
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResidualRunExchangeControls

/-!
# A fresh helper must not capture an existing context's helper

The local result and the context have the same declaration-frame shape. Their
placements nevertheless distinguish the fresh helper from the pre-existing
one. Both values remain jointly consistent in the actual native result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextResultControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Helpers.Consumer (tiny empty start first constant)

def oldFrame : Frames.Frame tiny := extend empty first.helper
def oldVariable : Term (signature tiny oldFrame.arity) [] () := fresh empty first.helper
def pinned : Equation (Observation tiny oldFrame.arity) :=
  (observe oldVariable, observe (constant (Γ := []) 42))

def context : Helpers.State tiny Nat := ⟨oldFrame, [pinned], ∅⟩

abbrev placed : ContextPlacement start context :=
  ⟨oldFrame, (fun impossible => impossible.elim), generator oldFrame.arity⟩

def solution : Assignment oldFrame.arity empty.arity
  | .inl impossible => impossible.elim
  | .inr () => constant 42

theorem context_solvable : (Frames.contextual tiny).Solvable context.knowledge := by
  refine ⟨empty, solution, ?_⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem placed_knowledge : placed.state.knowledge = context.knowledge := by
  change (Frames.contextual tiny).applyStore placed.leftMap [] ++
    (Frames.contextual tiny).applyStore ((Frames.contextual tiny).id oldFrame) [pinned] = [pinned]
  rw [Frames.applyStore_id]
  rfl

theorem placed_solvable : (Frames.contextual tiny).Solvable placed.state.knowledge :=
  placed_knowledge.symm ▸ context_solvable

theorem native_admitted : helperStep.Admits (s := placed.state) (placed.leftFiring first) :=
  (placed.admitted_left_iff first ResidualRunExchangeControls.first_admitted).mpr
    ⟨placed_solvable, by decide⟩

abbrev next := placed.afterLeft first

theorem source_frame_shapes_equal : first.after.frame = context.frame := rfl

theorem source_assignments_distinct : next.leftMap ≠ next.rightMap := by
  intro same
  have values := congrArg (fun assignment : Assignment oldFrame.arity next.frame.arity => assignment (.inr ())) same
  cases values

theorem fresh_and_context_remain_solvable : (Frames.contextual tiny).Solvable next.state.knowledge :=
  (placed.left_result_iso first).solvable_iff.mp
    (information_solvable (placed.leftFiring first) placed_solvable)

def native_result_corresponds : helperStep.StateIso
    (helperStep.result (placed.leftFiring first) native_admitted) next.state :=
  placed.admitted_left_result_iso first native_admitted

theorem scoped_snapshot_realization :
    helperStep.toStep.effectCore.configuration next.state =
      EffectCore.Systems.realize scopedHelperEffect [(false, first.after), (true, context)] next.placement :=
  next.native_realization

theorem fresh_scope_identity_matters :
    first.after.frame = context.frame ∧ next.leftMap ≠ next.rightMap ∧
      (Frames.contextual tiny).Solvable next.state.knowledge :=
  ⟨source_frame_shapes_equal, source_assignments_distinct, fresh_and_context_remain_solvable⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextResultControls
