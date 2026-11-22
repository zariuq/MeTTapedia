import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreHelperLent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorRunsControls

/-!
# Controls for the zoned reading of the helper step

The frame holds one helper pinned to the value `42`. A firing makes occurrence `3` and a
function-valued helper, guarded by the pin.

* `a_helper_run_is_a_zoned_proof`: its one-firing run, admitted where no occurrence is present,
  is a graded proof over the frames whose grade admits the empty extra context.
* `no_run_where_the_occurrence_is_present`, `no_zoned_proof_where_the_occurrence_is_present`:
  where occurrence `3` is already present the same use has no run, and so no graded proof that
  admits the empty extra context and ends in consistent knowledge.
* `a_placed_helper_run_is_a_lent_proof`: a two-step local run placed beside a context is a
  graded proof at the frame of the placement, with the identities of the context lent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.HelperZoned.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Helpers (State Firing helperStep)
open Helpers.Consumer (tiny constant)
open Helpers.ContextResultControls (context pinned)
open Helpers.TensorRunsControls (rightFiring right_allowed second)

/-- **A helper run is a zoned proof over the frames.** -/
theorem a_helper_run_is_a_zoned_proof :
    ∃ (last : Frames.Frame tiny) (along : FrameMap tiny context.frame last)
      (reached : Known tiny last) (left : Multiset Nat) (grade : Multiset Nat → Prop),
      grade 0 ∧
        (helperZoned tiny Nat).Proves context.frame 0
          (solutions (Frames.contextual tiny) context.knowledge) context.present.val grade
          (usesOf second) last along reached left ∧ reached.Nonempty :=
  (helper_run_iff_zoned_proof context (usesOf second)).mp ⟨second, rfl, right_allowed.2.2.1⟩

/-- The same frame and knowledge, with occurrence `3` already present. -/
def occupied : State tiny Nat := ⟨context.frame, context.knowledge, {3}⟩

/-- The same firing, read where occurrence `3` is present. -/
def crowded : Firing occupied := ⟨3, ([()], ()), constant 13, [pinned]⟩

theorem no_run_where_the_occurrence_is_present :
    ¬ ∃ run : helperStep.Run occupied, usesOf run = [⟨occupied.frame, ruleOf crowded⟩] ∧
      (Frames.contextual tiny).Solvable run.last.knowledge := by
  rintro ⟨run, word, _⟩
  cases run with
  | nil => exact absurd word.symm (List.cons_ne_nil _ _)
  | cons g allowed rest =>
      have parts := List.cons.inj word
      have same : ruleOf g = ruleOf crowded := eq_of_heq (Sigma.mk.inj parts.1).2
      have made : g.made = 3 := congrArg (fun rule => rule.made) same
      have absent : g.made ∉ occupied.present := ((Helpers.admits_iff g).mp allowed).2.1
      rw [made] at absent
      exact absent (by decide)

/-- **Where its occurrence is present, the use has no graded proof.** -/
theorem no_zoned_proof_where_the_occurrence_is_present :
    ¬ ∃ (last : Frames.Frame tiny) (along : FrameMap tiny occupied.frame last)
      (reached : Known tiny last) (left : Multiset Nat) (grade : Multiset Nat → Prop),
      grade 0 ∧
        (helperZoned tiny Nat).Proves occupied.frame 0
          (solutions (Frames.contextual tiny) occupied.knowledge) occupied.present.val grade
          [⟨occupied.frame, ruleOf crowded⟩] last along reached left ∧ reached.Nonempty :=
  fun proof => no_run_where_the_occurrence_is_present
    ((helper_run_iff_zoned_proof occupied [⟨occupied.frame, ruleOf crowded⟩]).mpr proof)

/-- **A placed helper run is a graded proof with its context lent.** The two-step local run of
the earlier control, placed beside the context that pins a helper to `42`, has a placed native
run that is a graded proof at the frame of the placement, from the meet of the two transported
knowledges. -/
theorem a_placed_helper_run_is_a_lent_proof :
    ∃ native : helperStep.Run Helpers.ContextResultControls.placed.state,
      Places Helpers.contextualRunInterpretation Helpers.ContextResultControls.placed
        Helpers.RunRebaseControls.localRun native ∧
      ∃ grade : Multiset Nat → Prop, grade 0 ∧
        (helperZoned tiny Nat).Proves Helpers.ContextResultControls.placed.frame
          (context.present \ Helpers.Consumer.start.present).val
          (pull (Frames.contextual tiny) Helpers.ContextResultControls.placed.leftMap
              (solutions (Frames.contextual tiny) Helpers.Consumer.start.knowledge) ⊓
            pull (Frames.contextual tiny) Helpers.ContextResultControls.placed.rightMap
              (solutions (Frames.contextual tiny) context.knowledge))
          Helpers.Consumer.start.present.val grade (usesOf native) native.last.frame
          (alongOf native) (solutions (Frames.contextual tiny) native.last.knowledge)
          (native.last.present \ (context.present \ Helpers.Consumer.start.present)).val :=
  helper_checks_gives_lent_proof Helpers.ContextResultControls.placed
    Helpers.RunRebaseControls.localRun
    ((Helpers.contextualRunInterpretation.plan_iff_checks Helpers.ContextResultControls.placed
      Helpers.RunRebaseControls.localRun).mp ⟨Helpers.RunRebaseControls.plan⟩)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.HelperZoned.Controls
