import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulFirstOrder

/-!
# The step over rational trees

The first-order step of the run layer (`AnnotatedRuns.firstOrder`) is stated for any substitution
action. Over the rational-tree action it is a step over the rational-tree frames
(`rationalStep`): the same occurrences, selections, shapes and enabling, with knowledge, asks and
solvability read over rational trees. The rational-tree action is faithful
(`rationalAction_faithful`), so its one-frame transport is lawful (`rationalLawful`). Every theorem
proved for `firstOrder A label` for arbitrary `A` holds for it, and so does every theorem about
`Interface.Step` (knowledge only refines along a run, runs form a free category, accounts are
functors).

**A firing admitted only over rational trees** (`tellLoop`): the firing that takes, reads and makes
nothing and tells `X = f(X)`.
* Over finite trees it is refused at every configuration (`tellLoopFinite_refused`): the occurs
  check makes its information unsolvable.
* Over rational trees, its image is admitted from no knowledge (`tellLoop_admitted`), and the run of
  that one firing ends in knowledge solved by `X := f(f(f(…)))` (`tellLoop_run`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

open Mettapedia.Logic.LP
open AnnotatedRuns (Firing firstOrder)

/-- **The step over the rational-tree frames**: the first-order step with the rational-tree action. -/
abbrev rationalStep (σ : LPSignature) {O : Type*} [DecidableEq O] (label : O → RTree σ) :
    Interface.Step.Standard (rationalFrames σ) O (Configuration (RTree σ) O) (fun _ => Firing (RTree σ) (RSubst σ) O) :=
  firstOrder (rationalAction σ) label

/-- **The rational-tree action is faithful**: substitutions acting alike on every tree are equal. -/
theorem rationalAction_faithful (σ : LPSignature) : AnnotatedRuns.Faithful (rationalAction σ) := by
  intro θ τ same
  funext v
  have atLeaf : RTree.subst θ (RTree.leaf v) = RTree.subst τ (RTree.leaf v) := same (RTree.leaf v)
  rwa [RTree.subst_leaf, RTree.subst_leaf] at atLeaf

/-- **The one-frame transport of the rational-tree step is lawful**, by the theorem for faithful
actions. -/
def rationalLawful (σ : LPSignature) {O : Type*} [DecidableEq O] (label : O → RTree σ) :=
  AnnotatedRuns.firstOrderLawful label (rationalAction_faithful σ)

namespace Controls

variable {O : Type*} [DecidableEq O]

/-- The finite firing that tells `X = f(X)` and does nothing else. -/
def tellLoopFinite : Firing (Term ctlSig) (Subst ctlSig) O :=
  ⟨⟨[], [], [(X, un .f X)], [], []⟩, [], ⟨[], [], []⟩⟩

/-- **The same firing over rational trees**: its rule read through `RTree.ofTerm`. -/
def tellLoop : Firing (RTree ctlSig) (RSubst ctlSig) O :=
  ⟨(tellLoopFinite (O := O)).rule.map RTree.ofTerm, [], (tellLoopFinite (O := O)).selection⟩

/-- **Over finite trees the firing is refused**, at every configuration. -/
theorem tellLoopFinite_refused (label : O → Term ctlSig) (C : Configuration (Term ctlSig) O) :
    ¬ (tellLoopFinite (O := O)).Valid (FirstOrder.action ctlSig) label C := by
  intro valid
  obtain ⟨θ, solved⟩ := valid.firing.consistent
  have told : (FirstOrder.action ctlSig).Models θ [(X, un .f X)] := fun e member =>
    solved e (by
      obtain rfl := List.mem_singleton.mp member
      simp [Selection.problem, tellLoopFinite])
  exact finite_occurs ⟨θ, told⟩

/-- **Over rational trees it is admitted**, from no knowledge. -/
theorem tellLoop_admitted (label : O → RTree ctlSig) (present : Finset O) :
    (rationalStep ctlSig label).Admits (s := ⟨[], present⟩) (tellLoop (O := O)) := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ?_, ?_, ?_⟩, ?_⟩
  · exact ⟨by simp [Selection.commit, tellLoop, tellLoopFinite],
      by simp [Selection.commit, tellLoop, tellLoopFinite],
      by simp [Selection.commit, tellLoop, tellLoopFinite],
      by simp [Selection.commit, tellLoop, tellLoopFinite],
      by simp [Selection.commit, tellLoop, tellLoopFinite]⟩
  · refine ⟨fun _ => loop .f, fun e member => loop_solves e ?_⟩
    simpa [Selection.problem, Selection.equations, tellLoop, tellLoopFinite, RuleInstance.map,
      loopStore] using member
  · intro check member
    simp [tellLoop, tellLoopFinite, RuleInstance.map] at member
  · intro query member
    simp [tellLoop] at member

/-- **The run of that one firing**, ending in knowledge solved by `X := f(f(f(…)))`. -/
theorem tellLoop_run (label : O → RTree ctlSig) (present : Finset O) :
    ∃ run : (rationalStep ctlSig label).Run ⟨[], present⟩,
      run.word.length = 1 ∧ (rationalAction ctlSig).Models (fun _ => loop .f) run.last.equations := by
  refine ⟨.cons tellLoop (tellLoop_admitted label present) (.nil _), rfl, ?_⟩
  show (rationalAction ctlSig).Models (fun _ => loop .f) loopStore
  exact loop_solves

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Rational.rationalStep
#print axioms Rational.rationalAction_faithful
#print axioms Rational.rationalLawful
#print axioms Rational.Controls.tellLoopFinite_refused
#print axioms Rational.Controls.tellLoop_admitted
#print axioms Rational.Controls.tellLoop_run

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
