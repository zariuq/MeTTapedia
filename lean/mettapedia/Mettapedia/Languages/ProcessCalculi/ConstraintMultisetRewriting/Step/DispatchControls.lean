import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DispatchFirstOrder

/-!
# Controls for dispatch

Over the control signature of `RationalControls` (constants `true`, `false`; unary `f`, `g`;
binary `arrow`; variables `X = 0`, `Y = 1`).

**The negative control: reflection without the license** (`dispatch_without_license`). The map of
finite trees into rational trees reflects the equivalence, and the firing that tells `X ≐ f(X)`,
read over rational trees, is a dispatched firing of the rational-tree step. Its problem is decided
by the source, by a refutation: the occurs check. The license fails there
(`loop_not_licensedAt`, `finiteToRational_not_licensed`), and answering in the source would give the
wrong admission: the rational-tree step admits the firing. So the license is not implied by
reflection and decision.

**The edge's controls** (`DispatchRational`):
* **commit** (`commit_control`): telling `X ≐ true` with the guard `X ≐ true` is admitted by the
  rational-tree step, from the finite principal answer;
* **guards** (`guard_control`): telling `X ≐ true` with the guard `X ≐ false` is refused, because
  the guard fails at the finite principal answer;
* **refutation** (`refutation_control`): telling `true ≐ false` is refused, from the finite
  refutation alone: the store is matched against ground data, so it is licensed without consulting
  the rational side.

**The first-order edge's controls** (`DispatchFirstOrder`):
* **commit** (`decomposition_dispatched`): every second-order solution of `f(X) ≐ f(Y)`, into any
  frame, metavariables with parameters included, solves `X ≐ Y`; this is read off the first-order
  answer, by dispatch;
* **refutation** (`clash_secondOrder_refuted`): `true ≐ false` has no second-order solution, from the
  first-order refutation;
* **the cyclic store is licensed here** (`loop_secondOrder_refuted`): the occurs-check refutation
  of `X ≐ f(X)` is a second-order refutation. On the rational edge the same store is the negative
  control: licenses belong to edges, not to stores.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational.Controls

open Mettapedia.Logic.LP
open Interface (Frames)
open Interface.Translation (FrameMap)
open AnnotatedRuns (Firing firstOrder)

/-! ## The negative control -/

/-- **`X ≐ f(X)` is not acyclic**: it is refuted by the occurs check and solved by `f(f(f(…)))`. -/
theorem loop_not_acyclic : ¬ Acyclic [(X, un .f X)] := by
  rw [acyclic_iff]
  rintro (consistent | refuted)
  · exact finite_occurs consistent
  · exact refuted ⟨fun _ => loop .f, loop_solves⟩

theorem loop_not_licensedAt : ¬ (finiteToRational ctlSig).LicensedAt (a := PUnit.unit) [(X, un .f X)] := by
  rw [finiteToRational_licensedAt_iff]
  exact loop_not_acyclic

/-- **The edge is not licensed on every store.** -/
theorem finiteToRational_not_licensed : ¬ (finiteToRational ctlSig).Licensed :=
  fun licensed => loop_not_licensedAt (licensed PUnit.unit _)

/-- **Reflection and decision without the license give the wrong admission.** Every hypothesis of
dispatch but the license holds at the lifted firing that tells `X ≐ f(X)`: the map reflects the
equivalence, the firing is dispatched with problem `X ≐ f(X)`, and the source decides it, by a
refutation. Still the rational-tree step admits the firing. -/
theorem dispatch_without_license {O : Type} [DecidableEq O] (label : O → Term ctlSig)
    (present : Finset O) :
    (finiteToRational ctlSig).Reflects ∧
      (dispatched label (tellLoopFinite (O := O)) ⟨[], present⟩
        (fun _ member => by cases member)).problem = [(X, un .f X)] ∧
      (finiteFrames ctlSig).Decides (a := PUnit.unit) [(X, un .f X)] ∧
      ¬ (finiteFrames ctlSig).Solvable (a := PUnit.unit) [(X, un .f X)] ∧
      ¬ (finiteToRational ctlSig).LicensedAt (a := PUnit.unit) [(X, un .f X)] ∧
      (rationalStep ctlSig (fun o => RTree.ofTerm (label o))).Admits (s := liftConfig ⟨[], present⟩)
        (liftFiring (tellLoopFinite (O := O))) := by
  have refuted : ¬ (finiteFrames ctlSig).Solvable (a := PUnit.unit) [(X, un .f X)] :=
    fun solvable => finite_occurs ((Frames.ofSubstitution_solvable_iff _ _).mp solvable)
  exact ⟨finiteToRational_reflects, rfl, Or.inr refuted, refuted, loop_not_licensedAt,
    tellLoop_admitted _ present⟩

/-! ## Commit, guard and refutation controls -/

section Edge

variable {O : Type} [DecidableEq O]

/-- The finite firing that tells `X ≐ true`, with one check, and does nothing else. -/
def tellTrue (check : Check (Term ctlSig)) : Firing (Term ctlSig) (Subst ctlSig) O :=
  ⟨⟨[], [], [(X, .const true)], [check], []⟩, [], ⟨[], [], []⟩⟩

omit [DecidableEq O] in
theorem tellTrue_consistent (check : Check (Term ctlSig)) (label : O → Term ctlSig)
    (present : Finset O) :
    (FirstOrder.action ctlSig).Consistent
      ((tellTrue (O := O) check).selection.problem label (tellTrue (O := O) check).rule
        ⟨[], present⟩) := by
  refine ⟨fun _ => .const true, fun e member => ?_⟩
  obtain rfl := List.mem_singleton.mp member
  rfl

/-- **Commit control**: telling `X ≐ true` under the guard `X ≐ true` is admitted by the
rational-tree step, from the finite principal answer. -/
theorem commit_control (label : O → Term ctlSig) (present : Finset O) :
    (rationalStep ctlSig (fun o => RTree.ofTerm (label o))).Admits (s := liftConfig ⟨[], present⟩)
      (liftFiring (tellTrue (O := O) (.equal X (.const true)))) := by
  obtain ⟨θ, -, principal⟩ := finite_principal_of_consistent
    (tellTrue_consistent (O := O) (.equal X (.const true)) label present)
  refine (lift_admits_iff_of_principal label _ ⟨[], present⟩
    (fun c member => ⟨_, _, List.mem_singleton.mp member⟩) principal).mpr
    ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl⟩,
      ⟨by simp [Selection.commit, tellTrue], by simp [Selection.commit, tellTrue],
        by simp [Selection.commit, tellTrue], by simp [Selection.commit, tellTrue],
        by simp [Selection.commit, tellTrue]⟩, ?_⟩
  intro e member
  obtain rfl := List.mem_singleton.mp member
  exact principal.sound _ (List.mem_singleton_self _)

/-- **Guard control**: telling `X ≐ true` under the guard `X ≐ false` is refused by the rational-tree
step: the guard fails at the finite principal answer. -/
theorem guard_control (label : O → Term ctlSig) (present : Finset O) :
    ¬ (rationalStep ctlSig (fun o => RTree.ofTerm (label o))).Admits (s := liftConfig ⟨[], present⟩)
      (liftFiring (tellTrue (O := O) (.equal X (.const false)))) := by
  obtain ⟨θ, -, principal⟩ := finite_principal_of_consistent
    (tellTrue_consistent (O := O) (.equal X (.const false)) label present)
  intro admitted
  obtain ⟨-, -, guards⟩ := (lift_admits_iff_of_principal label _ ⟨[], present⟩
    (fun c member => ⟨_, _, List.mem_singleton.mp member⟩) principal).mp admitted
  have toFalse : θ.applyTerm X = Term.const false := guards _ (List.mem_singleton_self _)
  have toTrue : θ.applyTerm X = Term.const true := principal.sound _ (List.mem_singleton_self _)
  cases toTrue.symm.trans toFalse

/-- **Refutation control**: telling `true ≐ false` is refused by the rational-tree step, from the
finite refutation; the store is matched against ground data, so the license needs nothing from the
rational side. -/
theorem refutation_control (label : O → Term ctlSig) (present : Finset O) :
    ¬ (rationalStep ctlSig (fun o => RTree.ofTerm (label o))).Admits (s := liftConfig ⟨[], present⟩)
      (liftFiring (AnnotatedRuns.tellClash (σ := ctlSig) (O := O) true false)) := by
  have ground : GroundSided ((AnnotatedRuns.tellClash (σ := ctlSig) (O := O) true false).selection.problem
      label (AnnotatedRuns.tellClash (σ := ctlSig) (O := O) true false).rule ⟨[], present⟩) := by
    intro e member
    obtain rfl := List.mem_singleton.mp member
    exact Or.inl trivial
  refine lift_refused label _ ⟨[], present⟩ (fun _ member => by cases member)
    (acyclic_of_groundSided ground) ?_
  rintro ⟨θ, solved⟩
  have clash : (Term.const true : Term ctlSig) = Term.const false := solved _ (List.mem_singleton_self _)
  cases clash

end Edge

/-! ## The first-order edge -/

section FirstOrderEdge

open FirstOrderDispatch

/-- **Commit control**: every second-order solution of `f(X) ≐ f(Y)` solves `X ≐ Y`, read off the
first-order principal answer. -/
theorem decomposition_dispatched :
    (Frames.contextual (lpSig ctlSig)).Entails
      ((firstOrderToSecond ctlSig).store (a := PUnit.unit) [(un .f X, un .f Y)])
      (fun _ g => (Frames.contextual (lpSig ctlSig)).Models g
        ((firstOrderToSecond ctlSig).store (a := PUnit.unit) [(X, Y)])) := by
  have consistent : (FirstOrder.action ctlSig).Consistent [(un .f X, un .f Y)] :=
    ⟨fun _ => .const true, fun e member => by
      obtain rfl := List.mem_singleton.mp member
      rfl⟩
  obtain ⟨θ, -, principal⟩ := finite_principal_of_consistent consistent
  refine ((firstOrderToSecond_licensed (σ := ctlSig) PUnit.unit _).entails_models_iff (firstOrderToSecond_reflects (σ := ctlSig))
    (Or.inl ⟨PUnit.unit, θ, (Frames.ofSubstitution_principal_iff _ _ _).mpr principal⟩) _).mpr ?_
  intro _ δ solved e member
  obtain rfl := List.mem_singleton.mp member
  have equation : Term.app Sym.f (fun _ => δ.applyTerm X) = Term.app Sym.f (fun _ => δ.applyTerm Y) :=
    solved _ (List.mem_singleton_self _)
  injection equation with _ kids
  exact congrFun kids ⟨0, by decide⟩

/-- **Refutation control**: `true ≐ false` has no second-order solution, from the first-order
refutation. -/
theorem clash_secondOrder_refuted :
    ¬ (Frames.contextual (lpSig ctlSig)).Solvable
      ((firstOrderToSecond ctlSig).store (a := PUnit.unit) [(Term.const true, Term.const false)]) := by
  refine (firstOrderToSecond_licensed (σ := ctlSig) PUnit.unit _).refutes ?_
  rintro ⟨_, θ, solved⟩
  have clash : (Term.const true : Term ctlSig) = Term.const false := solved _ (List.mem_singleton_self _)
  cases clash

/-- **The cyclic store is licensed on the first-order edge**: the occurs-check refutation of
`X ≐ f(X)` is a second-order refutation. -/
theorem loop_secondOrder_refuted :
    ¬ (Frames.contextual (lpSig ctlSig)).Solvable
      ((firstOrderToSecond ctlSig).store (a := PUnit.unit) [(X, un .f X)]) :=
  (firstOrderToSecond_licensed (σ := ctlSig) PUnit.unit _).refutes fun solvable =>
    finite_occurs ((Frames.ofSubstitution_solvable_iff _ _).mp solvable)

end FirstOrderEdge

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational.Controls

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Rational.Controls.loop_not_acyclic
#print axioms Rational.Controls.loop_not_licensedAt
#print axioms Rational.Controls.finiteToRational_not_licensed
#print axioms Rational.Controls.dispatch_without_license
#print axioms Rational.Controls.commit_control
#print axioms Rational.Controls.guard_control
#print axioms Rational.Controls.refutation_control
#print axioms Rational.Controls.decomposition_dispatched
#print axioms Rational.Controls.clash_secondOrder_refuted
#print axioms Rational.Controls.loop_secondOrder_refuted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
