import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullSwap

/-!
# The diamond of a helper firing and a firing without helpers

A firing `f` that makes a helper `x : A` and a firing `g` without helpers meet at the frame `Γ.A`:
`f`'s data already live there, and `g` is read there along the weakening (`Natural.move`). After `f`,
`g`'s residual is `g` carried along the weakening; after `g`, `f`'s residual is `f` itself, since `g`
keeps the frame.

**The diamond closes on the nose** (`mixed_diamond`): when the two readings at `Γ.A` are independent
(`Independent`) and both firings are admitted, each is admitted after the other, and the two
composites have the same frame `Γ.A`, the same present occurrences and labels, and knowledge with the
same solutions. No swap is needed: only one telescope grows.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}
  {O : Type} [DecidableEq O] {s : State rules O}

/-- **The diamond of a helper firing and a firing without helpers closes on the nose.** -/
theorem mixed_diamond {A : TypeOver s.frame} {f : Natural levels O (extend s.frame A)}
    {g : Natural levels O s.frame} (first : (Natural.withHelper A f).Admits)
    (second : (Plain.toFiring g.toPlain).Admits)
    (independent : Independent (s.toLocal.move (projectionHom s.frame A)) f.toPlain
      (g.move (projectionHom s.frame A)).toPlain) :
    ∃ (afterFirst : (Plain.toFiring (s := (Natural.withHelper A f).after first)
        (g.move (projectionHom s.frame A)).toPlain).Admits)
      (afterSecond : (Natural.withHelper (s := (Plain.toFiring g.toPlain).after second) A f).Admits),
      (frames levels).Equivalent
          ((Plain.toFiring (s := (Natural.withHelper A f).after first)
            (g.move (projectionHom s.frame A)).toPlain).after afterFirst).toLocal.knowledge
          ((Natural.withHelper (s := (Plain.toFiring g.toPlain).after second) A f).after afterSecond).toLocal.knowledge ∧
        ((Plain.toFiring (s := (Natural.withHelper A f).after first)
            (g.move (projectionHom s.frame A)).toPlain).after afterFirst).toLocal.present =
          ((Natural.withHelper (s := (Plain.toFiring g.toPlain).after second) A f).after afterSecond).toLocal.present ∧
        ((Plain.toFiring (s := (Natural.withHelper A f).after first)
            (g.move (projectionHom s.frame A)).toPlain).after afterFirst).toLocal.label =
          ((Natural.withHelper (s := (Plain.toFiring g.toPlain).after second) A f).after afterSecond).toLocal.label := by
  have localFirst := (Natural.admits_withHelper A f).mp first
  have localSecond := (Plain.admits_toFiring g.toPlain).mp second
  have jointSolvable := independent.joint_solvable
  have admitG : (g.move (projectionHom s.frame A)).toPlain.Admits (s.toLocal.move (projectionHom s.frame A)) :=
    Natural.admits_move (projectionHom s.frame A) g localSecond (by
      rw [← Natural.information_move]
      refine Frames.solvable_of_subset (fun e member => ?_) jointSolvable
      rcases List.mem_append.mp member with known | own
      · exact List.mem_append_left _ (List.mem_append_left _ known)
      · exact List.mem_append_right _ own)
  obtain ⟨gAfterF, fAfterG, knowledge, present, label⟩ := local_diamond localFirst admitG independent
  -- the states after each firing, at the frame `Γ.A`
  have stateOne : ((Natural.withHelper A f).after first).toLocal =
      f.toPlain.after (s.toLocal.move (projectionHom s.frame A)) localFirst.1.2.2.2.2 :=
    Natural.toLocal_after_withHelper A f first
  have stateTwo : ((Plain.toFiring g.toPlain).after second).toLocal.move (projectionHom s.frame A) =
      (g.move (projectionHom s.frame A)).toPlain.after (s.toLocal.move (projectionHom s.frame A))
        admitG.1.2.2.2.2 :=
    (congrArg (Local.move (projectionHom s.frame A)) (Plain.toLocal_after g.toPlain second)).trans
      (Natural.after_move (projectionHom s.frame A) g s.toLocal localSecond.1.2.2.2.2 admitG.1.2.2.2.2).symm
  have afterFirst : (Plain.toFiring (s := (Natural.withHelper A f).after first)
      (g.move (projectionHom s.frame A)).toPlain).Admits :=
    (Plain.admits_toFiring (s := (Natural.withHelper A f).after first) _).mpr
      ((Plain.admits_congr rfl stateOne).mpr gAfterF)
  have afterSecond : (Natural.withHelper (s := (Plain.toFiring g.toPlain).after second) A f).Admits :=
    (Natural.admits_withHelper (s := (Plain.toFiring g.toPlain).after second) A f).mpr
      ((Plain.admits_congr rfl stateTwo).mpr fAfterG)
  refine ⟨afterFirst, afterSecond, ?_⟩
  have one : ((Plain.toFiring (s := (Natural.withHelper A f).after first)
        (g.move (projectionHom s.frame A)).toPlain).after afterFirst).toLocal =
      (g.move (projectionHom s.frame A)).toPlain.after
        (f.toPlain.after (s.toLocal.move (projectionHom s.frame A)) localFirst.1.2.2.2.2) admitG.1.2.2.2.2 :=
    (Plain.toLocal_after (s := (Natural.withHelper A f).after first) _ afterFirst).trans
      (Plain.after_congr rfl stateOne _ _)
  have two : ((Natural.withHelper (s := (Plain.toFiring g.toPlain).after second) A f).after afterSecond).toLocal =
      f.toPlain.after ((g.move (projectionHom s.frame A)).toPlain.after (s.toLocal.move (projectionHom s.frame A))
        admitG.1.2.2.2.2) localFirst.1.2.2.2.2 :=
    (Natural.toLocal_after_withHelper (s := (Plain.toFiring g.toPlain).after second) A f afterSecond).trans
      (Plain.after_congr rfl stateTwo _ _)
  rw [one, two]
  exact ⟨knowledge, present, label⟩

end DependentFull

#print axioms DependentFull.mixed_diamond

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
