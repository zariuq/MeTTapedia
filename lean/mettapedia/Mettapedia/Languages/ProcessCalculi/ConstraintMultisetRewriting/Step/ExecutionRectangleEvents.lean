import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ExecutionRectanglePaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedEventRuns

/-!
# Native executions of prepared rectangles

Every proposed interleaving is a unique native run exactly when all proposed
edges are admitted. This is a criterion for a given prepared rectangle; it
does not assert that arbitrary local runs have a compatible rectangle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open ExecutionGeometry

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

namespace EffectCore

variable (effect : EffectCore X O State Firing) (allow : effect.Admission)

theorem rectangle_admitted_iff_unique_event_lifts {width height : Nat}
    (grid : Rectangle effect.PreparedObject width height) :
    Rectangle.AllPermitted (effect.admittedSubquiver allow) grid ↔
      ∀ shuffle : Shuffle width height,
        ∃! path : @Quiver.Path (effect.EventObject allow) _ grid.entry grid.exit,
          effect.forgetEventPath allow path = Rectangle.proposal shuffle grid := by
  rw [Rectangle.allPermitted_iff_all_shuffles]
  apply forall_congr'
  intro shuffle
  exact (Rectangle.proposal_permitted_iff (effect.admittedSubquiver allow) shuffle grid).symm.trans
    (effect.eventPath_exists_unique_iff allow (Rectangle.proposal shuffle grid)).symm

end EffectCore

namespace Step

variable (P : Step X O State Firing)

theorem selected_shuffle_iff_unique_run {width height : Nat}
    (grid : Rectangle P.effectCore.PreparedObject width height) (shuffle : Shuffle width height) :
    Rectangle.Admitted (P.effectCore.admittedSubquiver P.eventAdmission) grid shuffle ↔
      ∃! run : {r : P.Run grid.entry // r.last = grid.exit},
        P.preparedRunPath run = Rectangle.proposal shuffle grid :=
  (Rectangle.proposal_permitted_iff
    (P.effectCore.admittedSubquiver P.eventAdmission) shuffle grid).symm.trans
      (P.run_lift_exists_unique_iff (Rectangle.proposal shuffle grid)).symm

theorem some_shuffle_iff_native_run {width height : Nat}
    (grid : Rectangle P.effectCore.PreparedObject width height) :
    (∃ shuffle, Rectangle.Admitted (P.effectCore.admittedSubquiver P.eventAdmission) grid shuffle) ↔
      ∃ shuffle, ∃! run : {r : P.Run grid.entry // r.last = grid.exit},
        P.preparedRunPath run = Rectangle.proposal shuffle grid :=
  exists_congr (fun shuffle => P.selected_shuffle_iff_unique_run grid shuffle)

theorem rectangle_admitted_iff_unique_runs {width height : Nat}
    (grid : Rectangle P.effectCore.PreparedObject width height) :
    Rectangle.AllPermitted (P.effectCore.admittedSubquiver P.eventAdmission) grid ↔
      ∀ shuffle : Shuffle width height,
        ∃! run : {r : P.Run grid.entry // r.last = grid.exit},
          P.preparedRunPath run = Rectangle.proposal shuffle grid := by
  rw [Rectangle.allPermitted_iff_all_shuffles]
  apply forall_congr'
  intro shuffle
  exact (Rectangle.proposal_permitted_iff
    (P.effectCore.admittedSubquiver P.eventAdmission) shuffle grid).symm.trans
      (P.run_lift_exists_unique_iff (Rectangle.proposal shuffle grid)).symm

end Step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
