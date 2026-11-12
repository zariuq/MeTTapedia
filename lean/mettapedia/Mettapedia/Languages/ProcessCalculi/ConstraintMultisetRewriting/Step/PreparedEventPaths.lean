import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedEvents
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.GuardedPaths

/-!
# Actual admitted paths above prepared proposals

Permission lifting preserves and reflects the complete native event path.
The erasure is injective: only proof evidence is removed, never candidates,
preparations or their endpoint data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EffectCore

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (effect : EffectCore X O State Firing) (allow : effect.Admission)

theorem retain_admit_path : ∀ {source target : effect.admittedSubquiver allow}
    (path : Quiver.Path source target),
    (effect.retainGenerators allow).mapPath ((effect.admitGenerators allow).mapPath path) = path
  | _, _, .nil => rfl
  | _, _, .cons path edge => by
      change ((effect.retainGenerators allow).mapPath
        ((effect.admitGenerators allow).mapPath path)).cons
          ((effect.retainGenerators allow).map ((effect.admitGenerators allow).map edge)) = path.cons edge
      rw [retain_admit_path, retain_admit]

theorem admit_retain_path : ∀ {source target : effect.EventObject allow}
    (path : Quiver.Path source target),
    (effect.admitGenerators allow).mapPath ((effect.retainGenerators allow).mapPath path) = path
  | _, _, .nil => rfl
  | _, _, .cons path edge => by
      change ((effect.admitGenerators allow).mapPath
        ((effect.retainGenerators allow).mapPath path)).cons
          ((effect.admitGenerators allow).map ((effect.retainGenerators allow).map edge)) = path.cons edge
      rw [admit_retain_path, admit_retain]

def forgetEventPath {source target : State}
    (path : @Quiver.Path (effect.EventObject allow) _ source target) :
    @Quiver.Path effect.PreparedObject _ source target :=
  (GuardedPaths.inclusion (effect.admittedSubquiver allow)).mapPath
    ((effect.retainGenerators allow).mapPath path)

def admitEventPath {source target : State}
    (path : @Quiver.Path effect.PreparedObject _ source target)
    (permitted : GuardedPaths.Permitted (effect.admittedSubquiver allow) path) :
    @Quiver.Path (effect.EventObject allow) _ source target :=
  (effect.admitGenerators allow).mapPath
    (GuardedPaths.lift (effect.admittedSubquiver allow) path permitted)

theorem forget_admitEventPath {source target : State}
    (path : @Quiver.Path effect.PreparedObject _ source target)
    (permitted : GuardedPaths.Permitted (effect.admittedSubquiver allow) path) :
    effect.forgetEventPath allow (effect.admitEventPath allow path permitted) = path := by
  unfold forgetEventPath admitEventPath
  rw [retain_admit_path, GuardedPaths.inclusion_lift]

theorem forgetEventPath_injective {source target : State} :
    Function.Injective (effect.forgetEventPath allow :
      @Quiver.Path (effect.EventObject allow) _ source target → _) := by
  intro first second same
  have retained := GuardedPaths.inclusion_injective (effect.admittedSubquiver allow) same
  have original := congrArg ((effect.admitGenerators allow).mapPath) retained
  rw [admit_retain_path, admit_retain_path] at original
  exact original

theorem eventPath_exists_unique_iff {source target : State}
    (path : @Quiver.Path effect.PreparedObject _ source target) :
    (∃! admitted : @Quiver.Path (effect.EventObject allow) _ source target,
      effect.forgetEventPath allow admitted = path) ↔
        GuardedPaths.Permitted (effect.admittedSubquiver allow) path := by
  constructor
  · rintro ⟨admitted, agrees, _⟩
    rw [← agrees]
    exact GuardedPaths.permitted_of_lift _ ((effect.retainGenerators allow).mapPath admitted)
  · intro permitted
    refine ⟨effect.admitEventPath allow path permitted, effect.forget_admitEventPath allow path permitted, ?_⟩
    intro other agrees
    apply effect.forgetEventPath_injective allow
    rw [agrees, forget_admitEventPath]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EffectCore
