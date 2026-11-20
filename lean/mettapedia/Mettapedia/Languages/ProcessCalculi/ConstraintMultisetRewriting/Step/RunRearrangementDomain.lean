import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangementGrades

/-!
# Context-qualified domains of comparison certificates

The generator quiver is restricted to runs satisfying the chosen grade.
Its free groupoid maps to the unrestricted comparison groupoid. A raw path
lifts exactly when every visited run is in grade. Existence of a qualified
groupoid lift is a different, weaker question: it may use another raw
certificate for the same comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement

open _root_.CategoryTheory

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P} {start : State}

def Qualified (transport : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)
    {source : State} (grade : Object transport source → Prop) := {run : Object transport source // grade run}

instance qualifiedQuiver (grade : Object T start → Prop) : Quiver (Qualified T grade) where
  Hom first second := Generator T first.val second.val

def forgetGenerators (grade : Object T start → Prop) : Qualified T grade ⥤q Object T start where
  obj run := run.val
  map witness := witness

abbrev QualifiedPath (transport : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)
    {source : State} (grade : Object transport source → Prop) (first second : Qualified transport grade) :=
  @Quiver.Path (Quiver.Symmetrify (Qualified transport grade))
    (@Quiver.symmetrifyQuiver (Qualified transport grade) (qualifiedQuiver grade)) first second

def forgetPath {grade : Object T start → Prop} {first second : Qualified T grade}
    (path : QualifiedPath T grade first second) : RawCell T first.val second.val := by
  induction path with
  | nil => exact rawIdentity first.val
  | cons earlier edge ih => exact ih.cons edge

theorem within_forget {grade : Object T start → Prop} {first second : Qualified T grade}
    (path : QualifiedPath T grade first second) : Within grade (forgetPath path) := by
  induction path with
  | nil => exact first.property
  | @cons middle target earlier edge ih => exact ⟨ih, target.property⟩

def liftPath {grade : Object T start → Prop} {first second : Object T start}
    (path : RawCell T first second) (inside : Within grade path) :
    QualifiedPath T grade ⟨first, inside.atStart⟩ ⟨second, inside.last⟩ := by
  induction path with
  | nil =>
      exact @Quiver.Path.nil (Quiver.Symmetrify (Qualified T grade))
        (@Quiver.symmetrifyQuiver (Qualified T grade) (qualifiedQuiver grade)) ⟨first, inside⟩
  | cons earlier edge ih => exact (ih inside.1).cons edge

theorem forget_liftPath {grade : Object T start → Prop} {first second : Object T start}
    (path : RawCell T first second) (inside : Within grade path) : forgetPath (liftPath path inside) = path := by
  induction path with
  | nil => rfl
  | cons earlier edge ih => exact congrArg (fun path => path.cons edge) (ih inside.1)

theorem path_lifts_iff {grade : Object T start → Prop} {first second : Object T start}
    (path : RawCell T first second) :
    Within grade path ↔ ∃ (firstAllowed : grade first) (secondAllowed : grade second)
      (lifted : QualifiedPath T grade ⟨first, firstAllowed⟩ ⟨second, secondAllowed⟩),
      forgetPath lifted = path := by
  constructor
  · intro inside
    exact ⟨inside.atStart, inside.last, liftPath path inside, forget_liftPath path inside⟩
  · rintro ⟨_, _, lifted, same⟩
    exact same ▸ within_forget lifted

abbrev QualifiedGroupoid (grade : Object T start → Prop) := Quiver.FreeGroupoid (Qualified T grade)

def forgetFunctor (grade : Object T start → Prop) : QualifiedGroupoid grade ⥤ Groupoid T start :=
  Quiver.freeGroupoidFunctor (forgetGenerators grade)

def qualifiedObject {grade : Object T start → Prop} (run : Object T start) (allowed : grade run) :
    QualifiedGroupoid grade := (Quiver.FreeGroupoid.of (Qualified T grade)).obj ⟨run, allowed⟩

def Liftable (grade : Object T start → Prop) {first second : Object T start} (cell : Cell T first second) : Prop :=
  ∃ (firstAllowed : grade first) (secondAllowed : grade second)
    (lifted : qualifiedObject first firstAllowed ⟶ qualifiedObject second secondAllowed),
    (forgetFunctor grade).map lifted = cell

theorem liftable_identity {grade : Object T start → Prop} {run : Object T start} (allowed : grade run) :
    Liftable grade (𝟙 (object T run)) :=
  ⟨allowed, allowed, 𝟙 _, (forgetFunctor grade).map_id _⟩

theorem Liftable.comp {grade : Object T start → Prop} {first middle last : Object T start}
    {one : Cell T first middle} {two : Cell T middle last}
    (firstLift : Liftable grade one) (secondLift : Liftable grade two) : Liftable grade (one ≫ two) := by
  obtain ⟨firstAllowed, middleAllowed, left, leftMap⟩ := firstLift
  obtain ⟨middleAllowed', lastAllowed, right, rightMap⟩ := secondLift
  refine ⟨firstAllowed, lastAllowed, left ≫ right, ?_⟩
  exact ((forgetFunctor grade).map_comp left right).trans (congrArg₂ (fun a b => a ≫ b) leftMap rightMap)

theorem Liftable.inv {grade : Object T start → Prop} {first second : Object T start}
    {cell : Cell T first second} (lifted : Liftable grade cell) : Liftable grade (inv cell) := by
  obtain ⟨firstAllowed, secondAllowed, witness, maps⟩ := lifted
  refine ⟨secondAllowed, firstAllowed, CategoryTheory.inv witness, ?_⟩
  exact ((forgetFunctor grade).map_inv witness).trans (congrArg (fun arrow => CategoryTheory.inv arrow) maps)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement.path_lifts_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement.Liftable.comp
