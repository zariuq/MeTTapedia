import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Combinatorics.Quiver.Subquiver

/-!
# Admission of complete proposed paths

The wide subquiver retains every vertex and exactly the permitted arrows.
A proposed path has a unique lift precisely when every one of its generators
is permitted. The forgetful map retains the complete edge data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.GuardedPaths

open CategoryTheory

universe uV uE
variable {V : Type uV} [Quiver.{uE} V] (permit : WideSubquiver V)

inductive Permitted : {source target : V} → Quiver.Path source target → Prop
  | nil (source : V) : Permitted (.nil (a := source))
  | cons {source middle target : V} {path : Quiver.Path source middle} {edge : middle ⟶ target}
      (before : Permitted path) (last : edge ∈ permit middle target) : Permitted (path.cons edge)

theorem permitted_cons_iff {source middle target : V} (path : Quiver.Path source middle)
    (edge : middle ⟶ target) :
    Permitted permit (path.cons edge) ↔ Permitted permit path ∧ edge ∈ permit middle target := by
  constructor
  · intro all
    cases all with
    | cons before last => exact ⟨before, last⟩
  · exact fun ⟨before, last⟩ => .cons before last

theorem permitted_toPath_iff {source target : V} (edge : source ⟶ target) :
    Permitted permit edge.toPath ↔ edge ∈ permit source target :=
  ⟨fun all => (permitted_cons_iff permit _ _).mp all |>.2,
    fun allowed => .cons (.nil _) allowed⟩

theorem permitted_comp_iff {source middle target : V} (first : Quiver.Path source middle)
    (second : Quiver.Path middle target) :
    Permitted permit (first.comp second) ↔ Permitted permit first ∧ Permitted permit second := by
  induction second with
  | nil => exact ⟨fun all => ⟨all, .nil _⟩, And.left⟩
  | cons second edge ih =>
      rw [Quiver.Path.comp_cons, permitted_cons_iff, ih, permitted_cons_iff]
      tauto

def inclusion : permit ⥤q V where
  obj vertex := vertex
  map edge := edge.val

theorem permitted_of_lift {source target : permit} (path : Quiver.Path source target) :
    Permitted permit ((inclusion permit).mapPath path) := by
  induction path with
  | nil => exact .nil _
  | cons path edge ih => exact .cons ih edge.property

def lift {source : V} : ∀ {target : V} (path : Quiver.Path source target),
    Permitted permit path → @Quiver.Path permit _ source target
  | _, .nil, _ => .nil
  | _, .cons path edge, all =>
      let parts := (permitted_cons_iff permit path edge).mp all
      (lift path parts.1).cons ⟨edge, parts.2⟩

theorem inclusion_lift : ∀ {source target : V} (path : Quiver.Path source target)
    (all : Permitted permit path), (inclusion permit).mapPath (lift permit path all) = path
  | _, _, .nil, _ => by
      rw [lift]
      rfl
  | _, _, .cons path edge, all => by
      rw [lift]
      change ((inclusion permit).mapPath (lift permit path _)).cons edge = path.cons edge
      rw [inclusion_lift]

theorem lift_inclusion : ∀ {source target : permit} (path : Quiver.Path source target),
    lift permit ((inclusion permit).mapPath path) (permitted_of_lift permit path) = path
  | _, _, .nil => by
      change lift permit Quiver.Path.nil _ = Quiver.Path.nil
      rw [lift]
  | _, _, .cons path edge => by
      rcases edge with ⟨edge, allowed⟩
      change lift permit (((inclusion permit).mapPath path).cons edge) _ = path.cons ⟨edge, allowed⟩
      rw [lift]
      change (lift permit ((inclusion permit).mapPath path) _).cons ⟨edge, allowed⟩ =
        path.cons ⟨edge, allowed⟩
      rw [lift_inclusion]

theorem inclusion_injective {source target : permit} :
    Function.Injective ((inclusion permit).mapPath : Quiver.Path source target → _) := by
  intro first second same
  have packets :
      (⟨(inclusion permit).mapPath first, permitted_of_lift permit first⟩ :
        {path : @Quiver.Path V _ source target // Permitted permit path}) =
      ⟨(inclusion permit).mapPath second, permitted_of_lift permit second⟩ := Subtype.ext same
  have carried :
      lift permit ((inclusion permit).mapPath first) (permitted_of_lift permit first) =
      lift permit ((inclusion permit).mapPath second) (permitted_of_lift permit second) := by
    exact congrArg
      (fun packet : {path : @Quiver.Path V _ source target // Permitted permit path} =>
        lift permit packet.val packet.property) packets
  rw [lift_inclusion, lift_inclusion] at carried
  exact carried

theorem lift_exists_unique_iff {source target : V} (path : Quiver.Path source target) :
    (∃! lifted : @Quiver.Path permit _ source target, (inclusion permit).mapPath lifted = path) ↔
      Permitted permit path := by
  constructor
  · rintro ⟨lifted, agrees, _⟩
    rw [← agrees]
    exact permitted_of_lift permit lifted
  · intro all
    refine ⟨lift permit path all, inclusion_lift permit path all, ?_⟩
    intro other agrees
    apply inclusion_injective permit
    rw [agrees, inclusion_lift]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.GuardedPaths
