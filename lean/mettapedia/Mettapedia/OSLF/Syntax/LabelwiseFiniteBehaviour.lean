import Mettapedia.OSLF.Syntax.DeterministicGSOSBehaviour
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Option
import Mathlib.Data.Set.Finite.Lattice

/-!
# Labelwise finite behavior and total branching

Finite successor sets at each action form a genuine nondeterministic
endofunctor. Deterministic behavior embeds naturally by empty or singleton
sets. Total outgoing branching is finite exactly when the enabled action
support is finite; an arbitrary action alphabet cannot be omitted from
this distinction. No nondeterministic rule correspondence is inferred
from the embedding alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS

open CategoryTheory

universe u

variable (S : Signature.{u}) (Actions : S.Srt → Type u)

abbrev LabelwiseFiniteBehaviour (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt) :=
  Actions sort → Finset (X base sort)

/-- Relabel complete finite successor sets, including noninjective maps. -/
noncomputable def labelwiseFiniteMap {X Y : S.Families} (mapping : X ⟶ Y)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (behaviour : LabelwiseFiniteBehaviour S Actions X base sort) :
    LabelwiseFiniteBehaviour S Actions Y base sort := by
  classical
  exact fun action => (behaviour action).image (mapping base sort)

/-- The endofunctor of finitely many successors per action. -/
noncomputable def labelwiseFiniteFunctor : S.Families ⥤ S.Families where
  obj X := LabelwiseFiniteBehaviour S Actions X
  map mapping := fun base sort => ↾(labelwiseFiniteMap S Actions mapping base sort)
  map_id X := by
    classical
    funext base sort
    apply ConcreteCategory.hom_ext
    intro behaviour
    funext action
    change (behaviour action).image (fun value => value) = behaviour action
    simp
  map_comp earlier later := by
    classical
    funext base sort
    apply ConcreteCategory.hom_ext
    intro behaviour
    funext action
    change (behaviour action).image (fun value => later base sort (earlier base sort value)) =
      ((behaviour action).image (earlier base sort)).image (later base sort)
    exact Finset.image_image.symm

/-- Deterministic behavior is included by its actual empty or singleton support. -/
noncomputable def deterministicInclusion :
    behaviourFunctor S Actions ⟶ labelwiseFiniteFunctor S Actions where
  app X := fun base sort => ↾(fun behaviour action => (behaviour action).toFinset)
  naturality {X Y} mapping := by
    classical
    funext base sort
    apply ConcreteCategory.hom_ext
    intro behaviour
    funext action
    change ((behaviour action).map (mapping base sort)).toFinset =
      (behaviour action).toFinset.image (mapping base sort)
    cases behaviour action <;> simp

theorem deterministicInclusion_injective (X : S.Families)
    (base : PUnit.{u + 1}) (sort : S.Srt) :
    Function.Injective ((deterministicInclusion S Actions).app X base sort) := by
  classical
  intro first second equal
  funext action
  have same := congrFun equal action
  change (first action).toFinset = (second action).toFinset at same
  cases earlier : first action <;> cases later : second action <;> simp_all

/-- Finite images preserve and reflect the existence of an enabled action. -/
theorem labelwiseFiniteMap_enabled_iff {X Y : S.Families} (mapping : X ⟶ Y)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (behaviour : LabelwiseFiniteBehaviour S Actions X base sort) (action : Actions sort) :
    (labelwiseFiniteMap S Actions mapping base sort behaviour action).Nonempty ↔
      (behaviour action).Nonempty := by
  classical
  simp [labelwiseFiniteMap]

namespace LabelwiseFiniteBehaviour

variable {S Actions} {X : S.Families} {base : PUnit.{u + 1}} {sort : S.Srt}

def edges (behaviour : LabelwiseFiniteBehaviour S Actions X base sort) :
    Set (Actions sort × X base sort) :=
  {edge | edge.2 ∈ behaviour edge.1}

def enabled (behaviour : LabelwiseFiniteBehaviour S Actions X base sort) : Set (Actions sort) :=
  {action | (behaviour action).Nonempty}

theorem enabled_eq_image (behaviour : LabelwiseFiniteBehaviour S Actions X base sort) :
    behaviour.enabled = Prod.fst '' behaviour.edges := by
  ext action
  constructor
  · rintro ⟨successor, member⟩
    exact ⟨(action, successor), member, rfl⟩
  · rintro ⟨⟨label, successor⟩, member, equal⟩
    change label = action at equal
    subst label
    exact ⟨successor, member⟩

/-- Per-action finiteness becomes total finiteness precisely at finite enabled support. -/
theorem edges_finite_iff_enabled_finite (behaviour : LabelwiseFiniteBehaviour S Actions X base sort) :
    behaviour.edges.Finite ↔ behaviour.enabled.Finite := by
  classical
  constructor
  · intro finite
    rw [enabled_eq_image]
    exact finite.image Prod.fst
  · intro finite
    have unionFinite : (⋃ action ∈ behaviour.enabled,
        (fun successor => (action, successor)) '' (↑(behaviour action) : Set (X base sort))).Finite :=
      finite.biUnion (fun action _ => (behaviour action).finite_toSet.image _)
    apply unionFinite.subset
    rintro ⟨action, successor⟩ member
    apply Set.mem_iUnion.mpr
    refine ⟨action, Set.mem_iUnion.mpr ⟨⟨successor, member⟩, ?_⟩⟩
    exact ⟨successor, member, rfl⟩

theorem finiteActions_edges_finite (behaviour : LabelwiseFiniteBehaviour S Actions X base sort)
    [Finite (Actions sort)] : behaviour.edges.Finite :=
  (behaviour.edges_finite_iff_enabled_finite).mpr (Set.toFinite _)

end LabelwiseFiniteBehaviour

end Mettapedia.OSLF.DeterministicGSOS
