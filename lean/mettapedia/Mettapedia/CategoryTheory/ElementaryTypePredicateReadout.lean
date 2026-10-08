import Mettapedia.CategoryTheory.ElementaryToposPredicateDoctrine
import Mettapedia.CategoryTheory.TypeSubobjectClassifier
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Pointwise readouts of the earned elementary set doctrine

Membership retains an actual element of the predicate's monomorphism.
The order, pullback, meet, implication and both quantifier readouts are
derived from those maps and the earned adjunctions. No pointwise logical
interpretation is supplied to the doctrine as a law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryTypePredicateReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits

def doctrine := ElementaryToposPredicateDoctrine.doctrine TypeSubobjectClassifier.classifier

def Contains {X : Type} (predicate : Subobject X) (value : X) : Prop :=
  ∃ supplied, predicate.arrow supplied = value

def point {X : Type} (value : X) : PUnit ⟶ X := TypeCat.ofHom fun _ => value

instance point_mono {X : Type} (value : X) : Mono (point value) :=
  (mono_iff_injective _).mpr (fun _ _ _ => Subsingleton.elim _ _)

def singleton {X : Type} (value : X) : Subobject X := Subobject.mk (point value)

theorem singleton_le_iff {X : Type} (value : X) (predicate : Subobject X) :
    singleton value ≤ predicate ↔ Contains predicate value := by
  constructor
  · intro admitted
    refine ⟨(Subobject.ofMkLE (point value) predicate admitted) PUnit.unit, ?_⟩
    exact congrArg (fun arrow : PUnit ⟶ X => arrow PUnit.unit)
      (Subobject.ofMkLE_arrow admitted)
  · rintro ⟨supplied, reading⟩
    exact Subobject.mk_le_of_comm (TypeCat.ofHom fun _ => supplied)
      (by ext; exact reading)

theorem contains_singleton_iff {X : Type} (first second : X) :
    Contains (singleton first) second ↔ second = first := by
  constructor
  · rintro ⟨supplied, reading⟩
    have exactPoint := congrArg (fun arrow : (singleton first : Type) ⟶ X => arrow supplied)
        (Subobject.underlyingIso_hom_comp_eq_mk (point first))
    exact reading.symm.trans exactPoint.symm
  · intro same
    subst second
    refine ⟨(Subobject.underlyingIso (point first)).inv PUnit.unit, ?_⟩
    exact congrArg (fun arrow : PUnit ⟶ X => arrow PUnit.unit)
      (Subobject.underlyingIso_arrow (point first))

theorem le_iff_contains {X : Type} (first second : Subobject X) :
    first ≤ second ↔ ∀ value, Contains first value → Contains second value := by
  constructor
  · intro admitted value ⟨supplied, reading⟩
    refine ⟨Subobject.ofLE first second admitted supplied, ?_⟩
    exact (congrArg (fun arrow : (first : Type) ⟶ X => arrow supplied)
      (Subobject.ofLE_arrow admitted)).trans reading
  · intro included
    let retained (supplied : (first : Type)) : (second : Type) :=
      Classical.choose (included (first.arrow supplied) ⟨supplied, rfl⟩)
    apply Subobject.le_of_comm (TypeCat.ofHom retained)
    ext supplied
    exact Classical.choose_spec (included (first.arrow supplied) ⟨supplied, rfl⟩)

def fromSet {X : Type} (predicate : Set X) : Subobject X :=
  let inclusion : (predicate : Type) ⟶ X := TypeCat.ofHom Subtype.val
  let : Mono inclusion := (mono_iff_injective inclusion).mpr Subtype.val_injective
  Subobject.mk inclusion

theorem contains_fromSet {X : Type} (predicate : Set X) (value : X) :
    Contains (fromSet predicate) value ↔ value ∈ predicate := by
  let inclusion : (predicate : Type) ⟶ X := TypeCat.ofHom Subtype.val
  let : Mono inclusion := (mono_iff_injective inclusion).mpr Subtype.val_injective
  constructor
  · rintro ⟨supplied, reading⟩
    have whole := congrArg (fun arrow : (fromSet predicate : Type) ⟶ X => arrow supplied)
        (Subobject.underlyingIso_hom_comp_eq_mk inclusion)
    have valueRead : ((Subobject.underlyingIso inclusion).hom supplied).val = value :=
      whole.trans reading
    exact valueRead ▸ ((Subobject.underlyingIso inclusion).hom supplied).property
  · intro held
    refine ⟨(Subobject.underlyingIso inclusion).inv ⟨value, held⟩, ?_⟩
    exact congrArg (fun arrow : (predicate : Type) ⟶ X => arrow ⟨value, held⟩)
      (Subobject.underlyingIso_arrow inclusion)

theorem contains_inf {X : Type} (first second : Subobject X) (value : X) :
    Contains (first ⊓ second) value ↔ Contains first value ∧ Contains second value := by
  rw [← singleton_le_iff, le_inf_iff, singleton_le_iff, singleton_le_iff]

theorem contains_top {X : Type} (value : X) : Contains (⊤ : Subobject X) value :=
  (singleton_le_iff value ⊤).mp le_top

theorem eq_top_iff_contains {X : Type} (predicate : Subobject X) :
    predicate = ⊤ ↔ ∀ value, Contains predicate value := by
  constructor
  · rintro rfl
    exact contains_top
  · intro held
    exact eq_top_iff.mpr ((le_iff_contains ⊤ predicate).mpr (fun value _ => held value))

theorem contains_reindex {X Y : Type} (mapping : X ⟶ Y)
    (predicate : Subobject Y) (value : X) :
    Contains (doctrine.reindex mapping predicate) value ↔ Contains predicate (mapping value) := by
  let square := Subobject.isPullback mapping predicate
  constructor
  · rintro ⟨supplied, reading⟩
    refine ⟨(Subobject.pullbackπ mapping predicate) supplied, ?_⟩
    have exactValue := congrArg
      (fun arrow : (((Subobject.pullback mapping).obj predicate) : Type) ⟶ Y => arrow supplied) square.w
    exact exactValue.trans (congrArg mapping reading)
  · rintro ⟨supplied, reading⟩
    obtain ⟨retained, _, exactValue⟩ := Types.exists_of_isPullback square supplied value reading
    exact ⟨retained, exactValue⟩

theorem contains_implication {X : Type} (first second : Subobject X) (value : X) :
    Contains (doctrine.algebra X |>.himp first second) value ↔
      (Contains first value → Contains second value) := by
  let : HeytingAlgebra (Subobject X) := doctrine.algebra X
  change Contains (first ⇨ second) value ↔ _
  rw [← singleton_le_iff, le_himp_iff, le_iff_contains]
  constructor
  · intro held premise
    exact held value ((contains_inf _ _ value).mpr
      ⟨(contains_singleton_iff value value).mpr rfl, premise⟩)
  · intro held actual included
    obtain ⟨pointRead, premise⟩ := (contains_inf _ _ actual).mp included
    have same := (contains_singleton_iff value actual).mp pointRead
    subst actual
    exact held premise

theorem contains_forall {X Y : Type} (mapping : X ⟶ Y)
    (predicate : Subobject X) (value : Y) :
    Contains (doctrine.forallAlong mapping predicate) value ↔
      ∀ supplied, mapping supplied = value → Contains predicate supplied := by
  constructor
  · intro admitted supplied reading
    have fibre := (contains_reindex mapping _ supplied).mpr (reading.symm ▸ admitted)
    exact (le_iff_contains _ _).mp ((doctrine.forall_adj mapping).l_u_le predicate) supplied fibre
  · intro admitted
    let all : Set Y := {point | ∀ supplied, mapping supplied = point → Contains predicate supplied}
    have included : doctrine.reindex mapping (fromSet all) ≤ predicate := by
      apply (le_iff_contains _ _).mpr
      intro supplied held
      exact ((contains_fromSet all (mapping supplied)).mp
        ((contains_reindex mapping _ supplied).mp held)) supplied rfl
    have whole := (doctrine.forall_adj mapping (fromSet all) predicate).mp included
    exact (le_iff_contains _ _).mp whole value ((contains_fromSet all value).mpr admitted)

theorem contains_exists {X Y : Type} (mapping : X ⟶ Y)
    (predicate : Subobject X) (value : Y) :
    Contains (doctrine.existsAlong mapping predicate) value ↔
      ∃ supplied, Contains predicate supplied ∧ mapping supplied = value := by
  constructor
  · intro admitted
    let image : Set Y := {point | ∃ supplied, Contains predicate supplied ∧ mapping supplied = point}
    have included : predicate ≤ doctrine.reindex mapping (fromSet image) := by
      apply (le_iff_contains _ _).mpr
      intro supplied held
      apply (contains_reindex mapping _ supplied).mpr
      exact (contains_fromSet image _).mpr ⟨supplied, held, rfl⟩
    have whole := (doctrine.exists_adj mapping predicate (fromSet image)).mpr included
    exact (contains_fromSet image value).mp ((le_iff_contains _ _).mp whole value admitted)
  · rintro ⟨supplied, held, rfl⟩
    have included := (le_iff_contains _ _).mp ((doctrine.exists_adj mapping).le_u_l predicate) supplied held
    exact (contains_reindex mapping _ supplied).mp included

end Mettapedia.CategoryTheory.ElementaryTypePredicateReadout
