import Mettapedia.GSLT.Logic.SeparationAlgebra
import Mathlib.Data.Multiset.MapFold

/-!
# Transport of separating predicates

Translations of resources preserve their unit, separate compositions, and
separateness. This gives one direction of transport for separating conjunction
and the opposite direction for the wand. Equality of the transported predicates
requires different back conditions: lifting decompositions for conjunction and
lifting compatible extensions for the wand. Neither follows from injectivity.

The conditions compose. Mapping individual occurrences in a bag lifts every
decomposition, even when distinct occurrences have the same image. Lifting every
extension additionally follows when the map on occurrences is surjective.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.SeparationTransport

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
  [Zero A] [Add A] [SepAlgebra A]
  [Zero B] [Add B] [SepAlgebra B]
  [Zero C] [Add C] [SepAlgebra C]

/-- A map of resources preserving the defined compositions. -/
structure Hom (A : Type u) (B : Type v)
    [Zero A] [Add A] [SepAlgebra A] [Zero B] [Add B] [SepAlgebra B] where
  toFun : A → B
  map_zero : toFun 0 = 0
  map_add : ∀ {x y}, x ## y → toFun (x + y) = toFun x + toFun y
  map_separate : ∀ {x y}, x ## y → toFun x ## toFun y

instance : CoeFun (Hom A B) (fun _ => A → B) := ⟨Hom.toFun⟩

namespace Hom

/-- Identity resource translation. -/
def id (A : Type u) [Zero A] [Add A] [SepAlgebra A] : Hom A A where
  toFun := fun x => x
  map_zero := rfl
  map_add _ := rfl
  map_separate h := h

/-- Composition of resource translations. -/
def comp (g : Hom B C) (f : Hom A B) : Hom A C where
  toFun := fun x => g (f x)
  map_zero := by rw [f.map_zero, g.map_zero]
  map_add h := by rw [f.map_add h, g.map_add (f.map_separate h)]
  map_separate h := g.map_separate (f.map_separate h)

@[simp] theorem id_apply (x : A) : id A x = x := rfl
@[simp] theorem comp_apply (g : Hom B C) (f : Hom A B) (x : A) :
    comp g f x = g (f x) := rfl

/-- Reindexing a resource predicate along a translation. -/
def pull (f : Hom A B) (P : B → Prop) : A → Prop := fun x => P (f x)

@[simp] theorem pull_id (P : A → Prop) : (id A).pull P = P := rfl
@[simp] theorem pull_comp (g : Hom B C) (f : Hom A B) (P : C → Prop) :
    (comp g f).pull P = f.pull (g.pull P) := rfl

/-- Every decomposition of an image comes from separate source pieces. -/
def LiftsSplits (f : Hom A B) : Prop :=
  ∀ x b₁ b₂, b₁ ## b₂ → f x = b₁ + b₂ →
    ∃ a₁ a₂, a₁ ## a₂ ∧ x = a₁ + a₂ ∧ f a₁ = b₁ ∧ f a₂ = b₂

/-- Every resource compatible with an image has a compatible source preimage. -/
def LiftsExtensions (f : Hom A B) : Prop :=
  ∀ x b, f x ## b → ∃ a, x ## a ∧ f a = b

/-- A translation does not erase a nonempty source resource. -/
def ReflectsZero (f : Hom A B) : Prop := ∀ x, f x = 0 → x = 0

theorem sepConj_pull_le (f : Hom A B) (P Q : B → Prop) :
    sepConj (f.pull P) (f.pull Q) ≤ f.pull (sepConj P Q) := by
  rintro _ ⟨x, y, separate, rfl, hx, hy⟩
  exact ⟨f x, f y, f.map_separate separate, f.map_add separate, hx, hy⟩

theorem pull_sepConj (f : Hom A B) (lifts : f.LiftsSplits) (P Q : B → Prop) :
    f.pull (sepConj P Q) = sepConj (f.pull P) (f.pull Q) := by
  funext x
  apply propext
  constructor
  · rintro ⟨b₁, b₂, separate, decomposition, hP, hQ⟩
    obtain ⟨a₁, a₂, separateA, split, first, second⟩ :=
      lifts x b₁ b₂ separate decomposition
    exact ⟨a₁, a₂, separateA, split,
      by simpa only [pull, first] using hP,
      by simpa only [pull, second] using hQ⟩
  · exact f.sepConj_pull_le P Q x

/-- The split-lifting condition is necessary as well as sufficient for
preserving every separating conjunction by reindexing. -/
theorem liftsSplits_iff_pull_sepConj (f : Hom A B) :
    f.LiftsSplits ↔ ∀ P Q : B → Prop,
      f.pull (sepConj P Q) = sepConj (f.pull P) (f.pull Q) := by
  constructor
  · exact f.pull_sepConj
  · intro preserves x b₁ b₂ separate split
    have h : f.pull (sepConj (fun b => b = b₁) (fun b => b = b₂)) x :=
      ⟨b₁, b₂, separate, split, rfl, rfl⟩
    rw [preserves] at h
    exact h

theorem pull_wand_le (f : Hom A B) (Q R : B → Prop) :
    f.pull (wand Q R) ≤ wand (f.pull Q) (f.pull R) := by
  intro x h y separate holds
  change R (f (x + y))
  rw [f.map_add separate]
  exact h (f y) (f.map_separate separate) holds

theorem pull_wand (f : Hom A B) (lifts : f.LiftsExtensions) (Q R : B → Prop) :
    f.pull (wand Q R) = wand (f.pull Q) (f.pull R) := by
  funext x
  apply propext
  constructor
  · exact f.pull_wand_le Q R x
  · intro holds b separate hQ
    obtain ⟨a, sourceSeparate, image⟩ := lifts x b separate
    have hR := holds a sourceSeparate (by simpa only [pull, image] using hQ)
    change R (f (x + a)) at hR
    rwa [f.map_add sourceSeparate, image] at hR

/-- The extension-lifting condition exactly characterizes preservation of
all wands. The separating premise is essential. -/
theorem liftsExtensions_iff_pull_wand (f : Hom A B) :
    f.LiftsExtensions ↔ ∀ Q R : B → Prop,
      f.pull (wand Q R) = wand (f.pull Q) (f.pull R) := by
  constructor
  · exact f.pull_wand
  · intro preserves x b separate
    let hasLift : Prop := ∃ a, x ## a ∧ f a = b
    have holds : wand (f.pull (fun y => y = b)) (f.pull (fun _ => hasLift)) x := by
      intro a sourceSeparate image
      exact ⟨a, sourceSeparate, image⟩
    rw [← preserves] at holds
    exact holds b separate rfl

theorem emp_le_pull (f : Hom A B) : emp ≤ f.pull emp := by
  intro x empty
  change f x = 0
  rw [empty, f.map_zero]

theorem pull_emp (f : Hom A B) (reflects : f.ReflectsZero) : f.pull emp = emp := by
  funext x
  exact propext ⟨reflects x, f.emp_le_pull x⟩

theorem id_liftsSplits : (id A).LiftsSplits := by
  intro x a₁ a₂ separate split
  exact ⟨a₁, a₂, separate, split, rfl, rfl⟩

theorem id_liftsExtensions : (id A).LiftsExtensions := by
  intro x a separate
  exact ⟨a, separate, rfl⟩

theorem id_reflectsZero : (id A).ReflectsZero := by intro x h; exact h

theorem comp_liftsSplits (g : Hom B C) (f : Hom A B)
    (hg : g.LiftsSplits) (hf : f.LiftsSplits) : (comp g f).LiftsSplits := by
  intro x c₁ c₂ separate split
  obtain ⟨b₁, b₂, separateB, splitB, firstB, secondB⟩ :=
    hg (f x) c₁ c₂ separate split
  obtain ⟨a₁, a₂, separateA, splitA, firstA, secondA⟩ :=
    hf x b₁ b₂ separateB splitB
  exact ⟨a₁, a₂, separateA, splitA, by simp [firstA, firstB], by simp [secondA, secondB]⟩

theorem comp_liftsExtensions (g : Hom B C) (f : Hom A B)
    (hg : g.LiftsExtensions) (hf : f.LiftsExtensions) :
    (comp g f).LiftsExtensions := by
  intro x c separate
  obtain ⟨b, separateB, imageB⟩ := hg (f x) c separate
  obtain ⟨a, separateA, imageA⟩ := hf x b separateB
  exact ⟨a, separateA, by simp [imageA, imageB]⟩

theorem comp_reflectsZero (g : Hom B C) (f : Hom A B)
    (hg : g.ReflectsZero) (hf : f.ReflectsZero) : (comp g f).ReflectsZero := by
  intro x empty
  exact hf x (hg (f x) empty)

end Hom

/-! ## Occurrence maps -/

variable {α : Type u} {β : Type v}

/-- Mapping occurrences retains bag multiplicity. -/
def bagMap (f : α → β) : Hom (Multiset α) (Multiset β) where
  toFun := Multiset.map f
  map_zero := Multiset.map_zero f
  map_add _ := Multiset.map_add f _ _
  map_separate _ := trivial

theorem bagMap_reflectsZero (f : α → β) : (bagMap f).ReflectsZero := by
  intro bag empty
  exact Multiset.map_eq_zero.mp empty

/-- A target partition of mapped occurrences lifts to a partition of the
source occurrences. Injectivity is not needed. -/
theorem bagMap_liftsSplits (f : α → β) : (bagMap f).LiftsSplits := by
  classical
  intro source left
  induction left using Multiset.induction_on generalizing source with
  | empty =>
    intro right _ split
    exact ⟨0, source, trivial, by simp, by simp [bagMap], by simpa using split⟩
  | @cons atom left ih =>
    intro right _ split
    have mapCons : source.map f = atom ::ₘ (left + right) := by
      simpa only [bagMap, Multiset.cons_add] using split
    obtain ⟨a, member, image, remainder⟩ :=
      (Multiset.map_eq_cons f source (left + right) atom).mpr mapCons
    obtain ⟨first, second, separate, decomposition, mapFirst, mapSecond⟩ :=
      ih (source := source.erase a) right trivial remainder
    refine ⟨a ::ₘ first, second, trivial, ?_, ?_, mapSecond⟩
    · rw [Multiset.cons_add, ← decomposition, Multiset.cons_erase member]
    · change (a ::ₘ first).map f = atom ::ₘ left
      rw [Multiset.map_cons, image]
      exact congrArg (Multiset.cons atom) mapFirst

theorem bagMap_liftsExtensions (f : α → β) (surjective : Function.Surjective f) :
    (bagMap f).LiftsExtensions := by
  intro _ target _
  obtain ⟨source, image⟩ := Multiset.map_surjective_of_surjective surjective target
  exact ⟨source, trivial, image⟩

/-- A target singleton already tests the entire extension-lifting condition
for occurrence maps. -/
theorem bagMap_liftsExtensions_iff_surjective (f : α → β) :
    (bagMap f).LiftsExtensions ↔ Function.Surjective f := by
  constructor
  · intro lifts target
    obtain ⟨source, _, image⟩ := lifts 0 {target} trivial
    have member : target ∈ source.map f := by
      change source.map f = {target} at image
      rw [image]
      exact Multiset.mem_singleton_self target
    obtain ⟨atom, _, equal⟩ := Multiset.mem_map.mp member
    exact ⟨atom, equal⟩
  · exact bagMap_liftsExtensions f

theorem bagMap_pull_sepConj (f : α → β) (P Q : Multiset β → Prop) :
    (bagMap f).pull (sepConj P Q) =
      sepConj ((bagMap f).pull P) ((bagMap f).pull Q) :=
  (bagMap f).pull_sepConj (bagMap_liftsSplits f) P Q

theorem bagMap_pull_emp (f : α → β) : (bagMap f).pull emp = emp :=
  (bagMap f).pull_emp (bagMap_reflectsZero f)

theorem bagMap_pull_wand (f : α → β) (surjective : Function.Surjective f)
    (Q R : Multiset β → Prop) :
    (bagMap f).pull (wand Q R) = wand ((bagMap f).pull Q) ((bagMap f).pull R) :=
  (bagMap f).pull_wand (bagMap_liftsExtensions f surjective) Q R

end Mettapedia.GSLT.Logic.SeparationTransport
