import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.Basic

/-!
# Separation algebras

A separation algebra is a carrier of resources together with a way of putting
two resources side by side.  The combination is meaningful only for resources
that are *separate*; for any other pair it is still defined, but none of the
laws speaks about it.  This is the formulation of Klein, Kolanski and Boyton
(*Mechanised Separation Algebra*, ITP 2012) of the partial commutative monoids
of Calcagno, O'Hearn and Yang: a total addition, a separateness relation, and
seven laws that hold exactly where the pieces are separate.

On top of the structure sit the three connectives of bunched implications:

* `emp` holds of the empty resource;
* `P ∗ Q` holds of a resource that splits into two separate parts, one
  satisfying `P` and the other `Q`;
* `Q -∗ R` holds of a resource that, put beside any separate resource
  satisfying `Q`, gives a resource satisfying `R`.

The separating conjunction and the wand are adjoint (`sepConj_le_iff`), and
the separating conjunction is commutative, associative and has `emp` as its
unit.  Those three laws are where the commutativity and associativity of the
carrier are spent; the adjunction needs no law at all.

## Examples

* **Bags.**  Multisets under sum, with every two bags separate.  Any
  commutative monoid is a separation algebra this way (`ofAddCommMonoid`).
  A bag holding two copies of one atom splits into two singletons.
* **Located resources.**  A family of separation algebras indexed by
  locations is one, pointwise (`instPi`).  A network of occurrence stores is
  the case of bags at every location.
* **Exclusive ownership.**  `Excl` holds either nothing or a whole value, and
  two owned values are never separate.  A heap is a family of exclusive cells,
  and the negative example is the cell that cannot be owned twice
  (`not_sepConj_pointsTo_self`), where the bag above could be split.

## What the structure does not say

Cancellativity, positivity (only the empty resource has an inverse), and any
notion of permission are not consequences of these laws.  Where a later
statement needs one of them, it is a hypothesis of that statement or a fact
proved of a particular instance.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.SeparationAlgebra

universe u v

/-- **A separation algebra**: a total addition with a unit, and a separateness
relation, such that the commutative-monoid laws hold for separate resources and
separateness is preserved by regrouping. -/
class SepAlgebra (α : Type u) [Zero α] [Add α] where
  /-- The two resources can be put side by side. -/
  Separate : α → α → Prop
  /-- Every resource is separate from the empty one. -/
  separate_zero : ∀ x : α, Separate x 0
  /-- Separateness is symmetric. -/
  separate_symm : ∀ {x y : α}, Separate x y → Separate y x
  /-- The empty resource is a right unit. -/
  protected add_zero : ∀ x : α, x + 0 = x
  /-- Separate resources commute. -/
  protected add_comm : ∀ {x y : α}, Separate x y → x + y = y + x
  /-- Pairwise separate resources associate. -/
  protected add_assoc : ∀ {x y z : α}, Separate x y → Separate y z → Separate x z →
    x + y + z = x + (y + z)
  /-- A resource separate from a combination is separate from its first part. -/
  separate_of_separate_add : ∀ {x y z : α}, Separate x (y + z) → Separate y z →
    Separate x y
  /-- And the first part may be moved across. -/
  separate_add_of_separate_add : ∀ {x y z : α}, Separate x (y + z) → Separate y z →
    Separate (x + y) z

@[inherit_doc] scoped infix:50 " ## " => SepAlgebra.Separate

namespace SepAlgebra

variable {α : Type u} [Zero α] [Add α] [SepAlgebra α]

theorem zero_separate (x : α) : (0 : α) ## x := separate_symm (separate_zero x)

/-- The empty resource is also a left unit. -/
protected theorem zero_add (x : α) : 0 + x = x := by
  rw [SepAlgebra.add_comm (zero_separate x), SepAlgebra.add_zero]

/-- Regrouping a separate pair: if `x` and `y` are separate and their
combination is separate from `z`, then `x` is separate from `y + z` and `y`
from `z`. -/
theorem separate_add_right {x y z : α} (separateXY : x ## y)
    (separateSum : (x + y) ## z) : x ## (y + z) ∧ y ## z := by
  have zSum : z ## (y + x) := by
    rw [← SepAlgebra.add_comm separateXY]; exact separate_symm separateSum
  have zy : z ## y := separate_of_separate_add zSum (separate_symm separateXY)
  have zySum : (z + y) ## x :=
    separate_add_of_separate_add zSum (separate_symm separateXY)
  refine ⟨?_, separate_symm zy⟩
  rw [← SepAlgebra.add_comm zy]
  exact separate_symm zySum

/-- Associativity when the left pair is separate and its combination is
separate from the third resource. -/
theorem add_assoc_of_separate {x y z : α} (separateXY : x ## y)
    (separateSum : (x + y) ## z) : x + y + z = x + (y + z) := by
  have zSum : z ## (x + y) := separate_symm separateSum
  have zx : z ## x := separate_of_separate_add zSum separateXY
  exact SepAlgebra.add_assoc separateXY (separate_add_right separateXY separateSum).2
    (separate_symm zx)

/-- The mirror regrouping. -/
theorem separate_add_left {x y z : α} (separateYZ : y ## z)
    (separateSum : x ## (y + z)) : (x + y) ## z ∧ x ## y :=
  ⟨separate_add_of_separate_add separateSum separateYZ,
    separate_of_separate_add separateSum separateYZ⟩

end SepAlgebra

open SepAlgebra

variable {α : Type u} [Zero α] [Add α] [SepAlgebra α]

/-! ## The connectives of bunched implications -/

/-- The empty resource. -/
def emp : α → Prop := fun resource => resource = 0

/-- **Separating conjunction**: the resource splits into two separate parts
satisfying the two predicates. -/
def sepConj (P Q : α → Prop) : α → Prop :=
  fun resource => ∃ x y, x ## y ∧ resource = x + y ∧ P x ∧ Q y

/-- **Separating implication**: every separate extension satisfying `Q` gives
a combination satisfying `R`. -/
def wand (Q R : α → Prop) : α → Prop :=
  fun resource => ∀ extension, resource ## extension → Q extension → R (resource + extension)

@[inherit_doc] scoped infixr:35 " ∗ " => sepConj
@[inherit_doc] scoped infixr:25 " -∗ " => wand

/-- **The adjunction**: the separating conjunction with `Q` is left adjoint to
the wand from `Q`.  It holds in every separation algebra and uses none of the
laws. -/
theorem sepConj_le_iff {P Q R : α → Prop} : (P ∗ Q) ≤ R ↔ P ≤ (Q -∗ R) := by
  constructor
  · intro entails resource holdsP extension separate holdsQ
    exact entails _ ⟨resource, extension, separate, rfl, holdsP, holdsQ⟩
  · rintro entails _ ⟨x, y, separate, rfl, holdsP, holdsQ⟩
    exact entails x holdsP y separate holdsQ

/-- Modus ponens for the wand, the counit of the adjunction. -/
theorem sepConj_wand_le (Q R : α → Prop) : ((Q -∗ R) ∗ Q) ≤ R :=
  sepConj_le_iff.mpr le_rfl

theorem sepConj_mono {P P' Q Q' : α → Prop} (hP : P ≤ P') (hQ : Q ≤ Q') :
    (P ∗ Q) ≤ (P' ∗ Q') := by
  rintro _ ⟨x, y, separate, rfl, holdsP, holdsQ⟩
  exact ⟨x, y, separate, rfl, hP x holdsP, hQ y holdsQ⟩

/-- **Commutativity**, from the commutativity of separate resources. -/
theorem sepConj_comm (P Q : α → Prop) : (P ∗ Q) = (Q ∗ P) := by
  funext resource
  apply propext
  constructor
  · rintro ⟨x, y, separate, rfl, holdsP, holdsQ⟩
    exact ⟨y, x, separate_symm separate, SepAlgebra.add_comm separate, holdsQ, holdsP⟩
  · rintro ⟨x, y, separate, rfl, holdsQ, holdsP⟩
    exact ⟨y, x, separate_symm separate, SepAlgebra.add_comm separate, holdsP, holdsQ⟩

/-- **The unit law**. -/
theorem sepConj_emp (P : α → Prop) : (P ∗ emp) = P := by
  funext resource
  apply propext
  constructor
  · rintro ⟨x, y, -, rfl, holdsP, rfl⟩
    rwa [SepAlgebra.add_zero]
  · intro holdsP
    exact ⟨resource, 0, separate_zero resource, (SepAlgebra.add_zero resource).symm,
      holdsP, rfl⟩

theorem emp_sepConj (P : α → Prop) : (emp ∗ P) = P := by
  rw [sepConj_comm, sepConj_emp]

/-- **Associativity**, from associativity of separate resources and the two
regrouping laws. -/
theorem sepConj_assoc (P Q R : α → Prop) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) := by
  funext resource
  apply propext
  constructor
  · rintro ⟨_, z, separateSum, rfl, ⟨x, y, separateXY, rfl, holdsP, holdsQ⟩, holdsR⟩
    obtain ⟨separateX, separateYZ⟩ := separate_add_right separateXY separateSum
    exact ⟨x, y + z, separateX, add_assoc_of_separate separateXY separateSum,
      holdsP, y, z, separateYZ, rfl, holdsQ, holdsR⟩
  · rintro ⟨x, _, separateSum, rfl, holdsP, ⟨y, z, separateYZ, rfl, holdsQ, holdsR⟩⟩
    obtain ⟨separateXYZ, separateXY⟩ := separate_add_left separateYZ separateSum
    exact ⟨x + y, z, separateXYZ, (add_assoc_of_separate separateXY separateXYZ).symm,
      ⟨x, y, separateXY, rfl, holdsP, holdsQ⟩, holdsR⟩

/-! ## Commutative monoids: every two resources separate -/

/-- A commutative monoid is a separation algebra in which every two resources
are separate. -/
abbrev ofAddCommMonoid (M : Type u) [AddCommMonoid M] : SepAlgebra M where
  Separate _ _ := True
  separate_zero _ := trivial
  separate_symm _ := trivial
  add_zero := add_zero
  add_comm _ := add_comm _ _
  add_assoc _ _ _ := add_assoc _ _ _
  separate_of_separate_add _ _ := trivial
  separate_add_of_separate_add _ _ := trivial

/-- Bags under sum. -/
instance instMultiset (β : Type v) : SepAlgebra (Multiset β) := ofAddCommMonoid (Multiset β)

/-- Multiplicities under sum. -/
instance instNat : SepAlgebra ℕ := ofAddCommMonoid ℕ

/-- When every two resources are separate, the separating conjunction is the
plain existence of a sum decomposition. -/
theorem sepConj_iff_of_total (total : ∀ x y : α, x ## y) {P Q : α → Prop}
    {resource : α} :
    (P ∗ Q) resource ↔ ∃ x y, resource = x + y ∧ P x ∧ Q y := by
  constructor
  · rintro ⟨x, y, -, decomposition, holdsP, holdsQ⟩
    exact ⟨x, y, decomposition, holdsP, holdsQ⟩
  · rintro ⟨x, y, decomposition, holdsP, holdsQ⟩
    exact ⟨x, y, total x y, decomposition, holdsP, holdsQ⟩

/-- Positive control: a bag with two copies of one atom splits into two
singletons. -/
theorem sepConj_singleton_self {β : Type v} (atom : β) :
    ((fun bag : Multiset β => bag = {atom}) ∗ (fun bag => bag = {atom}))
      ({atom, atom} : Multiset β) :=
  ⟨{atom}, {atom}, trivial, rfl, rfl, rfl⟩

/-! ## Located resources -/

/-- A family of separation algebras indexed by locations, pointwise. -/
instance instPi {ι : Type u} {β : ι → Type v} [∀ i, Zero (β i)] [∀ i, Add (β i)]
    [∀ i, SepAlgebra (β i)] : SepAlgebra (∀ i, β i) where
  Separate f g := ∀ i, f i ## g i
  separate_zero f i := separate_zero (f i)
  separate_symm separate i := separate_symm (separate i)
  add_zero f := funext fun i => SepAlgebra.add_zero (f i)
  add_comm separate := funext fun i => SepAlgebra.add_comm (separate i)
  add_assoc separateFG separateGH separateFH :=
    funext fun i => SepAlgebra.add_assoc (separateFG i) (separateGH i) (separateFH i)
  separate_of_separate_add separate separateParts i :=
    separate_of_separate_add (separate i) (separateParts i)
  separate_add_of_separate_add separate separateParts i :=
    separate_add_of_separate_add (separate i) (separateParts i)

theorem separate_pi_iff {ι : Type u} {β : ι → Type v} [∀ i, Zero (β i)]
    [∀ i, Add (β i)] [∀ i, SepAlgebra (β i)] {f g : ∀ i, β i} :
    f ## g ↔ ∀ i, f i ## g i :=
  Iff.rfl

/-! ## Exclusive ownership -/

/-- A cell that is either empty or owns a whole value. -/
inductive Excl (β : Type v) where
  | empty
  | own (value : β)
  deriving DecidableEq

namespace Excl

variable {β : Type v}

instance : Zero (Excl β) := ⟨.empty⟩

/-- Putting cells together keeps the first owned value; the result matters only
when at most one of them owns a value. -/
instance : Add (Excl β) :=
  ⟨fun first second => match first with
    | .empty => second
    | .own value => .own value⟩

theorem zero_def : (0 : Excl β) = .empty := rfl

theorem empty_add (cell : Excl β) : (Excl.empty : Excl β) + cell = cell := rfl

theorem own_add (value : β) (cell : Excl β) : Excl.own value + cell = .own value := rfl

theorem add_eq_empty {first second : Excl β} (sum : first + second = .empty) :
    first = .empty ∧ second = .empty := by
  cases first with
  | empty => exact ⟨rfl, sum⟩
  | own value => cases sum

/-- Exclusive cells are a separation algebra: two cells are separate when at
most one of them owns a value. -/
instance instSepAlgebra : SepAlgebra (Excl β) where
  Separate first second := first = .empty ∨ second = .empty
  separate_zero _ := Or.inr rfl
  separate_symm separate := separate.symm
  add_zero cell := by cases cell <;> rfl
  add_comm := by
    rintro first second (rfl | rfl)
    · cases second <;> rfl
    · cases first <;> rfl
  add_assoc := by
    intro first second third _ _ _
    cases first <;> rfl
  separate_of_separate_add := by
    rintro first second third (rfl | sum) -
    · exact Or.inl rfl
    · exact Or.inr (add_eq_empty sum).1
  separate_add_of_separate_add := by
    rintro first second third (rfl | sum) separate
    · exact separate
    · exact Or.inr (add_eq_empty sum).2

/-- Two owned values are never separate. -/
theorem not_separate_own (first second : β) :
    ¬ ((Excl.own first : Excl β) ## Excl.own second) := by
  rintro (owned | owned) <;> cases owned

end Excl

section Heap

variable {Location : Type u} {β : Type v} [DecidableEq Location]

/-- The heap holding exactly one owned value at one location. -/
def pointsTo (location : Location) (value : β) : (Location → Excl β) → Prop :=
  fun heap => heap = Pi.single location (Excl.own value)

/-- **Negative control**: no heap splits into two parts that each own the same
location, whatever the two values.  Ownership is exclusive, which is the side
condition a bag of atoms does not impose (`sepConj_singleton_self`). -/
theorem not_sepConj_pointsTo_self (location : Location) (first second : β)
    (heap : Location → Excl β) :
    ¬ (pointsTo location first ∗ pointsTo location second) heap := by
  rintro ⟨x, y, separate, -, rfl, rfl⟩
  have atLocation := separate location
  simp only [Pi.single_eq_same] at atLocation
  exact Excl.not_separate_own first second atLocation

/-- **Positive control**: two distinct locations are owned side by side. -/
theorem sepConj_pointsTo_of_ne {location location' : Location}
    (different : location ≠ location') (first second : β) :
    (pointsTo location first ∗ pointsTo location' second)
      (Pi.single location (Excl.own first) + Pi.single location' (Excl.own second)) := by
  refine ⟨_, _, ?_, rfl, rfl, rfl⟩
  intro other
  by_cases atFirst : other = location
  · subst atFirst
    exact Or.inr (by simp [different, Excl.zero_def])
  · exact Or.inl (by simp [atFirst, Excl.zero_def])

end Heap

end Mettapedia.GSLT.SeparationAlgebra
