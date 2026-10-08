import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Set.Disjoint

/-!
# Scope separation and complete occurrence inventories

A scope of inventories has a name support: every name occurring in any of
its admitted inventories. Grade-zero separation forbids a common name in
any pair of admitted inventories. This earns uniqueness of both sides of
a parallel split, retaining all occurrence multiplicities. No partition of
the whole name universe, or reduction-based separation, is assumed.

An independently supplied Boolean name classifier computes the split by
filtering. Its support conditions earn equivalence between independently
defined composite membership and testing the computed components.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.SupportSeparatedDecomposition

universe u

variable {Name : Type u}

/-- All names carried by any member of an inventory scope. -/
def scopeSupport (scope : Multiset Name → Prop) : Set Name :=
  {name | ∃ inventory, scope inventory ∧ name ∈ inventory}

/-- Separation over the complete scope extensions, including cross pairs. -/
def GradeZero (left right : Multiset Name → Prop) : Prop :=
  ∀ first second, left first → right second →
    ∀ name, name ∈ first → name ∈ second → False

theorem gradeZero_iff_disjoint_support (left right : Multiset Name → Prop) :
    GradeZero left right ↔ Disjoint (scopeSupport left) (scopeSupport right) := by
  rw [Set.disjoint_left]
  constructor
  · intro separated name first second
    obtain ⟨a, admittedA, memberA⟩ := first
    obtain ⟨b, admittedB, memberB⟩ := second
    exact separated a b admittedA admittedB name memberA memberB
  · intro separated a b admittedA admittedB name memberA memberB
    exact separated ⟨a, admittedA, memberA⟩ ⟨b, admittedB, memberB⟩

/-- Two complete decompositions of the same inventory have the same halves. -/
theorem split_unique [DecidableEq Name]
    {left right : Multiset Name → Prop} (separated : GradeZero left right)
    {a b a' b' : Multiset Name} (admittedA : left a) (admittedB : right b)
    (admittedA' : left a') (admittedB' : right b')
    (same : a + b = a' + b') : a = a' ∧ b = b' := by
  have counts : ∀ name, a.count name + b.count name =
      a'.count name + b'.count name := by
    intro name
    simpa only [Multiset.count_add] using congrArg (Multiset.count name) same
  have first : ∀ name, a.count name = a'.count name := by
    intro name
    have total := counts name
    by_cases positive : 0 < a.count name
    · have otherZero : b'.count name = 0 := Multiset.count_eq_zero.mpr
        (fun member => separated a b' admittedA admittedB' name
          (Multiset.count_pos.mp positive) member)
      have positive' : 0 < a'.count name := by omega
      have otherZero' : b.count name = 0 := Multiset.count_eq_zero.mpr
        (fun member => separated a' b admittedA' admittedB name
          (Multiset.count_pos.mp positive') member)
      omega
    · by_cases positive' : 0 < a'.count name
      · have otherZero : b.count name = 0 := Multiset.count_eq_zero.mpr
          (fun member => separated a' b admittedA' admittedB name
            (Multiset.count_pos.mp positive') member)
        omega
      · omega
  refine ⟨Multiset.ext.mpr first, Multiset.ext.mpr ?_⟩
  intro name
  have total := counts name
  have equalFirst := first name
  omega

/-- Composite membership is defined by an admitted decomposition. -/
def Composite (left right : Multiset Name → Prop) (inventory : Multiset Name) : Prop :=
  ∃ a b, left a ∧ right b ∧ a + b = inventory

theorem composite_unique [DecidableEq Name]
    {left right : Multiset Name → Prop} (separated : GradeZero left right)
    {inventory : Multiset Name} (member : Composite left right inventory) :
    ∃! pair : Multiset Name × Multiset Name,
      left pair.1 ∧ right pair.2 ∧ pair.1 + pair.2 = inventory := by
  obtain ⟨a, b, admittedA, admittedB, whole⟩ := member
  refine ⟨(a, b), ⟨admittedA, admittedB, whole⟩, ?_⟩
  rintro ⟨a', b'⟩ ⟨admittedA', admittedB', whole'⟩
  obtain ⟨first, second⟩ := split_unique separated admittedA' admittedB'
    admittedA admittedB (whole'.trans whole.symm)
  exact Prod.ext first second

/-- The supplied name classifier selects the complete left inventory. -/
def leftPart (classify : Name → Bool) (inventory : Multiset Name) : Multiset Name :=
  inventory.filter (fun name => classify name = true)

/-- Every other occurrence goes to the right; multiplicities are retained. -/
def rightPart (classify : Name → Bool) (inventory : Multiset Name) : Multiset Name :=
  inventory.filter (fun name => classify name ≠ true)

theorem parts_add (classify : Name → Bool) (inventory : Multiset Name) :
    leftPart classify inventory + rightPart classify inventory = inventory := by
  exact Multiset.filter_add_not _ inventory

/-- Every name of an admitted left component has its declared colour. -/
def LeftSupported (classify : Name → Bool) (left : Multiset Name → Prop) : Prop :=
  ∀ inventory, left inventory → ∀ name ∈ inventory, classify name = true

/-- Every name of an admitted right component has the other colour. -/
def RightSupported (classify : Name → Bool) (right : Multiset Name → Prop) : Prop :=
  ∀ inventory, right inventory → ∀ name ∈ inventory, classify name ≠ true

theorem classified_gradeZero {classify : Name → Bool}
    {left right : Multiset Name → Prop} (first : LeftSupported classify left)
    (second : RightSupported classify right) : GradeZero left right := by
  intro a b admittedA admittedB name memberA memberB
  exact second b admittedB name memberB (first a admittedA name memberA)

/-- Filtering recovers the actual supplied left half, not merely its support. -/
theorem leftPart_split {classify : Name → Bool}
    {left right : Multiset Name → Prop} (first : LeftSupported classify left)
    (second : RightSupported classify right) {a b : Multiset Name}
    (admittedA : left a) (admittedB : right b) :
    leftPart classify (a + b) = a := by
  rw [leftPart, Multiset.filter_add]
  have leftEqual : a.filter (fun name => classify name = true) = a :=
    Multiset.filter_eq_self.mpr (first a admittedA)
  have rightEqual : b.filter (fun name => classify name = true) = 0 :=
    Multiset.filter_eq_nil.mpr (second b admittedB)
  rw [leftEqual, rightEqual, Multiset.add_zero]

theorem rightPart_split {classify : Name → Bool}
    {left right : Multiset Name → Prop} (first : LeftSupported classify left)
    (second : RightSupported classify right) {a b : Multiset Name}
    (admittedA : left a) (admittedB : right b) :
    rightPart classify (a + b) = b := by
  rw [rightPart, Multiset.filter_add]
  have leftEqual : a.filter (fun name => classify name ≠ true) = 0 :=
    Multiset.filter_eq_nil.mpr (fun name member absent =>
      absent (first a admittedA name member))
  have rightEqual : b.filter (fun name => classify name ≠ true) = b :=
    Multiset.filter_eq_self.mpr (second b admittedB)
  rw [leftEqual, rightEqual, Multiset.zero_add]

/-- Independent composite membership is exactly membership of both computed
parts under the actual support discipline. -/
theorem composite_iff_parts {classify : Name → Bool}
    {left right : Multiset Name → Prop} (first : LeftSupported classify left)
    (second : RightSupported classify right) (inventory : Multiset Name) :
    Composite left right inventory ↔
      left (leftPart classify inventory) ∧ right (rightPart classify inventory) := by
  constructor
  · rintro ⟨a, b, admittedA, admittedB, rfl⟩
    rw [leftPart_split first second admittedA admittedB,
      rightPart_split first second admittedA admittedB]
    exact ⟨admittedA, admittedB⟩
  · rintro ⟨admittedA, admittedB⟩
    exact ⟨_, _, admittedA, admittedB, parts_add classify inventory⟩

end Mettapedia.Algebra.SupportSeparatedDecomposition
