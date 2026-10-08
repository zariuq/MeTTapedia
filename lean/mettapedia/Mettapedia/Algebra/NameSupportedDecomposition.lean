import Mettapedia.Algebra.SupportSeparatedDecomposition

/-!+# Name support and the detection of parallel factors

A name support on particles induces the name support of a complete parallel
inventory. Separation of names earns uniqueness of the particle inventories
when every admitted particle carries a name. This additional detection
condition matters: disjoint scope extensions with disjoint name supports can
still move an unnamed factor from one half to the other.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.NameSupportedDecomposition

open SupportSeparatedDecomposition

universe u v

variable {Particle : Type u} {Name : Type v}

/-- The actual names carried by an occurrence inventory. -/
def names (support : Particle → Set Name) (inventory : Multiset Particle) : Set Name :=
  {name | ∃ particle ∈ inventory, name ∈ support particle}

/-- Whole scope extensions are separated by their actual name supports. -/
def NameSeparated (support : Particle → Set Name)
    (left right : Multiset Particle → Prop) : Prop :=
  ∀ first second, left first → right second →
    Disjoint (names support first) (names support second)

/-- The name-support comparison must detect each admitted particle. -/
def NamesDetect (support : Particle → Set Name)
    (scope : Multiset Particle → Prop) : Prop :=
  ∀ inventory, scope inventory → ∀ particle ∈ inventory,
    ∃ name, name ∈ support particle

theorem particle_separation_of_name_separation
    {support : Particle → Set Name} {left right : Multiset Particle → Prop}
    (separated : NameSeparated support left right) (detected : NamesDetect support left) :
    GradeZero left right := by
  intro first second admittedFirst admittedSecond particle memberFirst memberSecond
  obtain ⟨name, carried⟩ := detected first admittedFirst particle memberFirst
  exact Set.disjoint_left.mp (separated first second admittedFirst admittedSecond)
    ⟨particle, memberFirst, carried⟩ ⟨particle, memberSecond, carried⟩

/-- Detection and whole-scope name separation determine complete halves,
including repeated particle occurrences. -/
theorem split_unique_of_name_separation [DecidableEq Particle]
    {support : Particle → Set Name} {left right : Multiset Particle → Prop}
    (separated : NameSeparated support left right) (detected : NamesDetect support left)
    {first second first' second' : Multiset Particle}
    (admittedFirst : left first) (admittedSecond : right second)
    (admittedFirst' : left first') (admittedSecond' : right second')
    (same : first + second = first' + second') :
    first = first' ∧ second = second' :=
  split_unique (particle_separation_of_name_separation separated detected)
    admittedFirst admittedSecond admittedFirst' admittedSecond' same

namespace UnnamedFactor

/-- Two named particles and one independent unnamed particle. -/
inductive Factor where
  | left
  | right
  | closed
  deriving DecidableEq

def support : Factor → Set Bool
  | .left => {false}
  | .right => {true}
  | .closed => ∅

def leftScope (inventory : Multiset Factor) : Prop :=
  inventory = {.left} ∨ inventory = {.left, .closed}

def rightScope (inventory : Multiset Factor) : Prop :=
  inventory = {.right} ∨ inventory = {.right, .closed}

theorem left_names {inventory : Multiset Factor} (admitted : leftScope inventory) :
    names support inventory = {false} := by
  rcases admitted with rfl | rfl <;> ext name <;> simp [names, support]

theorem right_names {inventory : Multiset Factor} (admitted : rightScope inventory) :
    names support inventory = {true} := by
  rcases admitted with rfl | rfl <;> ext name <;> simp [names, support]

theorem extensions_disjoint :
    Disjoint {inventory | leftScope inventory} {inventory | rightScope inventory} := by
  apply Set.disjoint_left.mpr
  intro inventory admittedFirst admittedSecond
  have same := (left_names admittedFirst).symm.trans (right_names admittedSecond)
  have impossible : (false : Bool) ∈ ({true} : Set Bool) := by
    rw [← same]
    exact Set.mem_singleton false
  simp at impossible

theorem name_supports_separated : NameSeparated support leftScope rightScope := by
  intro first second admittedFirst admittedSecond
  rw [left_names admittedFirst, right_names admittedSecond]
  exact Set.disjoint_singleton.mpr Bool.false_ne_true

theorem two_complete_splits :
    ({Factor.left} : Multiset Factor) + {.right, .closed} =
      {.left, .closed} + {.right} := by
  apply Multiset.ext.mpr
  intro factor
  simp only [Multiset.insert_eq_cons, Multiset.count_add,
    Multiset.count_cons, Multiset.count_singleton]
  omega

theorem left_halves_differ :
    ({Factor.left} : Multiset Factor) ≠ {.left, .closed} := by
  intro same
  have lengths := congrArg Multiset.card same
  simp at lengths

theorem unnamed_particle_not_detected : ¬ NamesDetect support leftScope := by
  intro detected
  obtain ⟨name, carried⟩ := detected {.left, .closed} (Or.inr rfl)
    .closed (by simp)
  exact carried

/-- Extension disjointness and grade-zero shared-name separation do not
prevent reassignment of an unnamed nonunit factor. -/
theorem name_separation_does_not_determine_halves :
    ∃ first second first' second' : Multiset Factor,
      leftScope first ∧ rightScope second ∧
      leftScope first' ∧ rightScope second' ∧
      first + second = first' + second' ∧ first ≠ first' :=
  ⟨{.left}, {.right, .closed}, {.left, .closed}, {.right},
    Or.inl rfl, Or.inr rfl, Or.inr rfl, Or.inl rfl,
    two_complete_splits, left_halves_differ⟩

end UnnamedFactor

end Mettapedia.Algebra.NameSupportedDecomposition
