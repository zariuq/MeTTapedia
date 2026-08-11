import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Tactic

/-!
# Persistent spaces and linear channels are different protocols

The MeTTa-calculus manuscript intentionally uses one located-comprehension
shape for several operations associated with a space.  This module isolates
the semantic distinction that syntax alone cannot express:

* a persistent observation finds an occurrence and leaves it available;
* a linear take finds an occurrence and consumes exactly that occurrence.

The distinction is occurrence-sensitive.  It therefore uses finite
multisets rather than support sets.  Positive and negative controls show both
how the protocols are related and why they cannot be identified.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceChannelBoundary

universe u

variable {Atom : Type u}

/-- The finite occurrence carrier shared by the two small protocol models. -/
abbrev Store (Atom : Type u) := Multiset Atom

/-- Persistent observation: the requested occurrence exists and the store is
unchanged. -/
inductive PersistentRead (atom : Atom) : Store Atom → Store Atom → Prop where
  | found {store : Store Atom} (present : atom ∈ store) :
      PersistentRead atom store store

/-- Linear receive/take: one requested occurrence is removed. -/
inductive LinearTake (atom : Atom) : Store Atom → Store Atom → Prop where
  | found (rest : Store Atom) : LinearTake atom (atom ::ₘ rest) rest

/-- Sequential composition of state relations. -/
def Sequential {State : Type u}
    (first second : State → State → Prop) (source target : State) : Prop :=
  ∃ middle, first source middle ∧ second middle target

theorem persistentRead_iff {atom : Atom} {source target : Store Atom} :
    PersistentRead atom source target ↔ atom ∈ source ∧ target = source := by
  constructor
  · intro step
    cases step with
    | found present => exact ⟨present, rfl⟩
  · rintro ⟨present, rfl⟩
    exact .found present

/-- A persistent observation preserves every aspect of the occurrence
carrier, not merely support membership. -/
theorem persistentRead_preserves
    {atom : Atom} {source target : Store Atom}
    (step : PersistentRead atom source target) : target = source :=
  (persistentRead_iff.mp step).2

/-- A linear take changes the occurrence carrier. -/
theorem linearTake_changes_store
    {atom : Atom} {source target : Store Atom}
    (step : LinearTake atom source target) : source ≠ target := by
  intro equal
  have cardEquation : source.card = target.card + 1 := by
    cases step with
    | found rest => simp
  rw [equal] at cardEquation
  omega

/-- A linear take removes exactly one occurrence. -/
theorem linearTake_card
    {atom : Atom} {source target : Store Atom}
    (step : LinearTake atom source target) :
    source.card = target.card + 1 := by
  cases step with
  | found rest => simp

/-- Positive space control: one stored occurrence can be observed twice. -/
theorem persistentRead_singleton_twice (atom : Atom) :
    Sequential (PersistentRead atom) (PersistentRead atom)
      ({atom} : Store Atom) {atom} := by
  refine ⟨{atom}, ?_, ?_⟩
  · exact .found (by simp)
  · exact .found (by simp)

/-- Positive channel control: two stored occurrences support two takes. -/
theorem linearTake_two_occurrences (atom : Atom) :
    Sequential (LinearTake atom) (LinearTake atom)
      (atom ::ₘ atom ::ₘ 0 : Store Atom) 0 := by
  exact ⟨atom ::ₘ 0, .found (atom ::ₘ 0), .found 0⟩

/-- Negative channel control: one occurrence cannot be taken twice. -/
theorem linearTake_singleton_not_twice (atom : Atom) :
    ¬ ∃ target,
      Sequential (LinearTake atom) (LinearTake atom)
        ({atom} : Store Atom) target := by
  rintro ⟨target, middle, first, second⟩
  have firstCard := linearTake_card first
  have secondCard := linearTake_card second
  simp at firstCard secondCard
  rw [firstCard] at secondCard
  simp at secondCard

/-- The two protocols are not the same relation.  The singleton observation
is a separating example: reading preserves it, taking cannot. -/
theorem persistentRead_ne_linearTake (atom : Atom) :
    PersistentRead atom ≠ LinearTake atom := by
  intro equal
  have read : PersistentRead atom ({atom} : Store Atom) {atom} :=
    .found (by simp)
  rw [equal] at read
  exact (linearTake_changes_store read) rfl

/-- Consume-and-republish is the channel protocol that realizes a persistent
space read.  Replication is therefore an explicit residual behavior, not an
identity between read and take. -/
def TakeThenRepublish (atom : Atom) (source target : Store Atom) : Prop :=
  ∃ afterTake,
    LinearTake atom source afterTake ∧ target = atom ::ₘ afterTake

theorem persistentRead_iff_takeThenRepublish
    {atom : Atom} {source target : Store Atom} :
    PersistentRead atom source target ↔
      TakeThenRepublish atom source target := by
  constructor
  · intro read
    obtain ⟨present, rfl⟩ := persistentRead_iff.mp read
    obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem present
    exact ⟨rest, .found rest, rfl⟩
  · rintro ⟨afterTake, take, rfl⟩
    cases take with
    | found rest => exact .found (by simp)

/-- A two-party channel rendezvous has a genuinely linear footprint: both
guard occurrences can be consumed. -/
theorem two_party_linear_footprint (left right : Atom) :
    Sequential (LinearTake left) (LinearTake right)
      (left ::ₘ right ::ₘ 0 : Store Atom) 0 := by
  exact ⟨right ::ₘ 0, .found (right ::ₘ 0), .found 0⟩

/-- Persistent observations cannot implement the consuming footprint of a
two-party rendezvous without an additional update protocol. -/
theorem two_persistent_reads_do_not_consume (left right : Atom) :
    ¬ Sequential (PersistentRead left) (PersistentRead right)
      (left ::ₘ right ::ₘ 0 : Store Atom) 0 := by
  rintro ⟨middle, first, second⟩
  have middleEq := persistentRead_preserves first
  have targetEq := persistentRead_preserves second
  rw [middleEq] at targetEq
  have cards := congrArg Multiset.card targetEq
  simp at cards

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceChannelBoundary
