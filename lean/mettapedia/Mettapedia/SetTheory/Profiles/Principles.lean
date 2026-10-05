/-!
# Membership structures

A set profile is a carrier with a membership relation. Lean equality is the
equality of the carrier, so it substitutes. Each set principle is a proposition
about that relation. Nothing here chooses a set theory.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles

universe u

/-- Membership of elements of a carrier. -/
abbrev Mem (S : Type u) := S → S → Prop

variable {S : Type u} (mem : Mem S)

/-- Sets with the same members are equal. -/
def Extensional : Prop :=
  ∀ x y, (∀ z, mem z x ↔ mem z y) → x = y

/-- Some set has no members. -/
def HasEmpty : Prop :=
  ∃ e, ∀ z, ¬ mem z e

/-- Every set and every predicate determine a subset. -/
def HasSeparation : Prop :=
  ∀ (a : S) (P : S → Prop), ∃ b, ∀ z, mem z b ↔ mem z a ∧ P z

/-- Any two elements form an unordered pair. -/
def HasPairing : Prop :=
  ∀ x y, ∃ p, ∀ z, mem z p ↔ z = x ∨ z = y

/-- Every set has a power set. -/
def HasPower : Prop :=
  ∀ a, ∃ p, ∀ z, mem z p ↔ ∀ w, mem w z → mem w a

/-- Every set has a union. -/
def HasUnion : Prop :=
  ∀ a, ∃ u, ∀ z, mem z u ↔ ∃ y, mem y a ∧ mem z y

/-- `R x` holds of exactly one value. -/
def Functional (R : S → Prop) : Prop :=
  ∃ y, R y ∧ ∀ y', R y' → y' = y

/-- The image of a set under a functional relation is a set. -/
def HasReplacement : Prop :=
  ∀ (a : S) (R : S → S → Prop),
    (∀ x, mem x a → Functional (R x)) →
      ∃ b, ∀ y, mem y b ↔ ∃ x, mem x a ∧ R x y

/-- A property that passes from the members of a set to the set holds of every set. -/
def HasMemInduction : Prop :=
  ∀ (P : S → Prop), (∀ x, (∀ y, mem y x → P y) → P x) → ∀ x, P x

/-- The law of a global choice operator: a predicate true of a set is true of the chosen set. -/
def ChoiceLaw (eps : (S → Prop) → S) : Prop :=
  ∀ (P : S → Prop) (x : S), P x → P (eps P)

/-- A Quine atom is a set equal to its own singleton. -/
def HasQuineAtom : Prop :=
  ∃ q, ∀ z, mem z q ↔ z = q

variable {mem}

/-- The empty set belongs to the power set of any set. -/
theorem mem_power_of_empty {e a p : S} (he : ∀ z, ¬ mem z e)
    (hp : ∀ z, mem z p ↔ ∀ w, mem w z → mem w a) : mem e p :=
  (hp e).2 (fun w hw => (he w hw).elim)

/-- A set belongs to its own power set. -/
theorem mem_power_self {a p : S}
    (hp : ∀ z, mem z p ↔ ∀ w, mem w z → mem w a) : mem a p :=
  (hp a).2 (fun _ hw => hw)

/-- The empty set belongs to the power set of the empty set. -/
theorem empty_mem_power_empty {e p : S} (he : ∀ z, ¬ mem z e)
    (hp : ∀ z, mem z p ↔ ∀ w, mem w z → mem w e) : mem e p :=
  mem_power_of_empty (mem := mem) he hp

/-- The empty set is distinct from the power set of the empty set. -/
theorem empty_ne_power_empty {e p : S} (he : ∀ z, ¬ mem z e) (hep : mem e p) : e ≠ p := by
  intro h
  exact he e (h.symm ▸ hep)

end Mettapedia.SetTheory.Profiles
