import Mettapedia.TypeTheory.MaterialSets.Hypersets.Operations

/-!
# Unordered pairs from the other set operations

`PairingFreeOperations` collects a propositional membership with extensionality, the empty set,
power sets and separation, and no pairing. Two ways to obtain `{a, b}` from them are compared.

**The classical route.** Classically, `𝒫 𝒫 ∅ = {∅, 𝒫 ∅}`, and `{a, b}` is the image of `𝒫 𝒫 ∅`
under `z ↦ if ∅ ∈ z then b else a`. The classification of the members of `𝒫 𝒫 ∅` that this needs
is exactly excluded middle (`classification_iff_em`): separating `𝒫 ∅` by a proposition `p`
yields a member that is `∅` exactly when `¬ p` and `𝒫 ∅` exactly when `p`. In the hypersets it is
equivalent to excluded middle for Lean's propositions (`HSet.classification_iff_em`).

**Through description.** The members of `𝒫 𝒫 ∅` equal to `∅` or to `𝒫 ∅` form a set with two
decidably distinct members (`mem_two`). On it the relation `(z = ∅ ∧ w = a) ∨ (z = 𝒫 ∅ ∧ w = b)`
is functional without any case split, so a unique-description operator turns it into a function,
and replacement gives `{a, b}` (`exists_pair_of_description`). No excluded middle is used.

So pairing is definable from description, and the classical definition needs excluded middle; a
theory with neither states pairing as a law.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets

universe u

/-- Extensional propositional membership with the empty set, power sets and separation. -/
structure PairingFreeOperations (S : Type u) where
  /-- Membership. -/
  mem : S → S → Prop
  /-- Extensionality. -/
  ext : ∀ {x y : S}, (∀ z, mem z x ↔ mem z y) → x = y
  /-- The empty set. -/
  empty : S
  notMem_empty : ∀ z, ¬ mem z empty
  /-- The power set. -/
  power : S → S
  mem_power : ∀ {x y : S}, mem y (power x) ↔ ∀ z, mem z y → mem z x
  /-- Separation. -/
  sep : (S → Prop) → S → S
  mem_sep : ∀ {P : S → Prop} {x z : S}, mem z (sep P x) ↔ mem z x ∧ P z

namespace PairingFreeOperations

variable {S : Type u} (O : PairingFreeOperations S)

/-- `1 = 𝒫 ∅`. -/
def one : S :=
  O.power O.empty

theorem mem_one {w : S} : O.mem w O.one ↔ w = O.empty := by
  rw [one, O.mem_power]
  exact ⟨fun h => O.ext fun z => ⟨fun hz => (O.notMem_empty z (h z hz)).elim,
      fun hz => (O.notMem_empty z hz).elim⟩,
    fun e z hz => (O.notMem_empty z (e ▸ hz)).elim⟩

theorem empty_mem_one : O.mem O.empty O.one :=
  O.mem_one.mpr rfl

theorem empty_ne_one : O.empty ≠ O.one := fun e =>
  O.notMem_empty O.empty (e ▸ O.empty_mem_one)

/-- Every member of `𝒫 𝒫 ∅` is `∅` or `𝒫 ∅`. -/
def Classification : Prop :=
  ∀ z, O.mem z (O.power O.one) → z = O.empty ∨ z = O.one

/-- The classification of the members of `𝒫 𝒫 ∅` is excluded middle. -/
theorem classification_iff_em : O.Classification ↔ ∀ p : Prop, p ∨ ¬ p := by
  constructor
  · intro h p
    have hz : O.mem (O.sep (fun _ => p) O.one) (O.power O.one) :=
      O.mem_power.mpr fun _ hw => (O.mem_sep.mp hw).1
    rcases h _ hz with e | e
    · right
      intro hp
      have hmem : O.mem O.empty (O.sep (fun _ => p) O.one) :=
        O.mem_sep.mpr ⟨O.empty_mem_one, hp⟩
      rw [e] at hmem
      exact O.notMem_empty _ hmem
    · left
      have hmem : O.mem O.empty (O.sep (fun _ => p) O.one) := by
        rw [e]
        exact O.empty_mem_one
      exact (O.mem_sep.mp hmem).2
  · intro em z hz
    have sub : ∀ w, O.mem w z → w = O.empty := fun w hw => O.mem_one.mp (O.mem_power.mp hz w hw)
    rcases em (O.mem O.empty z) with h | h
    · right
      exact O.ext fun w => ⟨fun hw => O.mem_one.mpr (sub w hw),
        fun hw => (O.mem_one.mp hw) ▸ h⟩
    · left
      exact O.ext fun w => ⟨fun hw => (h ((sub w hw) ▸ hw)).elim,
        fun hw => (O.notMem_empty w hw).elim⟩

/-- The members of `𝒫 𝒫 ∅` that are `∅` or `𝒫 ∅`. -/
def two : S :=
  O.sep (fun z => z = O.empty ∨ z = O.one) (O.power O.one)

theorem mem_two {z : S} : O.mem z O.two ↔ z = O.empty ∨ z = O.one := by
  rw [two, O.mem_sep]
  refine ⟨And.right, fun h => ⟨O.mem_power.mpr fun w hw => ?_, h⟩⟩
  rcases h with rfl | rfl
  · exact (O.notMem_empty w hw).elim
  · exact hw

/-- **Pairing from description.** With replacement over functions and a unique-description
operator, every two sets have an unordered pair. No excluded middle is used. -/
theorem exists_pair_of_description (repl : S → (S → S) → S)
    (mem_repl : ∀ {x : S} {f : S → S} {y : S}, O.mem y (repl x f) ↔ ∃ z, O.mem z x ∧ f z = y)
    (desc : (S → Prop) → S) (desc_spec : ∀ P : S → Prop, (∃! x, P x) → P (desc P)) (a b : S) :
    ∃ p, ∀ z, O.mem z p ↔ z = a ∨ z = b := by
  let R : S → S → Prop := fun z w => (z = O.empty ∧ w = a) ∨ (z = O.one ∧ w = b)
  let f : S → S := fun z => desc (R z)
  have at_empty : f O.empty = a := by
    have unique : ∃! w, R O.empty w :=
      ⟨a, Or.inl ⟨rfl, rfl⟩, fun w hw => hw.elim And.right fun h => (O.empty_ne_one h.1).elim⟩
    exact (desc_spec _ unique).elim And.right fun h => (O.empty_ne_one h.1).elim
  have at_one : f O.one = b := by
    have unique : ∃! w, R O.one w :=
      ⟨b, Or.inr ⟨rfl, rfl⟩, fun w hw => hw.elim (fun h => (O.empty_ne_one h.1.symm).elim)
        And.right⟩
    exact (desc_spec _ unique).elim (fun h => (O.empty_ne_one h.1.symm).elim) And.right
  refine ⟨repl O.two f, fun y => mem_repl.trans ⟨?_, ?_⟩⟩
  · rintro ⟨z, hz, rfl⟩
    rcases O.mem_two.mp hz with rfl | rfl
    · exact Or.inl at_empty
    · exact Or.inr at_one
  · rintro (rfl | rfl)
    · exact ⟨O.empty, O.mem_two.mpr (Or.inl rfl), at_empty⟩
    · exact ⟨O.one, O.mem_two.mpr (Or.inr rfl), at_one⟩

end PairingFreeOperations

namespace Hypersets.HSet

/-- The hypersets with their empty set, power sets and separation. -/
def pairingFreeOperations : PairingFreeOperations HSet.{u} where
  mem := fun x y : HSet.{u} => x ∈ y
  ext := HSet.ext
  empty := ∅
  notMem_empty := notMem_empty
  power := powerset
  mem_power := mem_powerset
  sep := HSet.sep
  mem_sep := mem_sep

/-- In the hypersets, `𝒫 𝒫 ∅ = {∅, 𝒫 ∅}` as a classification of members is excluded middle for
Lean's propositions. -/
theorem classification_iff_em :
    pairingFreeOperations.{u}.Classification ↔ ∀ p : Prop, p ∨ ¬ p :=
  pairingFreeOperations.classification_iff_em

/-- The hypotheses of `exists_pair_of_description` hold in the hypersets, with replacement through
`Presentation.choice` and description through `Classical.epsilon`. -/
theorem exists_pair_of_description_choice (a b : HSet.{u}) :
    ∃ p : HSet.{u}, ∀ z, z ∈ p ↔ z = a ∨ z = b :=
  have : Nonempty HSet.{u} := ⟨∅⟩
  pairingFreeOperations.exists_pair_of_description
    (fun x f => image Presentation.choice x fun c => f c.1)
    (fun {_ _ _} => mem_image.trans
      ⟨fun ⟨c, e⟩ => ⟨c.1, c.2, e⟩, fun ⟨z, hz, e⟩ => ⟨⟨z, hz⟩, e⟩⟩)
    Classical.epsilon (fun _ h => Classical.epsilon_spec h.exists) a b

end Hypersets.HSet

end Mettapedia.TypeTheory.MaterialSets
