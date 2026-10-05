import Mettapedia.SetTheory.Profiles.Principles

/-!
# Unordered pairs

The power set of the power set of the empty set contains the empty set and the
power set of the empty set. Separation retains those elements of it for which
membership of the empty set is decided, and replacement sends the elements that
contain the empty set to one value and the elements that do not to the other.
The image is the unordered pair. No choice operator and no excluded middle are
used.

This is the intuitionistic form of the construction recorded by the Saarland
set-theory development: separate `Power (Power Empty)` to the elements `X` for
which `Empty ∈ X ∨ Empty ∉ X`, then replace. Zermelo observed in 1930 that
replacement yields pairs in the classical theory; Suppes and Paulson's
Isabelle-ZF give that classical argument. The separation step is what keeps
the argument intuitionistic.

Megalodon's pair is the same image, with the sending function written by the
choice operator and the index still cut down by that separation. Excluded
middle decides the membership for every element of the power set, so the
separation cut is not required and the choice operator is not used.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles

universe u

variable {S : Type u} {mem : Mem S}

private theorem pairing_of_decided {e p1 index : S}
    (notMem : ∀ z, ¬ mem z e)
    (powerEmpty : ∀ z, mem z p1 ↔ ∀ w, mem w z → mem w e)
    (rep : HasReplacement mem)
    (emptyIn : mem e index) (powerIn : mem p1 index)
    (decided : ∀ z, mem z index → mem e z ∨ ¬ mem e z) :
    HasPairing mem := by
  intro y z
  let R : S → S → Prop := fun X w => (mem e X ∧ w = y) ∨ (¬ mem e X ∧ w = z)
  have functional : ∀ X, mem X index → Functional (R X) := by
    intro X hX
    cases decided X hX with
    | inl hin =>
      refine ⟨y, Or.inl ⟨hin, rfl⟩, ?_⟩
      intro w hw
      cases hw with
      | inl h => exact h.2
      | inr h => exact (h.1 hin).elim
    | inr hout =>
      refine ⟨z, Or.inr ⟨hout, rfl⟩, ?_⟩
      intro w hw
      cases hw with
      | inl h => exact (hout h.1).elim
      | inr h => exact h.2
  obtain ⟨p, hp⟩ := rep index R functional
  have emptyMem : mem e p1 := empty_mem_power_empty notMem powerEmpty
  refine ⟨p, ?_⟩
  intro w
  constructor
  · intro hw
    obtain ⟨X, _, hR⟩ := (hp w).1 hw
    cases hR with
    | inl h => exact Or.inl h.2
    | inr h => exact Or.inr h.2
  · intro hw
    cases hw with
    | inl heq =>
      exact heq.symm ▸ (hp y).2 ⟨p1, powerIn, Or.inl ⟨emptyMem, rfl⟩⟩
    | inr heq =>
      exact heq.symm ▸ (hp z).2 ⟨e, emptyIn, Or.inr ⟨notMem e, rfl⟩⟩

/-- Empty set, power set, separation and replacement yield unordered pairs.
The index is the separated subset of the power set of the power set of the
empty set on which membership of the empty set is decided. -/
theorem unorderedPair (emp : HasEmpty mem) (pow : HasPower mem) (sep : HasSeparation mem)
    (rep : HasReplacement mem) : HasPairing mem := by
  obtain ⟨e, notMem⟩ := emp
  obtain ⟨p1, powerEmpty⟩ := pow e
  obtain ⟨p2, powerPower⟩ := pow p1
  obtain ⟨index, hIndex⟩ := sep p2 (fun X => mem e X ∨ ¬ mem e X)
  have emptyMem : mem e p1 := empty_mem_power_empty notMem powerEmpty
  have powerInPower : mem p1 p2 := mem_power_self powerPower
  have emptyInPower : mem e p2 := mem_power_of_empty notMem powerPower
  exact pairing_of_decided notMem powerEmpty rep
    ((hIndex e).2 ⟨emptyInPower, Or.inr (notMem e)⟩)
    ((hIndex p1).2 ⟨powerInPower, Or.inl emptyMem⟩)
    (fun z hz => ((hIndex z).1 hz).2)

/-- Megalodon's pair, with the index cut down by separation. On that index the
choice operator sends an element containing the empty set to the first value
and an element not containing it to the second. Replacement collects the image. -/
theorem unorderedPair_of_choice (emp : HasEmpty mem) (pow : HasPower mem)
    (sep : HasSeparation mem) (rep : HasReplacement mem) (eps : (S → Prop) → S)
    (choice : ChoiceLaw eps) : HasPairing mem := by
  obtain ⟨e, notMem⟩ := emp
  obtain ⟨p1, powerEmpty⟩ := pow e
  obtain ⟨p2, powerPower⟩ := pow p1
  obtain ⟨index, hIndex⟩ := sep p2 (fun X => mem e X ∨ ¬ mem e X)
  have emptyMem : mem e p1 := empty_mem_power_empty notMem powerEmpty
  have powerIn : mem p1 index :=
    (hIndex p1).2 ⟨mem_power_self powerPower, Or.inl emptyMem⟩
  have emptyIn : mem e index :=
    (hIndex e).2 ⟨mem_power_of_empty notMem powerPower, Or.inr (notMem e)⟩
  intro y z
  let cond : S → S := fun X =>
    eps (fun w => (mem e X ∧ w = y) ∨ (¬ mem e X ∧ w = z))
  have spec : ∀ X, mem X index →
      (mem e X ∧ cond X = y) ∨ (¬ mem e X ∧ cond X = z) := by
    intro X hX
    cases ((hIndex X).1 hX).2 with
    | inl hin =>
      exact choice (fun w => (mem e X ∧ w = y) ∨ (¬ mem e X ∧ w = z)) y
        (Or.inl ⟨hin, rfl⟩)
    | inr hout =>
      exact choice (fun w => (mem e X ∧ w = y) ∨ (¬ mem e X ∧ w = z)) z
        (Or.inr ⟨hout, rfl⟩)
  let R : S → S → Prop := fun X w => w = cond X
  have functional : ∀ X, mem X index → Functional (R X) := by
    intro X _
    refine ⟨cond X, rfl, ?_⟩
    intro w hw
    exact hw
  obtain ⟨p, hp⟩ := rep index R functional
  have condPower : cond p1 = y := by
    cases spec p1 powerIn with
    | inl h => exact h.2
    | inr h => exact (h.1 emptyMem).elim
  have condEmpty : cond e = z := by
    cases spec e emptyIn with
    | inl h => exact (notMem e h.1).elim
    | inr h => exact h.2
  refine ⟨p, ?_⟩
  intro w
  constructor
  · intro hw
    obtain ⟨X, hX, hR⟩ := (hp w).1 hw
    cases spec X hX with
    | inl h => exact Or.inl (hR.trans h.2)
    | inr h => exact Or.inr (hR.trans h.2)
  · intro hw
    cases hw with
    | inl heq =>
      exact heq.symm ▸ (hp y).2 ⟨p1, powerIn, condPower.symm⟩
    | inr heq =>
      exact heq.symm ▸ (hp z).2 ⟨e, emptyIn, condEmpty.symm⟩

/-- Excluded middle decides membership of the empty set on the whole power set,
so replacement forms the unordered pair with no choice operator and no
separation. -/
theorem unorderedPair_of_excludedMiddle (emp : HasEmpty mem) (pow : HasPower mem)
    (rep : HasReplacement mem) (em : ∀ p : Prop, p ∨ ¬ p) : HasPairing mem := by
  obtain ⟨e, notMem⟩ := emp
  obtain ⟨p1, powerEmpty⟩ := pow e
  obtain ⟨p2, powerPower⟩ := pow p1
  have emptyMem : mem e p1 := empty_mem_power_empty notMem powerEmpty
  exact pairing_of_decided notMem powerEmpty rep
    (mem_power_of_empty notMem powerPower)
    (mem_power_self powerPower)
    (fun z _ => em (mem e z))

end Mettapedia.SetTheory.Profiles
