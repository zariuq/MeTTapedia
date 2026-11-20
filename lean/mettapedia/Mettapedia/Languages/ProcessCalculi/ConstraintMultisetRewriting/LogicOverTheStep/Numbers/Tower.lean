import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.NumberLens

/-!
# The numeric tower as types of the value lens, and its closure table

The carrier is the number lens's model of stored numbers (`NumberLens.Stored`: an integer, or a
fraction that may happen to be whole), read through its value (`NumberLens.value`).

## The algebra

* **What is invariant**: the value, under every re-storing (`Restoring`: a change of storage that
  keeps every value; `toFrac` is one).
* **The value law** (`valueLaw_iff`, `valueLaw_iff_concepts`): an observer family factors through
  the value exactly when it cannot split two storages of one value, exactly when each of its types
  is a type of the value lens. The storage lens breaks it (`storageLens_breaks_valueLaw`).
* **What composes**: operations that respect a lens compose (`respects_comp`); every operation
  computed from the values respects the value lens (`lift_respects`).
* **What is decided by a finite test**: membership in the whole and the natural values
  (`mem_wholes_iff`, `mem_naturals_iff`, with `DecidablePred` instances) and equality of values. No
  claim about cost is made here.

## The tower

The naturals, the whole numbers and the rationals are the stored numbers whose value is a natural
number, an integer, or anything (`Naturals`, `Wholes`, `Rationals`). Each is a type of the value
lens (`naturals_isConcept`, `wholes_isConcept`, `rationals_isConcept`), so a number belongs to it
however it is stored. The inclusions are strict (`tower_strict`): `-1` is whole and not natural,
`1/2` is rational and not whole.

Control: **being stored as an integer is not a type** (`intStored_not_value_type`), and not even a
type of the storage lens (`intStored_not_storage_type`), since that lens cannot split the stored
integer `0` from the fraction `0`.

## The closure table (`closure_table`)

For each operation on values and each class of the tower, whether all arguments in the class give
a result in the class. Partial operations (`divV`, `quotV`, `remV`) answer only on their domain and
are asked about their answers (`PreservesPartial`).

| operation | naturals | whole numbers | rationals |
|---|---|---|---|
| `+` | yes | yes | yes |
| `-` | no: `1 - 2` | yes | yes |
| `*` | yes | yes | yes |
| exact division, divisor not zero | no: `1 / 2` | no: `1 / 2` | yes |
| quotient of whole values, toward zero | yes | yes | yes; defined exactly on whole values (`quotV_domain`) |
| remainder of whole values | yes | yes | yes; same domain |
| truncated subtraction `max (a - b) 0` | yes | yes | yes |
| comparison | a truth value (`leV_natCast`, `leV_intCast`) | | |

The rationals column holds for every operation because every value is rational; the content of
that column is the domain: the quotient and the remainder decline a value that is not whole.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Tower

open Set
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion
open Distinctions.ObserverConcepts Distinctions.NumberLens

/-! ## What is invariant -/

/-- **A re-storing**: a change of storage that keeps every value. -/
def Restoring (ρ : Stored → Stored) : Prop := ∀ x, value (ρ x) = value x

/-- Storing every number as a fraction. -/
def toFrac (x : Stored) : Stored := .frac (value x)

theorem toFrac_restoring : Restoring toFrac := fun _ => rfl

/-- Re-storings compose. -/
theorem restoring_comp {ρ ρ' : Stored → Stored} (first : Restoring ρ) (second : Restoring ρ') :
    Restoring (ρ' ∘ ρ) := fun x => (second (ρ x)).trans (first x)

/-- Indistinguishable to the value lens is equal in value. -/
theorem indist_value_iff (x y : Stored) : Indist valueLens x y ↔ value x = value y :=
  ⟨fun same => same (), fun equal _ => equal⟩

/-- **A re-storing keeps every type of the value lens.** -/
theorem restoring_mem {ρ : Stored → Stored} (restoring : Restoring ρ) {S : Set Stored}
    (concept : IsConcept (Apart valueLens) S) {x : Stored} (inS : x ∈ S) : ρ x ∈ S :=
  (isConcept_iff_saturated S).mp concept x inS (ρ x) ((indist_value_iff _ _).mpr (restoring x).symm)

/-! ## The value law -/

/-- **The value law for an observer family**: every reading factors through the value. -/
def ValueLaw {ι R : Type*} (read : ι → Stored → R) : Prop :=
  ∀ i, ∃ g : ℚ → R, ∀ x, read i x = g (value x)

/-- **The value law holds exactly when no reading splits two storages of one value.** -/
theorem valueLaw_iff {ι R : Type*} (read : ι → Stored → R) :
    ValueLaw read ↔ ∀ x y, value x = value y → Indist read x y := by
  constructor
  · intro law x y equal i
    obtain ⟨g, factors⟩ := law i
    rw [factors x, factors y, equal]
  · intro unsplit i
    refine ⟨fun q => read i (.frac q), fun x => ?_⟩
    exact unsplit x (.frac (value x)) rfl i

/-- **The value law holds exactly when every type of the family is a type of the value lens.** -/
theorem valueLaw_iff_concepts {ι R : Type*} (read : ι → Stored → R) :
    ValueLaw read ↔ ∀ S, IsConcept (Apart read) S → IsConcept (Apart valueLens) S := by
  rw [valueLaw_iff, concepts_subset_iff]
  exact ⟨fun unsplit x y same => unsplit x y ((indist_value_iff x y).mp same),
    fun refines x y equal => refines x y ((indist_value_iff x y).mpr equal)⟩

/-- **Control: the storage lens breaks the value law** at the two `5`s. -/
theorem storageLens_breaks_valueLaw : ¬ ValueLaw storageLens := by
  rw [valueLaw_iff]
  intro unsplit
  exact apart_iff_not_indist.mp apart_storage_five
    (unsplit five fiveFrac (value_five.trans value_fiveFrac.symm))

theorem valueLens_valueLaw : ValueLaw valueLens := fun _ => ⟨id, fun _ => rfl⟩

/-! ## What composes -/

/-- **Operations that respect lenses compose.** -/
theorem respects_comp {U V W ι κ μ P Q R : Type*} {readU : ι → U → P} {readV : κ → V → Q}
    {readW : μ → W → R} {f : U → V} {g : V → W} (first : Respects readU readV f)
    (second : Respects readV readW g) : Respects readU readW (g ∘ f) :=
  fun a b same => second (f a) (f b) (first a b same)

/-- An operation computed from the values, stored as a fraction. -/
def lift (f : ℚ → ℚ → ℚ) (p : Stored × Stored) : Stored := .frac (f (value p.1) (value p.2))

/-- **Every operation computed from the values respects the value lens.** -/
theorem lift_respects (f : ℚ → ℚ → ℚ) : Respects (pairRead valueLens valueLens) valueLens (lift f) := by
  rw [respects_pair_iff]
  intro a a' b b' first second _
  show f (value a) (value b) = f (value a') (value b')
  rw [show value a = value a' from first (), show value b = value b' from second ()]

/-! ## The tower -/

/-- The rationals that are natural numbers. -/
def natValues : Set ℚ := range (Nat.cast : ℕ → ℚ)

/-- The rationals that are integers. -/
def intValues : Set ℚ := range (Int.cast : ℤ → ℚ)

/-- **The naturals**: the stored numbers whose value is a natural number, however stored. -/
def Naturals : Set Stored := value ⁻¹' natValues

/-- **The whole numbers**: the stored numbers whose value is an integer, however stored. -/
def Wholes : Set Stored := value ⁻¹' intValues

/-- **The rationals**: every stored number. -/
def Rationals : Set Stored := univ

theorem naturals_isConcept : IsConcept (Apart valueLens) Naturals :=
  isConcept_preimage (read := valueLens) () natValues

theorem wholes_isConcept : IsConcept (Apart valueLens) Wholes :=
  isConcept_preimage (read := valueLens) () intValues

theorem rationals_isConcept : IsConcept (Apart valueLens) Rationals :=
  (isConcept_iff_saturated _).mpr fun _ _ _ _ => mem_univ _

/-- The cast of a non-negative integer is a natural value. -/
theorem natValues_of_nonneg {z : ℤ} (nonneg : 0 ≤ z) : (z : ℚ) ∈ natValues :=
  ⟨z.toNat, by rw [← Int.cast_natCast, Int.toNat_of_nonneg nonneg]⟩

theorem natValues_subset : natValues ⊆ intValues := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, Int.cast_natCast n⟩

theorem naturals_subset_wholes : Naturals ⊆ Wholes := fun _ member => natValues_subset member

theorem wholes_subset_rationals : Wholes ⊆ Rationals := fun _ _ => mem_univ _

theorem value_int (n : ℤ) : value (.int n) = n := rfl

theorem value_frac (q : ℚ) : value (.frac q) = q := rfl

/-- **The tower is strict**: `-1` is whole and not natural; `1/2` is rational and not whole. -/
theorem tower_strict :
    (Stored.int (-1) ∈ Wholes ∧ Stored.int (-1) ∉ Naturals) ∧
      (Stored.frac (1 / 2) ∈ Rationals ∧ Stored.frac (1 / 2) ∉ Wholes) := by
  refine ⟨⟨⟨-1, rfl⟩, ?_⟩, mem_univ _, ?_⟩
  · rintro ⟨n, equal⟩
    have nonneg : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    rw [equal, value_int] at nonneg
    norm_num at nonneg
  · rintro ⟨z, equal⟩
    rw [value_frac] at equal
    have doubled : ((2 * z : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
      push_cast
      rw [equal]
      norm_num
    have exact : 2 * z = 1 := by exact_mod_cast doubled
    omega

/-- **Membership of the whole numbers is a test of the denominator.** -/
theorem mem_wholes_iff (x : Stored) : x ∈ Wholes ↔ (value x).den = 1 := by
  constructor
  · rintro ⟨z, equal⟩
    rw [← equal]
    exact Rat.den_intCast z
  · intro whole
    exact ⟨(value x).num, Rat.coe_int_num_of_den_eq_one whole⟩

/-- **Membership of the naturals is a test of the denominator and the sign of the numerator.** -/
theorem mem_naturals_iff (x : Stored) : x ∈ Naturals ↔ (value x).den = 1 ∧ 0 ≤ (value x).num := by
  constructor
  · rintro ⟨n, equal⟩
    rw [← equal]
    exact ⟨Rat.den_natCast n, by rw [Rat.num_natCast]; exact Int.natCast_nonneg n⟩
  · rintro ⟨whole, nonneg⟩
    have member := natValues_of_nonneg nonneg
    rw [Rat.coe_int_num_of_den_eq_one whole] at member
    exact member

instance : DecidablePred (· ∈ Wholes) := fun x => decidable_of_iff _ (mem_wholes_iff x).symm

instance : DecidablePred (· ∈ Naturals) := fun x => decidable_of_iff _ (mem_naturals_iff x).symm

/-! ## Control: storage is not a type -/

/-- The numbers stored as integers. -/
def IntStored : Set Stored := {x | ∃ n, x = .int n}

/-- **Control: being stored as an integer is not a type of the value lens.** -/
theorem intStored_not_value_type : ¬ IsConcept (Apart valueLens) IntStored := by
  intro concept
  obtain ⟨n, same⟩ := (five_same_concepts IntStored concept).mp ⟨5, rfl⟩
  simp [fiveFrac] at same

/-- **Control: nor of the storage lens**, which cannot split the stored integer `0` from the
fraction `0`. -/
theorem intStored_not_storage_type : ¬ IsConcept (Apart storageLens) IntStored := by
  intro concept
  obtain ⟨n, same⟩ := (isConcept_iff_saturated IntStored).mp concept (.int 0) ⟨0, rfl⟩ (.frac 0)
    zero_not_split
  cases same

/-! ## The closure table -/

/-- A total operation keeps a class. -/
def Preserves (f : ℚ → ℚ → ℚ) (C : Set ℚ) : Prop := ∀ a ∈ C, ∀ b ∈ C, f a b ∈ C

/-- A partial operation keeps a class: every answer on arguments in the class is in it. -/
def PreservesPartial (f : ℚ → ℚ → Option ℚ) (C : Set ℚ) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ r, f a b = some r → r ∈ C

/-- Exact division, defined when the divisor is not zero. -/
def divV (a b : ℚ) : Option ℚ := if b = 0 then none else some (a / b)

/-- The quotient of whole values, truncating toward zero, defined when both values are whole and
the divisor is not zero. -/
def quotV (a b : ℚ) : Option ℚ :=
  if a.den = 1 ∧ b.den = 1 ∧ b ≠ 0 then some ((a.num.tdiv b.num : ℤ) : ℚ) else none

/-- The remainder of whole values, with the sign of the dividend, on the same domain. -/
def remV (a b : ℚ) : Option ℚ :=
  if a.den = 1 ∧ b.den = 1 ∧ b ≠ 0 then some ((a.num.tmod b.num : ℤ) : ℚ) else none

/-- Truncated subtraction. -/
def tsubV (a b : ℚ) : ℚ := max (a - b) 0

/-- Comparison. -/
def leV (a b : ℚ) : Bool := decide (a ≤ b)

theorem preserves_univ (f : ℚ → ℚ → ℚ) : Preserves f univ := fun _ _ _ _ => mem_univ _

theorem preservesPartial_univ (f : ℚ → ℚ → Option ℚ) : PreservesPartial f univ :=
  fun _ _ _ _ _ _ => mem_univ _

theorem one_mem_natValues : (1 : ℚ) ∈ natValues := ⟨1, Nat.cast_one⟩

theorem two_mem_natValues : (2 : ℚ) ∈ natValues := ⟨2, by norm_num⟩

theorem add_naturals : Preserves (· + ·) natValues := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  exact ⟨m + n, Nat.cast_add m n⟩

theorem add_wholes : Preserves (· + ·) intValues := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  exact ⟨m + n, Int.cast_add m n⟩

theorem mul_naturals : Preserves (· * ·) natValues := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  exact ⟨m * n, Nat.cast_mul m n⟩

theorem mul_wholes : Preserves (· * ·) intValues := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  exact ⟨m * n, Int.cast_mul m n⟩

theorem sub_wholes : Preserves (· - ·) intValues := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  exact ⟨m - n, Int.cast_sub m n⟩

/-- **Subtraction leaves the naturals**: `1 - 2`. -/
theorem sub_not_naturals : ¬ Preserves (· - ·) natValues := by
  intro keeps
  obtain ⟨n, equal⟩ := keeps 1 one_mem_natValues 2 two_mem_natValues
  have nonneg : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  rw [equal] at nonneg
  norm_num at nonneg

theorem divV_one_two : divV 1 2 = some (1 / 2) := by
  simp [divV]

theorem half_not_whole : (1 / 2 : ℚ) ∉ intValues := by
  rintro ⟨z, equal⟩
  have doubled : ((2 * z : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
    push_cast
    rw [equal]
    norm_num
  have exact : 2 * z = 1 := by exact_mod_cast doubled
  omega

/-- **Exact division leaves the whole numbers**: `1 / 2`. -/
theorem divV_not_wholes : ¬ PreservesPartial divV intValues :=
  fun keeps => half_not_whole (keeps 1 ⟨1, Int.cast_one⟩ 2 ⟨2, by norm_num⟩ _ divV_one_two)

/-- **And the naturals.** -/
theorem divV_not_naturals : ¬ PreservesPartial divV natValues :=
  fun keeps => half_not_whole (natValues_subset (keeps 1 one_mem_natValues 2 two_mem_natValues _
    divV_one_two))

/-- **The quotient is defined exactly on whole values with a nonzero divisor.** -/
theorem quotV_domain (a b : ℚ) : (∃ r, quotV a b = some r) ↔ a.den = 1 ∧ b.den = 1 ∧ b ≠ 0 := by
  unfold quotV
  split_ifs with domain
  · exact ⟨fun _ => domain, fun _ => ⟨_, rfl⟩⟩
  · exact ⟨fun ⟨_, equal⟩ => (by cases equal), fun inside => absurd inside domain⟩

theorem quotV_wholes : PreservesPartial quotV intValues := by
  intro a _ b _ r answer
  unfold quotV at answer
  split_ifs at answer
  cases answer
  exact ⟨_, rfl⟩

theorem remV_wholes : PreservesPartial remV intValues := by
  intro a _ b _ r answer
  unfold remV at answer
  split_ifs at answer
  cases answer
  exact ⟨_, rfl⟩

theorem quotV_naturals : PreservesPartial quotV natValues := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ r answer
  unfold quotV at answer
  split_ifs at answer
  cases answer
  rw [Rat.num_natCast, Rat.num_natCast]
  exact natValues_of_nonneg (Int.tdiv_nonneg (Int.natCast_nonneg m) (Int.natCast_nonneg n))

theorem remV_naturals : PreservesPartial remV natValues := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ r answer
  unfold remV at answer
  split_ifs at answer
  cases answer
  rw [Rat.num_natCast, Rat.num_natCast]
  exact natValues_of_nonneg (Int.tmod_nonneg _ (Int.natCast_nonneg m))

/-- **The quotient declines a value that is not whole**: `1/2` divided by `1`. -/
theorem quotV_half : quotV (1 / 2) 1 = none := by
  have notWhole : (1 / 2 : ℚ).den ≠ 1 := by
    intro whole
    exact half_not_whole ⟨_, Rat.coe_int_num_of_den_eq_one whole⟩
  unfold quotV
  rw [if_neg (fun inside => notWhole inside.1)]

theorem tsubV_naturals : Preserves tsubV natValues := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  refine ⟨m - n, ?_⟩
  show ((m - n : ℕ) : ℚ) = max ((m : ℚ) - n) 0
  by_cases le : n ≤ m
  · rw [Nat.cast_sub le, max_eq_left (sub_nonneg.mpr (Nat.cast_le.mpr le))]
  · have less : (m : ℚ) < n := Nat.cast_lt.mpr (by omega)
    rw [Nat.sub_eq_zero_of_le (show m ≤ n by omega), Nat.cast_zero,
      max_eq_right (show (m : ℚ) - n ≤ 0 by linarith)]

theorem tsubV_wholes : Preserves tsubV intValues := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  refine ⟨max (m - n) 0, ?_⟩
  show ((max (m - n) 0 : ℤ) : ℚ) = max ((m : ℚ) - n) 0
  rw [Int.cast_max, Int.cast_sub, Int.cast_zero]

/-- **Comparison of naturals is comparison of their values.** -/
theorem leV_natCast (m n : ℕ) : leV m n = decide (m ≤ n) := by
  simp [leV]

/-- **Comparison of integers is comparison of their values.** -/
theorem leV_intCast (m n : ℤ) : leV m n = decide (m ≤ n) := by
  simp [leV]

/-- **The closure table**: every cell is a theorem or a counterexample. -/
theorem closure_table :
    (Preserves (· + ·) natValues ∧ Preserves (· + ·) intValues ∧ Preserves (· + ·) univ) ∧
    (¬ Preserves (· - ·) natValues ∧ Preserves (· - ·) intValues ∧ Preserves (· - ·) univ) ∧
    (Preserves (· * ·) natValues ∧ Preserves (· * ·) intValues ∧ Preserves (· * ·) univ) ∧
    (¬ PreservesPartial divV natValues ∧ ¬ PreservesPartial divV intValues ∧
      PreservesPartial divV univ) ∧
    (PreservesPartial quotV natValues ∧ PreservesPartial quotV intValues ∧
      PreservesPartial quotV univ) ∧
    (PreservesPartial remV natValues ∧ PreservesPartial remV intValues ∧
      PreservesPartial remV univ) ∧
    (Preserves tsubV natValues ∧ Preserves tsubV intValues ∧ Preserves tsubV univ) :=
  ⟨⟨add_naturals, add_wholes, preserves_univ _⟩, ⟨sub_not_naturals, sub_wholes, preserves_univ _⟩,
    ⟨mul_naturals, mul_wholes, preserves_univ _⟩,
    ⟨divV_not_naturals, divV_not_wholes, preservesPartial_univ _⟩,
    ⟨quotV_naturals, quotV_wholes, preservesPartial_univ _⟩,
    ⟨remV_naturals, remV_wholes, preservesPartial_univ _⟩,
    ⟨tsubV_naturals, tsubV_wholes, preserves_univ _⟩⟩

/-- **On stored numbers**: an operation computed from the values keeps a type of the tower exactly
when it keeps the class of values. -/
theorem lift_preserves_iff (f : ℚ → ℚ → ℚ) (C : Set ℚ) :
    (∀ x ∈ value ⁻¹' C, ∀ y ∈ value ⁻¹' C, lift f (x, y) ∈ value ⁻¹' C) ↔ Preserves f C := by
  constructor
  · intro keeps a inA b inB
    exact keeps (.frac a) inA (.frac b) inB
  · intro keeps x inX y inY
    exact keeps _ inX _ inY

#print axioms toFrac_restoring
#print axioms restoring_comp
#print axioms restoring_mem
#print axioms valueLaw_iff
#print axioms valueLaw_iff_concepts
#print axioms storageLens_breaks_valueLaw
#print axioms valueLens_valueLaw
#print axioms respects_comp
#print axioms lift_respects
#print axioms naturals_isConcept
#print axioms wholes_isConcept
#print axioms rationals_isConcept
#print axioms naturals_subset_wholes
#print axioms wholes_subset_rationals
#print axioms tower_strict
#print axioms mem_wholes_iff
#print axioms mem_naturals_iff
#print axioms intStored_not_value_type
#print axioms intStored_not_storage_type
#print axioms sub_not_naturals
#print axioms divV_not_wholes
#print axioms divV_not_naturals
#print axioms quotV_domain
#print axioms quotV_naturals
#print axioms remV_naturals
#print axioms quotV_half
#print axioms tsubV_naturals
#print axioms tsubV_wholes
#print axioms leV_natCast
#print axioms leV_intCast
#print axioms closure_table
#print axioms lift_preserves_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Tower
