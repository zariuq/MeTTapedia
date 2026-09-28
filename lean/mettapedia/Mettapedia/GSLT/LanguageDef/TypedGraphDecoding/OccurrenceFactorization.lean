import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.ProbabilityAlignment
import Mathlib.Data.List.Nodup

/-!
# Exact factorization of finite candidate occurrences

A candidate list records occurrences, while its two projected supports record
only side values. Equal cardinality does not make this list a Cartesian
product: one pair may be repeated while another is missing.

The executable checker below tests the two conditions that do suffice:
unique pairs and the full product cardinality. Its admitted lists contain
exactly one occurrence of each supported pair. For separable weights their
normalizer factors, and independent side sampling has exactly the original
pair law. A second result admits factorizable multiplicities without erasing
them: their factors must be included in the side weights.

This is a finite sampling contract. It does not establish independence from
clause syntax, eventual acceptance probabilities, or executable RNG refinement.
When several occurrences share a pair, pair sampling additionally needs a
conditional occurrence selection; choosing the first occurrence is not that
selection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.OccurrenceFactorization

open scoped BigOperators

noncomputable section

universe u v

variable {Left : Type u} {Right : Type v} [DecidableEq Left] [DecidableEq Right]

private theorem lawful_beq_decide {α : Type*} [DecidableEq α] [BEq α] [LawfulBEq α]
    (first second : α) : (first == second) = decide (first = second) := by
  apply Bool.eq_iff_iff.mpr
  simp

def leftSupport (candidates : List (Left × Right)) : Finset Left :=
  (candidates.map Prod.fst).toFinset

def rightSupport (candidates : List (Left × Right)) : Finset Right :=
  (candidates.map Prod.snd).toFinset

def productSupport (candidates : List (Left × Right)) : Finset (Left × Right) :=
  leftSupport candidates ×ˢ rightSupport candidates

theorem support_subset_product (candidates : List (Left × Right)) :
    candidates.toFinset ⊆ productSupport candidates := by
  intro pair present
  have member : pair ∈ candidates := List.mem_toFinset.mp present
  exact Finset.mem_product.mpr
    ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨pair, member, rfl⟩),
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨pair, member, rfl⟩)⟩

/-- A finite, executable admission check, including pair uniqueness. -/
def factorable (candidates : List (Left × Right)) : Bool :=
  decide candidates.Nodup &&
    decide (candidates.length =
      (leftSupport candidates).card * (rightSupport candidates).card)

theorem factorable_iff (candidates : List (Left × Right)) :
    factorable candidates = true ↔
      candidates.Nodup ∧ candidates.length =
        (leftSupport candidates).card * (rightSupport candidates).card := by
  simp [factorable]

theorem support_eq_product {candidates : List (Left × Right)}
    (unique : candidates.Nodup)
    (cardinality : candidates.length =
      (leftSupport candidates).card * (rightSupport candidates).card) :
    candidates.toFinset = productSupport candidates := by
  apply Finset.eq_of_subset_of_card_le (support_subset_product candidates)
  rw [List.toFinset_card_of_nodup unique]
  simpa [productSupport] using cardinality.ge

theorem admitted_pair_count {candidates : List (Left × Right)}
    (admitted : factorable candidates = true)
    {pair : Left × Right} (present : pair ∈ productSupport candidates) :
    candidates.count pair = 1 := by
  obtain ⟨unique, cardinality⟩ := (factorable_iff candidates).mp admitted
  exact List.count_eq_one_of_mem unique
    (List.mem_toFinset.mp ((support_eq_product unique cardinality).symm ▸ present))

/-- Every independently selected pair resolves to exactly one occurrence. -/
theorem admitted_pair_occurrence {candidates : List (Left × Right)}
    (admitted : factorable candidates = true)
    {pair : Left × Right} (present : pair ∈ productSupport candidates) :
    ∃! position : Fin candidates.length, candidates.get position = pair := by
  obtain ⟨unique, cardinality⟩ := (factorable_iff candidates).mp admitted
  have member : pair ∈ candidates := List.mem_toFinset.mp
    ((support_eq_product unique cardinality).symm ▸ present)
  obtain ⟨position, exactAt⟩ := List.mem_iff_get.mp member
  refine ⟨position, exactAt, ?_⟩
  intro other same
  exact unique.injective_get (same.trans exactAt.symm)

def normalizer (candidates : List (Left × Right)) (weight : Left × Right → ℝ) : ℝ :=
  (candidates.map weight).sum

def pairMass (candidates : List (Left × Right))
    (weight : Left × Right → ℝ) (pair : Left × Right) : ℝ :=
  candidates.count pair * weight pair

/-- Aggregate identical pairs with their occurrence multiplicity retained. -/
theorem normalizer_counted (candidates : List (Left × Right))
    (weight : Left × Right → ℝ) :
    normalizer candidates weight =
      ∑ pair ∈ productSupport candidates, pairMass candidates weight pair := by
  calc
    normalizer candidates weight =
        ∑ pair ∈ candidates.toFinset, pairMass candidates weight pair := by
          simpa only [normalizer, pairMass, nsmul_eq_mul,
            List.count_eq_countP, lawful_beq_decide] using
              (Finset.sum_list_map_count candidates weight)
    _ = ∑ pair ∈ productSupport candidates, pairMass candidates weight pair := by
      apply Finset.sum_subset (support_subset_product candidates)
      intro pair _ absent
      have missing : pair ∉ candidates := by simpa using absent
      simp [pairMass, List.count_eq_zero.mpr missing]

def pairProbability (candidates : List (Left × Right))
    (weight : Left × Right → ℝ) (pair : Left × Right) : ℝ :=
  pairMass candidates weight pair / normalizer candidates weight

theorem normalizer_nonnegative (candidates : List (Left × Right))
    (weight : Left × Right → ℝ) (nonnegative : ∀ pair, 0 ≤ weight pair) :
    0 ≤ normalizer candidates weight := by
  rw [normalizer_counted]
  apply Finset.sum_nonneg
  intro pair _
  exact mul_nonneg (Nat.cast_nonneg _) (nonnegative pair)

theorem pairProbability_nonnegative (candidates : List (Left × Right))
    (weight : Left × Right → ℝ) (nonnegative : ∀ pair, 0 ≤ weight pair)
    (pair : Left × Right) : 0 ≤ pairProbability candidates weight pair := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (nonnegative pair))
    (normalizer_nonnegative candidates weight nonnegative)

theorem pairProbability_normalized (candidates : List (Left × Right))
    (weight : Left × Right → ℝ) (nonzero : normalizer candidates weight ≠ 0) :
    ∑ pair ∈ productSupport candidates, pairProbability candidates weight pair = 1 := by
  simp only [pairProbability]
  rw [← Finset.sum_div]
  rw [← normalizer_counted]
  exact div_self nonzero

/-- The projected kernel has rank one when pair multiplicity itself factors.
This is broader than uniqueness and includes repeated equivalent occurrences.
It proves a marginal law; occurrence identity still needs conditional sampling. -/
theorem normalizer_of_count_factors (candidates : List (Left × Right))
    (leftCount : Left → Nat) (rightCount : Right → Nat)
    (leftWeight : Left → ℝ) (rightWeight : Right → ℝ)
    (counts : ∀ pair ∈ productSupport candidates,
      candidates.count pair = leftCount pair.1 * rightCount pair.2) :
    normalizer candidates (fun pair => leftWeight pair.1 * rightWeight pair.2) =
      (∑ left ∈ leftSupport candidates, leftCount left * leftWeight left) *
      (∑ right ∈ rightSupport candidates, rightCount right * rightWeight right) := by
  rw [normalizer_counted]
  calc
    (∑ pair ∈ productSupport candidates,
        pairMass candidates (fun pair => leftWeight pair.1 * rightWeight pair.2) pair) =
      ∑ pair ∈ productSupport candidates,
        (leftCount pair.1 * leftWeight pair.1) *
          (rightCount pair.2 * rightWeight pair.2) := by
            apply Finset.sum_congr rfl
            intro pair present
            simp only [pairMass, counts pair present, Nat.cast_mul]
            ring
    _ = _ := by
      rw [productSupport, Finset.sum_product, Finset.sum_mul_sum]

theorem pairProbability_of_count_factors (candidates : List (Left × Right))
    (leftCount : Left → Nat) (rightCount : Right → Nat)
    (leftWeight : Left → ℝ) (rightWeight : Right → ℝ)
    (counts : ∀ pair ∈ productSupport candidates,
      candidates.count pair = leftCount pair.1 * rightCount pair.2)
    {pair : Left × Right} (present : pair ∈ productSupport candidates) :
    pairProbability candidates (fun pair => leftWeight pair.1 * rightWeight pair.2) pair =
      (leftCount pair.1 * leftWeight pair.1 /
        ∑ left ∈ leftSupport candidates, leftCount left * leftWeight left) *
      (rightCount pair.2 * rightWeight pair.2 /
        ∑ right ∈ rightSupport candidates, rightCount right * rightWeight right) := by
  rw [pairProbability, normalizer_of_count_factors candidates leftCount rightCount
    leftWeight rightWeight counts]
  simp only [pairMass, counts pair present, Nat.cast_mul]
  ring

/-- The executable complete-unique check licenses independent side weights. -/
theorem admitted_pairProbability {candidates : List (Left × Right)}
    (admitted : factorable candidates = true)
    (leftWeight : Left → ℝ) (rightWeight : Right → ℝ)
    {pair : Left × Right} (present : pair ∈ productSupport candidates) :
    pairProbability candidates (fun pair => leftWeight pair.1 * rightWeight pair.2) pair =
      (leftWeight pair.1 / ∑ left ∈ leftSupport candidates, leftWeight left) *
      (rightWeight pair.2 / ∑ right ∈ rightSupport candidates, rightWeight right) := by
  simpa using pairProbability_of_count_factors candidates (fun _ => 1) (fun _ => 1)
    leftWeight rightWeight
    (fun selected selectedPresent => by simpa using admitted_pair_count admitted selectedPresent)
    present

/-- The original lottery is over candidate positions, even when their side
values coincide. This expression is defined at one actual occurrence. -/
def occurrenceProbability (candidates : List (Left × Right))
    (weight : Left × Right → ℝ) (position : Fin candidates.length) : ℝ :=
  weight (candidates.get position) / normalizer candidates weight

/-- For pair-dependent weights, sample the pair with its aggregate mass and
then sample uniformly among its occurrences. This recovers every original
occurrence probability; selecting the first occurrence does not. -/
theorem pair_then_occurrence_exact (candidates : List (Left × Right))
    (weight : Left × Right → ℝ) (position : Fin candidates.length) :
    pairProbability candidates weight (candidates.get position) *
        (1 / (candidates.count (candidates.get position) : ℝ)) =
      occurrenceProbability candidates weight position := by
  have countPositive : 0 < candidates.count (candidates.get position) :=
    List.count_pos_iff.mpr (List.get_mem ..)
  have countNonzero : (candidates.count (candidates.get position) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt countPositive
  by_cases totalZero : normalizer candidates weight = 0
  · simp [pairProbability, occurrenceProbability, totalZero]
  · simp only [pairProbability, pairMass, occurrenceProbability]
    field_simp [countNonzero, totalZero]

namespace Controls

def complete : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

def duplicateMissing : List (Bool × Bool) :=
  [(false, false), (false, false), (true, false), (true, true)]

theorem complete_admitted : factorable complete = true := by decide

theorem equal_cardinality_is_insufficient :
    duplicateMissing.length =
        (leftSupport duplicateMissing).card * (rightSupport duplicateMissing).card ∧
      (false, true) ∈ productSupport duplicateMissing ∧
      (false, true) ∉ duplicateMissing ∧
      factorable duplicateMissing = false := by decide

theorem missing_pair_has_no_lookup :
    duplicateMissing.find? (fun pair => pair == (false, true)) = none := by decide

theorem actual_multiplicity_changes_law :
    pairProbability duplicateMissing (fun _ => 1) (false, false) = 1 / 2 ∧
      pairProbability duplicateMissing (fun _ => 1) (false, true) = 0 := by
  norm_num [pairProbability, pairMass, normalizer, duplicateMissing]

/-- Each side has two locally supported alternatives, but independent
uniform sides would put one quarter of the mass on an absent pair. -/
theorem local_uniform_sides_invent_mass :
    ProbabilityAlignment.locallyMasked (leftSupport duplicateMissing) (fun _ => 1) false *
      ProbabilityAlignment.locallyMasked (rightSupport duplicateMissing) (fun _ => 1) true =
        1 / 4 ∧
    pairProbability duplicateMissing (fun _ => 1) (false, true) = 0 := by
  norm_num [ProbabilityAlignment.locallyMasked, ProbabilityAlignment.legalMass,
    leftSupport, rightSupport, duplicateMissing, pairProbability, pairMass, normalizer]

theorem picking_first_drops_an_occurrence :
    duplicateMissing[0]? = some (false, false) ∧
      duplicateMissing[1]? = some (false, false) ∧
      duplicateMissing.findIdx (fun pair => pair == (false, false)) = 0 := by decide

end Controls

end

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.OccurrenceFactorization
