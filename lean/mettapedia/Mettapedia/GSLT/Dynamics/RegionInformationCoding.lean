import Mettapedia.GSLT.Dynamics.RegionObservations
import Mettapedia.GSLT.Dynamics.RegionModeInformation
import Mettapedia.InformationTheory.FiniteInterfaceCoding
import Mettapedia.Logic.CTLContextualInformation

/-!
# Observer-relative finite information budgets

The generic future-observation quotient determines the least fixed binary
width whenever its semantic classes are finite. Syntax and concrete source
states need not be finite. Refining observers can only increase this budget.

This is an abstract interface-code result. It does not select a native layout
or compute a shortest program. A finite-label mode counterexample shows that
even a fixed two-label universe needs unbounded information when arbitrary
future additions must remain answerable.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RegionInformationCoding

open RegionObservations
open Mettapedia.InformationTheory.FiniteInterfaceCoding

universe u v w

noncomputable def requiredBits {State : Type u} (family : Family.{u, v, w} State) : Nat :=
  Nat.clog 2 (Nat.card family.Classes)

theorem sufficient_bits_iff {State : Type u} (family : Family.{u, v, w} State)
    [Finite family.Classes] (bits : Nat) :
    (∃ code : State → Word bits, family.Sufficient code) ↔ requiredBits family ≤ bits :=
  exists_sufficient_word_iff family.setoid bits

noncomputable def leastCode {State : Type u} (family : Family.{u, v, w} State)
    [Finite family.Classes] : State → Word (requiredBits family) := quotientSummary family.setoid

theorem leastCode_exact {State : Type u} (family : Family.{u, v, w} State)
    [Finite family.Classes] : family.Exact (leastCode family) := quotientSummary_exact family.setoid

/-- A finite sufficient summary forces a finite observation quotient even
when there are infinitely many source states or formula spellings. -/
theorem finite_classes_of_summary {State : Type u} (family : Family.{u, v, w} State)
    {Code : Type*} [Finite Code] (code : State → Code) (sufficient : family.Sufficient code) :
    Finite family.Classes :=
  Finite.of_injective (representatives family.setoid code)
    (representatives_injective family.setoid code sufficient)

theorem refinement_increases_budget {State : Type u} {coarse fine : Family.{u, v, w} State}
    [Finite fine.Classes] (refinement : Refinement coarse fine) :
    requiredBits coarse ≤ requiredBits fine := by
  apply Nat.clog_mono_right 2
  exact Nat.card_le_card_of_surjective _ refinement.classes_surjective

namespace Existence

open RegionObservations.Controls

theorem classes_finite : Finite existence.Classes :=
  finite_classes_of_summary existence (fun count => decide (0 < count))
    (fun left right => (existence_exact left right).mp)

theorem classes_count : Nat.card existence.Classes = 2 := by
  let := classes_finite
  have upper := summary_card_bound existence.setoid (fun count => decide (0 < count))
    (fun left right => (existence_exact left right).mp)
  let witness : Bool → existence.Classes := fun bit => existence.classOf (if bit then 1 else 0)
  have injective : Function.Injective witness := by
    intro first second same
    have observed := (existence.classOf_eq_iff _ _).mp same (show existence.Question from (0 : Nat))
    change decide (0 < (if first then 1 else 0) + 0) = decide (0 < (if second then 1 else 0) + 0) at observed
    cases first <;> cases second <;> simp_all only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
      lt_self_iff_false, decide_false, Nat.zero_lt_one, decide_true]
  have lower := Nat.card_le_card_of_injective witness injective
  change Nat.card existence.Classes ≤ Nat.card Bool at upper
  change Nat.card Bool ≤ Nat.card existence.Classes at lower
  norm_num only [Nat.card_eq_fintype_card, Fintype.card_bool] at lower upper
  omega

theorem exact_one_bit_budget : requiredBits existence = 1 := by
  rw [requiredBits, classes_count]
  decide +kernel

theorem zero_bits_cannot_retain_presence :
    ¬∃ code : Nat → Word 0, existence.Sufficient code := by
  let := classes_finite
  rw [sufficient_bits_iff, exact_one_bit_budget]
  omega

end Existence

namespace Mode

open Mettapedia.Machines.ModeAggregation.FiniteInformation

def growing (count : Nat) : Counts 1 := ![0, count]

/-- Fixed labels do not imply a bounded code. Every distinct count in this
family has a distinguishing future addition, even if today's winner agrees. -/
theorem no_finite_summary {Code : Type} [Finite Code] (summary : Counts 1 → Code) :
    ¬(RegionObservations.Mode.futures 1).Sufficient summary := by
  intro sufficient
  have injective : Function.Injective (fun count => summary (growing count)) := by
    intro left right same
    have futures := sufficient (growing left) (growing right) same
    have summaryEqual := (sameFuture_iff_summary (growing left) (growing right)).mp futures
    have difference := congrArg (fun result : Summary 1 => result.differences 1) summaryEqual
    simpa [summarize, differences, growing] using difference
  exact not_injective_infinite_finite _ injective

theorem no_fixed_word (bits : Nat) :
    ¬∃ code : Counts 1 → Word bits, (RegionObservations.Mode.futures 1).Sufficient code := by
  rintro ⟨code, sufficient⟩
  exact no_finite_summary code sufficient

def boundedFutures (bound : Nat) : Family (Fin (bound + 1)) where
  Question := Counts 1
  Answer _ := Option (Label 1)
  read added count := mode (growing count.val + added)

theorem bounded_equivalent_iff (bound : Nat) (left right : Fin (bound + 1)) :
    (boundedFutures bound).Equivalent left right ↔ left = right := by
  constructor
  · intro futures
    have summaryEqual := (sameFuture_iff_summary (growing left.val) (growing right.val)).mp futures
    have difference := congrArg (fun result : Summary 1 => result.differences 1) summaryEqual
    apply Fin.ext
    simpa [summarize, differences, growing] using difference
  · rintro rfl
    intro _
    rfl

theorem bounded_classes_count (bound : Nat) : Nat.card (boundedFutures bound).Classes = bound + 1 := by
  have injective : Function.Injective (boundedFutures bound).classOf := by
    intro left right same
    exact (bounded_equivalent_iff bound left right).mp (((boundedFutures bound).classOf_eq_iff left right).mp same)
  have onto : Function.Surjective (boundedFutures bound).classOf := by
    intro cls
    induction cls using Quotient.inductionOn with
    | h state => exact ⟨state, rfl⟩
  have equal := Nat.card_congr (Equiv.ofBijective _ ⟨injective, onto⟩)
  simpa using equal.symm

/-- Already this bounded two-label family requires one distinguishable code
per possible count, despite having only two present-day winning labels. -/
theorem bounded_required_bits (bound : Nat) :
    requiredBits (boundedFutures bound) = Nat.clog 2 (bound + 1) := by
  rw [requiredBits, bounded_classes_count]

theorem bounded_word_admission (bound bits : Nat) :
    (∃ code : Fin (bound + 1) → Word bits, (boundedFutures bound).Sufficient code) ↔
      bound + 1 ≤ 2 ^ bits := by
  rw [sufficient_bits_iff, bounded_required_bits, Nat.clog_le_iff_le_pow (by decide : 1 < 2)]

end Mode

namespace CTL

open Mettapedia.Logic.CTLFormula Mettapedia.Logic.CTLContextualInformation

variable {State Label : Type} [Fintype State]

theorem budget_bounded_by_valid_states (domain : Set State) (relation : State → State → Prop)
    (atoms : Label → Set State) :
    requiredBits (observers domain relation atoms) ≤ domain.toFinite.toFinset.card := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  exact classes_bound_valid_domain domain relation atoms

theorem enough_bits (domain : Set State) (relation : State → State → Prop) (atoms : Label → Set State) :
    ∃ code : Formula Label → Word domain.toFinite.toFinset.card,
      (observers domain relation atoms).Sufficient code := by
  let := classes_finite domain relation atoms
  exact (sufficient_bits_iff _ _).mpr (budget_bounded_by_valid_states domain relation atoms)

def allPredicates : Finset State → Set State := fun states => states

omit [Fintype State] in
theorem all_predicates_have_distinct_classes (relation : State → State → Prop) :
    Function.Injective (fun states : Finset State =>
      (observers Set.univ relation allPredicates).classOf (.atom states)) := by
  intro first second same
  have equivalent := (observers Set.univ relation allPredicates).classOf_eq_iff _ _ |>.mp same
  ext state
  have observed := equivalent (.hole, state)
  simpa [observers, Context.plug, meaning, allPredicates] using Iff.of_eq observed

/-- If every state predicate is available as an atomic query, all subsets
are observable and the upper bound is attained. Restricted atom families
may admit strictly smaller budgets. -/
theorem full_predicate_budget (relation : State → State → Prop) :
    requiredBits (observers Set.univ relation (allPredicates : Finset State → Set State)) = Fintype.card State := by
  let := classes_finite Set.univ relation (allPredicates : Finset State → Set State)
  have lower := Nat.card_le_card_of_injective _ (all_predicates_have_distinct_classes relation)
  have upper := classes_bound Set.univ relation (allPredicates : Finset State → Set State)
  have count : Nat.card (observers Set.univ relation (allPredicates : Finset State → Set State)).Classes =
      2 ^ Fintype.card State := by
    have lower' : 2 ^ Fintype.card State ≤ Nat.card
        (observers Set.univ relation (allPredicates : Finset State → Set State)).Classes := by
      simpa [Nat.card_eq_fintype_card] using lower
    exact Nat.le_antisymm upper lower'
  rw [requiredBits, count, Nat.clog_pow 2 _ (by decide)]

end CTL

end Mettapedia.GSLT.Dynamics.RegionInformationCoding
