import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Basic

/-!
# Controls for graded execution, evidence algebra, choice and finite observation

Each negative result stands next to the positive law it bounds.

## Folding and probability

Three unit-weight events with outcomes `false, false, true` and two unit-weight representatives
`false, true` have the same possible outcomes and different masses
(`deduplicating_changes_probability`): a reachability-preserving quotient does not preserve
probability. A quotient that keeps multiplicities keeps every mass (`perm_preserves_mass`), and so
does lumping into representatives that carry the aggregated weight of their class
(`lumping_preserves_probability`).

## The split quantale

Intersection on the powerset of a point preserves joins (`primal_tensor_preserves_joins`). In the
opposite order the same product does not absorb the bottom (`dual_tensor_fails_bottom_absorption`),
so the order-dual coordinate of a split product is not a quantale with the unchanged product. The
product in the **knowledge order**, coordinatewise intersection on pairs, absorbs the bottom and
distributes over joins (`tensor_bot`, `tensor_sup`). A tolerance threshold is not an equivalence
(`threshold_nontransitive`); tolerance zero is equality (`within_zero_iff`).

## Recorded choice and symmetry

Recording a deterministic representative does not make it equivariant under the swap
(`recorded_choice_still_breaks_swap`); the enumerated set of both choices is invariant
(`enumerated_choices_swap_invariant`).

## Finite observation

The stream tail needs input depth `n + 1` for output depth `n` (`shift_modulus`) and does not
preserve depth (`shift_not_same_depth`): finite lookahead is broader than same-depth contraction.
Pointwise maps do preserve depth (`pointwise_same_depth`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CoreControls

/-! ## Folding and probability -/

/-- The mass of an outcome among unit-weight events. -/
noncomputable def uniformMass (events : List Bool) (outcome : Bool) : ℝ :=
  (events.count outcome : ℝ) / (events.length : ℝ)

/-- **Deduplication changes probability**: the same possible outcomes, different masses. -/
theorem deduplicating_changes_probability :
    (∀ b, b ∈ ([false, false, true] : List Bool) ↔ b ∈ ([false, true] : List Bool)) ∧
    uniformMass [false, false, true] false = 2 / 3 ∧
    uniformMass [false, true] false = 1 / 2 ∧
    uniformMass [false, false, true] false ≠ uniformMass [false, true] false := by
  constructor
  · intro b; cases b <;> decide
  · norm_num [uniformMass]

/-- **Keeping multiplicities keeps every mass.** -/
theorem perm_preserves_mass {events events' : List Bool} (same : events.Perm events') (outcome : Bool) :
    uniformMass events outcome = uniformMass events' outcome := by
  unfold uniformMass
  rw [same.count_eq outcome, same.length_eq]

/-- The mass of an outcome among weighted representatives. -/
noncomputable def weightedMass (weighted : List (Bool × ℕ)) (outcome : Bool) : ℝ :=
  (((weighted.filter fun w => w.1 == outcome).map Prod.snd).sum : ℝ) / ((weighted.map Prod.snd).sum : ℝ)

/-- **Lumping with aggregated weights keeps probability**: the representatives `false` with weight
`2` and `true` with weight `1` give the masses of the three events. -/
theorem lumping_preserves_probability (outcome : Bool) :
    weightedMass [(false, 2), (true, 1)] outcome = uniformMass [false, false, true] outcome := by
  cases outcome <;> norm_num [weightedMass, uniformMass]

/-! ## The split quantale -/

/-- Intersection on the powerset is the familiar commutative unital quantale product. -/
theorem primal_tensor_preserves_joins (s : Set Unit) (family : Set (Set Unit)) :
    s ∩ ⋃₀ family = ⋃ t ∈ family, s ∩ t := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_sUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨inside, t, member, tx⟩
    exact ⟨t, member, inside, tx⟩
  · rintro ⟨t, member, inside, tx⟩
    exact ⟨inside, t, member, tx⟩

/-- **The same product in the opposite order fails the empty-join law.** -/
theorem dual_tensor_fails_bottom_absorption :
    (∅ : Set Unit) ∩ (⊥ : OrderDual (Set Unit)) ≠ (⊥ : OrderDual (Set Unit)) := by
  change (∅ : Set Unit) ∩ Set.univ ≠ Set.univ
  intro same
  have point := congrArg (fun s : Set Unit => () ∈ s) same
  simp at point

/-- The product of the knowledge order: coordinatewise intersection. -/
def tensor (x y : Set Unit × Set Unit) : Set Unit × Set Unit := (x.1 ∩ y.1, x.2 ∩ y.2)

/-- **The knowledge-order product absorbs the bottom.** -/
theorem tensor_bot (x : Set Unit × Set Unit) : tensor x ⊥ = ⊥ :=
  Prod.ext (by simp [tensor]) (by simp [tensor])

/-- **The knowledge-order product distributes over joins.** -/
theorem tensor_sup (x y z : Set Unit × Set Unit) : tensor x (y ⊔ z) = tensor x y ⊔ tensor x z :=
  Prod.ext (Set.inter_union_distrib_left _ _ _) (Set.inter_union_distrib_left _ _ _)

/-- Two numbers within a tolerance of each other. -/
def Within (tolerance x y : ℕ) : Prop := x ≤ y + tolerance ∧ y ≤ x + tolerance

/-- **A tolerance threshold is not transitive.** -/
theorem threshold_nontransitive : Within 1 0 1 ∧ Within 1 1 2 ∧ ¬ Within 1 0 2 := by
  unfold Within
  decide

/-- **Tolerance zero is equality.** -/
theorem within_zero_iff (x y : ℕ) : Within 0 x y ↔ x = y := by
  unfold Within
  omega

/-! ## Recorded choice and symmetry -/

/-- **Keeping a record does not make a deterministic representative choice equivariant.** -/
theorem recorded_choice_still_breaks_swap (choice : Bool) :
    (choice, [choice]) ≠ (!choice, [!choice]) := by
  cases choice <;> decide

/-- **The enumerated set of both choices is invariant under the swap.** -/
theorem enumerated_choices_swap_invariant :
    (({false, true} : Finset Bool).image fun b => !b) = {false, true} := by
  decide

/-! ## Finite observation -/

/-- Two streams agree below a depth. -/
def Below (n : ℕ) (s t : ℕ → Bool) : Prop := ∀ i, i < n → s i = t i

/-- The stream tail. -/
def shift (s : ℕ → Bool) : ℕ → Bool := fun i => s (i + 1)

/-- **The tail needs one more input level per output level.** -/
theorem shift_modulus (n : ℕ) (s t : ℕ → Bool) (h : Below (n + 1) s t) :
    Below n (shift s) (shift t) := by
  intro i short
  exact h (i + 1) (Nat.succ_lt_succ short)

/-- **The tail does not preserve depth.** -/
theorem shift_not_same_depth :
    ∃ s t : ℕ → Bool, Below 1 s t ∧ ¬ Below 1 (shift s) (shift t) := by
  refine ⟨fun _ => false, fun i => decide (i = 1), ?_, ?_⟩
  · intro i short
    have zero : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ short)
    simp [zero]
  · intro agrees
    have point := agrees 0 (by decide)
    simp [shift] at point

/-- **Pointwise maps preserve depth.** -/
theorem pointwise_same_depth (g : Bool → Bool) (n : ℕ) (s t : ℕ → Bool) (h : Below n s t) :
    Below n (fun i => g (s i)) (fun i => g (t i)) := by
  intro i short
  exact congrArg g (h i short)

#print axioms deduplicating_changes_probability
#print axioms perm_preserves_mass
#print axioms lumping_preserves_probability
#print axioms primal_tensor_preserves_joins
#print axioms dual_tensor_fails_bottom_absorption
#print axioms tensor_bot
#print axioms tensor_sup
#print axioms threshold_nontransitive
#print axioms within_zero_iff
#print axioms recorded_choice_still_breaks_swap
#print axioms enumerated_choices_swap_invariant
#print axioms shift_modulus
#print axioms shift_not_same_depth
#print axioms pointwise_same_depth

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CoreControls
