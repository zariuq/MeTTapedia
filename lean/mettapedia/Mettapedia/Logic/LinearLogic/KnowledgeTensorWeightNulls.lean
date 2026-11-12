import Mettapedia.Logic.LinearLogic.KnowledgeTensorWeightChance
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.LinearCombination

/-!
# Two nulls of absence

Knowledge is a set of admissible completions; refining knowledge shrinks the set. Every fact has a
label at every completion. "No fact with a forbidden label" then has two readings.

* `KnownAbsent`: at every admissible completion, no fact has a forbidden label.
* `NotKnownPresent`: no fact has a forbidden label at every admissible completion.

They are different nulls.

* `knownAbsent_refines`, `knownAbsent_shrinks`: known absence survives refinement of knowledge
  and removal of facts. Those are exactly the stabilities a check of the step must have
  (`CheckedSystem.check_mono` for knowledge, the frame for facts).
* `notKnownPresent_does_not_refine`: not being known present does not survive refinement, so it
  is not a check of the step. `undetermined_separates`: a fact whose label the knowledge leaves
  open separates the two nulls. `notKnownPresent_of_knownAbsent`, `knownAbsent_iff_of_determined`:
  over consistent knowledge known absence is the stronger null, and the two coincide exactly when
  the knowledge decides every fact.

**Chances.** Give every fact two independent coins: whether its status is known (confidence `c`)
and whether it is present (strength `s`). As a random surrounding of `α ⊕ α`:

* `absent_chance`: the chance that no forbidden fact is present is `∏ (1 - s)`, the strength
  reading;
* `known_absent_chance`: the chance that every forbidden fact is known and absent is
  `(∏ c) · ∏ (1 - s)`: the grade's null is the strength reading scaled by the confidence;
* `not_known_present_chance`: for one fact, the chance that it is not known present is `1 - c s`;
  `nulls_gap`: the two nulls differ by exactly `1 - c`, whatever the strength.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensorWeight

open Finset

universe u v w

/-! ## The two readings -/

section Readings

variable {Completion : Type u} {Fact : Type v} {Label : Type w}

/-- **Known absence**: at every admissible completion of the knowledge, no fact has a forbidden
label. -/
def KnownAbsent (known : Set Completion) (facts : Finset Fact) (label : Fact → Completion → Label)
    (forbidden : Set Label) : Prop :=
  ∀ σ ∈ known, ∀ a ∈ facts, label a σ ∉ forbidden

/-- **Not known to be present**: no fact has a forbidden label at every admissible completion. -/
def NotKnownPresent (known : Set Completion) (facts : Finset Fact)
    (label : Fact → Completion → Label) (forbidden : Set Label) : Prop :=
  ∀ a ∈ facts, ∃ σ ∈ known, label a σ ∉ forbidden

variable {label : Fact → Completion → Label} {forbidden : Set Label}

/-- Known absence survives refinement of the knowledge. -/
theorem knownAbsent_refines {known known' : Set Completion} {facts : Finset Fact}
    (refines : known' ⊆ known) (absent : KnownAbsent known facts label forbidden) :
    KnownAbsent known' facts label forbidden :=
  fun σ admissible => absent σ (refines admissible)

/-- Known absence survives removal of facts. -/
theorem knownAbsent_shrinks {known : Set Completion} {facts facts' : Finset Fact}
    (smaller : facts' ⊆ facts) (absent : KnownAbsent known facts label forbidden) :
    KnownAbsent known facts' label forbidden :=
  fun σ admissible a member => absent σ admissible a (smaller member)

/-- Over consistent knowledge, known absence implies not being known present. -/
theorem notKnownPresent_of_knownAbsent {known : Set Completion} {facts : Finset Fact}
    (consistent : known.Nonempty) (absent : KnownAbsent known facts label forbidden) :
    NotKnownPresent known facts label forbidden := by
  intro a member
  obtain ⟨σ, admissible⟩ := consistent
  exact ⟨σ, admissible, absent σ admissible a member⟩

/-- **When the knowledge decides every fact, the two nulls coincide.** -/
theorem knownAbsent_iff_of_determined {known : Set Completion} {facts : Finset Fact}
    (consistent : known.Nonempty)
    (decided : ∀ a ∈ facts, (∀ σ ∈ known, label a σ ∈ forbidden) ∨
      (∀ σ ∈ known, label a σ ∉ forbidden)) :
    KnownAbsent known facts label forbidden ↔ NotKnownPresent known facts label forbidden := by
  refine ⟨notKnownPresent_of_knownAbsent consistent, fun notPresent σ admissible a member => ?_⟩
  rcases decided a member with always | never
  · obtain ⟨τ, admissibleτ, notForbidden⟩ := notPresent a member
    exact absurd (always τ admissibleτ) notForbidden
  · exact never σ admissible

end Readings

/-! ## Controls: one fact whose label is a variable -/

section Controls

/-- The fact's label is the value of the variable at the completion. -/
def variableLabel : Unit → ℕ → ℕ := fun _ σ => σ

/-- **An undetermined fact separates the nulls**: with the variable either `0` or `9`, the label
`9` is not known present, and not known absent. -/
theorem undetermined_separates :
    NotKnownPresent ({0, 9} : Set ℕ) {()} variableLabel {9} ∧
      ¬ KnownAbsent ({0, 9} : Set ℕ) {()} variableLabel {9} := by
  refine ⟨fun _ _ => ⟨0, Or.inl rfl, by simp [variableLabel]⟩, fun absent => ?_⟩
  exact absent 9 (Or.inr rfl) () (mem_singleton_self ()) rfl

/-- **Not being known present does not survive refinement**: telling that the variable is `9`
destroys it. So it is not a check of the step. -/
theorem notKnownPresent_does_not_refine :
    ({9} : Set ℕ) ⊆ {0, 9} ∧ NotKnownPresent ({0, 9} : Set ℕ) {()} variableLabel {9} ∧
      ¬ NotKnownPresent ({9} : Set ℕ) {()} variableLabel {9} := by
  refine ⟨fun σ member => Or.inr member, undetermined_separates.1, fun notPresent => ?_⟩
  obtain ⟨σ, admissible, notForbidden⟩ := notPresent () (mem_singleton_self ())
  exact notForbidden admissible

end Controls

/-! ## Chances: confidence and strength -/

section Chance

variable {α : Type u} [Fintype α] [DecidableEq α] {R : Type v} [CommRing R]

/-- The two coins of a fact: `inl a`, its status is known; `inr a`, it is present. -/
def coins (confidence strength : α → R) : α ⊕ α → R := Sum.elim confidence strength

/-- A grade and its negation share the total chance. -/
theorem measure_add_measure_not {β : Type u} [Fintype β] [DecidableEq β] (p : β → R)
    (G : Finset β → Prop) : measure p G + measure p (fun T => ¬ G T) = 1 := by
  rw [← measure_true p]
  unfold measure
  rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun T _ => ?_
  split_ifs <;> simp_all

/-- **The strength reading**: no forbidden fact is present, with chance `∏ (1 - s)`. -/
theorem absent_chance (c s : α → R) (F : Finset α) :
    measure (coins c s) (fun T => Disjoint T (F.map Function.Embedding.inr)) =
      ∏ a ∈ F, (1 - s a) := by
  rw [measure_absence, prod_map]
  rfl

/-- **The grade's null**: every forbidden fact is known and absent, with chance
`(∏ c) · ∏ (1 - s)`. -/
theorem known_absent_chance (c s : α → R) (F : Finset α) :
    measure (coins c s) (fun T => F.map Function.Embedding.inl ⊆ T ∧
      Disjoint T (F.map Function.Embedding.inr)) =
      (∏ a ∈ F, c a) * ∏ a ∈ F, (1 - s a) := by
  rw [measure_presence_absence, if_pos (disjoint_map_inl_map_inr F F), prod_map, prod_map]
  rfl

/-- **Known absence is the strength reading scaled by the confidence.** -/
theorem known_absent_eq_confidence_mul_absent (c s : α → R) (F : Finset α) :
    measure (coins c s) (fun T => F.map Function.Embedding.inl ⊆ T ∧
      Disjoint T (F.map Function.Embedding.inr)) =
      (∏ a ∈ F, c a) * measure (coins c s) (fun T => Disjoint T (F.map Function.Embedding.inr)) := by
  rw [known_absent_chance, absent_chance]

/-- **Not known present**, for one fact: chance `1 - c s`. -/
theorem not_known_present_chance (c s : α → R) (a : α) :
    measure (coins c s) (fun T => ¬ (Sum.inl a ∈ T ∧ Sum.inr a ∈ T)) = 1 - c a * s a := by
  have both : measure (coins c s) (fun T => Sum.inl a ∈ T ∧ Sum.inr a ∈ T) = c a * s a := by
    rw [measure_congr (coins c s) (G := fun T => Sum.inl a ∈ T ∧ Sum.inr a ∈ T)
      (H := fun T => {Sum.inl a, Sum.inr a} ⊆ T)
      (fun T => by rw [insert_subset_iff, singleton_subset_iff]), measure_presence,
      prod_pair Sum.inl_ne_inr]
    rfl
  have total := measure_add_measure_not (coins c s) (fun T => Sum.inl a ∈ T ∧ Sum.inr a ∈ T)
  rw [both] at total
  linear_combination total

/-- **The two nulls differ by the unknown mass `1 - c`, whatever the strength.** -/
theorem nulls_gap (c s : α → R) (a : α) :
    measure (coins c s) (fun T => ¬ (Sum.inl a ∈ T ∧ Sum.inr a ∈ T)) -
        measure (coins c s) (fun T => ({a} : Finset α).map Function.Embedding.inl ⊆ T ∧
          Disjoint T (({a} : Finset α).map Function.Embedding.inr)) = 1 - c a := by
  rw [not_known_present_chance, known_absent_chance, prod_singleton, prod_singleton]
  ring

end Chance

end Mettapedia.Logic.LinearLogic.KnowledgeTensorWeight
