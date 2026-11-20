import Mettapedia.ProbabilityTheory.ImpreciseProbability.ConditionalConstraintBounds
import Mettapedia.Logic.Arithmetic.FourierMotzkinBudget

/-!
# Anytime bounds for conditional credal queries

The semantics is the set of conditional values over the common set of
admissible models with positive support. A work budget limits arithmetic
projection. The readout intersects new outer bounds with earlier ones.
Exhaustive projection gives both attainable endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.AnytimeConditional

open Mettapedia.Logic.Arithmetic.FourierMotzkin
open FiniteConditionalConstraints ConditionalConstraintBounds

abbrev Answer := Option (ℚ × ℚ)

def range : Answer → Set ℝ
  | none => ∅
  | some (lo, hi) => Set.Icc (lo : ℝ) (hi : ℝ)

def initial : Answer := some (0, 1)

theorem range_initial : range initial = Set.Icc (0 : ℝ) 1 := by simp [initial, range]

/-- Intersect two enclosures for the same query and knowledge snapshot. -/
def tighten : Answer → Answer → Answer
  | some (lo, hi), some (nextLo, nextHi) =>
    let lower := max lo nextLo
    let upper := min hi nextHi
    if lower ≤ upper then some (lower, upper) else none
  | _, _ => none

theorem range_tighten (current next : Answer) :
    range (tighten current next) = range current ∩ range next := by
  cases current with
  | none => cases next <;> simp [tighten, range]
  | some current =>
    cases next with
    | none => simp [tighten, range]
    | some next =>
      obtain ⟨lo, hi⟩ := current
      obtain ⟨nlo, nhi⟩ := next
      ext v
      by_cases compatible : max lo nlo ≤ min hi nhi
      · rw [tighten, if_pos compatible]
        simp only [range, Set.mem_inter_iff, Set.mem_Icc,
          Rat.cast_max, Rat.cast_min, max_le_iff, le_min_iff]
        tauto
      · rw [tighten, if_neg compatible]
        simp only [range, Set.mem_empty_iff_false,
          Set.mem_inter_iff, Set.mem_Icc, false_iff]
        rintro ⟨⟨l, u⟩, nl, nu⟩
        apply compatible
        have ordered : max (lo : ℝ) (nlo : ℝ) ≤ min (hi : ℝ) (nhi : ℝ) :=
          (max_le l nl).trans (le_min u nu)
        have lifted : ((max lo nlo : ℚ) : ℝ) ≤ ((min hi nhi : ℚ) : ℝ) := by
          rw [Rat.cast_max, Rat.cast_min]
          exact ordered
        exact Rat.cast_le.mp lifted

private theorem fullStep_closed {n : Nat} {rows : List (Atom (n + 1))} (closed : NonStrict rows) :
    NonStrict (Budget.fullStep rows) := by
  intro row member
  obtain ⟨a, original, rfl⟩ := Budget.fullStep_member rows row member
  rw [Budget.normalize_rel]
  rcases List.mem_append.mp original with residual | pair
  · exact residuals_closed _ closed a residual
  · obtain ⟨lo, lmem, found⟩ := List.mem_flatMap.mp pair
    obtain ⟨hi, hmem, rfl⟩ := List.mem_map.mp found
    simp [cross, lower_closed _ closed lo lmem, upper_closed _ closed hi hmem]

private theorem partial_closed (fuel n : Nat) (rows : List (Atom (n + 1))) (closed : NonStrict rows) :
    NonStrict (Budget.limited fuel n rows) := by
  induction n with
  | zero => exact closed
  | succ n ih =>
    exact ih _ (fun row h => fullStep_closed closed row (Budget.step_subset fuel rows h))

/-- In the last dimension only constants and endpoint comparisons are needed. -/
def rowsAnswer (rows : List (Atom 1)) : Answer :=
  let lo := lowerEndpoint rows
  let hi := upperEndpoint rows
  if decideSat (residuals rows) && decide (lo ≤ hi) then some (lo, hi) else none

theorem rowsAnswer_range (rows : List (Atom 1)) (closed : NonStrict rows) (v : ℝ) :
    v ∈ range (rowsAnswer rows) ↔ allSat rows (fun _ => v) ∧ v ∈ Set.Icc (0 : ℝ) 1 := by
  rw [oneDimensional_in_unit closed]
  have constants : decideSat (residuals rows) = true ↔
      allSat (residuals rows) (Fin.elim0 : Fin 0 → ℝ) := by
    rw [decideSat_iff (R := ℝ)]
    constructor
    · rintro ⟨e, held⟩
      exact unique_env e ▸ held
    · exact fun held => ⟨_, held⟩
  by_cases holds : allSat (residuals rows) (Fin.elim0 : Fin 0 → ℝ)
  · have evaluated := constants.mpr holds
    by_cases ordered : lowerEndpoint rows ≤ upperEndpoint rows
    · simp only [rowsAnswer, evaluated, Bool.true_and, decide_eq_true_eq, if_pos ordered,
        range, holds, true_and]
    · simp only [rowsAnswer, evaluated, Bool.true_and, decide_eq_true_eq, if_neg ordered,
        range, holds, true_and, Set.mem_empty_iff_false, false_iff, Set.mem_Icc]
      rintro ⟨insideLow, insideHigh⟩
      exact ordered (Rat.cast_le.mp (insideLow.trans insideHigh))
  · have evaluated : decideSat (residuals rows) = false :=
      Bool.eq_false_iff.mpr (fun yes => holds (constants.mp yes))
    simp only [rowsAnswer, evaluated, Bool.false_and, Bool.false_eq_true, if_false, range, holds,
      false_and, Set.mem_empty_iff_false]

def queryAt {n : Nat} (fuel : Nat) (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) :
    Answer := rowsAnswer (Budget.limited fuel n (scaledAtoms base event condition))

theorem queryAt_sound {n : Nat} (fuel : Nat) (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) :
    queryValues base event condition ⊆ range (queryAt fuel base event condition) := by
  intro v possible
  have closed := scaledAtoms_closed base event condition
  rw [queryAt, rowsAnswer_range _ (partial_closed fuel n _ closed)]
  obtain ⟨e, held, same⟩ := (projectToOne_sat n _ v).mp ((projected_values base event condition v).mpr possible)
  exact ⟨same ▸ Budget.partial_sound fuel n _ e held, queryValues_subset_unit base event condition possible⟩

private theorem queryAt_eq_exact_of_projection {n : Nat} (fuel : Nat) (base : KnowledgeBase (Fin n))
    (event condition : Event (Fin n))
    (complete : Budget.limited fuel n (scaledAtoms base event condition) =
      Budget.complete n (scaledAtoms base event condition)) :
    range (queryAt fuel base event condition) = queryValues base event condition := by
  refine Set.Subset.antisymm ?_ (queryAt_sound fuel base event condition)
  intro v member
  have closed := scaledAtoms_closed base event condition
  rw [queryAt, rowsAnswer_range _ (partial_closed fuel n _ closed), complete] at member
  obtain ⟨e, held, same⟩ := (Budget.complete_iff n _ v).mp member.1
  exact (projected_values base event condition v).mp ((projectToOne_sat n _ v).mpr ⟨e, held, same⟩)

theorem queryAt_eventually_exact {n : Nat} (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) :
    ∃ sufficient, ∀ fuel ≥ sufficient,
      range (queryAt fuel base event condition) = queryValues base event condition := by
  obtain ⟨sufficient, stable⟩ := Budget.eventually_complete n (scaledAtoms base event condition)
  exact ⟨sufficient, fun fuel enough => queryAt_eq_exact_of_projection fuel _ _ _ (stable fuel enough)⟩

theorem tighten_query_sound {n : Nat} (current : Answer) (fuel : Nat) (base : KnowledgeBase (Fin n))
    (event condition : Event (Fin n)) (sound : queryValues base event condition ⊆ range current) :
    queryValues base event condition ⊆ range (tighten current (queryAt fuel base event condition)) := by
  rw [range_tighten]
  exact Set.subset_inter sound (queryAt_sound fuel base event condition)

theorem tighten_refines (current next : Answer) : range (tighten current next) ⊆ range current := by
  rw [range_tighten]
  exact Set.inter_subset_left

/-- Additional constraints may tighten what is known. An enclosure for the
earlier snapshot still applies when the query and conditioning event agree. -/
theorem retain_on_append {Ω : Type*} [Fintype Ω] (base extra : KnowledgeBase Ω)
    (event condition : Event Ω) (current : Answer)
    (sound : queryValues base event condition ⊆ range current) :
    queryValues (base ++ extra) event condition ⊆ range current := by
  rintro v ⟨model, member, positive, equal⟩
  apply sound
  exact ⟨model, fun c h => member c (List.mem_append_left _ h), positive, equal⟩

def queryReported {n : Nat} (fuel : Nat) (base : KnowledgeBase (Fin n)) (event condition : Event (Fin n)) :
    Answer × Bool :=
  let projection := Budget.run fuel n (scaledAtoms base event condition)
  (rowsAnswer projection.1, projection.2)

theorem queryReported_agrees {n : Nat} (fuel : Nat) (base : KnowledgeBase (Fin n))
    (event condition : Event (Fin n)) :
    (queryReported fuel base event condition).1 = queryAt fuel base event condition := by
  simp only [queryReported, queryAt, Budget.run_rows]

theorem queryReported_complete {n : Nat} (fuel : Nat) (base : KnowledgeBase (Fin n))
    (event condition : Event (Fin n)) (done : (queryReported fuel base event condition).2 = true) :
    range (queryReported fuel base event condition).1 = queryValues base event condition := by
  rw [queryReported_agrees]
  apply queryAt_eq_exact_of_projection
  rw [← Budget.run_rows]
  exact Budget.run_completed fuel n _ done

end Mettapedia.ProbabilityTheory.ImpreciseProbability.AnytimeConditional
