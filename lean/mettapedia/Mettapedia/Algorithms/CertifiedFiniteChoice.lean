import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Exact finite choice and interval-certified comparisons

The algorithm accepts an ordinary finite list and rational scores. It returns
an actual member attaining the largest score. Interval comparisons have a
separate checker: overlapping score intervals provide no rejection evidence.
-/

namespace Mettapedia.Algorithms.CertifiedFiniteChoice

variable {Candidate : Type*}

/-- Exact maximization of a rational score over a finite candidate list. -/
def chooseBest (score : Candidate → ℚ) : List Candidate → Option Candidate
  | [] => none
  | c :: cs => match chooseBest score cs with
    | none => some c
    | some best => if score c ≤ score best then some best else some c

theorem chooseBest_eq_none_iff (score : Candidate → ℚ) (candidates : List Candidate) :
    chooseBest score candidates = none ↔ candidates = [] := by
  cases candidates with
  | nil => simp [chooseBest]
  | cons c cs =>
      cases h : chooseBest score cs with
      | none => simp [chooseBest, h]
      | some best => simp [chooseBest, h]; split_ifs <;> simp_all

/-- A chosen optimum belongs to the input list and dominates every listed score. -/
theorem chooseBest_correct (score : Candidate → ℚ) (candidates : List Candidate)
    (selected : Candidate) (chosen : chooseBest score candidates = some selected) :
    selected ∈ candidates ∧ ∀ c ∈ candidates, score c ≤ score selected := by
  induction candidates generalizing selected with
  | nil => simp [chooseBest] at chosen
  | cons c cs ih =>
      cases h : chooseBest score cs with
      | none =>
          have empty := (chooseBest_eq_none_iff score cs).mp h
          subst cs
          simp [chooseBest] at chosen
          subst selected
          simp
      | some best =>
          obtain ⟨member, maximal⟩ := ih best h
          by_cases prefer : score c ≤ score best
          · simp only [chooseBest, h, prefer, if_true, Option.some.injEq] at chosen
            subst selected
            refine ⟨List.mem_cons_of_mem c member, ?_⟩
            intro other hother
            rcases List.mem_cons.mp hother with rfl | rest
            · exact prefer
            · exact maximal other rest
          · simp only [chooseBest, h, prefer, if_false, Option.some.injEq] at chosen
            subst selected
            refine ⟨List.mem_cons_self, ?_⟩
            intro other hother
            rcases List.mem_cons.mp hother with rfl | rest
            · exact le_rfl
            · exact (maximal other rest).trans (le_of_lt (lt_of_not_ge prefer))

/-- A finite interval comparison certifies all competitors; it never treats overlap as falsehood. -/
def checkIntervals [DecidableEq Candidate] (candidates : List Candidate)
    (lower upper : Candidate → ℚ) (selected : Candidate) : Bool :=
  decide (selected ∈ candidates ∧ ∀ c ∈ candidates, c ≠ selected → upper c ≤ lower selected)

/-- A successful comparison proves optimality for every real score enclosed by the intervals. -/
theorem checkIntervals_sound [DecidableEq Candidate] (candidates : List Candidate)
    (lower upper : Candidate → ℚ) (actual : Candidate → ℝ) (selected : Candidate)
    (encloses : ∀ c ∈ candidates, (lower c : ℝ) ≤ actual c ∧ actual c ≤ (upper c : ℝ))
    (accepted : checkIntervals candidates lower upper selected = true) :
    selected ∈ candidates ∧ ∀ c ∈ candidates, actual c ≤ actual selected := by
  have checked : selected ∈ candidates ∧
      ∀ c ∈ candidates, c ≠ selected → upper c ≤ lower selected := by
    simpa only [checkIntervals, decide_eq_true_eq] using accepted
  refine ⟨checked.1, ?_⟩
  intro c hc
  by_cases same : c = selected
  · simp [same]
  · have hr : (upper c : ℝ) ≤ (lower selected : ℝ) := by
      exact_mod_cast checked.2 c hc same
    exact (encloses c hc).2.trans (hr.trans (encloses selected checked.1).1)

end Mettapedia.Algorithms.CertifiedFiniteChoice
