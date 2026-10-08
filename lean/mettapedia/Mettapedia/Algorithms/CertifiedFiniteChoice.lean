import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Exact finite choice and interval-certified comparisons

Scalar maximization accepts an ordinary finite list and rational scores. It
returns an actual member attaining the largest score. A separate dominance
filter retains every undominated occurrence in input order, including ties.
Interval comparisons have a separate checker: overlapping score intervals
provide no rejection evidence.
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

/-- The finite dominance scan and its filtering loop keep their reference
collection separate from the unexamined suffix. Neither merges equal rows. -/
def dominated (dominates : Candidate → Candidate → Bool) (candidate : Candidate) :
    List Candidate → Bool
  | [] => false
  | other :: rest => dominates other candidate || dominated dominates candidate rest

def paretoLoop (dominates : Candidate → Candidate → Bool) (all : List Candidate) :
    List Candidate → List Candidate
  | [] => []
  | candidate :: rest =>
      if dominated dominates candidate all then paretoLoop dominates all rest
      else candidate :: paretoLoop dominates all rest

def pareto (dominates : Candidate → Candidate → Bool) (candidates : List Candidate) :
    List Candidate := paretoLoop dominates candidates candidates

/-- A specification over the input collection, independent of the scan. -/
def Undominated (dominates : Candidate → Candidate → Bool)
    (candidates : List Candidate) (candidate : Candidate) : Prop :=
  ∀ other ∈ candidates, dominates other candidate = false

theorem dominated_eq_any (dominates : Candidate → Candidate → Bool)
    (candidate : Candidate) (candidates : List Candidate) :
    dominated dominates candidate candidates = candidates.any (dominates · candidate) := by
  induction candidates with
  | nil => rfl
  | cons other rest ih => simp [dominated, ih]

theorem dominated_false_iff (dominates : Candidate → Candidate → Bool)
    (candidate : Candidate) (candidates : List Candidate) :
    dominated dominates candidate candidates = false ↔
      Undominated dominates candidates candidate := by
  simp [dominated_eq_any, Undominated]

theorem paretoLoop_eq_filter (dominates : Candidate → Candidate → Bool)
    (all remaining : List Candidate) :
    paretoLoop dominates all remaining =
      remaining.filter (fun candidate => !dominated dominates candidate all) := by
  induction remaining with
  | nil => rfl
  | cons candidate rest ih =>
      cases checked : dominated dominates candidate all <;> simp [paretoLoop, checked, ih]

/-- Exactly the input members that lack a strict dominator survive. The
relation may be a partial order comparison; no scalar score is introduced. -/
theorem mem_pareto_iff (dominates : Candidate → Candidate → Bool)
    (candidates : List Candidate) (candidate : Candidate) :
    candidate ∈ pareto dominates candidates ↔
      candidate ∈ candidates ∧ Undominated dominates candidates candidate := by
  simp [pareto, paretoLoop_eq_filter, dominated_false_iff]

/-- Complete packets remain in their original order, with no replacement of
their labels, evidence or provenance. -/
theorem pareto_sublist (dominates : Candidate → Candidate → Bool)
    (candidates : List Candidate) : (pareto dominates candidates).Sublist candidates := by
  rw [pareto, paretoLoop_eq_filter]
  exact List.filter_sublist

theorem pareto_count_of_undominated [DecidableEq Candidate]
    (dominates : Candidate → Candidate → Bool) (candidates : List Candidate)
    (candidate : Candidate) (retained : Undominated dominates candidates candidate) :
    (pareto dominates candidates).count candidate = candidates.count candidate := by
  rw [pareto, paretoLoop_eq_filter]
  apply List.count_filter
  simp [(dominated_false_iff dominates candidate candidates).mpr retained]

/-- A permutation of a completed input bag permutes the output bag. It does
not identify different ordered prefixes of an unfinished search. -/
theorem pareto_perm (dominates : Candidate → Candidate → Bool)
    {first second : List Candidate} (same : first.Perm second) :
    (pareto dominates first).Perm (pareto dominates second) := by
  have predicate : (fun candidate => !dominated dominates candidate first) =
      (fun candidate => !dominated dominates candidate second) := by
    funext candidate
    rw [dominated_eq_any, dominated_eq_any, same.any_eq]
  simp only [pareto, paretoLoop_eq_filter]
  rw [predicate]
  exact same.filter _

namespace ParetoControls

def smaller (left right : Nat) : Bool := decide (left < right)

theorem equal_occurrences_survive : pareto smaller [2, 1, 1, 3] = [1, 1] := by decide

theorem an_open_prefix_can_lose_its_minimum :
    pareto smaller [2] = [2] ∧ pareto smaller [2, 1] = [1] := by decide

theorem weak_dominance_wrongly_deletes_ties :
    pareto (fun left right : Nat => decide (left ≤ right)) [1, 1] = [] := by decide

end ParetoControls

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
