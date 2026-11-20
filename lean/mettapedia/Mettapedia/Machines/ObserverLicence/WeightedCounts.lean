import Mettapedia.Machines.RuntimePlumbing.SuccessPriority
import Mathlib.Tactic

/-!
# Weighted counting, including success-priority fallback

A weighted occurrence denotes repeated replies. The summary computes normal
and error cardinalities in one traversal without materializing repetitions.
Its preferred readout is proved equal to counting the expanded boundary's
success-priority replies. Keeping only the raw total is not sufficient.
Fixed-width overflow and the native reply classifier are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ObserverLicence.WeightedCounts

open RuntimePlumbing

variable {Reply : Type}

structure Counts where
  normal : Nat
  errors : Nat
  deriving Repr, DecidableEq

def combine (left right : Counts) : Counts :=
  ⟨left.normal + right.normal, left.errors + right.errors⟩

def expand (weighted : List (Reply × Nat)) : List Reply :=
  weighted.flatMap fun entry => List.replicate entry.2 entry.1

def rawCount (weighted : List (Reply × Nat)) : Nat := (weighted.map Prod.snd).sum

def summarize (isError : Reply → Bool) : List (Reply × Nat) → Counts
  | [] => ⟨0, 0⟩
  | (value, weight) :: rest =>
      let later := summarize isError rest
      if isError value then {later with errors := weight + later.errors}
      else {later with normal := weight + later.normal}

def preferredCount (counts : Counts) : Nat :=
  if counts.normal = 0 then counts.errors else counts.normal

theorem expanded_length (weighted : List (Reply × Nat)) :
    (expand weighted).length = rawCount weighted := by
  simp [expand, rawCount, List.length_flatMap]

theorem summary_total (isError : Reply → Bool) (weighted : List (Reply × Nat)) :
    (summarize isError weighted).normal + (summarize isError weighted).errors = rawCount weighted := by
  induction weighted with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨value, weight⟩
      cases classified : isError value <;> simp [summarize, classified, rawCount] <;>
        simp [rawCount] at ih <;> omega

theorem summary_successes (isError : Reply → Bool) (weighted : List (Reply × Nat)) :
    (summarize isError weighted).normal =
      (SuccessPriority.successes isError (expand weighted)).length := by
  induction weighted with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨value, weight⟩
      cases classified : isError value <;>
        simp [summarize, expand, classified, SuccessPriority.successes, ih]

theorem summary_append (isError : Reply → Bool) (first second : List (Reply × Nat)) :
    summarize isError (first ++ second) = combine (summarize isError first) (summarize isError second) := by
  induction first with
  | nil => simp [summarize, combine]
  | cons entry rest ih =>
      rcases entry with ⟨value, weight⟩
      cases classified : isError value <;> simp [summarize, classified, ih, combine, Nat.add_assoc]

theorem preferred_count_exact (isError : Reply → Bool) (weighted : List (Reply × Nat)) :
    preferredCount (summarize isError weighted) =
      (SuccessPriority.select isError (expand weighted)).length := by
  have normals := summary_successes isError weighted
  have total := summary_total isError weighted
  cases successes : SuccessPriority.successes isError (expand weighted) with
  | nil =>
      rw [successes, List.length_nil] at normals
      simp only [preferredCount, normals, ↓reduceIte, SuccessPriority.select, successes]
      rw [expanded_length]
      omega
  | cons first rest =>
      rw [successes, List.length_cons] at normals
      have nonzero : (summarize isError weighted).normal ≠ 0 := by omega
      simp only [preferredCount, nonzero, ↓reduceIte, SuccessPriority.select, successes]
      exact normals

theorem raw_count_fusion (weighted : List (Reply × Nat)) :
    rawCount weighted = (expand weighted).foldl (fun count _ => count + 1) 0 := by
  have foldLength : ∀ (values : List Reply) (start : Nat),
      values.foldl (fun count _ => count + 1) start = start + values.length := by
    intro values
    induction values with
    | nil => intro start; simp
    | cons value rest ih =>
        intro start
        rw [List.foldl_cons, ih]
        simp only [List.length_cons]
        omega
  rw [foldLength, Nat.zero_add, expanded_length]

namespace Controls

def isError : Except Nat Nat → Bool
  | .error _ => true
  | .ok _ => false

theorem multiplicity_is_not_a_set_cardinality :
    rawCount ([(7, 3), (7, 2)] : List (Nat × Nat)) = 5 := by decide

theorem raw_total_does_not_determine_he_count :
    rawCount ([(Except.error 3, 2), (.ok 7, 1)] : List (Except Nat Nat × Nat)) = 3 ∧
      preferredCount (summarize isError [(.error 3, 2), (.ok 7, 1)]) = 1 := by decide

theorem error_only_weights_remain_visible :
    preferredCount (summarize isError [(.error 3, 2), (.error 4, 3)]) = 5 := by decide

theorem different_nonzero_weights_have_different_counts :
    preferredCount (summarize isError [(.ok 7, 2)]) = 2 ∧
      preferredCount (summarize isError [(.ok 7, 3)]) = 3 := by decide

end Controls

end Mettapedia.Machines.ObserverLicence.WeightedCounts
