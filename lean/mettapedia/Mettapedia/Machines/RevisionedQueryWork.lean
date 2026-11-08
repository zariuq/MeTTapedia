import Mettapedia.Machines.RevisionedQueryFacts
import Mathlib.Data.Finset.Card

/-!
# Exact service-computation count for a revision-scoped query history

This extends the existing cache algorithm, not its representation. With no
eviction, each distinct stamped key missing at entry causes exactly one
service computation. The count says nothing about key acquisition, lookup,
allocation or the internal cost of the service. Repeated occurrences and
their answers are still present in the history.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RevisionedQueryWork

open RevisionedQueryFacts

variable {Stamp Key Fact : Type} [DecidableEq Stamp] [DecidableEq Key]

def retained (cache : Cache Stamp Key Fact) : Finset (Request Stamp Key) :=
  (cache.map fun entry => (⟨entry.stamp, entry.key⟩ : Request Stamp Key)).toFinset

theorem lookup_none_iff (query : Request Stamp Key) (cache : Cache Stamp Key Fact) :
    lookup query.stamp query.key cache = none ↔ query ∉ retained cache := by
  induction cache with
  | nil => simp [lookup, retained]
  | cons entry rest ih =>
      cases query with
      | mk stamp key =>
          rw [show retained (entry :: rest) = insert ⟨entry.stamp, entry.key⟩ (retained rest) from
            by simp [retained]]
          change (if entry.stamp = stamp ∧ entry.key = key then some entry.facts
            else lookup stamp key rest) = none ↔
              (⟨stamp, key⟩ : Request Stamp Key) ∉ insert ⟨entry.stamp, entry.key⟩ (retained rest)
          by_cases same : entry.stamp = stamp ∧ entry.key = key
          · simp [same]
          · have different : (⟨stamp, key⟩ : Request Stamp Key) ≠ ⟨entry.stamp, entry.key⟩ := by
              intro equality
              have parts := Request.mk.inj equality
              exact same ⟨parts.1.symm, parts.2.symm⟩
            simpa only [if_neg same, Finset.mem_insert, not_or, different, not_false_eq_true,
              true_and] using ih

theorem request_retained (compute : Stamp → Key → List Fact) (query : Request Stamp Key)
    (cache : Cache Stamp Key Fact) :
    retained (request compute query cache).cache = insert query (retained cache) := by
  cases hit : lookup query.stamp query.key cache with
  | none => simp [request, hit, retained]
  | some facts =>
      have member : query ∈ retained cache := by
        by_contra absent
        have none := (lookup_none_iff query cache).mpr absent
        rw [hit] at none
        contradiction
      simp [request, hit, Finset.insert_eq_of_mem member]

theorem request_work_card (compute : Stamp → Key → List Fact) (query : Request Stamp Key)
    (cache : Cache Stamp Key Fact) :
    (request compute query cache).computations + (retained cache).card =
      (retained (request compute query cache).cache).card := by
  rw [request_retained]
  cases hit : lookup query.stamp query.key cache with
  | none =>
      have absent := (lookup_none_iff query cache).mp hit
      simp [request, hit, Finset.card_insert_of_notMem absent, Nat.add_comm]
  | some facts =>
      have member : query ∈ retained cache := by
        by_contra absent
        have none := (lookup_none_iff query cache).mpr absent
        rw [hit] at none
        contradiction
      simp [request, hit, Finset.insert_eq_of_mem member]

theorem requests_retained (compute : Stamp → Key → List Fact)
    (queries : List (Request Stamp Key)) (cache : Cache Stamp Key Fact) :
    retained (requests compute queries cache).cache = retained cache ∪ queries.toFinset := by
  induction queries generalizing cache with
  | nil => simp [requests]
  | cons query queries ih =>
      simp only [requests, ih, request_retained, List.toFinset_cons]
      ext item
      simp

theorem requests_work_card (compute : Stamp → Key → List Fact)
    (queries : List (Request Stamp Key)) (cache : Cache Stamp Key Fact) :
    (requests compute queries cache).computations + (retained cache).card =
      (retained cache ∪ queries.toFinset).card := by
  induction queries generalizing cache with
  | nil => simp [requests]
  | cons query queries ih =>
      have first := request_work_card compute query cache
      have later := ih (request compute query cache).cache
      have union : retained (request compute query cache).cache ∪ queries.toFinset =
          retained cache ∪ (query :: queries).toFinset := by
        rw [request_retained, List.toFinset_cons]
        ext item
        simp
      rw [union] at later
      simp only [requests]
      omega

theorem cold_work_exact (compute : Stamp → Key → List Fact)
    (queries : List (Request Stamp Key)) :
    (requests compute queries []).computations = queries.toFinset.card := by
  simpa [retained] using requests_work_card compute queries []

theorem cold_work_le_length (compute : Stamp → Key → List Fact)
    (queries : List (Request Stamp Key)) :
    (requests compute queries []).computations ≤ queries.length := by
  rw [cold_work_exact]
  exact List.toFinset_card_le _

namespace Controls

def compute (revision key : Nat) : List Nat := [revision + key, revision + key]
def query : Request Nat Nat := ⟨0, 1⟩
def revised : Request Nat Nat := ⟨1, 1⟩
def other : Request Nat Nat := ⟨0, 2⟩

theorem repeated_boundary_preserves_occurrences :
    (requests compute [query, query] []).computations = 1 ∧
      (requests compute [query, query] []).facts = [[1, 1], [1, 1]] := by decide +kernel

theorem two_distinct_obligations_cost_two :
    (requests compute [query, other] []).computations = 2 := by decide +kernel

theorem revised_obligation_is_not_a_hit :
    (requests compute [query, revised, query] []).computations = 2 ∧
      (requests compute [query, revised, query] []).facts = [[1, 1], [2, 2], [1, 1]] := by decide +kernel

end Controls

end Mettapedia.Machines.RevisionedQueryWork
