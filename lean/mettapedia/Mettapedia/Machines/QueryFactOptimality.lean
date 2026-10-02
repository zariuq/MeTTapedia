import Mettapedia.Machines.RevisionedQueryFacts
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Query-fact computation counts and an oracle lower bound

The memoizing batch algorithm performs exactly one service computation for
each distinct requested stamp/key pair absent from its initial cache. This
does not assert constant-time lookup or bound the cost of computing a fact.

For a separate information lower bound, an arbitrary adaptive finite decision
tree accesses an otherwise unknown Boolean service. If it must return every
requested answer correctly for every service consistent with its initially
known entries, it must read every distinct unknown requested key. The proof
changes one unread answer and establishes observational indistinguishability
of the two runs. Thus the cache count attains this lower bound in the black-box
service-access model, also with arbitrary nonnegative per-key access weights.
Static knowledge or type-specific inference can beat
that model; cache memory, publication, allocation and elapsed time are not
charged here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.QueryFactOptimality

open RevisionedQueryFacts

variable {Stamp Key Fact : Type} [DecidableEq Stamp] [DecidableEq Key]

def cacheKeys (cache : Cache Stamp Key Fact) : Finset (Request Stamp Key) :=
  (cache.map (fun entry => (⟨entry.stamp, entry.key⟩ : Request Stamp Key))).toFinset

theorem lookup_iff_key (cache : Cache Stamp Key Fact) (query : Request Stamp Key) :
    (lookup query.stamp query.key cache).isSome ↔ query ∈ cacheKeys cache := by
  induction cache with
  | nil => simp [lookup, cacheKeys]
  | cons entry cache ih =>
      simp only [lookup, cacheKeys, List.map_cons, List.toFinset_cons, Finset.mem_insert]
      split
      · rename_i same
        have queryEq : query = ⟨entry.stamp, entry.key⟩ := by
          cases query
          simp_all
        simp [queryEq]
      · rename_i different
        have queryNe : query ≠ ⟨entry.stamp, entry.key⟩ := by
          intro equal
          exact different ⟨(congrArg Request.stamp equal).symm, (congrArg Request.key equal).symm⟩
        simpa [queryNe, cacheKeys] using ih

theorem request_cache_keys (compute : Stamp → Key → List Fact)
    (query : Request Stamp Key) (cache : Cache Stamp Key Fact) :
    cacheKeys (request compute query cache).cache = insert query (cacheKeys cache) := by
  cases found : lookup query.stamp query.key cache with
  | none => simp [request, found, cacheKeys]
  | some facts =>
      have member : query ∈ cacheKeys cache := (lookup_iff_key cache query).mp (by simp [found])
      simp [request, found, Finset.insert_eq_of_mem member]

theorem request_count (compute : Stamp → Key → List Fact)
    (query : Request Stamp Key) (cache : Cache Stamp Key Fact) :
    (request compute query cache).computations = if query ∈ cacheKeys cache then 0 else 1 := by
  cases found : lookup query.stamp query.key cache with
  | none =>
      have absent : query ∉ cacheKeys cache := by
        intro member
        have hit := (lookup_iff_key cache query).mpr member
        simp [found] at hit
      simp [request, found, absent]
  | some facts =>
      have member := (lookup_iff_key cache query).mp (by simp [found])
      simp [request, found, member]

theorem missing_insert_count (queries known : Finset (Request Stamp Key))
    (query : Request Stamp Key) :
    (insert query queries \ known).card =
      (if query ∈ known then 0 else 1) + (queries \ insert query known).card := by
  by_cases present : query ∈ known
  · simp [present, Finset.insert_sdiff_of_mem queries present, Finset.insert_eq_of_mem present]
  · have splitKeys : insert query queries \ known = insert query (queries \ insert query known) := by
      ext key
      by_cases same : key = query
      · subst key; simp [present]
      · simp [same]
    rw [splitKeys, Finset.card_insert_of_notMem (by simp)]
    simp [present, Nat.add_comm]

/-- Exact count, including owner/revision/mode distinctions in request keys.
Repeated occurrences still have repeated answer lists; only service work is
shared. No uniqueness or validity assumption is needed for this count. -/
theorem batch_computations_exact (compute : Stamp → Key → List Fact)
    (queries : List (Request Stamp Key)) (cache : Cache Stamp Key Fact) :
    (requests compute queries cache).computations =
      (queries.toFinset \ cacheKeys cache).card := by
  induction queries generalizing cache with
  | nil => simp [requests]
  | cons query queries ih =>
      simp only [requests, List.toFinset_cons]
      rw [request_count, ih, request_cache_keys, missing_insert_count]

/-- A key may stand for a cheap intrinsic fact or an expensive compound query.
This counter charges the actual memoizing request path, not every occurrence. -/
def weightedWork (compute : Stamp → Key → List Fact)
    (cost : Request Stamp Key → Nat) :
    List (Request Stamp Key) → Cache Stamp Key Fact → Nat
  | [], _ => 0
  | query :: queries, cache =>
      let here := request compute query cache
      here.computations * cost query + weightedWork compute cost queries here.cache

theorem missing_insert_sum (cost : Request Stamp Key → Nat)
    (queries known : Finset (Request Stamp Key)) (query : Request Stamp Key) :
    (∑ key ∈ insert query queries \ known, cost key) =
      (if query ∈ known then 0 else cost query) +
        ∑ key ∈ queries \ insert query known, cost key := by
  by_cases present : query ∈ known
  · simp [present, Finset.insert_sdiff_of_mem queries present, Finset.insert_eq_of_mem present]
  · have splitKeys : insert query queries \ known = insert query (queries \ insert query known) := by
      ext key
      by_cases same : key = query
      · subst key; simp [present]
      · simp [same]
    rw [splitKeys, Finset.sum_insert (by simp)]
    simp [present]

theorem batch_weighted_work_exact (compute : Stamp → Key → List Fact)
    (cost : Request Stamp Key → Nat) (queries : List (Request Stamp Key))
    (cache : Cache Stamp Key Fact) :
    weightedWork compute cost queries cache =
      ∑ key ∈ queries.toFinset \ cacheKeys cache, cost key := by
  induction queries generalizing cache with
  | nil => simp [weightedWork]
  | cons query queries ih =>
      simp only [weightedWork, List.toFinset_cons]
      rw [request_count, ih, request_cache_keys, missing_insert_sum]
      split <;> simp_all

section Oracle

variable {AccessKey : Type} [DecidableEq AccessKey]

/-- Finite adaptive access programs. Branches can choose different future
reads from the answers already observed. This is a cost model, not a runtime
typing evaluator. -/
inductive Program (AccessKey : Type) where
  | done (answers : List Bool)
  | read (key : AccessKey) (next : Bool → Program AccessKey)

def execute (oracle : AccessKey → Bool) : Program AccessKey → List Bool × List AccessKey
  | .done answers => (answers, [])
  | .read key next =>
      let result := execute oracle (next (oracle key))
      (result.1, key :: result.2)

omit [DecidableEq AccessKey] in
/-- The second oracle may differ arbitrarily at unobserved keys. The program
still follows exactly the same adaptive branches and returns the same answer. -/
theorem unread_change_indistinguishable (first second : AccessKey → Bool)
    (program : Program AccessKey)
    (agree : ∀ key ∈ (execute first program).2, first key = second key) :
    execute first program = execute second program := by
  induction program with
  | done answers => rfl
  | read key next ih =>
      have here : first key = second key := agree key (by simp [execute])
      have later : ∀ observed ∈ (execute first (next (first key))).2,
          first observed = second observed := by
        intro observed member
        exact agree observed (by simp [execute, member])
      simp only [execute, ← here, ih (first key) later]

def flip (oracle : AccessKey → Bool) (key : AccessKey) : AccessKey → Bool :=
  fun observed => if observed = key then !(oracle key) else oracle observed

omit [DecidableEq AccessKey] in
theorem equal_maps_agree_on_member {Value : Type} (first second : AccessKey → Value)
    (queries : List AccessKey) (key : AccessKey) (member : key ∈ queries)
    (same : queries.map first = queries.map second) : first key = second key := by
  induction queries with
  | nil => simp at member
  | cons head queries ih =>
      simp only [List.map_cons, List.cons.injEq] at same
      rcases List.mem_cons.mp member with rfl | member
      · exact same.1
      · exact ih member same.2

omit [DecidableEq Stamp] [DecidableEq Key] in
/-- A service-correct adaptive program must work for every oracle compatible
with the values initially known. It does not receive answers for unknown keys
except through `read`. -/
def Correct (known : Finset AccessKey) (initial : AccessKey → Bool)
    (queries : List AccessKey) (program : Program AccessKey) : Prop :=
  ∀ oracle, (∀ key ∈ known, oracle key = initial key) →
    (execute oracle program).1 = queries.map oracle

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem demanded_unknown_key_is_read (known : Finset AccessKey)
    (initial oracle : AccessKey → Bool) (queries : List AccessKey) (program : Program AccessKey)
    (correct : Correct known initial queries program)
    (compatible : ∀ key ∈ known, oracle key = initial key)
    (key : AccessKey) (demanded : key ∈ queries) (unknown : key ∉ known) :
    key ∈ (execute oracle program).2 := by
  by_contra unread
  have compatibleFlip : ∀ observed ∈ known, flip oracle key observed = initial observed := by
    intro observed member
    have different : observed ≠ key := fun equal => unknown (equal ▸ member)
    simp [flip, different, compatible observed member]
  have sameRun := unread_change_indistinguishable oracle (flip oracle key) program (by
    intro observed member
    have different : observed ≠ key := fun equal => unread (equal ▸ member)
    simp [flip, different])
  have sameAnswers : queries.map oracle = queries.map (flip oracle key) := by
    rw [← correct oracle compatible, ← correct _ compatibleFlip, sameRun]
  have atKey : oracle key = flip oracle key key := by
    exact equal_maps_agree_on_member oracle (flip oracle key) queries key demanded sameAnswers
  simp only [flip] at atKey
  cases value : oracle key <;> simp [value] at atKey

omit [DecidableEq Stamp] [DecidableEq Key] in
/-- Distinct unknown requested answers impose this service-read lower bound,
even on a program whose next query adapts to all previous replies. -/
theorem distinct_unknown_lower_bound (known : Finset AccessKey)
    (initial oracle : AccessKey → Bool) (queries : List AccessKey) (program : Program AccessKey)
    (correct : Correct known initial queries program)
    (compatible : ∀ key ∈ known, oracle key = initial key) :
    (queries.toFinset \ known).card ≤ (execute oracle program).2.length := by
  apply le_trans (Finset.card_le_card ?_) (List.toFinset_card_le _)
  intro key member
  simp only [Finset.mem_sdiff, List.mem_toFinset] at member ⊢
  exact demanded_unknown_key_is_read known initial oracle queries program correct compatible
    key member.1 member.2

theorem distinct_weight_le_list (cost : AccessKey → Nat) (keys : List AccessKey) :
    (∑ key ∈ keys.toFinset, cost key) ≤ (keys.map cost).sum := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
      by_cases present : key ∈ keys.toFinset
      · simpa [Finset.insert_eq_of_mem present] using
          le_trans ih (Nat.le_add_left (keys.map cost).sum (cost key))
      · simpa [present] using Nat.add_le_add_left ih (cost key)

omit [DecidableEq Stamp] [DecidableEq Key] in
/-- The same indistinguishability argument supports unequal query costs.
Lookup, allocation, publication and retention remain outside this oracle cost. -/
theorem distinct_unknown_weighted_lower_bound (cost : AccessKey → Nat)
    (known : Finset AccessKey) (initial oracle : AccessKey → Bool)
    (queries : List AccessKey) (program : Program AccessKey)
    (correct : Correct known initial queries program)
    (compatible : ∀ key ∈ known, oracle key = initial key) :
    (∑ key ∈ queries.toFinset \ known, cost key) ≤
      ((execute oracle program).2.map cost).sum := by
  have included : queries.toFinset \ known ⊆ (execute oracle program).2.toFinset := by
    intro key member
    simp only [Finset.mem_sdiff, List.mem_toFinset] at member ⊢
    exact demanded_unknown_key_is_read known initial oracle queries program correct compatible
      key member.1 member.2
  exact le_trans (Finset.sum_le_sum_of_subset included)
    (distinct_weight_le_list cost (execute oracle program).2)

end Oracle

/-- The independent cache runner attains the black-box read lower bound.
This compares the same full stamp/key queries, not merely subject terms. -/
theorem memo_computation_optimal (oracle : Request Stamp Key → Bool)
    (queries : List (Request Stamp Key)) (cache : Cache Stamp Key Bool)
    (program : Program (Request Stamp Key))
    (correct : Correct (cacheKeys cache) oracle queries program) :
    (requests (fun stamp key => [oracle ⟨stamp, key⟩]) queries cache).computations ≤
      (execute oracle program).2.length := by
  rw [batch_computations_exact]
  exact distinct_unknown_lower_bound (cacheKeys cache) oracle oracle queries program
    correct (fun _ _ => rfl)

theorem memo_exact_and_optimal (oracle : Request Stamp Key → Bool)
    (queries : List (Request Stamp Key)) (cache : Cache Stamp Key Bool)
    (valid : Valid (fun stamp key => [oracle ⟨stamp, key⟩]) cache)
    (program : Program (Request Stamp Key))
    (correct : Correct (cacheKeys cache) oracle queries program) :
    (requests (fun stamp key => [oracle ⟨stamp, key⟩]) queries cache).facts =
        queries.map (fun query => [oracle query]) ∧
      (requests (fun stamp key => [oracle ⟨stamp, key⟩]) queries cache).computations ≤
        (execute oracle program).2.length :=
  ⟨requests_exact _ _ _ valid, memo_computation_optimal oracle queries cache program correct⟩

theorem memo_weighted_computation_optimal (oracle : Request Stamp Key → Bool)
    (cost : Request Stamp Key → Nat) (queries : List (Request Stamp Key))
    (cache : Cache Stamp Key Bool) (program : Program (Request Stamp Key))
    (correct : Correct (cacheKeys cache) oracle queries program) :
    weightedWork (fun stamp key => [oracle ⟨stamp, key⟩]) cost queries cache ≤
      ((execute oracle program).2.map cost).sum := by
  rw [batch_weighted_work_exact]
  exact distinct_unknown_weighted_lower_bound cost (cacheKeys cache) oracle oracle
    queries program correct (fun _ _ => rfl)

namespace Controls

def repeated : Program Nat := .read 7 (fun answer => .done [answer, answer])

theorem repeated_service_is_correct : Correct ∅ (fun _ => false) [7, 7] repeated := by
  intro oracle _
  rfl

theorem repeated_service_needs_only_one_read (oracle : Nat → Bool) :
    (execute oracle repeated).2 = [7] := rfl

theorem guessing_an_unknown_answer_is_not_correct :
    ¬Correct ∅ (fun _ => false) [7] (.done [false]) := by
  intro correct
  have wrong := correct (fun _ => true) (by simp)
  simp [execute] at wrong

theorem cache_retains_every_answer_occurrence :
    (requests (fun (_stamp : Nat) (key : Nat) => [key, key])
      [⟨0, 7⟩, ⟨0, 7⟩, ⟨0, 8⟩] []).facts = [[7, 7], [7, 7], [8, 8]] ∧
    (requests (fun (_stamp : Nat) (key : Nat) => [key, key])
      [⟨0, 7⟩, ⟨0, 7⟩, ⟨0, 8⟩] []).computations = 2 := by decide

theorem unequal_queries_are_charged_once_each :
    weightedWork (fun (_stamp : Nat) (key : Nat) => [key])
      (fun query => query.key) [⟨0, 7⟩, ⟨0, 7⟩, ⟨0, 8⟩] [] = 15 := by decide

end Controls

end Mettapedia.Machines.QueryFactOptimality
