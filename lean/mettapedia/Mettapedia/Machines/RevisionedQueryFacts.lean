import Mettapedia.Machines.RevisionDependencySet
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Reusing revision-scoped, mode-specific pure facts

The cache stores ordered immutable facts, not live substitutions, query
continuations or arbitrary classifier answers. Its semantic input is a stamp
and a key. A stamp includes the owner and every governing revision; the key
includes the actual inquiry mode and all relevant instantiated operands.
`Factorization` states this admission obligation against an independently
supplied pure service. It is not automatically true for a relational service.

Cache lookup/fill and repeated-request execution are independent algorithms.
Their transparency, validity and miss counts are proved below. The count is
of service computations, not lookup work, allocation or elapsed time. An
answer list retains order and duplicate occurrences. A per-call materializer
can produce fresh binding payloads from the retained facts.

Dependency-aware reuse is motivated by rustc's pure query system and
Nominal Adapton's from-scratch consistency. This cache proves its own
transparency; it does not import those systems' semantics or an incremental
change-propagation algorithm.
See https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html
and https://arxiv.org/abs/1503.07792.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RevisionedQueryFacts

variable {Stamp Key Fact Query : Type}
variable [DecidableEq Stamp] [DecidableEq Key]

structure Entry (Stamp Key Fact : Type) where
  stamp : Stamp
  key : Key
  facts : List Fact
  deriving Repr

abbrev Cache (Stamp Key Fact : Type) := List (Entry Stamp Key Fact)

def lookup (stamp : Stamp) (key : Key) : Cache Stamp Key Fact → Option (List Fact)
  | [] => none
  | entry :: rest =>
      if entry.stamp = stamp ∧ entry.key = key then some entry.facts
      else lookup stamp key rest

def Valid (compute : Stamp → Key → List Fact) (cache : Cache Stamp Key Fact) : Prop :=
  ∀ entry ∈ cache, entry.facts = compute entry.stamp entry.key

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem valid_nil (compute : Stamp → Key → List Fact) : Valid compute [] := by
  simp [Valid]

theorem lookup_sound (compute : Stamp → Key → List Fact)
    (cache : Cache Stamp Key Fact) (valid : Valid compute cache)
    (stamp : Stamp) (key : Key) {facts : List Fact}
    (found : lookup stamp key cache = some facts) :
    facts = compute stamp key := by
  induction cache with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
      simp only [lookup] at found
      split at found
      · rename_i same
        have here := valid entry (by simp)
        have eqFacts := Option.some.inj found
        rw [← eqFacts, here, same.1, same.2]
      · exact ih (fun item member => valid item (by simp [member])) found

structure Request (Stamp Key : Type) where
  stamp : Stamp
  key : Key
  deriving DecidableEq, Repr

structure Result (Stamp Key Fact : Type) where
  facts : List Fact
  cache : Cache Stamp Key Fact
  computations : Nat

def request (compute : Stamp → Key → List Fact)
    (query : Request Stamp Key) (cache : Cache Stamp Key Fact) :
    Result Stamp Key Fact :=
  match lookup query.stamp query.key cache with
  | some facts => ⟨facts, cache, 0⟩
  | none =>
      let facts := compute query.stamp query.key
      ⟨facts, ⟨query.stamp, query.key, facts⟩ :: cache, 1⟩

theorem request_exact (compute : Stamp → Key → List Fact)
    (query : Request Stamp Key) (cache : Cache Stamp Key Fact)
    (valid : Valid compute cache) :
    (request compute query cache).facts = compute query.stamp query.key := by
  cases found : lookup query.stamp query.key cache with
  | none => simp [request, found]
  | some facts =>
      simpa [request, found] using
        lookup_sound compute cache valid query.stamp query.key found

theorem request_valid (compute : Stamp → Key → List Fact)
    (query : Request Stamp Key) (cache : Cache Stamp Key Fact)
    (valid : Valid compute cache) :
    Valid compute (request compute query cache).cache := by
  cases found : lookup query.stamp query.key cache with
  | none =>
      simp only [request, found, Valid, List.mem_cons]
      intro entry member
      rcases member with rfl | member
      · rfl
      · exact valid entry member
  | some facts => simpa [request, found] using valid

theorem request_installs (compute : Stamp → Key → List Fact)
    (query : Request Stamp Key) (cache : Cache Stamp Key Fact)
    (valid : Valid compute cache) :
    lookup query.stamp query.key (request compute query cache).cache =
      some (compute query.stamp query.key) := by
  cases found : lookup query.stamp query.key cache with
  | none => simp [request, found, lookup]
  | some facts =>
      have same := lookup_sound compute cache valid query.stamp query.key found
      simpa [request, found] using found.trans (congrArg some same)

theorem request_work_le_one (compute : Stamp → Key → List Fact)
    (query : Request Stamp Key) (cache : Cache Stamp Key Fact) :
    (request compute query cache).computations ≤ 1 := by
  cases found : lookup query.stamp query.key cache <;> simp [request, found]

theorem hit_skips_computation (compute : Stamp → Key → List Fact)
    (query : Request Stamp Key) (cache : Cache Stamp Key Fact)
    (hit : (lookup query.stamp query.key cache).isSome) :
    (request compute query cache).computations = 0 := by
  cases found : lookup query.stamp query.key cache <;> simp_all [request]

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem valid_take (compute : Stamp → Key → List Fact)
    (cache : Cache Stamp Key Fact) (valid : Valid compute cache) (capacity : Nat) :
    Valid compute (cache.take capacity) := by
  intro entry member
  exact valid entry (List.mem_of_mem_take member)

/-- An optional bounded retention policy changes performance, not answers.
Returned facts are retained separately from the entries that may be evicted. -/
def boundedRequest (capacity : Nat) (compute : Stamp → Key → List Fact)
    (query : Request Stamp Key) (cache : Cache Stamp Key Fact) : Result Stamp Key Fact :=
  let result := request compute query cache
  { result with cache := result.cache.take capacity }

theorem bounded_request_exact (capacity : Nat) (compute : Stamp → Key → List Fact)
    (query : Request Stamp Key) (cache : Cache Stamp Key Fact) (valid : Valid compute cache) :
    (boundedRequest capacity compute query cache).facts = compute query.stamp query.key ∧
      Valid compute (boundedRequest capacity compute query cache).cache ∧
      (boundedRequest capacity compute query cache).cache.length ≤ capacity := by
  refine ⟨request_exact compute query cache valid,
    valid_take compute _ (request_valid compute query cache valid) capacity, ?_⟩
  simp [boundedRequest, List.length_take]

structure Batch (Stamp Key Fact : Type) where
  facts : List (List Fact)
  cache : Cache Stamp Key Fact
  computations : Nat

def requests (compute : Stamp → Key → List Fact) :
    List (Request Stamp Key) → Cache Stamp Key Fact → Batch Stamp Key Fact
  | [], cache => ⟨[], cache, 0⟩
  | query :: queries, cache =>
      let here := request compute query cache
      let later := requests compute queries here.cache
      ⟨here.facts :: later.facts, later.cache, here.computations + later.computations⟩

theorem requests_exact (compute : Stamp → Key → List Fact)
    (queries : List (Request Stamp Key)) (cache : Cache Stamp Key Fact)
    (valid : Valid compute cache) :
    (requests compute queries cache).facts =
      queries.map (fun query => compute query.stamp query.key) := by
  induction queries generalizing cache with
  | nil => rfl
  | cons query queries ih =>
      simp only [requests, List.map_cons]
      rw [request_exact compute query cache valid,
        ih _ (request_valid compute query cache valid)]

theorem requests_valid (compute : Stamp → Key → List Fact)
    (queries : List (Request Stamp Key)) (cache : Cache Stamp Key Fact)
    (valid : Valid compute cache) : Valid compute (requests compute queries cache).cache := by
  induction queries generalizing cache with
  | nil => exact valid
  | cons query queries ih => exact ih _ (request_valid compute query cache valid)

theorem requests_work_le_length (compute : Stamp → Key → List Fact)
    (queries : List (Request Stamp Key)) (cache : Cache Stamp Key Fact) :
    (requests compute queries cache).computations ≤ queries.length := by
  induction queries generalizing cache with
  | nil => exact Nat.le_refl 0
  | cons query queries ih =>
      simpa only [requests, List.length_cons, Nat.add_comm 1] using
        Nat.add_le_add (request_work_le_one compute query cache) (ih _)

theorem repeated_hit_work_zero (compute : Stamp → Key → List Fact)
    (query : Request Stamp Key) (count : Nat) (cache : Cache Stamp Key Fact)
    (hit : (lookup query.stamp query.key cache).isSome) :
    (requests compute (List.replicate count query) cache).computations = 0 := by
  induction count generalizing cache with
  | zero => rfl
  | succ count ih =>
      cases found : lookup query.stamp query.key cache with
      | none => simp [found] at hit
      | some facts =>
          simp only [List.replicate_succ, requests, request, found]
          simpa using ih cache hit

theorem repeated_cold_work_one (compute : Stamp → Key → List Fact)
    (query : Request Stamp Key) (count : Nat) :
    (requests compute (List.replicate (count + 1) query) []).computations = 1 := by
  simp only [List.replicate_succ, requests]
  have hit := request_installs compute query [] (valid_nil compute)
  have zero := repeated_hit_work_zero compute query count
    (request compute query []).cache (by simp [hit])
  rw [zero]
  rfl

/-- These primitive service laws must be established for an admitted family.
No factorization is asserted for effects, authored classifiers or unkeyed
incoming bindings. Materialization below remains per invocation. -/
structure Factorization (Context Query Stamp Key Fact : Type) where
  stamp : Context → Query → Stamp
  key : Context → Query → Key
  compute : Stamp → Key → List Fact
  service : Context → Query → List Fact
  correct : ∀ context query,
    service context query = compute (stamp context query) (key context query)

theorem materialized_exact {Context Answer : Type}
    (admission : Factorization Context Query Stamp Key Fact)
    (context : Context) (query : Query) (cache : Cache Stamp Key Fact)
    (valid : Valid admission.compute cache)
    (materialize : Query → List Fact → List Answer) :
    materialize query (request admission.compute
        ⟨admission.stamp context query, admission.key context query⟩ cache).facts =
      materialize query (admission.service context query) := by
  rw [request_exact _ _ _ valid, admission.correct]

omit [DecidableEq Stamp] [DecidableEq Key] in
/-- It is impossible to factor two different answers through the same key.
This detects omissions of modes, requirements, owners or revision evidence. -/
theorem incomplete_key_impossible {Context : Type}
    (admission : Factorization Context Query Stamp Key Fact)
    (firstContext secondContext : Context) (first second : Query)
    (sameStamp : admission.stamp firstContext first = admission.stamp secondContext second)
    (sameKey : admission.key firstContext first = admission.key secondContext second) :
    admission.service firstContext first = admission.service secondContext second := by
  rw [admission.correct, admission.correct, sameStamp, sameKey]

section Dependencies

variable {Store Revision : Type} [DecidableEq Store]

/-- Whole-store read tokens also cover absence of declarations and classifiers.
An empty answer must not be stamped with an empty dependency set merely
because no positive occurrence was found. -/
def footprint (environment : RevisionEnvironment Store Revision)
    (support : List Store) : List (StoreReadToken Store Revision) :=
  support.map (fun store => ⟨store, environment.current store⟩)

omit [DecidableEq Stamp] [DecidableEq Key] [DecidableEq Store] in
theorem footprint_exact (first second : RevisionEnvironment Store Revision)
    (support : List Store) :
    footprint first support = footprint second support ↔
      ∀ store ∈ support, first.current store = second.current store := by
  induction support with
  | nil => simp [footprint]
  | cons store support ih =>
      simp only [footprint, List.map_cons, List.cons.injEq, StoreReadToken.mk.injEq,
        true_and] at *
      rw [ih]
      simp only [List.mem_cons, forall_eq_or_imp]

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem unrelated_update_keeps_footprint
    (environment : RevisionEnvironment Store Revision) (support : List Store)
    (changed : Store) (revision : Revision) (outside : changed ∉ support) :
    footprint (environment.update changed revision) support = footprint environment support := by
  apply (footprint_exact _ _ _).mpr
  intro observed member
  have different : observed ≠ changed := fun equal => outside (equal ▸ member)
  simp [RevisionEnvironment.update, different]

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem governing_update_changes_footprint
    (environment : RevisionEnvironment Store Revision) (support : List Store)
    (changed : Store) (revision : Revision) (member : changed ∈ support)
    (different : revision ≠ environment.current changed) :
    footprint (environment.update changed revision) support ≠ footprint environment support := by
  intro same
  have equality := (footprint_exact _ _ _).mp same changed member
  simp [RevisionEnvironment.update] at equality
  exact different equality

omit [DecidableEq Stamp] [DecidableEq Key] [DecidableEq Store] in
theorem footprint_union (environment : RevisionEnvironment Store Revision)
    (first later : List Store) :
    footprint environment (first ++ later) =
      footprint environment first ++ footprint environment later := by
  simp [footprint]

end Dependencies

namespace Controls

inductive Mode where | infer | check deriving DecidableEq, Repr
structure ScopeStamp where
  owner : Nat
  declarations : Nat
  classifiers : Nat
  profile : Nat
  deriving DecidableEq, Repr
structure ModeKey where
  mode : Mode
  subject : Nat
  required : Option Nat
  deriving DecidableEq, Repr

def compute (stamp : ScopeStamp) (key : ModeKey) : List Nat :=
  if stamp.classifiers > 0 then [stamp.owner, stamp.owner]
  else match key.mode, key.required with
    | .infer, _ => [0]
    | .check, some required => [required + stamp.declarations]
    | .check, none => [0]

def initial : ScopeStamp := ⟨1, 0, 0, 0⟩
def fresh : ModeKey := ⟨.infer, 6, none⟩
def bound : ModeKey := ⟨.check, 6, some 7⟩

theorem mode_changes_answers : compute initial fresh ≠ compute initial bound := by decide
theorem term_only_key_loses_bound_answers : fresh.subject = bound.subject ∧
    compute initial fresh ≠ compute initial bound := ⟨rfl, mode_changes_answers⟩

theorem duplicate_facts_are_not_deduplicated :
    (requests compute [⟨{initial with classifiers := 1}, fresh⟩,
      ⟨{initial with classifiers := 1}, fresh⟩] []).facts = [[1, 1], [1, 1]] := by decide

theorem repeated_checks_compute_once :
    (requests compute (List.replicate 100 ⟨initial, bound⟩) []).computations = 1 :=
  repeated_cold_work_one compute ⟨initial, bound⟩ 99

theorem declaration_change_recomputes :
    (requests compute [⟨initial, bound⟩, ⟨{initial with declarations := 1}, bound⟩]
      []).computations = 2 := by decide

theorem owner_change_does_not_reuse_other_space :
    (requests compute [⟨initial, fresh⟩, ⟨{initial with owner := 2}, fresh⟩]
      []).computations = 2 := by decide

end Controls

end Mettapedia.Machines.RevisionedQueryFacts
