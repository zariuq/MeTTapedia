import Mettapedia.GSLT.Dynamics.CacheCoherence
import Mettapedia.GSLT.LanguageDef.ComputationContract

/-!
# Scoped cache coherence for reused computed evidence

A runtime cache stores answers under keys, not under authored queries. A key
names its query only in an environment: a live table handle denotes the rows
it currently holds. Reading every cached key in an environment gives a memo of
authored queries, and the cache is **authorized** there when that memo
satisfies the contract of reused computed evidence (`Contract.Holds`). The
authorized-result predicate stays the authored relation; the cache's own
bookkeeping never replaces it.

* Recording a successful run and replaying a related answer keep the cache
  authorized, through the contract's own step preservation
  (`authorized_record`, `authorized_replay`).
* A transition that keeps the readings every cached key consults keeps the
  cache authorized (`authorized_of_readings`); clearing is always authorized
  (`authorized_nil`). Together: a cache cleared before every epoch, recorded
  from runs and frozen within the epoch, stays authorized
  (`authorized_of_reflTransGen`).
* A lookup by key returns an answer related to the query the key denotes now
  (`lookupKey_authorized`).
* Refusals need their own evidence: a refused run, never an exhausted one
  (`refusal_of_applies`, `answerable_has_no_refusal`, `runs_not_exhausted`).

This is a statement about the engine's semantics and about cache models. It
does not cover any C implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.CacheCoherenceContract

open Mettapedia.Machines
open Mettapedia.GSLT.Dynamics.CacheCoherence
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.GSLT.LanguageDef.Authored.Contract
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

variable {Query Answer Key Dep Reading : Type}

/-- A runtime cache entry: a key, an answer and its provenance. -/
structure KeyedEntry (Key Answer : Type) where
  key : Key
  answer : Answer
  provenance : Provenance

/-- Read every cached key as the authored query it denotes in an
environment. -/
def resolve (scope : RevisionEnvironment Dep Reading → Key → Query)
    (live : RevisionEnvironment Dep Reading) (cache : List (KeyedEntry Key Answer)) :
    List (Entry Query Answer) :=
  cache.map fun entry => ⟨scope live entry.key, entry.answer, entry.provenance⟩

/-- **The cache is authorized** in an environment when the contract of reused
computed evidence holds for its reading there. -/
def Authorized (C : AuthoredComputation Query Answer)
    (scope : RevisionEnvironment Dep Reading → Key → Query)
    (live : RevisionEnvironment Dep Reading) (cache : List (KeyedEntry Key Answer)) : Prop :=
  Holds C (resolve scope live cache)

variable (C : AuthoredComputation Query Answer)

theorem authorized_nil (scope : RevisionEnvironment Dep Reading → Key → Query)
    (live : RevisionEnvironment Dep Reading) : Authorized C scope live ([] : List (KeyedEntry Key Answer)) :=
  holds_nil C

/-- Recording a successful run keeps the cache authorized. -/
theorem authorized_record {scope : RevisionEnvironment Dep Reading → Key → Query}
    {live : RevisionEnvironment Dep Reading} {cache : List (KeyedEntry Key Answer)}
    (holds : Authorized C scope live cache) {key : Key} {answer : Answer} {fuel : Nat}
    (ran : C.runs ⟨scope live key, answer, fuel⟩ = true) :
    Authorized C scope live (⟨key, answer, .computed fuel⟩ :: cache) :=
  holds_preserved C (resolve scope live cache) holds
    (Step.record (resolve scope live cache) ⟨scope live key, answer, fuel⟩ ran) rfl

/-- Replaying a related answer keeps the cache authorized. -/
theorem authorized_replay {scope : RevisionEnvironment Dep Reading → Key → Query}
    {live : RevisionEnvironment Dep Reading} {cache : List (KeyedEntry Key Answer)}
    (holds : Authorized C scope live cache) {key : Key} {answer : Answer}
    (checked : C.relation (scope live key) answer) :
    Authorized C scope live (⟨key, answer, .replayed⟩ :: cache) :=
  holds_preserved C (resolve scope live cache) holds
    (Step.replay (resolve scope live cache) (scope live key) answer checked) rfl

/-- A transition that keeps the query every cached key denotes keeps the cache
authorized. -/
theorem authorized_of_scope_eq {scope : RevisionEnvironment Dep Reading → Key → Query}
    {before after : RevisionEnvironment Dep Reading} {cache : List (KeyedEntry Key Answer)}
    (same : ∀ entry ∈ cache, scope after entry.key = scope before entry.key)
    (holds : Authorized C scope before cache) : Authorized C scope after cache := by
  have resolved : resolve scope after cache = resolve scope before cache := by
    apply List.map_congr_left
    intro entry member
    rw [same entry member]
  unfold Authorized
  rw [resolved]
  exact holds

/-- **The transition-level invariant for keys.** When the query a key denotes
is determined by the readings it consults, a transition that keeps those
readings for every cached key keeps the cache authorized. -/
theorem authorized_of_readings [DecidableEq Dep]
    {scope : RevisionEnvironment Dep Reading → Key → Query}
    {consults : RevisionEnvironment Dep Reading → Key → List Dep}
    (determines : ReadsDetermine scope consults)
    {before after : RevisionEnvironment Dep Reading} {cache : List (KeyedEntry Key Answer)}
    (keeps : ∀ entry ∈ cache, RevisionEnvironment.AgreesOn
      (consults before entry.key).toFinset after before)
    (holds : Authorized C scope before cache) : Authorized C scope after cache :=
  authorized_of_scope_eq C (fun entry member => determines before after entry.key
    (keeps entry member)) holds

/-- The steps of a contract cache with epochs: clear; move to a state that
keeps the consulted readings of every key; record a successful run; replay a
related answer. -/
inductive EpochStep [DecidableEq Dep] {State : Type}
    (environment : State → RevisionEnvironment Dep Reading)
    (scope : RevisionEnvironment Dep Reading → Key → Query)
    (consults : RevisionEnvironment Dep Reading → Key → List Dep) :
    State × List (KeyedEntry Key Answer) → State × List (KeyedEntry Key Answer) → Prop
  | clear (state next : State) (cache : List (KeyedEntry Key Answer)) :
      EpochStep environment scope consults (state, cache) (next, [])
  | frozen (state next : State) (cache : List (KeyedEntry Key Answer))
      (keeps : ∀ key, RevisionEnvironment.AgreesOn
        (consults (environment state) key).toFinset (environment next) (environment state)) :
      EpochStep environment scope consults (state, cache) (next, cache)
  | record (state : State) (cache : List (KeyedEntry Key Answer)) (key : Key) (answer : Answer)
      (fuel : Nat) (ran : C.runs ⟨scope (environment state) key, answer, fuel⟩ = true) :
      EpochStep environment scope consults (state, cache)
        (state, ⟨key, answer, .computed fuel⟩ :: cache)
  | replay (state : State) (cache : List (KeyedEntry Key Answer)) (key : Key) (answer : Answer)
      (checked : C.relation (scope (environment state) key) answer) :
      EpochStep environment scope consults (state, cache) (state, ⟨key, answer, .replayed⟩ :: cache)

/-- **A cache cleared before every epoch, recorded from runs and frozen within
the epoch, stays authorized.** -/
theorem authorized_of_reflTransGen [DecidableEq Dep] {State : Type}
    {environment : State → RevisionEnvironment Dep Reading}
    {scope : RevisionEnvironment Dep Reading → Key → Query}
    {consults : RevisionEnvironment Dep Reading → Key → List Dep}
    (determines : ReadsDetermine scope consults)
    {start finish : State × List (KeyedEntry Key Answer)}
    (run : Relation.ReflTransGen (EpochStep C environment scope consults) start finish)
    (holds : Authorized C scope (environment start.1) start.2) :
    Authorized C scope (environment finish.1) finish.2 := by
  induction run with
  | refl => exact holds
  | tail _ moves ih =>
      cases moves with
      | clear state next cache => exact authorized_nil C scope _
      | frozen state next cache keeps =>
          exact authorized_of_readings C determines (fun entry _ => keeps entry.key) ih
      | record state cache key answer fuel ran => exact authorized_record C ih ran
      | replay state cache key answer checked => exact authorized_replay C ih checked

/-- Lookup by key: the first entry with that key. -/
def lookupKey [DecidableEq Key] : List (KeyedEntry Key Answer) → Key → Option Answer
  | [], _ => none
  | entry :: rest, key => if entry.key = key then some entry.answer else lookupKey rest key

/-- **A lookup by key answers the query the key denotes now.** -/
theorem lookupKey_authorized [DecidableEq Key]
    {scope : RevisionEnvironment Dep Reading → Key → Query}
    {live : RevisionEnvironment Dep Reading} :
    ∀ {cache : List (KeyedEntry Key Answer)} {key : Key} {answer : Answer},
      Authorized C scope live cache → lookupKey cache key = some answer →
        C.relation (scope live key) answer
  | [], _, _, _, found => by cases found
  | entry :: rest, key, answer, holds, found => by
      unfold lookupKey at found
      split at found
      next same =>
        cases found
        have first := (holds _ List.mem_cons_self).1
        rw [← same]
        exact first
      next =>
        exact lookupKey_authorized
          (fun other member => holds other (List.mem_cons_of_mem _ member)) found

/-! ## Refusals and exhaustion -/

/-- A refusal is evidenced by a run returning the encoded refusal. -/
theorem refusal_of_applies {query : Query}
    (refused : Applies C.program C.host C.head (C.encodeQuery query) (C.encodeAnswer none)) :
    ¬ ∃ answer, C.relation query answer :=
  (C.refuses query).mp refused

/-- An answerable query has no refusal evidence at any fuel. -/
theorem answerable_has_no_refusal {query : Query} {answer : Answer}
    (related : C.relation query answer) :
    ¬ Applies C.program C.host C.head (C.encodeQuery query) (C.encodeAnswer none) :=
  fun refused => (C.refuses query).mp refused ⟨answer, related⟩

/-- A successful run is never an exhausted one. -/
theorem runs_not_exhausted {leaf : Leaf Query Answer} (ran : C.runs leaf = true) :
    apply C.program C.host leaf.fuel C.head (C.encodeQuery leaf.query) ≠ .exhausted := by
  rw [(C.runs_eq_true_iff leaf).mp ran]
  intro impossible
  cases impossible

#print axioms authorized_record
#print axioms authorized_replay
#print axioms authorized_of_readings
#print axioms authorized_of_reflTransGen
#print axioms lookupKey_authorized
#print axioms answerable_has_no_refusal
#print axioms runs_not_exhausted

end Mettapedia.GSLT.Dynamics.CacheCoherenceContract
