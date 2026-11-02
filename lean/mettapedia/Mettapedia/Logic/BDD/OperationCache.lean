import Mettapedia.Logic.BDD.Canonical

/-!
# Canonical Boolean-operation memoization

Keys contain all four truth-table bits and both reduced ordered input diagrams.
The semantic key law follows from diagram canonicity. Cache misses execute the
existing BDD apply algorithm; hits reuse its previously certified result.

The ledger counts apply invocations, not lookup comparisons or elapsed time.
This reference uses lists and tree-valued keys; it does not claim physical
hash-consing, bounded native memory or an efficient recursive apply cache.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.OperationCache

open StatePredicates

structure BooleanOperator where
  ff : Bool
  ft : Bool
  tf : Bool
  tt : Bool
  deriving DecidableEq, Repr

def BooleanOperator.eval (operator : BooleanOperator) : Bool → Bool → Bool
  | false, false => operator.ff
  | false, true => operator.ft
  | true, false => operator.tf
  | true, true => operator.tt

def BooleanOperator.ofFunction (operation : Bool → Bool → Bool) : BooleanOperator :=
  ⟨operation false false, operation false true, operation true false, operation true true⟩

theorem operator_encoding_exact (operation : Bool → Bool → Bool) :
    (BooleanOperator.ofFunction operation).eval = operation := by
  funext left right
  cases left <;> cases right <;> rfl

structure Key (n : Nat) where
  operator : BooleanOperator
  left : Diagram n
  right : Diagram n
  deriving DecidableEq

def Key.compute {n : Nat} (key : Key n) : Diagram n :=
  ⟨apply key.operator.eval key.left.val key.right.val,
    apply_ordered _ _ _ none key.left.property key.right.property⟩

theorem compute_eval {n : Nat} (key : Key n) (state : State n) :
    key.compute.val.eval state = key.operator.eval (key.left.val.eval state) (key.right.val.eval state) :=
  apply_eval _ _ _ _

theorem key_ext {n : Nat} (first second : Key n)
    (operator : first.operator = second.operator)
    (left : denote first.left = denote second.left) (right : denote first.right = denote second.right) :
    first = second := by
  have leftEq := (Canonical.diagram_eq_iff_denote first.left second.left).mpr left
  have rightEq := (Canonical.diagram_eq_iff_denote first.right second.right).mpr right
  cases first
  cases second
  simp_all

structure Entry (n : Nat) where
  key : Key n
  value : Diagram n

abbrev Cache (n : Nat) := List (Entry n)

def Valid {n : Nat} (cache : Cache n) : Prop := ∀ entry ∈ cache, entry.value = entry.key.compute

def lookup {n : Nat} (key : Key n) : Cache n → Option (Diagram n)
  | [] => none
  | entry :: rest => if entry.key = key then some entry.value else lookup key rest

theorem lookup_exact {n : Nat} (cache : Cache n) (valid : Valid cache) (key : Key n)
    (value : Diagram n) (found : lookup key cache = some value) : value = key.compute := by
  induction cache with
  | nil => cases found
  | cons entry rest ih =>
      simp only [lookup] at found
      split at found
      next same =>
        cases found
        rw [valid entry (by simp), same]
      next => exact ih (fun e present => valid e (by simp [present])) found

structure Reply (n : Nat) where
  value : Diagram n
  cache : Cache n
  applies : Nat

def execute {n : Nat} (cache : Cache n) (key : Key n) : Reply n :=
  match lookup key cache with
  | some value => ⟨value, cache, 0⟩
  | none => let value := key.compute; ⟨value, ⟨key, value⟩ :: cache, 1⟩

theorem execute_exact {n : Nat} (cache : Cache n) (valid : Valid cache) (key : Key n) :
    (execute cache key).value = key.compute := by
  cases found : lookup key cache with
  | none => simp [execute, found]
  | some value => simpa [execute, found] using lookup_exact cache valid key value found

theorem execute_valid {n : Nat} (cache : Cache n) (valid : Valid cache) (key : Key n) :
    Valid (execute cache key).cache := by
  cases found : lookup key cache with
  | none =>
      intro entry member
      simp only [execute, found, List.mem_cons] at member
      rcases member with rfl | present
      · rfl
      · exact valid entry present
  | some value => simpa [execute, found] using valid

theorem execute_remembers {n : Nat} (cache : Cache n) (key : Key n) :
    lookup key (execute cache key).cache = some (execute cache key).value := by
  cases found : lookup key cache <;> simp [execute, found, lookup]

/-- The second invocation with the same complete key does no new apply. -/
theorem warm_hit {n : Nat} (cache : Cache n) (key : Key n) :
    (execute (execute cache key).cache key).applies = 0 ∧
      (execute (execute cache key).cache key).value = (execute cache key).value := by
  have warmed : execute (execute cache key).cache key =
      ⟨(execute cache key).value, (execute cache key).cache, 0⟩ := by
    rw [execute, execute_remembers]
  rw [warmed]
  exact ⟨rfl, rfl⟩

theorem one_apply_at_most {n : Nat} (cache : Cache n) (key : Key n) : (execute cache key).applies ≤ 1 := by
  cases found : lookup key cache <;> simp [execute, found]

theorem semantic_input_equality_reuses_key {n : Nat} (cache : Cache n) (first second : Key n)
    (operator : first.operator = second.operator)
    (left : denote first.left = denote second.left) (right : denote first.right = denote second.right) :
    (execute (execute cache first).cache second).applies = 0 := by
  rw [← key_ext first second operator left right]
  exact (warm_hit cache first).1

structure CertifiedCache (n : Nat) where
  entries : Cache n
  valid : Valid entries

def CertifiedCache.empty (n : Nat) : CertifiedCache n := ⟨[], by simp [Valid]⟩

def CertifiedCache.perform {n : Nat} (cache : CertifiedCache n) (key : Key n) :
    Diagram n × CertifiedCache n × Nat :=
  let result := execute cache.entries key
  (result.value, ⟨result.cache, execute_valid cache.entries cache.valid key⟩, result.applies)

theorem certified_perform_eval {n : Nat} (cache : CertifiedCache n) (key : Key n) (state : State n) :
    (cache.perform key).1.val.eval state =
      key.operator.eval (key.left.val.eval state) (key.right.val.eval state) := by
  change (execute cache.entries key).value.val.eval state = _
  rw [execute_exact cache.entries cache.valid, compute_eval]

namespace Controls

def conjunction : Key 1 := ⟨BooleanOperator.ofFunction (· && ·), bit 0, truth 1⟩
def disjunction : Key 1 := ⟨BooleanOperator.ofFunction (· || ·), bit 0, truth 1⟩

theorem operator_identity_is_required :
    conjunction.compute.val.eval (fun _ => false) = false ∧
      disjunction.compute.val.eval (fun _ => false) = true := by
  constructor <;> rw [compute_eval] <;> rfl

theorem corrupted_cache_is_not_valid : ¬Valid ([⟨disjunction, falsity 1⟩] : Cache 1) := by
  intro valid
  have wrong := congrArg (fun d : Diagram 1 => d.val.eval (fun _ => false))
    (valid ⟨disjunction, falsity 1⟩ (by simp))
  have truth := operator_identity_is_required.2
  change false = disjunction.compute.val.eval (fun _ => false) at wrong
  rw [truth] at wrong
  cases wrong

theorem cold_then_warm :
    (execute [] conjunction).applies = 1 ∧
      (execute (execute [] conjunction).cache conjunction).applies = 0 :=
  ⟨rfl, (warm_hit [] conjunction).1⟩

end Controls

end Mettapedia.Logic.BDDCore.OperationCache
