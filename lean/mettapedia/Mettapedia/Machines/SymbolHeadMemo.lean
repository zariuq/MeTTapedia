import Mettapedia.Machines.SymbolTableHeadCache
import Mettapedia.Machines.BoundedAdmissionCache

/-!
# Exact-key memoization of scoped head classifications

The memo stores matching family indices for one compiled symbol-table cache.
Its 16 direct-mapped banks use the existing bounded-cache implementation. A
hash chooses storage; the complete head ID still decides a hit. Rebuilding a
symbol-table cache resets these banks, so no classification from an old ID
interpretation is reused under a new one.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SymbolHeadMemo

open SymbolTableHeadCache BoundedAdmissionCache
variable {k : Nat} {Name Query : Type} [DecidableEq Name]

def indices (cache : Cache k) (head : Nat) : List (Fin k) :=
  (List.finRange k).filter fun index => decide (head = cache.ids index)

def compute (cache : Cache k) (_ : Unit) (head : Nat) : List (Fin k) := indices cache head

def bank (_ : Unit) (head : Nat) : Fin 16 := ⟨head % 16, Nat.mod_lt _ (by decide)⟩

abbrev Memo (k : Nat) := Banks 16 Unit Nat (Fin k)

def empty : Memo k := fun _ => []

def lookup (cache : Cache k) (permits : Fin k → Query → Bool) (memo : Memo k)
    (head : Nat) (question : Query) : Bool :=
  match (probe () head (memo (bank () head))).1 with
  | none => recognized cache permits head question
  | some found => found.any (fun index => permits index question)

def retainHead (cache : Cache k) (memo : Memo k) (head : Nat) : Memo k :=
  publish bank 1 0 true (compute cache) () head memo

theorem empty_good (cache : Cache k) : ValidBanks (compute cache) (empty : Memo k) :=
  empty_valid (compute cache)

theorem retain_good (cache : Cache k) (memo : Memo k) (good : ValidBanks (compute cache) memo)
    (head : Nat) : ValidBanks (compute cache) (retainHead cache memo head) :=
  publish_valid bank 1 0 true (compute cache) () head memo good

theorem retain_bounded (cache : Cache k) (memo : Memo k) (bounded : Bounded 1 memo)
    (head : Nat) : Bounded 1 (retainHead cache memo head) :=
  publish_bounded bank 1 0 true (compute cache) () head memo bounded

theorem indices_recognize (cache : Cache k) (permits : Fin k → Query → Bool)
    (head : Nat) (question : Query) :
    (indices cache head).any (fun index => permits index question) = recognized cache permits head question := by
  simp [indices, recognized, List.any_filter]

theorem lookup_exact (cache : Cache k) (permits : Fin k → Query → Bool)
    (memo : Memo k) (good : ValidBanks (compute cache) memo) (head : Nat) (question : Query) :
    lookup cache permits memo head question = recognized cache permits head question := by
  cases found : (probe () head (memo (bank () head))).1 with
  | none => simp [lookup, found]
  | some matched =>
      have exact := hashed_hit_exact bank (compute cache) memo good () head found
      simp only [lookup, found]
      rw [exact]
      exact indices_recognize cache permits head question

theorem scoped_lookup_exact (table : Table Name) (names : Fin k → Name)
    (permits : Fin k → Query → Bool) (cache : Cache k) (compiled : Good table names cache)
    (memo : Memo k) (valid : ValidBanks (compute cache) memo) (head : Nat) (question : Query) :
    lookup cache permits memo head question = source table names permits head question :=
  (lookup_exact cache permits memo valid head question).trans
    (recognized_exact table names permits cache compiled head question)

namespace Controls

def compiled : Cache 1 := ⟨(3, 1), fun _ => 1⟩
def permits : Fin 1 → Nat → Bool := fun _ arity => arity == 2
def cached : Memo 1 := retainHead compiled empty 1

theorem colliding_head_is_not_the_cached_head :
    bank () 1 = bank () 17 ∧
      (probe () 17 (cached (bank () 17))).1 = none ∧
      lookup compiled permits cached 17 2 = false ∧
      lookup compiled permits cached 1 2 = true := by decide

theorem wrong_arity_does_not_prove_an_absent_name :
    lookup compiled permits cached 1 3 = false ∧
      lookup compiled permits cached 1 2 = true := by decide

end Controls

end Mettapedia.Machines.SymbolHeadMemo
