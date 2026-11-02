import Mettapedia.Machines.RelationOccurrenceBounds
import Mathlib.Data.Fintype.Card

/-!
# A sharper counter bound for unique binary relations

With n numbered IDs, an ID occurs in at most n first columns and n second
columns of a set of pairs. Thus the hold counter is at most 2*n, regardless
of the number of pairs. Together with the numbering table's load bound this
provides word capacity without a per-insertion count guard. Higher arities
do not inherit this binary bound.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationBinaryUseBound

open ArenaHeldResources (logHolds)
open RelationColumnOwnership
open RelationWordOwnership

variable {n : Nat}

def columns (pairs : List (Fin n × Fin n)) : List (List (Fin n)) :=
  pairs.map (fun pair => [pair.1, pair.2])

theorem uses_split (pairs : List (Fin n × Fin n)) (id : Fin n) :
    logHolds (columns pairs) id =
      (pairs.filter (fun pair => decide (pair.1 = id))).length +
      (pairs.filter (fun pair => decide (pair.2 = id))).length := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      by_cases first : pair.1 = id <;> by_cases second : pair.2 = id <;>
        simp [columns, logHolds, first, second] at ih ⊢ <;> omega

theorem first_column_bound (pairs : List (Fin n × Fin n)) (distinct : pairs.Nodup) (id : Fin n) :
    (pairs.filter (fun pair => decide (pair.1 = id))).length ≤ n := by
  have projected : ((pairs.filter (fun pair => decide (pair.1 = id))).map Prod.snd).Nodup := by
    apply List.Nodup.map_on ?_ (distinct.filter _)
    intro first firstMember second secondMember same
    have firstKey : first.1 = id := by simpa using (List.mem_filter.mp firstMember).2
    have secondKey : second.1 = id := by simpa using (List.mem_filter.mp secondMember).2
    exact Prod.ext (firstKey.trans secondKey.symm) same
  simpa using projected.length_le_card

theorem second_column_bound (pairs : List (Fin n × Fin n)) (distinct : pairs.Nodup) (id : Fin n) :
    (pairs.filter (fun pair => decide (pair.2 = id))).length ≤ n := by
  have projected : ((pairs.filter (fun pair => decide (pair.2 = id))).map Prod.fst).Nodup := by
    apply List.Nodup.map_on ?_ (distinct.filter _)
    intro first firstMember second secondMember same
    have firstKey : first.2 = id := by simpa using (List.mem_filter.mp firstMember).2
    have secondKey : second.2 = id := by simpa using (List.mem_filter.mp secondMember).2
    exact Prod.ext same (firstKey.trans secondKey.symm)
  simpa using projected.length_le_card

theorem uses_le_twice_numbers (pairs : List (Fin n × Fin n)) (distinct : pairs.Nodup) (id : Fin n) :
    logHolds (columns pairs) id ≤ 2 * n := by
  rw [uses_split]
  have first := first_column_bound pairs distinct id
  have second := second_column_bound pairs distinct id
  omega

theorem hash_load_implies_range (numbers slots : Nat)
    (slotBound : slots ≤ 2147483648) (load : 4 * numbers ≤ 3 * slots) :
    numbers < 2147483648 := by omega

theorem unique_binary_insert_fits (state : Words (Fin n)) (pairs : List (Fin n × Fin n))
    (pair : Fin n × Fin n) (distinct : pairs.Nodup) (fresh : pair ∉ pairs)
    (valid : (⟨columns pairs, interpret state⟩ : State (Fin n)).Valid)
    (range : n < 2147483648) : FitsAddition state [pair.1, pair.2] := by
  intro id
  have afterDistinct : (pair :: pairs).Nodup := List.nodup_cons.mpr ⟨fresh, distinct⟩
  have bound := uses_le_twice_numbers (pair :: pairs) afterDistinct id
  have represented := valid.2 id
  change (state.uses id).toNat = logHolds (columns pairs) id at represented
  change (state.uses id).toNat + [pair.1, pair.2].count id < modulus
  simp only [columns, List.map_cons, logHolds, List.sum_cons] at bound represented
  unfold modulus
  omega

theorem binary_insert_word_admission (state : Words (Fin n)) (pairs : List (Fin n × Fin n))
    (pair : Fin n × Fin n) (distinct : pairs.Nodup) (fresh : pair ∉ pairs)
    (valid : (⟨columns pairs, interpret state⟩ : State (Fin n)).Valid)
    (slots : Nat) (slotBound : slots ≤ 2147483648) (load : 4 * n ≤ 3 * slots) :
    admitWords state [pair.1, pair.2] = true :=
  (admitWords_iff state _).mpr
    (unique_binary_insert_fits state pairs pair distinct fresh valid (hash_load_implies_range n slots slotBound load))

namespace Controls

def allPairs : List (Fin 2 × Fin 2) := [(0, 0), (0, 1), (1, 0), (1, 1)]

theorem binary_bound_is_attained :
    allPairs.Nodup ∧ logHolds (columns allPairs) 0 = 2 * 2 := by decide

theorem bags_do_not_have_the_set_bound :
    logHolds (columns ([(0, 0), (0, 0)] : List (Fin 1 × Fin 1))) 0 > 2 * 1 := by decide

end Controls
end Mettapedia.Machines.RelationBinaryUseBound
