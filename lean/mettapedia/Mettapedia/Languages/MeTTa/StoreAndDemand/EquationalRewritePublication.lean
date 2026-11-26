import Mettapedia.Languages.MeTTa.StoreAndDemand.MatchRewritePublication
import Mettapedia.GSLT.Equations.OccurrenceChoices
import Mathlib.Data.List.Dedup

/-! # Coalesce raw replacements before ordered publication

On a complete read of one occurrence, several match witnesses can produce
one literal replacement. The ordered publisher already refuses competing
replacements and incomplete searches. It needs only the distinct raw
replacement values, not the original witness multiplicities. Coalescing
*inside* each occurrence's fibre does not coalesce equal stored rows.
Nothing is equated by a mutable equation view when testing this agreement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StoreAndDemand.EquationalRewritePublication

open Mettapedia.GSLT.Equations.OccurrenceChoices (Exact)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open MatchRewritePublication

variable {T : Type*}

private theorem dedup_single_iff [DecidableEq T] (answers : List T) (value : T) :
    answers.dedup = [value] ↔ Exact answers (some value) := by
  constructor
  · intro single x
    rw [← List.mem_dedup, single]
    simp [eq_comm]
  · intro exact
    apply List.perm_singleton.mp
    apply (List.perm_ext_iff_of_nodup (List.nodup_dedup _) (by simp)).mpr
    intro x
    simpa only [List.mem_dedup, List.mem_singleton, Exact, Option.some.injEq, eq_comm]
      using exact x

def coalesce (replace : Replacement) : Replacement :=
  fun use row => (replace use row).map List.dedup

theorem incomplete_iff (replace : Replacement) (use : Nat) (row : Atom) :
    coalesce replace use row = none ↔ replace use row = none := by
  cases h : replace use row <;> simp [coalesce, h]

theorem miss_iff (replace : Replacement) (use : Nat) (row : Atom) :
    coalesce replace use row = some [] ↔ replace use row = some [] := by
  cases h : replace use row <;> simp [coalesce, h, List.dedup_eq_nil]

theorem chosen_iff (replace : Replacement) (use : Nat) (row value : Atom) :
    coalesce replace use row = some [value] ↔
      ∃ alternatives, replace use row = some alternatives ∧ Exact alternatives (some value) := by
  cases h : replace use row with
  | none => simp [coalesce, h]
  | some answers => simp [coalesce, h, dedup_single_iff]

/-- The existing ordered census, with this single change to the query
producer, captures exactly the agreed raw replacement for every hit. The
fresh output occurrence allocation and store publication are still the
existing ones. -/
theorem prepared_member_iff {O : Type*} (label : O → Atom) (replace : Replacement)
    {use : Nat} {rows : List O} {items : List (O × Atom)} (item : O × Atom)
    (ready : prepare label (coalesce replace) use rows = .ok items) :
    item ∈ items ↔ ∃ (i : Nat) (h : i < rows.length) (alternatives : List Atom),
      rows[i] = item.1 ∧ replace (use + i) (label rows[i]) = some alternatives ∧
      Exact alternatives (some item.2) := by
  have spec := Census.member_iff label (coalesce replace)
    ((prepare_iff label (coalesce replace) use rows items).mp ready) item
  rw [spec]
  constructor
  · rintro ⟨i, hi, identifies, hit⟩
    obtain ⟨choices, computed, result⟩ := (chosen_iff replace _ _ _).mp hit
    exact ⟨i, hi, choices, identifies, computed, result⟩
  · rintro ⟨i, hi, choices, identifies, computed, result⟩
    exact ⟨i, hi, identifies, (chosen_iff replace _ _ _).mpr ⟨choices, computed, result⟩⟩

end Mettapedia.Languages.MeTTa.StoreAndDemand.EquationalRewritePublication
