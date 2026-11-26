import Mettapedia.GSLT.Contracts.ScopedAliasDispatch

/-! Maintaining materialized keys when a scoped equation is added. Occurrences,
not input terms, are the positions: two identical rules can both need repair.
The work measure counts installed key values, not time to discover support,
hash-cons a term, or publish an index. -/
set_option autoImplicit false
namespace Mettapedia.GSLT.Contracts.LiveAliasRepair

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations

variable {I K : Type*} [DecidableEq I]

/-- Replay explicit point writes. The next key is requested only at listed
positions. The representation of the map is not part of its meaning. -/
def patch (previous fresh : I → K) : List I → I → K
  | [] => previous
  | i :: rest => Function.update (patch previous fresh rest) i (fresh i)

theorem patch_apply (previous fresh : I → K) (work : List I) (i : I) :
    patch previous fresh work i = if i ∈ work then fresh i else previous i := by
  induction work with
  | nil => simp [patch]
  | cons x xs ih =>
    by_cases h : i = x <;> simp [patch, Function.update, h, ih]

theorem patch_exact_iff (previous fresh : I → K) (work : List I) :
    patch previous fresh work = fresh ↔ ∀ i, previous i ≠ fresh i → i ∈ work := by
  constructor
  · intro eq i diff
    by_contra missing
    exact diff (by simpa [patch_apply, missing] using congrFun eq i)
  · intro covers
    funext i
    by_cases hit : i ∈ work
    · simp [patch_apply, hit]
    · have same : previous i = fresh i := by by_contra h; exact hit (covers i h)
      simp [patch_apply, hit, same]

def changed [Fintype I] [DecidableEq K] (previous fresh : I → K) : Finset I :=
  Finset.univ.filter (fun i => previous i ≠ fresh i)

/-- Lower bound for *any* point-write implementation, even one which does
not compute keys as this algorithm does. A shared indirection table is a
different representation, to which this lower bound does not apply. -/
theorem minimum_writes [Fintype I] [DecidableEq K] (previous fresh : I → K)
    (touched : List I) (unchanged_elsewhere : ∀ i ∉ touched, previous i = fresh i) :
    (changed previous fresh).card ≤ touched.length := by
  refine (Finset.card_le_card (t := touched.toFinset) ?_).trans (List.toFinset_card_le touched)
  intro i hi
  apply List.mem_toFinset.mpr
  by_contra missing
  exact (Finset.mem_filter.mp hi).2 (unchanged_elsewhere i missing)

theorem minimum_attained [Fintype I] [DecidableEq K] (previous fresh : I → K) :
    patch previous fresh (changed previous fresh).toList = fresh ∧
    (changed previous fresh).toList.length = (changed previous fresh).card := by
  refine ⟨(patch_exact_iff ..).2 (fun i diff => ?_), Finset.length_toList _⟩
  simp [changed, diff]

/-- The inverse constructor-support lookup. A precomputed posting for this
head can supply the same set without inspecting all keys on every edit. -/
def affected [Fintype I] (lhs : I → Pattern) (head : String) : Finset I :=
  Finset.univ.filter (fun i => !checkAvoids head (lhs i))

/-- A new definition unfolds before its older dependencies. Therefore only
raw keys containing its head need reconsideration, including *nested* hits. -/
theorem repair_using (lhs : I → Pattern) (defs : List Row) (d : Row) (work : List I)
    (covers : ∀ i, checkAvoids d.head (lhs i) = false → i ∈ work) :
    patch (fun i => expand defs (lhs i)) (fun i => expand (defs ++ [d]) (lhs i))
      work = (fun i => expand (defs ++ [d]) (lhs i)) := by
  apply (patch_exact_iff ..).2
  intro i differs
  cases h : checkAvoids d.head (lhs i) with
  | false => exact covers i h
  | true => exact (differs (by rw [expand_append_singleton,
      unfoldOne_eq_self ((checkAvoids_iff ..).1 h)])).elim

theorem repair_alias [Fintype I] (lhs : I → Pattern) (defs : List Row) (d : Row) :
    patch (fun i => expand defs (lhs i)) (fun i => expand (defs ++ [d]) (lhs i))
      (affected lhs d.head).toList = (fun i => expand (defs ++ [d]) (lhs i)) :=
  repair_using lhs defs d _ (fun i h => by simp [affected, h])

/-- With a common per-key charge, sparse repair pays precisely when the
saved key computations exceed its additional discovery/maintenance work.
The uniform-rate assumption is explicit. -/
theorem sparse_pays_iff (total candidates perKey overhead : Nat) (le : candidates ≤ total) :
    overhead + candidates * perKey < total * perKey ↔
      overhead < (total - candidates) * perKey := by
  obtain ⟨spared, rfl⟩ := Nat.exists_eq_add_of_le le
  simp only [Nat.add_sub_cancel_left, Nat.add_mul]
  omega

end Mettapedia.GSLT.Contracts.LiveAliasRepair
