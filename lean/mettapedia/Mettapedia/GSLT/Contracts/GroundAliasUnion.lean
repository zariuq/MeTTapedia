import Mettapedia.GSLT.Contracts.LiveAliasRepair

/-! An atomic equation joins two existing equivalence classes. Which old
key survives is an implementation choice. For a table with one physical
key per occurrence, preserving the larger bucket minimizes point writes.
This does not model congruence closure inside structured terms. -/
set_option autoImplicit false
namespace Mettapedia.GSLT.Contracts.GroundAliasUnion

open LiveAliasRepair (changed)
variable {S K I : Type*} [DecidableEq K]

def redirect (keep lose : K) (k : K) : K := if k = lose then keep else k

/-- Independently generated equality: retain all old equalities and add
one edge. The symmetric/transitive closure matters, even for a repeated
equation, a cycle, or an equation given in the opposite orientation. -/
def Adds (old : Setoid S) (a b : S) : S → S → Prop :=
  Relation.EqvGen (fun x y => old.r x y ∨ (x = a ∧ y = b))

theorem redirect_exact (old : Setoid S) (key : S → K)
    (exactKey : ∀ x y, key x = key y ↔ old.r x y) (a b x y : S) :
    redirect (key a) (key b) (key x) = redirect (key a) (key b) (key y) ↔ Adds old a b x y := by
  have prior {i j : S} (same : key i = key j) : Adds old a b i j :=
    .rel _ _ (.inl ((exactKey i j).1 same))
  have link : Adds old a b a b := .rel _ _ (.inr ⟨rfl, rfl⟩)
  constructor
  · intro same
    by_cases hx : key x = key b <;> by_cases hy : key y = key b
    · exact prior (hx.trans hy.symm)
    · have ay : key a = key y := by simpa [redirect, hx, hy] using same
      exact .trans _ _ _ (prior hx) (.trans _ _ _ (.symm _ _ link) (prior ay))
    · have xa : key x = key a := by simpa [redirect, hx, hy] using same
      exact .trans _ _ _ (prior xa) (.trans _ _ _ link (prior hy.symm))
    · exact prior (by simpa [redirect, hx, hy] using same)
  · intro path
    induction path with
    | rel i j edge =>
      rcases edge with h | ⟨rfl, rfl⟩
      · exact congrArg _ ((exactKey i j).2 h)
      · simp [redirect]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ one two => exact one.trans two

theorem orientation_irrelevant (a b x y : K) :
    redirect a b x = redirect a b y ↔ redirect b a x = redirect b a y := by
  unfold redirect
  split_ifs <;> simp_all <;> grind

variable [Fintype I]

def bucket (keys : I → K) (k : K) : Finset I := Finset.univ.filter fun i => keys i = k

theorem redirected_writes (keys : I → K) (a b : K) (different : a ≠ b) :
    changed keys (redirect a b ∘ keys) = bucket keys b := by
  ext i
  by_cases h : keys i = b <;> simp [changed, bucket, redirect, h, Ne.symm different]

/-- If both old buckets must receive one key, even choosing an entirely new
class key cannot improve on writing the smaller bucket. Counts are counts
of live occurrences, not counts of spellings. -/
theorem lower_bound (keys next : I → K) (a b common : K) (different : a ≠ b)
    (coalesce : ∀ i, keys i = a ∨ keys i = b → next i = common) :
    min (bucket keys a).card (bucket keys b).card ≤ (changed keys next).card := by
  have includes (k : K) (which : k = a ∨ k = b) (moves : k ≠ common) :
      bucket keys k ⊆ changed keys next := by
    intro i hi
    have hit := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have writes := coalesce i (which.elim (fun h => Or.inl (hit.trans h)) (fun h => Or.inr (hit.trans h)))
    exact fun eq => moves (hit.symm.trans (eq.trans writes))
  by_cases h : a = common
  · exact (min_le_right ..).trans (Finset.card_le_card
      (includes b (.inr rfl) (fun eq => different (h.trans eq.symm))))
  · exact (min_le_left ..).trans (Finset.card_le_card (includes a (.inl rfl) h))

def byWeight (keys : I → K) (a b : K) : K → K :=
  if (bucket keys a).card ≤ (bucket keys b).card then redirect b a else redirect a b

theorem byWeight_attains (keys : I → K) (a b : K) (different : a ≠ b) :
    (changed keys (byWeight keys a b ∘ keys)).card = min (bucket keys a).card (bucket keys b).card := by
  unfold byWeight
  split
  · rename_i le
    rw [redirected_writes keys b a different.symm, min_eq_left le]
  · rename_i notLe
    rw [redirected_writes keys a b different, min_eq_right (le_of_not_ge notLe)]

theorem byWeight_exact (old : Setoid S) (key : S → K)
    (exactKey : ∀ x y, key x = key y ↔ old.r x y) (rowKeys : I → K) (a b x y : S) :
    byWeight rowKeys (key a) (key b) (key x) = byWeight rowKeys (key a) (key b) (key y) ↔
      Adds old a b x y := by
  unfold byWeight
  split
  · exact (orientation_irrelevant ..).symm.trans (redirect_exact old key exactKey a b x y)
  · exact redirect_exact old key exactKey a b x y

private def fourRows (i : Fin 4) : Bool := decide (i.val = 0)

/-- The same new equality, one physical update instead of three. -/
theorem one_not_three :
    (changed fourRows (byWeight fourRows false true ∘ fourRows)).card = 1 ∧
    (changed fourRows (redirect true false ∘ fourRows)).card = 3 ∧
    (∀ x y, byWeight fourRows false true x = byWeight fourRows false true y ↔
      redirect true false x = redirect true false y) := by
  decide +kernel

end Mettapedia.GSLT.Contracts.GroundAliasUnion
