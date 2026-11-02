import Mettapedia.Machines.ShapeStore

/-!
# Compact unique tuples with ordinary multiset rows

This is the logical multiplicity boundary for shape-table promotion: a compact
component holds at most one copy; ordinary rows retain duplicates and may also
contain older, unpromoted facts. No disjointness or canonical placement is
assumed. Settling materializes the compact component into rows. The laws concern
bag observations, not physical row identities, storage order or concurrent C
execution.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HybridShapeStore

variable {α : Type} [DecidableEq α]

structure Store (α : Type) where
  compact : Finset α
  rows : Multiset α

def denote (s : Store α) : Multiset α := s.compact.val + s.rows

theorem count_denote (x : α) (s : Store α) :
    (denote s).count x = (if x ∈ s.compact then 1 else 0) + s.rows.count x := by
  rw [denote, Multiset.count_add]
  by_cases hx : x ∈ s.compact
  · rw [Multiset.count_eq_one_of_mem s.compact.nodup hx, if_pos hx]
  · rw [Multiset.count_eq_zero_of_notMem hx, if_neg hx]

/-- A compact duplicate is appended to ordinary rows rather than discarded. -/
def add (x : α) (s : Store α) : Store α :=
  if x ∈ s.compact then ⟨s.compact, x ::ₘ s.rows⟩ else ⟨insert x s.compact, s.rows⟩

/-- Remove one copy, preferring the compact copy when both representations hold it. -/
def removeOne (x : α) (s : Store α) : Bool × Store α :=
  if x ∈ s.compact then (true, ⟨s.compact.erase x, s.rows⟩)
  else if x ∈ s.rows then (true, ⟨s.compact, s.rows.erase x⟩)
  else (false, s)

def settle (s : Store α) : Store α := ⟨∅, s.compact.val + s.rows⟩

theorem denote_add (x : α) (s : Store α) : denote (add x s) = x ::ₘ denote s := by
  by_cases hx : x ∈ s.compact
  · simp [add, hx, denote]
  · simp [add, hx, denote, Finset.insert_val_of_notMem hx]

theorem denote_removeOne (x : α) (s : Store α) :
    denote (removeOne x s).2 = (denote s).erase x := by
  by_cases hc : x ∈ s.compact
  · simp [removeOne, hc, denote, Multiset.erase_add_left_pos s.rows hc]
  · by_cases hr : x ∈ s.rows
    · simp [removeOne, hc, hr, denote, Multiset.erase_add_right_pos s.compact.val hr]
    · have hn : x ∉ denote s := by simp [denote, hc, hr]
      simp [removeOne, hc, hr, Multiset.erase_of_notMem hn]

theorem removed_iff (x : α) (s : Store α) :
    (removeOne x s).1 = true ↔ x ∈ denote s := by
  by_cases hc : x ∈ s.compact <;> by_cases hr : x ∈ s.rows <;>
    simp [removeOne, denote, hc, hr]

theorem remove_absent (x : α) (s : Store α) (h : x ∉ denote s) :
    removeOne x s = (false, s) := by
  have hc : x ∉ s.compact := fun hc => h (Multiset.mem_add.mpr (.inl hc))
  have hr : x ∉ s.rows := fun hr => h (Multiset.mem_add.mpr (.inr hr))
  simp [removeOne, hc, hr]

omit [DecidableEq α] in
@[simp] theorem denote_settle (s : Store α) : denote (settle s) = denote s := by
  simp [denote, settle]

omit [DecidableEq α] in
@[simp] theorem settle_idempotent (s : Store α) : settle (settle s) = settle s := by
  simp [settle]

/-- Promotion/fallback need not preserve physical placement; they preserve counts. -/
theorem settle_add_observation (x : α) (s : Store α) :
    denote (settle (add x s)) = denote (add x (settle s)) := by
  simp [denote_add]

theorem settle_remove_observation (x : α) (s : Store α) :
    denote (settle (removeOne x s).2) = denote (removeOne x (settle s)).2 := by
  simp [denote_removeOne]

theorem settle_remove_status (x : α) (s : Store α) :
    (removeOne x (settle s)).1 = (removeOne x s).1 := by
  apply Bool.eq_iff_iff.mpr
  simp [removed_iff]

omit [DecidableEq α] in
/-- Arbitrary row observers, including duplicate-sensitive matching, compose. -/
theorem observe_settle {β : Type} (observe : α → Option β) (s : Store α) :
    (denote (settle s)).filterMap observe = (denote s).filterMap observe := by
  rw [denote_settle]

/-- The compact branch uses the existing shape matcher; ordinary rows use term matching. -/
def matchHybrid (k : ShapeStore.Cut α) (p : ShapeStore.Pat α)
    (s : Store (ShapeStore.Tm α)) : Multiset (ShapeStore.Subst α) :=
  ShapeStore.matchStore p (ShapeStore.store k s.compact.val) +
    s.rows.filterMap (fun t => ShapeStore.matchTm p t [])

theorem matchHybrid_denote (k : ShapeStore.Cut α) (p : ShapeStore.Pat α)
    (s : Store (ShapeStore.Tm α)) :
    matchHybrid k p s = (denote s).filterMap (fun t => ShapeStore.matchTm p t []) := by
  simp [matchHybrid, ShapeStore.matchStore_store, denote, Multiset.filterMap_add]

theorem matchHybrid_settle (k : ShapeStore.Cut α) (p : ShapeStore.Pat α)
    (s : Store (ShapeStore.Tm α)) : matchHybrid k p (settle s) = matchHybrid k p s := by
  rw [matchHybrid_denote, matchHybrid_denote, denote_settle]

theorem matchHybrid_recut (k₁ k₂ : ShapeStore.Cut α) (p : ShapeStore.Pat α)
    (s : Store (ShapeStore.Tm α)) : matchHybrid k₁ p s = matchHybrid k₂ p s := by
  rw [matchHybrid_denote, matchHybrid_denote]

/-- The second copy is still present in the logical bag. -/
example : (denote (add "p" (⟨{"p"}, 0⟩ : Store String))).count "p" = 2 := by decide

/-- Existing ordinary rows do not need an accompanying compact copy. -/
example : denote (add "p" (⟨∅, {"p"}⟩ : Store String)) = {"p", "p"} := by decide

/-- Commutation is observational: settling and insertion can place copies differently. -/
example : settle (add "p" (⟨∅, 0⟩ : Store String)) ≠
    add "p" (settle (⟨∅, 0⟩ : Store String)) := by
  intro h
  have := congrArg Store.compact h
  simp [settle, add] at this

#print axioms denote_add
#print axioms count_denote
#print axioms denote_removeOne
#print axioms removed_iff
#print axioms matchHybrid_settle
#print axioms matchHybrid_recut

end Mettapedia.Machines.HybridShapeStore
