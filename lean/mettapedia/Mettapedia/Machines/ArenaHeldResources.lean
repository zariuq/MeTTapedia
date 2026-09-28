import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Basic

/-!
# Resources held by arena allocations

A runtime keeps nodes in arenas.  An arena is a log of allocations, oldest
first; resetting it to a mark truncates the log, and freeing it truncates it
to nothing.  Some nodes refer to a *resource* outside the arenas, such as a
foreign object.  Each allocation that refers to a resource registers a *hold*
on it in the same arena at the same moment, so the holds of an arena are the
resources its log refers to, and a truncation drops a node together with its
hold.  A resource is released when a truncation leaves no hold on it.

This module proves the two sides of that discipline.
- **Safety** (`inv_alloc`, `inv_reset`): no allocation still in a log refers
  to a released resource.  An allocation may refer only to a resource that is
  not released, which a runtime meets by copying a node it can still reach.
- **Reclamation** (`reset_releases`): a resource that a truncation leaves
  with no hold is released at that truncation.
- **Exactness** (`held_iff_count_pos`): a count of the holds, the runtime's
  representation, is positive exactly when some allocation refers to the
  resource.

Liveness of the *nodes* is the arenas' own discipline (a node's children live
in its arena, an older generation, or storage never released; see
`Machines.Cursor.GenerationalSharing`); this module adds only that the
resources a live node refers to stay unreleased.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ArenaHeldResources

variable {ArenaId Resource : Type} [DecidableEq ArenaId] [DecidableEq Resource]

/-- An arena's allocations, oldest first: each lists the resources its node
refers to directly. -/
abbrev Log (Resource : Type) := List (List Resource)

structure State (ArenaId Resource : Type) where
  arenas : ArenaId → Log Resource
  released : Finset Resource

/-- Some allocation, in some arena, refers to `r`. -/
def Held (s : State ArenaId Resource) (r : Resource) : Prop :=
  ∃ a, ∃ e ∈ s.arenas a, r ∈ e

/-- Safety: no allocation refers to a released resource. -/
def Inv (s : State ArenaId Resource) : Prop :=
  ∀ a, ∀ e ∈ s.arenas a, ∀ r ∈ e, r ∉ s.released

/-- Allocate a node in arena `a` referring to the resources `e`. -/
def alloc (s : State ArenaId Resource) (a : ArenaId) (e : List Resource) :
    State ArenaId Resource :=
  { s with arenas := Function.update s.arenas a (s.arenas a ++ [e]) }

/-- Truncate arena `a` to its first `k` allocations; the resources that are
held before and not after are released. -/
noncomputable def reset (s : State ArenaId Resource) (a : ArenaId) (k : Nat)
    (candidates : Finset Resource) : State ArenaId Resource := by
  classical
  let arenas := Function.update s.arenas a ((s.arenas a).take k)
  exact { arenas := arenas,
          released := s.released ∪
            candidates.filter (fun r => ¬ ∃ b, ∃ e ∈ arenas b, r ∈ e) }

omit [DecidableEq ArenaId] [DecidableEq Resource] in
theorem held_of_mem {s : State ArenaId Resource} {a : ArenaId}
    {e : List Resource} (member : e ∈ s.arenas a) {r : Resource}
    (refers : r ∈ e) : Held s r :=
  ⟨a, e, member, refers⟩

omit [DecidableEq Resource] in
theorem mem_update_arenas {s : State ArenaId Resource} {a b : ArenaId}
    {log : Log Resource} {e : List Resource}
    (member : e ∈ Function.update s.arenas a log b) :
    (b = a ∧ e ∈ log) ∨ (b ≠ a ∧ e ∈ s.arenas b) := by
  by_cases same : b = a
  · subst same
    simp only [Function.update_self] at member
    exact Or.inl ⟨rfl, member⟩
  · rw [Function.update_of_ne same] at member
    exact Or.inr ⟨same, member⟩

omit [DecidableEq Resource] in
/-- Safety survives an allocation that refers only to unreleased resources. -/
theorem inv_alloc {s : State ArenaId Resource} (inv : Inv s) (a : ArenaId)
    (e : List Resource) (fresh : ∀ r ∈ e, r ∉ s.released) :
    Inv (alloc s a e) := by
  intro b e' member r refers
  rcases mem_update_arenas member with ⟨rfl, inLog⟩ | ⟨_, inOld⟩
  · rcases List.mem_append.mp inLog with old | new
    · exact inv b e' old r refers
    · have : e' = e := by simpa using new
      subst this
      exact fresh r refers
  · exact inv b e' inOld r refers

/-- Safety survives a truncation: what remains was not released before, and
what the truncation releases is held by nothing that remains. -/
theorem inv_reset {s : State ArenaId Resource} (inv : Inv s) (a : ArenaId)
    (k : Nat) (candidates : Finset Resource) :
    Inv (reset s a k candidates) := by
  classical
  intro b e member r refers
  simp only [reset, Finset.mem_union, Finset.mem_filter, not_or, not_and,
    not_not]
  have remained : e ∈ s.arenas b := by
    rcases mem_update_arenas member with ⟨rfl, inLog⟩ | ⟨_, inOld⟩
    · exact List.mem_of_mem_take inLog
    · exact inOld
  refine ⟨inv b e remained r refers, fun _ => ⟨b, e, member, refers⟩⟩

/-- Reclamation: a candidate that the truncation leaves with no hold is
released by it. -/
theorem reset_releases (s : State ArenaId Resource) (a : ArenaId) (k : Nat)
    (candidates : Finset Resource) {r : Resource} (candidate : r ∈ candidates)
    (unheld : ¬ Held (reset s a k candidates) r) :
    r ∈ (reset s a k candidates).released := by
  classical
  simp only [reset, Finset.mem_union, Finset.mem_filter]
  exact Or.inr ⟨candidate, unheld⟩

/-- The holds on `r` in one log. -/
def logHolds (log : Log Resource) (r : Resource) : Nat :=
  (log.map (fun e => e.count r)).sum

/-- A log holds `r` exactly when one of its allocations refers to it. -/
theorem logHolds_pos_iff (log : Log Resource) (r : Resource) :
    0 < logHolds log r ↔ ∃ e ∈ log, r ∈ e := by
  induction log with
  | nil => simp [logHolds]
  | cons head tail ih =>
      simp only [logHolds, List.map_cons, List.sum_cons] at ih ⊢
      constructor
      · intro positive
        by_cases here : 0 < head.count r
        · exact ⟨head, List.mem_cons_self .., List.count_pos_iff.mp here⟩
        · have rest : 0 < (tail.map fun e => e.count r).sum := by omega
          obtain ⟨e, member, refers⟩ := ih.mp rest
          exact ⟨e, List.mem_cons_of_mem _ member, refers⟩
      · rintro ⟨e, member, refers⟩
        rcases List.mem_cons.mp member with rfl | later
        · have := List.count_pos_iff.mpr refers
          omega
        · have := ih.mpr ⟨e, later, refers⟩
          omega

/-- The runtime counts holds over the arenas in use; the count is positive
exactly when some allocation in them refers to the resource. -/
theorem held_iff_count_pos (s : State ArenaId Resource) (inUse : Finset ArenaId)
    (outside : ∀ a ∉ inUse, s.arenas a = []) (r : Resource) :
    Held s r ↔ 0 < ∑ a ∈ inUse, logHolds (s.arenas a) r := by
  constructor
  · rintro ⟨a, e, member, refers⟩
    have used : a ∈ inUse := by
      by_contra absent
      rw [outside a absent] at member
      cases member
    have positive : 0 < logHolds (s.arenas a) r :=
      (logHolds_pos_iff _ r).mpr ⟨e, member, refers⟩
    exact lt_of_lt_of_le positive
      (Finset.single_le_sum (f := fun b => logHolds (s.arenas b) r)
        (fun b _ => Nat.zero_le _) used)
  · intro positive
    by_contra unheld
    have none : ∀ a ∈ inUse, logHolds (s.arenas a) r = 0 := by
      intro a _
      by_contra nonzero
      obtain ⟨e, member, refers⟩ :=
        (logHolds_pos_iff _ r).mp (Nat.pos_of_ne_zero nonzero)
      exact unheld ⟨a, e, member, refers⟩
    rw [Finset.sum_eq_zero none] at positive
    exact Nat.lt_irrefl 0 positive

end Mettapedia.Machines.ArenaHeldResources
