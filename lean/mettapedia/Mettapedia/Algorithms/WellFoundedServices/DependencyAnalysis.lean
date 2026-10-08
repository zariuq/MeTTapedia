import Mettapedia.Algorithms.WellFoundedServices.MeasuredLoop
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Relation
import Mathlib.Data.List.Forall2
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Dependency analysis over a finite catalogue

A catalogue lists its items and, for each item, the items it depends on. Four
services, each a measured loop or a measured recursion:

* `Catalogue.affected`: the items affected by a change, found by a reverse
  sweep; `mem_affected` says they are exactly the items that depend, directly
  or not, on a changed item. Variant: the number of catalogue items not yet
  seen.
* `Catalogue.schedule`: parallel rebuild waves (Kahn's algorithm) or a blocked
  set. `schedule_spec`: the waves list every target once, no item depends on
  itself, on an item of its own wave or on a later one; a blocked set is a
  nonempty set of targets each of which depends on a member. Variant: the
  number of pending targets.
* `Catalogue.findCycle`: an explicit dependency cycle through a blocked set,
  found by walking inside it until an item repeats (`findCycle_spec`).
  Variant: the number of members of the set not yet visited.
  `Catalogue.cycle?` finds a cycle among the catalogue items exactly when one
  exists (`cycle?_isSome_iff`).
* `Catalogue.Acyclic.recOrder`: recursion over the dependency relation itself,
  from an acyclicity certificate (a rebuild order of the whole catalogue): the
  value at an item is computed from the values at its dependencies. The
  certificate makes every item accessible (`Acyclic.accCode`).

The bounded `OccurrenceGraph` service is specified by the same independent
dependency-fold judgment. It retains its ordered DFS cursor, memo and
analysis expense across resumptions, and proves soundness of successful
bound readouts. Native memory and source-coverage adapters are separate.

Each loop also runs through the accessibility route (`affectedAcc`,
`scheduleAcc`, `Acyclic.recAcc`), and the two versions agree for every inert
recursor.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.WellFoundedServices

open Relation Mettapedia.Order

universe u v

/-- A catalogue of items, each listing the items it depends on. -/
structure Catalogue (α : Type u) where
  items : List α
  deps : α → List α

/-- The segment of a reversed walk from its head down to the first occurrence
of `y`, in walk order. -/
def cycleAt {α : Type u} [DecidableEq α] (y : α) : List α → List α
  | [] => []
  | a :: l => if a = y then [a] else cycleAt y l ++ [a]

/-- A strictly stronger filter keeps strictly fewer elements. -/
theorem length_filter_lt {α : Type u} {l : List α} {p q : α → Bool}
    (hpq : ∀ x, p x = true → q x = true) {z : α} (hz : z ∈ l) (hq : q z = true)
    (hp : p z = false) : (l.filter p).length < (l.filter q).length := by
  have e : l.filter p = (l.filter q).filter p := by
    rw [List.filter_filter]
    congr 1
    funext x
    cases h : p x
    · rfl
    · simp [hpq x h]
  rw [e, List.length_filter_lt_length_iff_exists]
  exact ⟨z, List.mem_filter.2 ⟨hz, hq⟩, by simp [hp]⟩

theorem transGen_of_isChain {α : Type u} {R : α → α → Prop} :
    ∀ {a b : α} {rest : List α}, List.IsChain R (a :: rest ++ [b]) → TransGen R a b
  | _, _, [], h => .single (List.isChain_pair.1 h)
  | _, _, _ :: _, h => by
      rw [List.cons_append, List.cons_append, List.isChain_cons_cons] at h
      exact .head h.1 (transGen_of_isChain (by simpa using h.2))

/-- Appending one element to a chain. -/
theorem isChain_append_singleton {α : Type u} {R : α → α → Prop} {b : α} :
    ∀ {l : List α}, List.IsChain R l → (∀ x ∈ l.getLast?, R x b) → List.IsChain R (l ++ [b])
  | [], _, _ => List.isChain_singleton b
  | [a], _, h => List.isChain_pair.2 (h a rfl)
  | _ :: _ :: _, hc, h => by
      rw [List.cons_append, List.cons_append]
      exact List.isChain_cons_cons.2 ⟨(List.isChain_cons_cons.1 hc).1,
        by rw [← List.cons_append]; exact isChain_append_singleton (List.isChain_cons_cons.1 hc).2 h⟩

/-- The first occurrence of each element, in order. -/
def firstOccurrences {α : Type u} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (firstOccurrences xs).filter fun y => decide (y ≠ x)

theorem mem_firstOccurrences {α : Type u} [DecidableEq α] {x : α} :
    ∀ {l : List α}, x ∈ firstOccurrences l ↔ x ∈ l
  | [] => Iff.rfl
  | a :: l => by
      rw [firstOccurrences, List.mem_cons, List.mem_cons, List.mem_filter, mem_firstOccurrences]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact .inl h
        · exact .inr h
      · intro h
        by_cases hx : x = a
        · exact .inl hx
        · exact .inr ⟨h.resolve_left hx, decide_eq_true hx⟩

theorem nodup_firstOccurrences {α : Type u} [DecidableEq α] :
    ∀ l : List α, (firstOccurrences l).Nodup
  | [] => List.nodup_nil
  | _ :: l => List.nodup_cons.2
      ⟨fun h => of_decide_eq_true (List.mem_filter.1 h).2 rfl,
        (nodup_firstOccurrences l).filter _⟩

namespace Catalogue

variable {α : Type u} [DecidableEq α] (c : Catalogue α)

/-- The catalogue item `x` lists `y` among its dependencies. -/
def Uses (x y : α) : Prop := x ∈ c.items ∧ y ∈ c.deps x

/-! ## Affected items -/

/-- The state of a reverse sweep: the items found so far, and those found in
the last round. -/
structure Sweep (α : Type u) where
  seen : List α
  frontier : List α

/-- Catalogue items outside `seen` that list a frontier item among their
dependencies. -/
def fresh (s : Sweep α) : List α :=
  c.items.filter fun x => decide (x ∉ s.seen ∧ ∃ y ∈ s.frontier, y ∈ c.deps x)

theorem mem_fresh {s : Sweep α} {x : α} :
    x ∈ c.fresh s ↔ x ∈ c.items ∧ x ∉ s.seen ∧ ∃ y ∈ s.frontier, y ∈ c.deps x := by
  simp only [fresh, List.mem_filter, decide_eq_true_eq]

/-- The number of catalogue items outside `seen`. -/
def unseen (seen : List α) : ℕ := (c.items.filter fun x => decide (x ∉ seen)).length

theorem unseen_lt {s : Sweep α} (h : c.fresh s ≠ []) :
    c.unseen (s.seen ++ c.fresh s) < c.unseen s.seen := by
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨hzi, hzs, -⟩ := c.mem_fresh.1 hz
  refine length_filter_lt (fun x hx => ?_) hzi (by simpa using hzs) (by simp [hz])
  simp only [decide_eq_true_eq, List.mem_append, not_or] at hx ⊢
  exact hx.1

/-- One round of the reverse sweep. -/
def sweep : MeasuredLoop (Sweep α) (List α) where
  measure s := c.unseen s.seen
  step s :=
    if h : c.fresh s = [] then .inr s.seen
    else .inl ⟨⟨s.seen ++ c.fresh s, c.fresh s⟩, c.unseen_lt h⟩

/-- **Affected items**: the changed items and everything that depends on one
of them, directly or not. -/
def affected (changed : List α) : List α := c.sweep.run ⟨changed, changed⟩

/-- The same service through the accessibility route. -/
def affectedAcc (I : InertRecursor.{u + 1, u + 1} fun y x => c.sweep.measure y < c.sweep.measure x)
    (changed : List α) : List α :=
  c.sweep.loopAcc I ⟨changed, changed⟩

theorem affectedAcc_eq (I : InertRecursor.{u + 1, u + 1} fun y x => c.sweep.measure y < c.sweep.measure x)
    (changed : List α) : c.affectedAcc I changed = c.affected changed :=
  c.sweep.loopAcc_eq_run I _

theorem sweep_inl {s s' : Sweep α} {hs : c.sweep.measure s' < c.sweep.measure s}
    (e : c.sweep.step s = .inl ⟨s', hs⟩) : s' = ⟨s.seen ++ c.fresh s, c.fresh s⟩ := by
  simp only [sweep] at e
  by_cases h : c.fresh s = []
  · rw [dif_pos h] at e; cases e
  · rw [dif_neg h] at e
    exact (congrArg Subtype.val (Sum.inl.inj e)).symm

theorem sweep_inr {s : Sweep α} {b : List α} (e : c.sweep.step s = .inr b) :
    c.fresh s = [] ∧ b = s.seen := by
  simp only [sweep] at e
  by_cases h : c.fresh s = []
  · rw [dif_pos h] at e
    simp only [Sum.inr.injEq] at e
    exact ⟨h, e.symm⟩
  · rw [dif_neg h] at e; cases e

/-- The invariant of the sweep from `changed`. -/
structure SweepInv (changed : List α) (s : Sweep α) : Prop where
  changed_seen : ∀ y ∈ changed, y ∈ s.seen
  seen_reach : ∀ x ∈ s.seen, ∃ y ∈ changed, ReflTransGen c.Uses x y
  frontier_seen : ∀ x ∈ s.frontier, x ∈ s.seen
  closed : ∀ x z, c.Uses x z → z ∈ s.seen → z ∉ s.frontier → x ∈ s.seen

omit [DecidableEq α] in
theorem sweepInv_start (changed : List α) : c.SweepInv changed ⟨changed, changed⟩ where
  changed_seen _ h := h
  seen_reach x h := ⟨x, h, .refl⟩
  frontier_seen _ h := h
  closed _ _ _ hz hf := absurd hz hf

theorem sweepInv_step {changed : List α} {s : Sweep α} (inv : c.SweepInv changed s) :
    c.SweepInv changed ⟨s.seen ++ c.fresh s, c.fresh s⟩ where
  changed_seen y h := List.mem_append_left _ (inv.changed_seen y h)
  seen_reach x h := by
    rcases List.mem_append.1 h with h | h
    · exact inv.seen_reach x h
    · obtain ⟨hx, -, y, hy, hd⟩ := c.mem_fresh.1 h
      obtain ⟨w, hw, r⟩ := inv.seen_reach y (inv.frontier_seen y hy)
      exact ⟨w, hw, .head ⟨hx, hd⟩ r⟩
  frontier_seen _ h := List.mem_append_right _ h
  closed x z hu hz hf := by
    have hz' : z ∈ s.seen := by
      rcases List.mem_append.1 hz with h | h
      · exact h
      · exact absurd h hf
    by_cases hzf : z ∈ s.frontier
    · by_cases hx : x ∈ s.seen
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (c.mem_fresh.2 ⟨hu.1, hx, z, hzf, hu.2⟩)
    · exact List.mem_append_left _ (inv.closed x z hu hz' hzf)

theorem sweepInv_stop {changed : List α} {s : Sweep α} (inv : c.SweepInv changed s)
    (h : c.fresh s = []) (x : α) : x ∈ s.seen ↔ ∃ y ∈ changed, ReflTransGen c.Uses x y := by
  refine ⟨inv.seen_reach x, ?_⟩
  rintro ⟨y, hy, r⟩
  have closed : ∀ a b, c.Uses a b → b ∈ s.seen → a ∈ s.seen := by
    intro a b hu hb
    by_cases hbf : b ∈ s.frontier
    · by_cases ha : a ∈ s.seen
      · exact ha
      · have : a ∈ c.fresh s := c.mem_fresh.2 ⟨hu.1, ha, b, hbf, hu.2⟩
        rw [h] at this
        exact absurd this List.not_mem_nil
    · exact inv.closed a b hu hb hbf
  induction r using ReflTransGen.head_induction_on with
  | refl => exact inv.changed_seen y hy
  | head hu _ ih => exact closed _ _ hu ih

/-- **Affected = reverse-reachable.** -/
theorem mem_affected (changed : List α) (x : α) :
    x ∈ c.affected changed ↔ ∃ y ∈ changed, ReflTransGen c.Uses x y :=
  c.sweep.run_induction (c.SweepInv changed)
    (fun r => ∀ x, x ∈ r ↔ ∃ y ∈ changed, ReflTransGen c.Uses x y)
    (fun _ _ _ inv e => c.sweep_inl e ▸ c.sweepInv_step inv)
    (fun _ _ inv e => (c.sweep_inr e).2 ▸ c.sweepInv_stop inv (c.sweep_inr e).1)
    _ (c.sweepInv_start changed) x

/-- The same characterization through the accessibility route, proved from
the unfolding alone. -/
theorem mem_affectedAcc
    (I : InertRecursor.{u + 1, u + 1} fun y x => c.sweep.measure y < c.sweep.measure x)
    (changed : List α) (x : α) :
    x ∈ c.affectedAcc I changed ↔ ∃ y ∈ changed, ReflTransGen c.Uses x y :=
  c.sweep.loopAcc_induction I (c.SweepInv changed)
    (fun r => ∀ x, x ∈ r ↔ ∃ y ∈ changed, ReflTransGen c.Uses x y)
    (fun _ _ _ inv e => c.sweep_inl e ▸ c.sweepInv_step inv)
    (fun _ _ inv e => (c.sweep_inr e).2 ▸ c.sweepInv_stop inv (c.sweep_inr e).1)
    _ (c.sweepInv_start changed) x

/-! ## Rebuild schedule -/

/-- The result of scheduling: parallel rebuild waves, or a blocked set. -/
inductive Schedule (α : Type u) where
  | waves (layers : List (List α))
  | blocked (items : List α)
  deriving DecidableEq, Repr

/-- The state of Kahn's algorithm: the waves so far and the pending targets. -/
structure Plan (α : Type u) where
  layers : List (List α)
  remaining : List α

/-- Pending items none of whose dependencies is pending. -/
def ready (remaining : List α) : List α :=
  remaining.filter fun x => decide (∀ y ∈ c.deps x, y ∉ remaining)

theorem mem_ready {remaining : List α} {x : α} :
    x ∈ c.ready remaining ↔ x ∈ remaining ∧ ∀ y ∈ c.deps x, y ∉ remaining := by
  simp only [ready, List.mem_filter, decide_eq_true_eq]

theorem remaining_lt {remaining : List α} (h : c.ready remaining ≠ []) :
    (remaining.filter fun x => decide (x ∉ c.ready remaining)).length < remaining.length := by
  rw [List.length_filter_lt_length_iff_exists]
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ h
  exact ⟨z, (c.mem_ready.1 hz).1, by simpa using hz⟩

/-- One round of Kahn's algorithm: emit the ready items as a wave. -/
def kahn : MeasuredLoop (Plan α) (Schedule α) where
  measure p := p.remaining.length
  step p :=
    if p.remaining = [] then .inr (.waves p.layers)
    else if h : c.ready p.remaining = [] then .inr (.blocked p.remaining)
    else .inl ⟨⟨p.layers ++ [c.ready p.remaining],
      p.remaining.filter fun x => decide (x ∉ c.ready p.remaining)⟩, c.remaining_lt h⟩

/-- **Rebuild schedule** for a list of targets. -/
def schedule (target : List α) : Schedule α := c.kahn.run ⟨[], firstOccurrences target⟩

/-- The same service through the accessibility route. -/
def scheduleAcc (I : InertRecursor.{u + 1, u + 1} fun y x => c.kahn.measure y < c.kahn.measure x)
    (target : List α) : Schedule α :=
  c.kahn.loopAcc I ⟨[], firstOccurrences target⟩

theorem scheduleAcc_eq (I : InertRecursor.{u + 1, u + 1} fun y x => c.kahn.measure y < c.kahn.measure x)
    (target : List α) : c.scheduleAcc I target = c.schedule target :=
  c.kahn.loopAcc_eq_run I _

/-- `order` lists each item once, and no item depends on itself or on a later
item. -/
structure Respects (order : List α) : Prop where
  nodup : order.Nodup
  pairwise : order.Pairwise fun a b => b ∉ c.deps a
  irrefl : ∀ x ∈ order, x ∉ c.deps x

/-- A blocked set: nonempty, and each member depends on a member. -/
structure Blocked (B : List α) : Prop where
  ne_nil : B ≠ []
  closed : ∀ x ∈ B, ∃ y ∈ c.deps x, y ∈ B

/-- What a schedule for `target` guarantees. -/
def ScheduleSpec (target : List α) : Schedule α → Prop
  | .waves layers =>
      (∀ x, x ∈ layers.flatten ↔ x ∈ target) ∧ c.Respects layers.flatten ∧ ∀ w ∈ layers, w ≠ []
  | .blocked B => c.Blocked B ∧ ∀ x ∈ B, x ∈ target

/-- The invariant of Kahn's algorithm for `target`. -/
structure PlanInv (target : List α) (p : Plan α) : Prop where
  cover : ∀ x, x ∈ target ↔ x ∈ p.layers.flatten ∨ x ∈ p.remaining
  disjoint : ∀ x ∈ p.layers.flatten, x ∉ p.remaining
  nodup_done : p.layers.flatten.Nodup
  nodup_remaining : p.remaining.Nodup
  pairwise : p.layers.flatten.Pairwise fun a b => b ∉ c.deps a
  irrefl : ∀ x ∈ p.layers.flatten, x ∉ c.deps x
  settled : ∀ x ∈ p.layers.flatten, ∀ y ∈ c.deps x, y ∉ p.remaining
  nonempty : ∀ w ∈ p.layers, w ≠ []

theorem planInv_start (target : List α) : c.PlanInv target ⟨[], firstOccurrences target⟩ where
  cover _ := ⟨fun h => .inr (mem_firstOccurrences.2 h),
    fun h => h.elim (fun h => absurd h List.not_mem_nil) mem_firstOccurrences.1⟩
  disjoint _ h := absurd h List.not_mem_nil
  nodup_done := List.nodup_nil
  nodup_remaining := nodup_firstOccurrences target
  pairwise := List.Pairwise.nil
  irrefl _ h := absurd h List.not_mem_nil
  settled _ h := absurd h List.not_mem_nil
  nonempty _ h := absurd h List.not_mem_nil

theorem planInv_step {target : List α} {p : Plan α} (inv : c.PlanInv target p)
    (h : c.ready p.remaining ≠ []) :
    c.PlanInv target ⟨p.layers ++ [c.ready p.remaining],
      p.remaining.filter fun x => decide (x ∉ c.ready p.remaining)⟩ := by
  have hY : ∀ {x}, x ∈ c.ready p.remaining → x ∈ p.remaining := fun hx => (c.mem_ready.1 hx).1
  have hR' : ∀ {x}, x ∈ p.remaining.filter (fun x => decide (x ∉ c.ready p.remaining)) ↔
      x ∈ p.remaining ∧ x ∉ c.ready p.remaining := by
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
  have hF : (p.layers ++ [c.ready p.remaining]).flatten = p.layers.flatten ++ c.ready p.remaining := by
    simp
  refine
    { cover := fun x => ?_, disjoint := fun x hx => ?_, nodup_done := ?_,
      nodup_remaining := inv.nodup_remaining.filter _, pairwise := ?_,
      irrefl := fun x hx => ?_, settled := fun x hx y hy => ?_, nonempty := fun w hw => ?_ } <;>
    dsimp only at * <;> simp only [hF] at *
  · rw [inv.cover x, List.mem_append, hR']
    constructor
    · rintro (hx | hx)
      · exact .inl (.inl hx)
      · by_cases hy : x ∈ c.ready p.remaining
        · exact .inl (.inr hy)
        · exact .inr ⟨hx, hy⟩
    · rintro ((hx | hx) | hx)
      · exact .inl hx
      · exact .inr (hY hx)
      · exact .inr hx.1
  · rw [hR']
    rcases List.mem_append.1 hx with hx | hx
    · exact fun h' => inv.disjoint x hx h'.1
    · exact fun h' => h'.2 hx
  · refine List.nodup_append.2 ⟨inv.nodup_done, inv.nodup_remaining.filter _, ?_⟩
    rintro a ha b hb rfl
    exact inv.disjoint a ha (hY hb)
  · refine List.pairwise_append.2 ⟨inv.pairwise, ?_, ?_⟩
    · exact List.pairwise_of_forall_mem_list fun a ha b hb hd =>
        (c.mem_ready.1 ha).2 b hd (hY hb)
    · exact fun a ha b hb hd => inv.settled a ha b hd (hY hb)
  · rcases List.mem_append.1 hx with hx | hx
    · exact inv.irrefl x hx
    · exact fun hd => (c.mem_ready.1 hx).2 x hd (hY hx)
  · rw [hR']
    rcases List.mem_append.1 hx with hx | hx
    · exact fun h' => inv.settled x hx y hy h'.1
    · exact fun h' => (c.mem_ready.1 hx).2 y hy h'.1
  · rcases List.mem_append.1 hw with hw | hw
    · exact inv.nonempty w hw
    · rw [List.mem_singleton.1 hw]; exact h

omit [DecidableEq α] in
theorem planInv_waves {target : List α} {p : Plan α} (inv : c.PlanInv target p)
    (h : p.remaining = []) : c.ScheduleSpec target (.waves p.layers) :=
  ⟨fun x => by rw [inv.cover x, h]; simp, ⟨inv.nodup_done, inv.pairwise, inv.irrefl⟩, inv.nonempty⟩

theorem planInv_blocked {target : List α} {p : Plan α} (inv : c.PlanInv target p)
    (h0 : p.remaining ≠ []) (h : c.ready p.remaining = []) :
    c.ScheduleSpec target (.blocked p.remaining) := by
  refine ⟨⟨h0, fun x hx => ?_⟩, fun x hx => (inv.cover x).2 (.inr hx)⟩
  refine Decidable.byContradiction fun hn => ?_
  have hx' : x ∈ c.ready p.remaining :=
    c.mem_ready.2 ⟨hx, fun y hy hyR => hn ⟨y, hy, hyR⟩⟩
  rw [h] at hx'
  exact List.not_mem_nil hx'

theorem kahn_inl {p p' : Plan α} {hs : c.kahn.measure p' < c.kahn.measure p}
    (e : c.kahn.step p = .inl ⟨p', hs⟩) :
    c.ready p.remaining ≠ [] ∧ p' = ⟨p.layers ++ [c.ready p.remaining],
      p.remaining.filter fun x => decide (x ∉ c.ready p.remaining)⟩ := by
  simp only [kahn] at e
  by_cases h0 : p.remaining = []
  · rw [if_pos h0] at e; cases e
  · rw [if_neg h0] at e
    by_cases h : c.ready p.remaining = []
    · rw [dif_pos h] at e; cases e
    · rw [dif_neg h] at e
      exact ⟨h, (congrArg Subtype.val (Sum.inl.inj e)).symm⟩

theorem kahn_inr {target : List α} {p : Plan α} {b : Schedule α} (inv : c.PlanInv target p)
    (e : c.kahn.step p = .inr b) : c.ScheduleSpec target b := by
  simp only [kahn] at e
  by_cases h0 : p.remaining = []
  · rw [if_pos h0] at e
    simp only [Sum.inr.injEq] at e
    exact e ▸ c.planInv_waves inv h0
  · rw [if_neg h0] at e
    by_cases h : c.ready p.remaining = []
    · rw [dif_pos h] at e
      simp only [Sum.inr.injEq] at e
      exact e ▸ c.planInv_blocked inv h0 h
    · rw [dif_neg h] at e; cases e

/-- **The schedule is correct.** -/
theorem schedule_spec (target : List α) : c.ScheduleSpec target (c.schedule target) :=
  c.kahn.run_induction (c.PlanInv target) (c.ScheduleSpec target)
    (fun _ _ _ inv e => (c.kahn_inl e).2 ▸ c.planInv_step inv (c.kahn_inl e).1)
    (fun _ _ inv e => c.kahn_inr inv e) _ (c.planInv_start target)

/-! ## Orders and cycles -/

/-- A closed walk along dependencies. -/
def IsCycle (w : List α) : Prop :=
  ∃ a rest, w = a :: rest ∧ List.IsChain c.Uses (a :: rest ++ [a])

/-- The measure given by a rebuild order: one more than the position, and zero
outside the catalogue. -/
def orderMeasure (order : List α) (x : α) : ℕ :=
  if x ∈ c.items then order.idxOf x + 1 else 0

section

variable {c}

omit [DecidableEq α] in
theorem IsCycle.transGen {w : List α} (h : c.IsCycle w) : ∃ a, TransGen c.Uses a a := by
  obtain ⟨a, rest, -, hc⟩ := h
  exact ⟨a, transGen_of_isChain hc⟩

/-- In a respecting order, a dependency comes first. -/
theorem Respects.idxOf_lt {order : List α} (h : c.Respects order) {x y : α} (hx : x ∈ order)
    (hy : y ∈ order) (hd : y ∈ c.deps x) : order.idxOf y < order.idxOf x := by
  have hx' := List.idxOf_lt_length_of_mem hx
  have hy' := List.idxOf_lt_length_of_mem hy
  rcases lt_trichotomy (order.idxOf y) (order.idxOf x) with hlt | heq | hgt
  · exact hlt
  · have ey : order[order.idxOf y]? = some y :=
      (List.getElem?_eq_getElem hy').trans (congrArg some (List.getElem_idxOf hy'))
    have ex : order[order.idxOf x]? = some x :=
      (List.getElem?_eq_getElem hx').trans (congrArg some (List.getElem_idxOf hx'))
    rw [heq, ex] at ey
    cases ey
    exact absurd hd (h.irrefl _ hx)
  · have := List.pairwise_iff_getElem.1 h.pairwise _ _ hx' hy' hgt
    rw [List.getElem_idxOf, List.getElem_idxOf] at this
    exact absurd hd this

theorem Respects.orderMeasure_lt {order : List α} (h : c.Respects order)
    (hcov : ∀ x ∈ c.items, x ∈ order) {x y : α} (hu : c.Uses x y) :
    c.orderMeasure order y < c.orderMeasure order x := by
  unfold orderMeasure
  rw [if_pos hu.1]
  by_cases hy : y ∈ c.items
  · rw [if_pos hy]
    exact Nat.succ_lt_succ (h.idxOf_lt (hcov x hu.1) (hcov y hy) hu.2)
  · rw [if_neg hy]
    exact Nat.succ_pos _

/-- A respecting order of the whole catalogue excludes dependency cycles. -/
theorem Respects.acyclic {order : List α} (h : c.Respects order)
    (hcov : ∀ x ∈ c.items, x ∈ order) (a : α) : ¬ TransGen c.Uses a a := by
  intro t
  have key : ∀ {x y}, TransGen c.Uses x y → c.orderMeasure order y < c.orderMeasure order x := by
    intro x y t
    induction t with
    | single hu => exact h.orderMeasure_lt hcov hu
    | tail _ hu ih => exact lt_trans (h.orderMeasure_lt hcov hu) ih
  exact lt_irrefl _ (key t)

/-- A blocked set inside a respecting order is impossible. -/
theorem Blocked.not_respects {B order : List α} (hB : c.Blocked B) (h : c.Respects order)
    (hsub : ∀ x ∈ B, x ∈ order) : False := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hB.ne_nil
  have key : ∀ n, ∀ x ∈ B, order.idxOf x < n → False := by
    intro n
    induction n with
    | zero => intro x _ hn; exact Nat.not_lt_zero _ hn
    | succ n ih =>
        intro x hx hn
        obtain ⟨y, hy, hyB⟩ := hB.closed x hx
        exact ih y hyB (Nat.lt_of_lt_of_le (h.idxOf_lt (hsub x hx) (hsub y hyB) hy)
          (Nat.le_of_lt_succ hn))
  exact key _ x hx (Nat.lt_succ_self _)

end

/-! ## Finding a cycle -/

/-- The first member of `B` among the dependencies of `x`. -/
def nextIn (B : List α) (x : α) : Option α := (c.deps x).find? fun y => decide (y ∈ B)

theorem nextIn_spec {B : List α} {x y : α} (h : c.nextIn B x = some y) :
    y ∈ c.deps x ∧ y ∈ B :=
  ⟨List.mem_of_find?_eq_some (p := fun y => decide (y ∈ B)) h,
    of_decide_eq_true (List.find?_some (p := fun y => decide (y ∈ B)) (l := c.deps x) h)⟩

theorem nextIn_ne_none {B : List α} {x y : α} (hy : y ∈ c.deps x) (hyB : y ∈ B) :
    c.nextIn B x ≠ none := fun h =>
  (List.find?_eq_none (p := fun y => decide (y ∈ B)) (l := c.deps x)).1 h y hy (decide_eq_true hyB)

/-- One step of the walk inside `B`: follow the first dependency in `B`, and
close the cycle when an item repeats. The path is kept reversed. -/
def walkStep (B : List α) : (path : List α) →
    {p : List α // (B.filter fun x => decide (x ∉ p)).length <
      (B.filter fun x => decide (x ∉ path)).length} ⊕ List α
  | [] => .inr []
  | x :: rest =>
      match h : c.nextIn B x with
      | none => .inr []
      | some y =>
          if hy : y ∈ x :: rest then .inr (cycleAt y (x :: rest))
          else .inl ⟨y :: x :: rest, length_filter_lt (fun z hz => by
              simp only [decide_eq_true_eq, List.mem_cons, not_or] at hz ⊢
              exact ⟨hz.2.1, hz.2.2⟩)
            (c.nextIn_spec h).2 (by simpa using hy) (by simp)⟩

/-- The walk as a measured loop. -/
def walk (B : List α) : MeasuredLoop (List α) (List α) where
  measure path := (B.filter fun x => decide (x ∉ path)).length
  step := c.walkStep B

/-- **A cycle through a blocked set.** -/
def findCycle (B : List α) : List α :=
  match B with
  | [] => []
  | x :: _ => (c.walk B).run [x]

/-- The invariant of the walk: a nonempty reversed walk inside `B`. -/
structure WalkInv (B path : List α) : Prop where
  ne_nil : path ≠ []
  sub : ∀ x ∈ path, x ∈ B
  chain : List.IsChain (fun a b => c.Uses b a) path

omit [DecidableEq α] in
theorem walkInv_start {B : List α} {x : α} (hx : x ∈ B) : c.WalkInv B [x] where
  ne_nil := List.cons_ne_nil _ _
  sub z h := by rw [List.mem_singleton.1 h]; exact hx
  chain := List.isChain_singleton _

theorem cycleAt_spec {y : α} :
    ∀ {path : List α}, List.IsChain (fun a b => c.Uses b a) path → y ∈ path →
      ∃ rest, cycleAt y path = y :: rest ∧ List.IsChain c.Uses (cycleAt y path) ∧
        (cycleAt y path).getLast? = path.head? ∧ ∀ z ∈ cycleAt y path, z ∈ path
  | [], _, hy => absurd hy List.not_mem_nil
  | a :: l, hc, hy => by
      by_cases ha : a = y
      · subst ha
        have e : cycleAt a (a :: l) = [a] := by simp [cycleAt]
        rw [e]
        refine ⟨[], rfl, List.isChain_singleton _, by simp, ?_⟩
        intro z hz
        rw [List.mem_singleton.1 hz]
        exact List.mem_cons_self
      · have hyl : y ∈ l := (List.mem_cons.1 hy).resolve_left (Ne.symm ha)
        obtain ⟨b, l', rfl⟩ : ∃ b l', l = b :: l' :=
          List.exists_cons_of_ne_nil (List.ne_nil_of_mem hyl)
        have hab : c.Uses b a := (List.isChain_cons_cons.1 hc).1
        obtain ⟨rest, e, hch, hlast, hmem⟩ := cycleAt_spec (List.isChain_cons_cons.1 hc).2 hyl
        have e' : cycleAt y (a :: b :: l') = cycleAt y (b :: l') ++ [a] := by
          simp only [cycleAt, if_neg ha]
        rw [e']
        refine ⟨rest ++ [a], by rw [e]; rfl, ?_, ?_, ?_⟩
        · refine isChain_append_singleton hch fun u hu => ?_
          rw [hlast, List.head?_cons, Option.mem_some_iff] at hu
          rw [← hu]
          exact hab
        · rw [List.getLast?_append, List.getLast?_singleton, List.head?_cons]
          rfl
        · intro z hz
          rcases List.mem_append.1 hz with hz | hz
          · exact List.mem_cons_of_mem _ (hmem z hz)
          · rw [List.mem_singleton.1 hz]
            exact List.mem_cons_self

theorem walk_inl {B path path' : List α}
    {hs : (c.walk B).measure path' < (c.walk B).measure path}
    (hBI : ∀ x ∈ B, x ∈ c.items) (inv : c.WalkInv B path)
    (e : (c.walk B).step path = .inl ⟨path', hs⟩) : c.WalkInv B path' := by
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil inv.ne_nil
  simp only [walk, walkStep] at e
  split at e
  · cases e
  · rename_i y h
    by_cases hy : y ∈ x :: rest
    · rw [dif_pos hy] at e; cases e
    · rw [dif_neg hy] at e
      have e' := congrArg Subtype.val (Sum.inl.inj e)
      dsimp only at e'
      subst e'
      obtain ⟨hd, hyB⟩ := c.nextIn_spec h
      refine ⟨List.cons_ne_nil _ _, fun z hz => ?_, ?_⟩
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact hyB
        · exact inv.sub z hz
      · exact List.isChain_cons_cons.2 ⟨⟨hBI x (inv.sub x List.mem_cons_self), hd⟩, inv.chain⟩

theorem walk_inr {B path w : List α} (hB : c.Blocked B) (hBI : ∀ x ∈ B, x ∈ c.items)
    (inv : c.WalkInv B path) (e : (c.walk B).step path = .inr w) :
    c.IsCycle w ∧ ∀ z ∈ w, z ∈ B := by
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil inv.ne_nil
  simp only [walk, walkStep] at e
  split at e
  · rename_i h
    obtain ⟨y, hy, hyB⟩ := hB.closed x (inv.sub x List.mem_cons_self)
    exact absurd h (c.nextIn_ne_none hy hyB)
  · rename_i y h
    by_cases hy : y ∈ x :: rest
    · rw [dif_pos hy] at e
      have e' := Sum.inr.inj e
      subst e'
      obtain ⟨hd, -⟩ := c.nextIn_spec h
      obtain ⟨rest', e, hch, hlast, hmem⟩ := c.cycleAt_spec inv.chain hy
      refine ⟨⟨y, rest', e, ?_⟩, fun z hz => inv.sub z (hmem z hz)⟩
      rw [← e]
      refine isChain_append_singleton hch fun u hu => ?_
      rw [hlast, List.head?_cons, Option.mem_some_iff] at hu
      rw [← hu]
      exact ⟨hBI x (inv.sub x List.mem_cons_self), hd⟩
    · rw [dif_neg hy] at e; cases e

/-- **The cycle found through a blocked set is a cycle inside it.** -/
theorem findCycle_spec {B : List α} (hB : c.Blocked B) (hBI : ∀ x ∈ B, x ∈ c.items) :
    c.IsCycle (c.findCycle B) ∧ ∀ z ∈ c.findCycle B, z ∈ B := by
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hB.ne_nil
  exact (c.walk _).run_induction (c.WalkInv (x :: rest))
    (fun w => c.IsCycle w ∧ ∀ z ∈ w, z ∈ x :: rest)
    (fun _ _ _ inv e => c.walk_inl hBI inv e) (fun _ _ inv e => c.walk_inr hB hBI inv e)
    _ (c.walkInv_start List.mem_cons_self)

/-- **Cycle detection** over the whole catalogue. -/
def cycle? : Option (List α) :=
  match c.schedule c.items with
  | .waves _ => none
  | .blocked B => some (c.findCycle B)

theorem cycle?_sound {w : List α} (h : c.cycle? = some w) :
    c.IsCycle w ∧ ∀ z ∈ w, z ∈ c.items := by
  unfold cycle? at h
  have spec := c.schedule_spec c.items
  split at h
  · cases h
  · rename_i B hs
    cases h
    rw [hs] at spec
    obtain ⟨hB, hsub⟩ := spec
    obtain ⟨hc, hm⟩ := c.findCycle_spec hB hsub
    exact ⟨hc, fun z hz => hsub z (hm z hz)⟩

theorem cycle?_none (h : c.cycle? = none) (a : α) : ¬ TransGen c.Uses a a := by
  unfold cycle? at h
  have spec := c.schedule_spec c.items
  split at h
  · rename_i ws hs
    rw [hs] at spec
    obtain ⟨hcov, hresp, -⟩ := spec
    exact hresp.acyclic (fun x hx => (hcov x).2 hx) a
  · cases h

/-- **Cycle detection is sound and complete.** -/
theorem cycle?_isSome_iff : c.cycle?.isSome ↔ ∃ a, TransGen c.Uses a a := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 h
    exact (c.cycle?_sound hw).1.transGen
  · rintro ⟨a, t⟩
    cases hc : c.cycle? with
    | none => exact absurd t (c.cycle?_none hc a)
    | some w => rfl

/-! ## Recursion over dependencies -/

/-- An acyclicity certificate: a rebuild order of the whole catalogue. -/
structure Acyclic where
  order : List α
  respects : c.Respects order
  covers : ∀ x ∈ c.items, x ∈ order

/-- The certificate from the schedule of the whole catalogue, when there is
one. -/
def acyclic? : Option c.Acyclic :=
  match h : c.schedule c.items with
  | .waves ws =>
      have spec : c.ScheduleSpec c.items (.waves ws) := h ▸ c.schedule_spec c.items
      some ⟨ws.flatten, spec.2.1, fun x hx => (spec.1 x).2 hx⟩
  | .blocked _ => none

theorem acyclic?_isSome_iff : c.acyclic?.isSome ↔ ∀ a, ¬ TransGen c.Uses a a := by
  constructor
  · intro h a
    obtain ⟨A, -⟩ := Option.isSome_iff_exists.1 h
    exact A.respects.acyclic A.covers a
  · intro h
    have hc : c.cycle? = none := by
      cases hc : c.cycle? with
      | none => rfl
      | some w =>
          obtain ⟨a, t⟩ := (c.cycle?_sound hc).1.transGen
          exact absurd t (h a)
    unfold cycle? at hc
    unfold acyclic?
    split
    · rfl
    · rename_i B hs
      rw [hs] at hc
      cases hc

namespace Acyclic

variable {c}

/-- **Every item is accessible** for the dependency relation of an acyclic
catalogue. -/
theorem accCode (A : c.Acyclic) (x : α) : AccCode (fun y x => c.Uses x y) x :=
  (accCode_measure (c.orderMeasure A.order) x).mono fun _ _ hu =>
    A.respects.orderMeasure_lt A.covers hu

/-- **Measure-based recursion over dependencies**, with the rebuild order as
the measure. -/
def recOrder (A : c.Acyclic) {C : α → Sort v} (F : ∀ x, (∀ y, c.Uses x y → C y) → C x)
    (x : α) : C x :=
  recMeasure (c.orderMeasure A.order)
    (fun x ih => F x fun y hy => ih y (A.respects.orderMeasure_lt A.covers hy)) x

theorem recOrder_eq (A : c.Acyclic) {C : α → Sort v} (F : ∀ x, (∀ y, c.Uses x y → C y) → C x)
    (x : α) : A.recOrder F x = F x fun y _ => A.recOrder F y :=
  recMeasure_eq _ _ x

/-- **Recursion over dependencies through the accessibility route.** -/
def recAcc (A : c.Acyclic) (I : InertRecursor.{u + 1, v} fun y x => c.Uses x y) {C : α → Sort v}
    (F : ∀ x, (∀ y, c.Uses x y → C y) → C x) (x : α) : C x :=
  I.recursor F x (A.accCode x)

/-- **Agreement.** -/
theorem recAcc_eq (A : c.Acyclic) (I : InertRecursor.{u + 1, v} fun y x => c.Uses x y)
    {C : α → Sort v} (F : ∀ x, (∀ y, c.Uses x y → C y) → C x) (x : α) :
    A.recAcc I F x = A.recOrder F x :=
  I.rec_eq_of_fix F (A.recOrder F) (A.recOrder_eq F) _

/-- **Uniqueness**: every function satisfying the recursion equation is the
recursion. -/
theorem eq_recOrder (A : c.Acyclic) {C : α → Sort v} (F : ∀ x, (∀ y, c.Uses x y → C y) → C x)
    (g : ∀ x, C x) (hg : ∀ x, g x = F x fun y _ => g y) (x : α) : g x = A.recOrder F x := by
  rw [← A.recAcc_eq (InertRecursor.ofAcc _) F x]
  exact ((InertRecursor.ofAcc _).rec_eq_of_fix F g hg _).symm

/-- **Locality**: two recursions agree on a set closed under dependencies on
which their steps agree. -/
theorem recOrder_congr (A : c.Acyclic) {C : α → Sort v}
    (F₁ F₂ : ∀ x, (∀ y, c.Uses x y → C y) → C x) (S : α → Prop)
    (hS : ∀ x y, S x → c.Uses x y → S y)
    (hF : ∀ x, S x → ∀ k₁ k₂ : ∀ y, c.Uses x y → C y, (∀ y h, k₁ y h = k₂ y h) →
      F₁ x k₁ = F₂ x k₂) (x : α) (hx : S x) : A.recOrder F₁ x = A.recOrder F₂ x := by
  induction acc_of_accCode (A.accCode x) with
  | intro x _ ih =>
      rw [A.recOrder_eq F₁, A.recOrder_eq F₂]
      exact hF x hx _ _ fun y h => ih y h (hS x y hx h)

end Acyclic

/-! ## Folds over dependencies -/

/-- One step of a dependency fold: combine an item with the values at its
dependencies, in the order the catalogue lists them. -/
def foldStep {β : Type v} (f : α → List β → β) (x : α) (k : ∀ y, c.Uses x y → β) : β :=
  if hx : x ∈ c.items then f x ((c.deps x).attach.map fun y => k y.1 ⟨hx, y.2⟩) else f x []

/-- **A dependency fold**: the value at an item combines the item with the
values at its dependencies. Derivation keys, critical-path lengths and
transitive input lists are instances. -/
def depFold (A : c.Acyclic) {β : Type v} (f : α → List β → β) : α → β :=
  A.recOrder (c.foldStep f)

/-- The same fold through the accessibility route. -/
def depFoldAcc (A : c.Acyclic) (I : InertRecursor.{u + 1, v + 1} fun y x => c.Uses x y)
    {β : Type v} (f : α → List β → β) : α → β :=
  A.recAcc I (c.foldStep f)

theorem depFoldAcc_eq (A : c.Acyclic) (I : InertRecursor.{u + 1, v + 1} fun y x => c.Uses x y)
    {β : Type v} (f : α → List β → β) (x : α) : c.depFoldAcc A I f x = c.depFold A f x :=
  A.recAcc_eq I _ x

/-- The equation of a dependency fold. -/
theorem depFold_eq (A : c.Acyclic) {β : Type v} (f : α → List β → β) (x : α) :
    c.depFold A f x = f x (if x ∈ c.items then (c.deps x).map (c.depFold A f) else []) := by
  rw [depFold, Acyclic.recOrder_eq]
  unfold foldStep
  by_cases hx : x ∈ c.items
  · rw [dif_pos hx, if_pos hx]
    congr 1
    conv_rhs => rw [← List.attach_map_subtype_val (c.deps x), List.map_map]
    rfl
  · rw [dif_neg hx, if_neg hx]

/-- **Incremental rebuild is sound.** If a fold changes only at changed items,
its values outside the affected set do not change. -/
theorem depFold_eq_of_not_affected (A : c.Acyclic) {β : Type v} (f₁ f₂ : α → List β → β)
    (changed : List α) (hf : ∀ x, x ∉ changed → f₁ x = f₂ x) {x : α}
    (hx : x ∉ c.affected changed) : c.depFold A f₁ x = c.depFold A f₂ x := by
  refine A.recOrder_congr _ _ (fun x => x ∉ c.affected changed) ?_ ?_ x hx
  · intro x y hx hu hy
    obtain ⟨z, hz, r⟩ := (c.mem_affected changed y).1 hy
    exact hx ((c.mem_affected changed x).2 ⟨z, hz, .head hu r⟩)
  · intro x hx k₁ k₂ hk
    have hxc : x ∉ changed := fun h => hx ((c.mem_affected changed x).2 ⟨x, h, .refl⟩)
    unfold foldStep
    rw [hf x hxc]
    split
    · congr 1
      exact List.map_congr_left fun y _ => hk _ _
    · rfl

/-! ## Independent derivations of dependency-fold values -/

/-- A catalogue is closed when every dependency of an admitted item is also
admitted. A missing item cannot silently be treated as a leaf. -/
def DependencyClosed : Prop := ∀ x ∈ c.items, ∀ y ∈ c.deps x, y ∈ c.items

/-- Independent evaluation by the listed dependencies. The premise retains
their order and multiplicity; the computed fold is not a premise. -/
inductive FoldDerivation {β : Type v} (combine : α → List β → β) : α → β → Prop where
  | node {item : α} {values : List β}
      (admitted : item ∈ c.items)
      (children : List.Forall₂ (FoldDerivation combine) (c.deps item) values) :
      FoldDerivation combine item (combine item values)

/-- Every independently derived value agrees with the existing executable
fold. The proof follows the catalogue's established accessibility relation. -/
theorem FoldDerivation.value_eq_depFold (A : c.Acyclic) {β : Type v}
    (combine : α → List β → β) (item : α) :
    ∀ value, c.FoldDerivation combine item value → value = c.depFold A combine item := by
  induction acc_of_accCode (A.accCode item) with
  | intro item _ ih =>
    intro value derived
    cases derived with
    | node admitted children =>
      have values : ∀ {dependencies values},
          List.Forall₂ (c.FoldDerivation combine) dependencies values →
          (∀ child ∈ dependencies, child ∈ c.deps item) →
          values = dependencies.map (c.depFold A combine) := by
        intro dependencies values derivations
        induction derivations with
        | nil => intro _; rfl
        | @cons child value rest values derivation remaining inductionHypothesis =>
          intro included
          rw [List.map_cons, ih child ⟨admitted, included child List.mem_cons_self⟩ value derivation,
            inductionHypothesis (fun other member => included other (List.mem_cons_of_mem _ member))]
      rw [values children (fun _ member => member), c.depFold_eq A combine item,
        if_pos admitted]

/-- A closed acyclic catalogue derives the executable fold's value at every
admitted item, by the independent judgment. -/
theorem depFold_has_derivation (A : c.Acyclic) {β : Type v}
    (combine : α → List β → β) (closed : c.DependencyClosed) (item : α)
    (admitted : item ∈ c.items) :
    c.FoldDerivation combine item (c.depFold A combine item) := by
  induction acc_of_accCode (A.accCode item) with
  | intro item _ ih =>
    rw [c.depFold_eq A combine item, if_pos admitted]
    apply FoldDerivation.node admitted
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro child member
    exact ih child ⟨admitted, member⟩ (closed item admitted child member)

theorem foldDerivation_iff (A : c.Acyclic) {β : Type v}
    (combine : α → List β → β) (closed : c.DependencyClosed)
    (item : α) (admitted : item ∈ c.items) (value : β) :
    c.FoldDerivation combine item value ↔ value = c.depFold A combine item := by
  constructor
  · exact FoldDerivation.value_eq_depFold c A combine item value
  · intro equal
    rw [equal]
    exact c.depFold_has_derivation A combine closed item admitted

/-- Total occurrence work unfolds each dependency occurrence. Memoizing a
child fold does not remove a repeated child's contribution from the sum. -/
abbrev unfoldingWork (A : c.Acyclic) (localWork : α → Nat) : α → Nat :=
  c.depFold A (fun item childWork => localWork item + childWork.sum)

theorem unfoldingWork_eq (A : c.Acyclic) (localWork : α → Nat)
    (item : α) (admitted : item ∈ c.items) :
    c.unfoldingWork A localWork item =
      localWork item + ((c.deps item).map (c.unfoldingWork A localWork)).sum := by
  exact (c.depFold_eq A (fun item childWork => localWork item + childWork.sum) item).trans
    (by rw [if_pos admitted])

end Catalogue

/-! ## Bounded traversal of physical occurrence rows

The traversal stores a completed child's value once, while adding that value
for every distinct referring row. Its independent specification is the
catalogue's existing `FoldDerivation`, not the traversal's own cache.
Source coverage, terminal inertness, and the lifetime of a native graph are
separate adapter obligations. -/

namespace OccurrenceGraph

structure Row where
  physical : Nat
  successor : Option Nat
  deriving DecidableEq, Repr

structure Graph where
  nodes : List (List Row)
  deriving DecidableEq, Repr

def Graph.rows (graph : Graph) (node : Nat) : List Row :=
  (graph.nodes[node]?).getD []

def Graph.catalogue (graph : Graph) : Catalogue Nat where
  items := List.range graph.nodes.length
  deps node := (graph.rows node).filterMap Row.successor

def Graph.combine (graph : Graph) (node : Nat) (children : List Nat) : Nat :=
  (graph.rows node).length + children.sum

abbrev Graph.Derived (graph : Graph) : Nat → Nat → Prop :=
  graph.catalogue.FoldDerivation graph.combine

inductive RowValue (graph : Graph) : Row → Nat → Prop where
  | terminal (physical : Nat) : RowValue graph ⟨physical, none⟩ 1
  | linked (physical child value : Nat) (derived : graph.Derived child value) :
      RowValue graph ⟨physical, some child⟩ (1 + value)

/-- Ordered row contributions yield ordered child derivations. Terminal rows
still contribute one, and repeated references are not deduplicated. -/
theorem rows_derive (graph : Graph) {rows : List Row} {values : List Nat}
    (derived : List.Forall₂ (RowValue graph) rows values) :
    ∃ children,
      List.Forall₂ graph.Derived (rows.filterMap Row.successor) children ∧
        values.sum = rows.length + children.sum := by
  induction derived with
  | nil => exact ⟨[], .nil, rfl⟩
  | @cons row value rows values rowDerived remaining ih =>
    obtain ⟨children, childDerived, total⟩ := ih
    cases rowDerived with
    | terminal physical =>
      refine ⟨children, ?_, ?_⟩
      · simpa only [List.filterMap_cons, Row.successor] using childDerived
      · simp only [List.sum_cons, List.length_cons]
        omega
    | linked physical child value derived =>
      refine ⟨value :: children, ?_, ?_⟩
      · simpa only [List.filterMap_cons, Row.successor] using
          List.Forall₂.cons derived childDerived
      · simp only [List.sum_cons, List.length_cons]
        omega

structure Frame where
  node : Nat
  row : Nat := 0
  total : Nat := 0
  deriving DecidableEq, Repr

inductive Color where
  | fresh | active | done
  deriving DecidableEq, Repr

inductive Status where
  | pending | bound | cycle | invalid | overflow
  deriving DecidableEq, Repr

structure State where
  root : Nat
  capacity : Nat
  stack : List Frame
  colors : Nat → Color
  memo : Nat → Nat
  ticks : Nat := 0
  indexVisits : Nat := 0
  status : Status := .pending

def init (graph : Graph) (root : Nat) : Option State :=
  if root < graph.nodes.length then
    some {
      root := root
      capacity := graph.nodes.length
      stack := [⟨root, 0, 0⟩]
      colors := Function.update (fun _ => .fresh) root .active
      memo := fun _ => 0 }
  else none

def fail (state : State) (status : Status) : State :=
  { state with status }

def finish (state : State) (frame : Frame) (rest : List Frame) : State :=
  { state with
    stack := rest
    colors := Function.update state.colors frame.node .done
    memo := Function.update state.memo frame.node frame.total
    status := if rest.isEmpty then .bound else .pending }

def push (state : State) (child : Nat) : State :=
  { state with
    stack := ⟨child, 0, 0⟩ :: state.stack
    colors := Function.update state.colors child .active }

def advance (state : State) (frame : Frame) (rest : List Frame)
    (contribution : Nat) : State :=
  { state with
    stack := { frame with row := frame.row + 1, total := frame.total + contribution } :: rest }

def addRow (maximum : Nat) (state : State) (frame : Frame) (rest : List Frame)
    (contribution : Nat) : State :=
  if maximum < frame.total + contribution then fail state .overflow
  else advance state frame rest contribution

/-- The scalar control order of the native graph service. Array access and
counter charging have their own memory and account interpretations. -/
def step (graph : Graph) (maximum : Nat) (state : State) : State :=
  if state.status ≠ .pending then state
  else if state.capacity ≠ graph.nodes.length ∨ state.stack = [] ∨ state.ticks = maximum then
    fail state .invalid
  else
    let paid := { state with ticks := state.ticks + 1 }
    match state.stack with
    | [] => fail paid .invalid
    | frame :: rest =>
      let rows := graph.rows frame.node
      if frame.row = rows.length then finish paid frame rest
      else match rows[frame.row]? with
      | none => fail paid .invalid
      | some row =>
        if row.physical = 0 ∨ (row.successor.any fun child => graph.nodes.length ≤ child) then
          fail paid .invalid
        else
          let previous := rows.take frame.row
          match previous.findIdx? (fun earlier => earlier.physical == row.physical) with
          | some index => fail { paid with indexVisits := paid.indexVisits + index + 1 } .invalid
          | none =>
            let scanned := { paid with indexVisits := paid.indexVisits + frame.row }
            match row.successor with
            | none => addRow maximum scanned frame rest 1
            | some child =>
              match state.colors child with
              | .active => fail scanned .cycle
              | .fresh =>
                if state.stack.length = state.capacity then fail scanned .invalid
                else push scanned child
              | .done =>
                if state.memo child = maximum then fail scanned .overflow
                else addRow maximum scanned frame rest (1 + state.memo child)

/-- A bounded call retains the full DFS stack, memo and accounting cursor. -/
def run (graph : Graph) (maximum : Nat) : Nat → State → State
  | 0, state => state
  | fuel + 1, state => run graph maximum fuel (step graph maximum state)

def bound? (state : State) : Option Nat :=
  if state.status = .bound then some (state.memo state.root) else none

def Rooted (root : Nat) : List Frame → Prop
  | [] => True
  | [frame] => frame.node = root
  | _ :: second :: rest => Rooted root (second :: rest)

def Graph.FrameDerived (graph : Graph) (maximum : Nat) (frame : Frame) : Prop :=
  frame.node < graph.nodes.length ∧ frame.row ≤ (graph.rows frame.node).length ∧
    frame.total ≤ maximum ∧
      ∃ values, List.Forall₂ (RowValue graph) ((graph.rows frame.node).take frame.row) values ∧
        frame.total = values.sum

structure Valid (graph : Graph) (maximum : Nat) (state : State) : Prop where
  frames : ∀ frame ∈ state.stack, graph.FrameDerived maximum frame
  ticksWithin : state.ticks ≤ maximum
  cached : ∀ node, state.colors node = .done →
    graph.Derived node (state.memo node) ∧ state.memo node ≤ maximum
  rooted : Rooted state.root state.stack
  completed : state.status = .bound → state.colors state.root = .done

theorem frame_zero (graph : Graph) (maximum node : Nat)
    (admitted : node < graph.nodes.length) :
    graph.FrameDerived maximum ⟨node, 0, 0⟩ := by
  exact ⟨admitted, Nat.zero_le _, Nat.zero_le _, [], by simp, rfl⟩

theorem frame_complete (graph : Graph) (maximum : Nat) (frame : Frame)
    (valid : graph.FrameDerived maximum frame)
    (finished : frame.row = (graph.rows frame.node).length) :
    graph.Derived frame.node frame.total := by
  obtain ⟨admitted, _, _, values, rows, total⟩ := valid
  rw [finished, List.take_length] at rows
  obtain ⟨children, derived, sum⟩ := rows_derive graph rows
  rw [total, sum]
  exact Catalogue.FoldDerivation.node (by simpa [Graph.catalogue] using admitted) derived

theorem frame_advance (graph : Graph) (maximum : Nat) (frame : Frame)
    (valid : graph.FrameDerived maximum frame)
    (available : frame.row < (graph.rows frame.node).length) (contribution : Nat)
    (derived : RowValue graph (graph.rows frame.node)[frame.row] contribution)
    (within : frame.total + contribution ≤ maximum) :
    graph.FrameDerived maximum
      { frame with row := frame.row + 1, total := frame.total + contribution } := by
  obtain ⟨admitted, _, _, values, rows, total⟩ := valid
  change frame.node < graph.nodes.length ∧ frame.row + 1 ≤ (graph.rows frame.node).length ∧
    frame.total + contribution ≤ maximum ∧ _
  refine ⟨admitted, by omega, within, values ++ [contribution], ?_, ?_⟩
  · rw [List.take_succ_eq_append_getElem available]
    exact List.rel_append rows (.cons derived .nil)
  · simp only [List.sum_append, List.sum_singleton, total]

theorem run_add (graph : Graph) (maximum first second : Nat) (state : State) :
    run graph maximum (first + second) state =
      run graph maximum second (run graph maximum first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih => simpa only [Nat.succ_add, run] using ih (step graph maximum state)

theorem Valid.withCounters {graph : Graph} {maximum : Nat} {state : State}
    (valid : Valid graph maximum state) (ticks visits : Nat) (within : ticks ≤ maximum) :
    Valid graph maximum { state with ticks := ticks, indexVisits := visits } :=
  ⟨valid.frames, within, valid.cached, valid.rooted, valid.completed⟩

theorem Valid.fail {graph : Graph} {maximum : Nat} {state : State}
    (valid : Valid graph maximum state) (status : Status) (notBound : status ≠ .bound) :
    Valid graph maximum (OccurrenceGraph.fail state status) := by
  refine ⟨valid.frames, valid.ticksWithin, valid.cached, valid.rooted, ?_⟩
  intro completed
  exact False.elim (notBound completed)

theorem Rooted.tail (root : Nat) (frame : Frame) (rest : List Frame)
    (rooted : Rooted root (frame :: rest)) : Rooted root rest := by
  cases rest with
  | nil => trivial
  | cons second rest => exact rooted

theorem init_valid (graph : Graph) (maximum root : Nat) (state : State)
    (issued : init graph root = some state) : Valid graph maximum state := by
  unfold init at issued
  split at issued
  · rename_i admitted
    cases issued
    refine ⟨?_, Nat.zero_le _, ?_, rfl, ?_⟩
    · intro frame member
      have equal : frame = ⟨root, 0, 0⟩ := List.mem_singleton.1 member
      subst frame
      exact frame_zero graph maximum root admitted
    · intro node done
      simp only [Function.update_apply] at done
      split at done <;> contradiction
    · intro completed
      cases completed
  · contradiction

theorem Valid.finish {graph : Graph} {maximum : Nat} {state : State}
    (valid : Valid graph maximum state) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest)
    (finished : frame.row = (graph.rows frame.node).length) :
    Valid graph maximum (OccurrenceGraph.finish state frame rest) := by
  have frameValid := valid.frames frame (by simp [stack])
  refine ⟨?_, valid.ticksWithin, ?_, ?_, ?_⟩
  · intro other member
    exact valid.frames other (by simp only [stack, List.mem_cons]; exact Or.inr member)
  · intro node done
    by_cases equal : node = frame.node
    · subst node
      simpa only [OccurrenceGraph.finish, Function.update_self] using
        And.intro (frame_complete graph maximum frame frameValid finished) frameValid.2.2.1
    · have previous : state.colors node = .done := by
        simpa only [OccurrenceGraph.finish, Function.update_of_ne equal] using done
      simpa only [OccurrenceGraph.finish, Function.update_of_ne equal] using valid.cached node previous
  · exact Rooted.tail state.root frame rest (by simpa only [stack] using valid.rooted)
  · intro completed
    cases rest with
    | nil =>
      have root : frame.node = state.root := by
        simpa only [stack, Rooted] using valid.rooted
      simp only [OccurrenceGraph.finish, ← root, Function.update_self]
    | cons second rest => simp [OccurrenceGraph.finish] at completed

theorem Valid.push {graph : Graph} {maximum : Nat} {state : State}
    (valid : Valid graph maximum state) (child : Nat)
    (admitted : child < graph.nodes.length) (nonempty : state.stack ≠ [])
    (pending : state.status = .pending) : Valid graph maximum (OccurrenceGraph.push state child) := by
  refine ⟨?_, valid.ticksWithin, ?_, ?_, ?_⟩
  · intro frame member
    rcases List.mem_cons.1 member with equal | member
    · subst frame
      exact frame_zero graph maximum child admitted
    · exact valid.frames frame member
  · intro node done
    by_cases equal : node = child
    · subst node
      simp [OccurrenceGraph.push] at done
    · have previous : state.colors node = .done := by
        simpa only [OccurrenceGraph.push, Function.update_of_ne equal] using done
      exact valid.cached node previous
  · cases stack : state.stack with
    | nil => exact False.elim (nonempty stack)
    | cons frame rest => simpa only [OccurrenceGraph.push, stack, Rooted] using valid.rooted
  · intro completed
    simp [OccurrenceGraph.push, pending] at completed

theorem Valid.advance {graph : Graph} {maximum : Nat} {state : State}
    (valid : Valid graph maximum state) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest)
    (available : frame.row < (graph.rows frame.node).length) (contribution : Nat)
    (derived : RowValue graph (graph.rows frame.node)[frame.row] contribution)
    (within : frame.total + contribution ≤ maximum) :
    Valid graph maximum (OccurrenceGraph.advance state frame rest contribution) := by
  refine ⟨?_, valid.ticksWithin, valid.cached, ?_, valid.completed⟩
  · intro other member
    rcases List.mem_cons.1 member with equal | member
    · subst other
      exact frame_advance graph maximum frame (valid.frames frame (by simp [stack]))
        available contribution derived within
    · exact valid.frames other (by simp only [stack, List.mem_cons]; exact Or.inr member)
  · cases rest with
    | nil => simpa only [OccurrenceGraph.advance, stack, Rooted] using valid.rooted
    | cons second rest => simpa only [OccurrenceGraph.advance, stack, Rooted] using valid.rooted

theorem Valid.addRow {graph : Graph} {maximum : Nat} {state : State}
    (valid : Valid graph maximum state) (frame : Frame) (rest : List Frame)
    (stack : state.stack = frame :: rest)
    (available : frame.row < (graph.rows frame.node).length) (contribution : Nat)
    (derived : RowValue graph (graph.rows frame.node)[frame.row] contribution) :
    Valid graph maximum (OccurrenceGraph.addRow maximum state frame rest contribution) := by
  unfold OccurrenceGraph.addRow
  split
  · exact valid.fail .overflow (by decide)
  · rename_i within
    exact valid.advance frame rest stack available contribution derived (by omega)

theorem addRow_guard_eq (maximum total contribution : Nat) (within : total ≤ maximum) :
    (maximum < total + contribution) ↔ (maximum - total < contribution) := by omega

theorem RowValue.of_terminal (graph : Graph) (row : Row)
    (terminal : row.successor = none) : RowValue graph row 1 := by
  cases row with
  | mk physical successor =>
    change successor = none at terminal
    subst successor
    exact RowValue.terminal physical

theorem RowValue.of_linked (graph : Graph) (row : Row) (child value : Nat)
    (linked : row.successor = some child) (derived : graph.Derived child value) :
    RowValue graph row (1 + value) := by
  cases row with
  | mk physical successor =>
    change successor = some child at linked
    subst successor
    exact RowValue.linked physical child value derived

/-- Every scalar traversal transition preserves independently justified
completed entries and the full ordered prefix of every unfinished frame. -/
theorem step_valid (graph : Graph) (maximum : Nat) (state : State)
    (valid : Valid graph maximum state) : Valid graph maximum (step graph maximum state) := by
  unfold step
  split
  · exact valid
  · rename_i isPending
    have pending : state.status = .pending := by
      by_cases equal : state.status = .pending
      · exact equal
      · exact False.elim (isPending equal)
    split
    · exact valid.fail .invalid (by decide)
    · rename_i admitted
      have beforeLimit : state.ticks ≠ maximum := fun equal =>
        admitted (Or.inr (Or.inr equal))
      let paid : State := { state with ticks := state.ticks + 1 }
      have paidValid : Valid graph maximum paid :=
        valid.withCounters (state.ticks + 1) state.indexVisits (by
          have := valid.ticksWithin
          omega)
      cases stack : state.stack with
      | nil =>
        simp only
        simpa only [paid, stack] using paidValid.fail .invalid (by decide)
      | cons frame rest =>
        simp only
        split
        · rename_i finished
          exact paidValid.finish frame rest stack finished
        · cases found : (graph.rows frame.node)[frame.row]? with
          | none =>
            simp only
            simpa only [paid, stack] using paidValid.fail .invalid (by decide)
          | some row =>
            simp only
            obtain ⟨available, rowEqual⟩ := List.getElem?_eq_some_iff.1 found
            split
            · simpa only [paid, stack] using paidValid.fail .invalid (by decide)
            · rename_i rowValid
              cases visited : ((graph.rows frame.node).take frame.row).findIdx?
                  (fun earlier => earlier.physical == row.physical) with
              | some index =>
                simp only
                simpa only [paid, stack] using
                  (paidValid.withCounters paid.ticks (paid.indexVisits + index + 1)
                    paidValid.ticksWithin).fail .invalid (by decide)
              | none =>
                simp only
                let scanned : State := { paid with indexVisits := paid.indexVisits + frame.row }
                have scannedValid : Valid graph maximum scanned :=
                  paidValid.withCounters paid.ticks (paid.indexVisits + frame.row)
                    paidValid.ticksWithin
                cases successor : row.successor with
                | none =>
                  simp only
                  have derived : RowValue graph (graph.rows frame.node)[frame.row] 1 := by
                    rw [rowEqual]
                    exact RowValue.of_terminal graph row successor
                  simpa only [scanned, paid, stack] using
                    scannedValid.addRow frame rest stack available 1 derived
                | some child =>
                  simp only
                  have childAdmitted : child < graph.nodes.length := by
                    have excluded : ¬graph.nodes.length ≤ child := by
                      intro outside
                      apply rowValid
                      exact Or.inr (by simp [successor, outside])
                    omega
                  cases color : state.colors child with
                  | active =>
                    simp only
                    simpa only [scanned, paid, stack] using scannedValid.fail .cycle (by decide)
                  | fresh =>
                    simp only
                    split
                    · simpa only [scanned, paid, stack] using scannedValid.fail .invalid (by decide)
                    · simpa only [scanned, paid, stack] using
                        scannedValid.push child childAdmitted (by simp [scanned, paid, stack]) pending
                  | done =>
                    simp only
                    split
                    · simpa only [scanned, paid, stack] using scannedValid.fail .overflow (by decide)
                    · have derived : RowValue graph (graph.rows frame.node)[frame.row]
                          (1 + state.memo child) := by
                        rw [rowEqual]
                        exact RowValue.of_linked graph row child (state.memo child) successor
                          (valid.cached child color).1
                      simpa only [scanned, paid, stack] using
                        scannedValid.addRow frame rest stack available (1 + state.memo child) derived

theorem run_valid (graph : Graph) (maximum fuel : Nat) (state : State)
    (valid : Valid graph maximum state) :
    Valid graph maximum (run graph maximum fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih => exact ih (step graph maximum state) (step_valid graph maximum state valid)

/-- A reported bound has a derivation independent of the DFS memo, including
every listed dependency occurrence, and fits the selected scalar range. -/
theorem bound_derived (graph : Graph) (maximum : Nat) (state : State) (value : Nat)
    (valid : Valid graph maximum state) (reported : bound? state = some value) :
    graph.Derived state.root value ∧ value ≤ maximum := by
  unfold bound? at reported
  split at reported
  · rename_i completed
    cases reported
    exact valid.cached state.root (valid.completed completed)
  · contradiction

theorem bound_unfoldingWork (graph : Graph) (maximum : Nat) (state : State) (value : Nat)
    (acyclic : graph.catalogue.Acyclic) (valid : Valid graph maximum state)
    (reported : bound? state = some value) :
    value = graph.catalogue.unfoldingWork acyclic (fun node => (graph.rows node).length)
      state.root ∧ value ≤ maximum := by
  obtain ⟨derived, within⟩ := bound_derived graph maximum state value valid reported
  exact ⟨Catalogue.FoldDerivation.value_eq_depFold graph.catalogue acyclic graph.combine
    state.root value derived, within⟩

theorem step_root (graph : Graph) (maximum : Nat) (memory : State) :
    (step graph maximum memory).root = memory.root := by
  unfold step
  split
  · rfl
  · split
    · rfl
    · dsimp only
      cases stack : memory.stack with
      | nil => rfl
      | cons frame rest =>
        simp only
        split
        · rfl
        · cases found : (graph.rows frame.node)[frame.row]? with
          | none => rfl
          | some row =>
            simp only
            split
            · rfl
            · cases visited : ((graph.rows frame.node).take frame.row).findIdx?
                  (fun earlier => earlier.physical == row.physical) with
              | some index => rfl
              | none =>
                simp only
                cases successor : row.successor with
                | none => simp only; unfold addRow; split <;> rfl
                | some child =>
                  simp only
                  cases color : memory.colors child with
                  | active => rfl
                  | fresh => simp only; split <;> rfl
                  | done =>
                    simp only
                    split
                    · rfl
                    · unfold addRow; split <;> rfl
theorem run_root (graph : Graph) (maximum fuel : Nat) (state : State) :
    (run graph maximum fuel state).root = state.root := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => rw [run, ih, step_root]

theorem initialized_run_bound (graph : Graph) (maximum root fuel : Nat) (state : State)
    (issued : init graph root = some state) (value : Nat) (acyclic : graph.catalogue.Acyclic)
    (reported : bound? (run graph maximum fuel state) = some value) :
    value = graph.catalogue.unfoldingWork acyclic (fun node => (graph.rows node).length)
      root ∧ value ≤ maximum := by
  have rooted : state.root = root := by
    unfold init at issued
    split at issued
    · cases issued; rfl
    · contradiction
  have result := bound_unfoldingWork graph maximum (run graph maximum fuel state) value
    acyclic (run_valid graph maximum fuel state (init_valid graph maximum root state issued)) reported
  simpa only [run_root, rooted] using result

end OccurrenceGraph

end Mettapedia.Algorithms.WellFoundedServices
