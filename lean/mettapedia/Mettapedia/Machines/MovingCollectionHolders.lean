import Mathlib.Tactic
import Mathlib.Logic.Relation

/-!
# Moving collection and the holders it does not move

A copying collector copies what its listed holders reach into a fresh space,
rewrites those holders to the copies, and then frees the collected region.
Every other holder keeps its references as they were.  For a non-moving
collector it is enough that the roots reach an object for it to survive
(`NestedSafePoints.collect_keeps_held`).  For a moving collector it is not:
the object survives only as a copy, and a holder that was not rewritten still
names the original.

The model: a heap maps an address to a label and child addresses.  A
collection copies a set of addresses closed under the heap's edges (it
contains the listed holders) to `Sum.inr`, keeps every address outside the
freed region in place at `Sum.inl`, and frees the rest.  Values are compared
by unfolding the heap from an address to any finite depth.

This file proves:
* `unfold_moved`: a moved holder's value after the collection is its value
  before;
* `unfold_kept`: an unmoved holder keeps its value when everything it reaches
  lies outside the freed region;
* `kept_iff_avoids`: in a heap where everything the holder reaches is
  allocated, that condition is also necessary, so an exact admission check
  for an unmoved holder asks no more and no less;
* `release_keeps_iff_avoids`: releasing a region is a collection that moves
  nothing, so a holder sharing objects with a shorter-lived region must own
  copies, collector or not;
* `copy_survives_original_dangles`: an object the listed holders reach, in
  the freed region, survives as a copy while an unmoved holder of it dangles;
* `sharing_split`: a moved and an unmoved holder of one object end up with
  equal values at distinct addresses, so identity between them is not kept;
* `walk_sound`, `walk_sound_continued`: an audit that inspects each address
  once, fails at a freed one and pushes the children of each new address
  establishes that condition for every holder it starts from, also when later
  walks of one audit reuse the addresses earlier walks inspected;
* `closed_owner_sound`, `mixed_path_admitted`: a world laid out as a path of
  frames that is closed in one arena other than the freed one holds nothing in
  the freed arena, but a path through two other arenas also holds nothing
  there without being closed in either, so "closed" is a sufficient test and
  not the exact one.

These are abstract contracts.  They do not verify a particular runtime's
root enumeration or allocator.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.MovingCollectionHolders

open Relation

section Heap

variable {Label : Type}

/-- A heap: an allocated address holds a label and its children. -/
abbrev Heap (A Label : Type) := A → Option (Label × List A)

/-- What a holder sees from an address, unfolded to a finite depth. -/
inductive View (Label : Type) where
  | cut
  | dangling
  | node (label : Label) (children : List (View Label))

/-- A view contains a dangling reference somewhere. -/
inductive View.Dangles : View Label → Prop
  | here : View.Dangles .dangling
  | child {label : Label} {children : List (View Label)} {view : View Label} :
      view ∈ children → View.Dangles view → View.Dangles (.node label children)

variable {A : Type}

/-- Unfold the heap from an address to depth `n`. -/
def unfold (heap : Heap A Label) : ℕ → A → View Label
  | 0, _ => .cut
  | n + 1, a =>
    match heap a with
    | none => .dangling
    | some entry => .node entry.1 (entry.2.map (unfold heap n))

/-- One step of the heap's reference graph. -/
def Edge (heap : Heap A Label) (a b : A) : Prop :=
  ∃ entry, heap a = some entry ∧ b ∈ entry.2

/-- Everything reachable from `a` lies outside `freed`. -/
def Avoids (heap : Heap A Label) (freed : A → Prop) (a : A) : Prop :=
  ∀ b, ReflTransGen (Edge heap) a b → ¬ freed b

/-- Everything reachable from `a` is allocated. -/
def Allocated (heap : Heap A Label) (a : A) : Prop :=
  ∀ b, ReflTransGen (Edge heap) a b → heap b ≠ none

theorem Avoids.child {heap : Heap A Label} {freed : A → Prop} {a b : A}
    (h : Avoids heap freed a) (edge : Edge heap a b) : Avoids heap freed b :=
  fun c hc => h c (ReflTransGen.head edge hc)

theorem Allocated.child {heap : Heap A Label} {a b : A}
    (h : Allocated heap a) (edge : Edge heap a b) : Allocated heap b :=
  fun c hc => h c (ReflTransGen.head edge hc)

/-- A view unfolded from a fully allocated address never dangles. -/
theorem not_dangles_of_allocated (heap : Heap A Label) :
    ∀ n a, Allocated heap a → ¬ (unfold heap n a).Dangles := by
  intro n
  induction n with
  | zero => intro a _ h; cases h
  | succ n ih =>
    intro a ha h
    cases hheap : heap a with
    | none => exact ha a ReflTransGen.refl hheap
    | some entry =>
      simp only [unfold, hheap] at h
      cases h with
      | child hview hd =>
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hview
        exact ih b (ha.child ⟨entry, hheap, hb⟩) hd

end Heap

section Collection

variable {α Label : Type}

/-- A moving collection: the `moved` set is copied to `Sum.inr`, every
address outside `freed` stays at `Sum.inl`, and the rest is freed. -/
def collect (heap : Heap α Label) (moved freed : α → Prop)
    [DecidablePred moved] [DecidablePred freed] : Heap (α ⊕ α) Label
  | .inl a => if freed a then none else (heap a).map fun entry => (entry.1, entry.2.map Sum.inl)
  | .inr a => if moved a then (heap a).map fun entry => (entry.1, entry.2.map Sum.inr) else none

variable (heap : Heap α Label) (moved freed : α → Prop)
  [DecidablePred moved] [DecidablePred freed]

/-- A moved holder sees, after the collection, what it saw before. -/
theorem unfold_moved (closed : ∀ a b, moved a → Edge heap a b → moved b) :
    ∀ n a, moved a → unfold (collect heap moved freed) n (.inr a) = unfold heap n a := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a ha
    cases hheap : heap a with
    | none => simp [unfold, collect, ha, hheap]
    | some entry =>
      simp only [unfold, collect, ha, hheap, if_true, Option.map_some]
      congr 1
      rw [List.map_map]
      exact List.map_congr_left fun b hb => ih b (closed a b ha ⟨entry, hheap, hb⟩)

/-- An unmoved holder keeps its value when everything it reaches lies
outside the freed region. -/
theorem unfold_kept :
    ∀ n a, Avoids heap freed a → unfold (collect heap moved freed) n (.inl a) = unfold heap n a := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a ha
    have hfree : ¬ freed a := ha a ReflTransGen.refl
    cases hheap : heap a with
    | none => simp [unfold, collect, hfree, hheap]
    | some entry =>
      simp only [unfold, collect, hfree, hheap, if_false, Option.map_some]
      congr 1
      rw [List.map_map]
      exact List.map_congr_left fun b hb => ih b (ha.child ⟨entry, hheap, hb⟩)

/-- An unmoved holder that reaches the freed region sees a dangling
reference after the collection. -/
theorem dangles_of_reaches {a b : α} (path : ReflTransGen (Edge heap) a b) (hb : freed b) :
    ∃ n, (unfold (collect heap moved freed) n (.inl a)).Dangles := by
  induction path using ReflTransGen.head_induction_on with
  | refl =>
    have hfreed : collect heap moved freed (.inl b) = none := by simp [collect, hb]
    exact ⟨1, by simp only [unfold, hfreed]; exact View.Dangles.here⟩
  | @head x c edge _ ih =>
    obtain ⟨n, hn⟩ := ih
    by_cases hx : freed x
    · have hfreed : collect heap moved freed (.inl x) = none := by simp [collect, hx]
      exact ⟨1, by simp only [unfold, hfreed]; exact View.Dangles.here⟩
    · obtain ⟨entry, hentry, hc⟩ := edge
      have hkept : collect heap moved freed (.inl x) = some (entry.1, entry.2.map Sum.inl) := by
        simp [collect, hx, hentry]
      refine ⟨n + 1, ?_⟩
      simp only [unfold, hkept]
      exact View.Dangles.child
        (List.mem_map.mpr ⟨Sum.inl c, List.mem_map.mpr ⟨c, hc, rfl⟩, rfl⟩) hn

/-- For an unmoved holder in an allocated heap, keeping its value at every
depth is exactly avoiding the freed region. -/
theorem kept_iff_avoids {a : α} (allocated : Allocated heap a) :
    (∀ n, unfold (collect heap moved freed) n (.inl a) = unfold heap n a) ↔
      Avoids heap freed a := by
  constructor
  · intro keep b path hb
    obtain ⟨n, hn⟩ := dangles_of_reaches heap moved freed path hb
    rw [keep n] at hn
    exact not_dangles_of_allocated heap n a allocated hn
  · intro avoids n
    exact unfold_kept heap moved freed n a avoids

/-- Releasing a region is a collection that moves nothing: a holder keeps its
value exactly when it avoids the released region.  A holder that shares
objects with a shorter-lived region dangles when that region is released,
whether or not a collector ever runs; it must own copies instead. -/
theorem release_keeps_iff_avoids {a : α} (allocated : Allocated heap a) :
    (∀ n, unfold (collect heap (fun _ => False) freed) n (.inl a) = unfold heap n a) ↔
      Avoids heap freed a :=
  kept_iff_avoids heap (fun _ => False) freed allocated

/-- An object the listed holders reach, in the freed region, survives as a
copy, while an unmoved holder of the original sees it dangle. -/
theorem copy_survives_original_dangles
    (closed : ∀ a b, moved a → Edge heap a b → moved b)
    {a : α} (hmoved : moved a) (hfreed : freed a) :
    (∀ n, unfold (collect heap moved freed) n (.inr a) = unfold heap n a) ∧
      unfold (collect heap moved freed) 1 (.inl a) = .dangling := by
  refine ⟨fun n => unfold_moved heap moved freed closed n a hmoved, ?_⟩
  simp [unfold, collect, hfreed]

/-- A moved and an unmoved holder of one object, outside the freed region,
end up at distinct addresses with equal values. -/
theorem sharing_split
    (closed : ∀ a b, moved a → Edge heap a b → moved b)
    {a : α} (hmoved : moved a) (avoids : Avoids heap freed a) :
    (Sum.inr a : α ⊕ α) ≠ Sum.inl a ∧
      ∀ n, unfold (collect heap moved freed) n (.inr a) =
        unfold (collect heap moved freed) n (.inl a) := by
  refine ⟨Sum.inr_ne_inl, fun n => ?_⟩
  rw [unfold_moved heap moved freed closed n a hmoved, unfold_kept heap moved freed n a avoids]

/-- Moved holders share an object afterwards exactly when they did before. -/
theorem moved_sharing_iff (a b : α) : (Sum.inr a : α ⊕ α) = Sum.inr b ↔ a = b :=
  Sum.inr_injective.eq_iff

/-- The whole contract: listed holders moved, unlisted holders avoiding the
freed region, and every holder keeps its value. -/
theorem collect_preserves
    (closed : ∀ a b, moved a → Edge heap a b → moved b)
    (listed unlisted : List α) (hlisted : ∀ a ∈ listed, moved a)
    (hunlisted : ∀ a ∈ unlisted, Avoids heap freed a) :
    (∀ a ∈ listed, ∀ n, unfold (collect heap moved freed) n (.inr a) = unfold heap n a) ∧
      (∀ a ∈ unlisted, ∀ n, unfold (collect heap moved freed) n (.inl a) = unfold heap n a) :=
  ⟨fun a ha n => unfold_moved heap moved freed closed n a (hlisted a ha),
    fun a ha n => unfold_kept heap moved freed n a (hunlisted a ha)⟩

end Collection

section Walk

variable {A Label : Type} [DecidableEq A]

/-- The children an address holds; an unallocated address holds none. -/
def children (heap : Heap A Label) (a : A) : List A :=
  match heap a with
  | none => []
  | some entry => entry.2

omit [DecidableEq A] in
theorem mem_children {heap : Heap A Label} {a b : A} :
    b ∈ children heap a ↔ Edge heap a b := by
  unfold children Edge
  cases heap a with
  | none => simp
  | some entry => simp

/-- An audit walk: inspect each address once, fail at a freed one, and push
the children of every address inspected for the first time.  Addresses in
`seen` were inspected earlier, possibly by an earlier walk of the same audit. -/
def walk (heap : Heap A Label) (freed : A → Prop) [DecidablePred freed] :
    ℕ → List A → Finset A → Bool
  | 0, stack, _ => stack.isEmpty
  | _ + 1, [], _ => true
  | fuel + 1, a :: rest, seen =>
    if a ∈ seen then walk heap freed fuel rest seen
    else if freed a then false
    else walk heap freed fuel (children heap a ++ rest) (insert a seen)

/-- What the inspected set promises: none of it is freed, and each child of
it is inspected or still waiting on the stack. -/
def WalkInv (heap : Heap A Label) (freed : A → Prop) (stack : List A) (seen : Finset A) : Prop :=
  ∀ x ∈ seen, ¬ freed x ∧ ∀ y, Edge heap x y → y ∈ seen ∨ y ∈ stack

variable (heap : Heap A Label) (freed : A → Prop) [DecidablePred freed]

/-- A successful walk ends with an inspected set that contains the stack and
the earlier inspected set, is closed under the heap's edges, and holds
nothing freed. -/
theorem walk_closure :
    ∀ fuel stack seen, walk heap freed fuel stack seen = true →
      WalkInv heap freed stack seen →
      ∃ final : Finset A, seen ⊆ final ∧ (∀ a ∈ stack, a ∈ final) ∧
        ∀ x ∈ final, ¬ freed x ∧ ∀ y, Edge heap x y → y ∈ final := by
  intro fuel
  induction fuel with
  | zero =>
    intro stack seen hwalk hinv
    have hnil : stack = [] := by simpa [walk] using hwalk
    subst hnil
    exact ⟨seen, le_rfl, by simp, fun x hx =>
      ⟨(hinv x hx).1, fun y hy => ((hinv x hx).2 y hy).resolve_right (by simp)⟩⟩
  | succ fuel ih =>
    intro stack seen hwalk hinv
    cases stack with
    | nil =>
      exact ⟨seen, le_rfl, by simp, fun x hx =>
        ⟨(hinv x hx).1, fun y hy => ((hinv x hx).2 y hy).resolve_right (by simp)⟩⟩
    | cons a rest =>
      by_cases hseen : a ∈ seen
      · have hrest : walk heap freed fuel rest seen = true := by
          simpa [walk, hseen] using hwalk
        have hinv' : WalkInv heap freed rest seen := by
          intro x hx
          refine ⟨(hinv x hx).1, fun y hy => ?_⟩
          rcases (hinv x hx).2 y hy with h | h
          · exact Or.inl h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inl hseen
            · exact Or.inr h
        obtain ⟨final, hsub, hstack, hclosed⟩ := ih rest seen hrest hinv'
        refine ⟨final, hsub, fun b hb => ?_, hclosed⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hsub hseen
        · exact hstack b hb
      · by_cases hfreed : freed a
        · simp [walk, hseen, hfreed] at hwalk
        · have hnext : walk heap freed fuel (children heap a ++ rest) (insert a seen) = true := by
            simpa [walk, hseen, hfreed] using hwalk
          have hinv' : WalkInv heap freed (children heap a ++ rest) (insert a seen) := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact ⟨hfreed, fun y hy => Or.inr (List.mem_append_left _ (mem_children.mpr hy))⟩
            · refine ⟨(hinv x hx).1, fun y hy => ?_⟩
              rcases (hinv x hx).2 y hy with h | h
              · exact Or.inl (Finset.mem_insert_of_mem h)
              · rcases List.mem_cons.mp h with rfl | h
                · exact Or.inl (Finset.mem_insert_self _ _)
                · exact Or.inr (List.mem_append_right _ h)
          obtain ⟨final, hsub, hstack, hclosed⟩ := ih _ _ hnext hinv'
          refine ⟨final, fun x hx => hsub (Finset.mem_insert_of_mem hx), fun b hb => ?_, hclosed⟩
          rcases List.mem_cons.mp hb with rfl | hb
          · exact hsub (Finset.mem_insert_self _ _)
          · exact hstack b (List.mem_append_right _ hb)

omit [DecidableEq A] [DecidablePred freed] in
/-- A closed set with nothing freed in it: everything its members reach
avoids the freed region. -/
theorem avoids_of_closed {final : Finset A}
    (hclosed : ∀ x ∈ final, ¬ freed x ∧ ∀ y, Edge heap x y → y ∈ final)
    {a : A} (ha : a ∈ final) : Avoids heap freed a := by
  intro b path
  have hb : b ∈ final := by
    induction path with
    | refl => exact ha
    | tail _ edge ih => exact (hclosed _ ih).2 _ edge
  exact (hclosed b hb).1

/-- Soundness of the audit walk: when a walk from an empty inspected set
succeeds, every holder it started from avoids the freed region, so the
collection keeps its value (`unfold_kept`). -/
theorem walk_sound {fuel : ℕ} {stack : List A}
    (hwalk : walk heap freed fuel stack ∅ = true) {a : A} (ha : a ∈ stack) :
    Avoids heap freed a := by
  obtain ⟨final, -, hstack, hclosed⟩ :=
    walk_closure heap freed fuel stack ∅ hwalk (by intro x hx; simp at hx)
  exact avoids_of_closed heap freed hclosed (hstack a ha)

/-- Later walks of one audit start from the earlier walks' inspected set;
their holders avoid the freed region on the same terms. -/
theorem walk_sound_continued {fuel : ℕ} {stack : List A} {seen : Finset A}
    (hwalk : walk heap freed fuel stack seen = true)
    (hseen : ∀ x ∈ seen, ¬ freed x ∧ ∀ y, Edge heap x y → y ∈ seen) {a : A}
    (ha : a ∈ stack ∨ a ∈ seen) : Avoids heap freed a := by
  have hinv : WalkInv heap freed stack seen :=
    fun x hx => ⟨(hseen x hx).1, fun y hy => Or.inl ((hseen x hx).2 y hy)⟩
  obtain ⟨final, hsub, hstack, hclosed⟩ := walk_closure heap freed fuel stack seen hwalk hinv
  rcases ha with ha | ha
  · exact avoids_of_closed heap freed hclosed (hstack a ha)
  · exact avoids_of_closed heap freed hclosed (hsub ha)

end Walk

section Paths

variable {Arena : Type} [DecidableEq Arena]

/-- The one arena a path of frames is closed in, if there is one. -/
def closedOwner : List Arena → Option Arena
  | [] => none
  | a :: rest => if rest.all (· = a) then some a else none

/-- The shortcut: the path is closed in an arena other than the forbidden one. -/
def ClosedOutside (forbidden : Arena) (path : List Arena) : Prop :=
  ∃ owner, closedOwner path = some owner ∧ owner ≠ forbidden

/-- The exact test: no frame of the path lies in the forbidden arena. -/
def Excludes (forbidden : Arena) (path : List Arena) : Prop :=
  ∀ arena ∈ path, arena ≠ forbidden

theorem closed_owner_sound {forbidden : Arena} {path : List Arena}
    (h : ClosedOutside forbidden path) : Excludes forbidden path := by
  obtain ⟨owner, hclosed, hne⟩ := h
  cases path with
  | nil => simp [closedOwner] at hclosed
  | cons a rest =>
    simp only [closedOwner] at hclosed
    split_ifs at hclosed with hall
    cases hclosed
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hne
    · have := List.all_eq_true.mp hall x hx
      simp only [decide_eq_true_eq] at this
      rw [this]
      exact hne

/-- A path through two arenas, neither forbidden, excludes the forbidden arena
without being closed in either. -/
theorem mixed_path_admitted :
    Excludes (0 : Fin 3) [1, 2] ∧ ¬ ClosedOutside (0 : Fin 3) [1, 2] := by
  refine ⟨fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> decide
  · rintro ⟨owner, hclosed, -⟩
    simp [closedOwner] at hclosed

/-- Requiring both tests is requiring the shortcut. -/
theorem both_iff_closed {forbidden : Arena} {path : List Arena} :
    (ClosedOutside forbidden path ∧ Excludes forbidden path) ↔
      ClosedOutside forbidden path :=
  ⟨And.left, fun h => ⟨h, closed_owner_sound h⟩⟩

end Paths

end Mettapedia.Machines.MovingCollectionHolders
