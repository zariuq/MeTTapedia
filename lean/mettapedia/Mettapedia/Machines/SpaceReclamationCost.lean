import Mathlib.Tactic
import Mettapedia.Machines.ArenaHeldResources

/-!
# Reclaiming spaces: kept for the session, or freed with their region

A program may make a space per item.  Kept until the session ends, every space
made stays, so the memory grows with the spaces made, whatever is live.

A space belongs to the directive that made it until it escapes: stored into a
row that outlives the directive, or bound to a name.  When the directive ends,
its spaces that did not escape are freed; an escaped space is freed when what
held it lets it go.  No space is freed while something holds it.

The model: a run is a list of directives; each makes some spaces (fresh
numbers), lets some of them escape, and releases some spaces that escaped
before.  This file proves:
* `kept_eq_made`: keeping every space retains all the spaces made;
* `region_freed_unheld`: a space the region frees at a directive's end is held
  by nothing: it did not escape, or what held it released it;
* `region_kept_le`: under regions, what a run leaves held is within what
  escaped;
* `region_kept_bounded`: a run whose spaces never escape keeps none, while
  keeping every space retains all of them;
* `kept_card_of_fresh`: keeping every space retains as many as were made.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SpaceReclamationCost

/-- One directive: the spaces it makes, those of them that escape, and the
earlier escaped spaces it releases. -/
structure Directive where
  made : Finset Nat
  escaped : Finset Nat
  released : Finset Nat
  escaped_sub : escaped ⊆ made

/-- The spaces a run made. -/
def madeAll : List Directive → Finset Nat
  | [] => ∅
  | d :: rest => d.made ∪ madeAll rest

/-- Keeping every space for the session: the spaces retained after a run. -/
def kept (run : List Directive) : Finset Nat := madeAll run

theorem kept_eq_made (run : List Directive) : kept run = madeAll run := rfl

/-- The spaces held after a run under regions: those that escaped and were not
released by a later directive.  `held` is what earlier directives left held. -/
def regionHeld : Finset Nat → List Directive → Finset Nat
  | held, [] => held
  | held, d :: rest => regionHeld ((held \ d.released) ∪ d.escaped) rest

/-- What a directive's end frees: its spaces that did not escape, and the
spaces it released. -/
def freedAt (held : Finset Nat) (d : Directive) : Finset Nat :=
  (d.made \ d.escaped) ∪ (held ∩ d.released)

/-- A space freed at a directive's end is held by nothing after it, provided
the directive's fresh spaces are not among those already held. -/
theorem region_freed_unheld (held : Finset Nat) (d : Directive)
    (fresh : Disjoint d.made held) (s : Nat) (hs : s ∈ freedAt held d) :
    s ∉ (held \ d.released) ∪ d.escaped := by
  simp only [freedAt, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_inter] at hs
  simp only [Finset.mem_union, Finset.mem_sdiff, not_or, not_and, not_not]
  rcases hs with ⟨hmade, hesc⟩ | ⟨hheld, hrel⟩
  · exact ⟨fun hheld' => absurd hheld' (Finset.disjoint_left.mp fresh hmade),
      hesc⟩
  · exact ⟨fun _ => hrel,
      fun hesc => Finset.disjoint_left.mp fresh (d.escaped_sub hesc) hheld⟩

/-- Under regions, what a run leaves held is within what escaped. -/
theorem region_kept_le (held : Finset Nat) (run : List Directive) :
    regionHeld held run ⊆
      held ∪ (run.map Directive.escaped).foldr (· ∪ ·) ∅ := by
  induction run generalizing held with
  | nil => simp [regionHeld]
  | cons d rest ih =>
    intro s hs
    have := ih ((held \ d.released) ∪ d.escaped) hs
    simp only [Finset.mem_union, Finset.mem_sdiff, List.map_cons,
      List.foldr_cons] at this ⊢
    tauto

/-- A run whose spaces never escape keeps none under regions, while keeping
every space retains all it made. -/
theorem region_kept_bounded (run : List Directive)
    (hnone : ∀ d ∈ run, d.escaped = ∅) :
    regionHeld ∅ run = ∅ ∧ kept run = madeAll run := by
  refine ⟨?_, rfl⟩
  suffices h : ∀ held : Finset Nat, held = ∅ → regionHeld held run = ∅ by
    exact h ∅ rfl
  induction run with
  | nil => intro held h; simp [regionHeld, h]
  | cons d rest ih =>
    intro held h
    simp only [regionHeld]
    apply ih (fun d' hd' => hnone d' (List.mem_cons_of_mem d hd'))
    rw [hnone d List.mem_cons_self, h]
    simp

theorem disjoint_madeAll (m : Finset Nat) (rest : List Directive)
    (h : ∀ e ∈ rest, Disjoint m e.made) : Disjoint m (madeAll rest) := by
  induction rest with
  | nil => simp [madeAll]
  | cons e more ih =>
    simp only [madeAll]
    rw [Finset.disjoint_union_right]
    exact ⟨h e List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem e hx))⟩

/-- Without reclamation, a run of directives making fresh spaces keeps every
one: the memory is the spaces made. -/
theorem kept_card_of_fresh (run : List Directive)
    (hdisj : run.Pairwise (fun a b => Disjoint a.made b.made)) :
    (kept run).card = (run.map (fun d => d.made.card)).sum := by
  induction run with
  | nil => simp [kept, madeAll]
  | cons d rest ih =>
    rw [List.pairwise_cons] at hdisj
    simp only [kept, madeAll, List.map_cons, List.sum_cons] at ih ⊢
    rw [Finset.card_union_of_disjoint (disjoint_madeAll d.made rest hdisj.1),
      ih hdisj.2]

/-! ## Spaces held by arenas

The discipline of `ArenaHeldResources`, applied to spaces: an arena holding an
atom of a space holds the space, and a reset that leaves a space without a hold
releases it.  A loop makes a space per step, its atom in the machine's young
arena, and collects every `c` steps: the young arena is reset and only the live
state, which holds no earlier step's space, is kept.  Each collection releases
its round's spaces, so the loop retains at most the spaces made since the last
collection, where keeping every space retains all it made (`loop_kept_card`).
A space copied into the persistent arena stays held and is never released.

This section proves:
* `rounds_release`: after `k` rounds, every space the rounds made is released;
* `retained_le`: after `k` rounds and `j` more steps, at most `j` spaces made
  are unreleased;
* `escaped_kept`: a space the persistent arena holds is never released;
* `loop_kept_card`: keeping every space retains all `n` a loop makes.
-/

open Mettapedia.Machines.ArenaHeldResources

/-- The machine's young arena, where a step's atoms live, and the persistent
arena. -/
inductive LoopArena
  | young
  | persistent
  deriving DecidableEq

/-- `j` steps from space number `base`: step `i` makes space `base + i`, its
atom allocated in the young arena. -/
def steps (s : State LoopArena Nat) (base : Nat) : Nat → State LoopArena Nat
  | 0 => s
  | j + 1 => alloc (steps s base j) .young [base + j]

/-- A round: `c` steps, then a collection resetting the young arena; its
candidates are the round's spaces. -/
noncomputable def round (s : State LoopArena Nat) (base c : Nat) :
    State LoopArena Nat :=
  reset (steps s base c) .young 0 ((Finset.range c).image (base + ·))

/-- `k` rounds of `c` steps, numbering spaces from zero. -/
noncomputable def rounds (s : State LoopArena Nat) (c : Nat) :
    Nat → State LoopArena Nat
  | 0 => s
  | k + 1 => round (rounds s c k) (k * c) c

theorem steps_persistent (s : State LoopArena Nat) (base j : Nat) :
    (steps s base j).arenas .persistent = s.arenas .persistent := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [steps, alloc]
    rw [Function.update_of_ne (by decide)]
    exact ih

theorem steps_released (s : State LoopArena Nat) (base j : Nat) :
    (steps s base j).released = s.released := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

theorem round_persistent (s : State LoopArena Nat) (base c : Nat) :
    (round s base c).arenas .persistent = s.arenas .persistent := by
  simp only [round, reset]
  rw [Function.update_of_ne (by decide)]
  exact steps_persistent s base c

theorem round_young (s : State LoopArena Nat) (base c : Nat) :
    (round s base c).arenas .young = [] := by
  simp [round, reset]

theorem round_released_mono (s : State LoopArena Nat) (base c : Nat) :
    s.released ⊆ (round s base c).released := by
  intro r hr
  simp only [round, reset, Finset.mem_union]
  exact Or.inl (by rw [steps_released]; exact hr)

/-- A collection releases its round's spaces when the persistent arena holds
none of them. -/
theorem round_releases (s : State LoopArena Nat) (base c : Nat)
    (quiet : ∀ e ∈ s.arenas .persistent, ∀ r ∈ e, r < base ∨ base + c ≤ r)
    (i : Nat) (hi : i < c) : base + i ∈ (round s base c).released := by
  apply reset_releases
  · exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  · rintro ⟨a, e, member, refers⟩
    cases a with
    | young =>
      have empty : (round s base c).arenas .young = [] := round_young s base c
      simp only [round] at empty
      rw [empty] at member
      cases member
    | persistent =>
      have same := round_persistent s base c
      simp only [round] at same
      rw [same] at member
      rcases quiet e member _ refers with h | h <;> omega

theorem rounds_persistent (s : State LoopArena Nat) (c k : Nat) :
    (rounds s c k).arenas .persistent = s.arenas .persistent := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rounds]; rw [round_persistent, ih]

/-- After `k` rounds, every space the rounds made is released, provided the
persistent arena holds none of them. -/
theorem rounds_release (s : State LoopArena Nat) (c k : Nat)
    (quiet : ∀ e ∈ s.arenas .persistent, ∀ r ∈ e, k * c ≤ r) :
    ∀ r < k * c, r ∈ (rounds s c k).released := by
  induction k with
  | zero => intro r hr; omega
  | succ k ih =>
    intro r hr
    have quiet' : ∀ e ∈ s.arenas .persistent, ∀ r ∈ e, k * c ≤ r := by
      intro e he r' hr'
      have := quiet e he r' hr'
      rw [Nat.succ_mul] at this
      omega
    simp only [rounds]
    by_cases early : r < k * c
    · exact round_released_mono _ _ _ (ih quiet' r early)
    · have hround := round_releases (rounds s c k) (k * c) c
        (by
          intro e he r' hr'
          rw [rounds_persistent] at he
          have := quiet e he r' hr'
          rw [Nat.succ_mul] at this
          omega)
        (r - k * c) (by rw [Nat.succ_mul] at hr; omega)
      rwa [Nat.add_sub_cancel' (by omega)] at hround

/-- After `k` rounds and `j` more steps, at most `j` of the spaces made are
unreleased: the loop retains the spaces made since its last collection. -/
theorem retained_le (s : State LoopArena Nat) (c k j : Nat)
    (quiet : ∀ e ∈ s.arenas .persistent, ∀ r ∈ e, k * c ≤ r) :
    ((Finset.range (k * c + j)).filter
        (· ∉ (steps (rounds s c k) (k * c) j).released)).card ≤ j := by
  rw [steps_released]
  calc ((Finset.range (k * c + j)).filter
          (· ∉ (rounds s c k).released)).card
      ≤ ((Finset.range j).image (k * c + ·)).card := by
        apply Finset.card_le_card
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr
        have late : k * c ≤ r := by
          by_contra early
          exact hr.2 (rounds_release s c k quiet r (by omega))
        exact Finset.mem_image.mpr
          ⟨r - k * c, Finset.mem_range.mpr (by omega), by omega⟩
    _ ≤ (Finset.range j).card := Finset.card_image_le
    _ = j := Finset.card_range j

/-- A space the persistent arena holds is never released: a space copied
there, the escape, is kept. -/
theorem escaped_kept (s : State LoopArena Nat) (c k r : Nat)
    (fresh : r ∉ s.released)
    (held : ∃ e ∈ s.arenas .persistent, r ∈ e) :
    r ∉ (rounds s c k).released := by
  induction k with
  | zero => exact fresh
  | succ k ih =>
    simp only [rounds, round, reset, Finset.mem_union, Finset.mem_filter,
      not_or, not_and, not_not]
    refine ⟨by rw [steps_released]; exact ih, fun _ => ?_⟩
    obtain ⟨e, he, hr⟩ := held
    refine ⟨.persistent, e, ?_, hr⟩
    rw [Function.update_of_ne (by decide), steps_persistent, rounds_persistent]
    exact he

/-- The same loop as one directive, keeping every space: all `n` stay. -/
def loopDirective (n : Nat) : Directive :=
  { made := Finset.range n, escaped := ∅, released := ∅,
    escaped_sub := Finset.empty_subset _ }

theorem loop_kept_card (n : Nat) : (kept [loopDirective n]).card = n := by
  simp [kept, madeAll, loopDirective]

end Mettapedia.Machines.SpaceReclamationCost
