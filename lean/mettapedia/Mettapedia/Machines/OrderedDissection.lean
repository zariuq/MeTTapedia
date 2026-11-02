import Mettapedia.Machines.PolyCursor
import Mathlib.Data.List.OfFn

/-!
# Finite ordered dissections

An ordered polynomial gives each shape `s` the positions `Fin (arity s)`.
A dissection stores already processed positions (in reverse) and pending
positions, which may have different types. Advancement, bounded resumption
and conversion of processed values compose. Arbitrary containers need a chosen
finite ordering before using this cursor; no such ordering is inferred here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDissection

variable {S X Y Z : Type} {arity : S → Nat}

abbrev orderedPolynomial (S : Type) (arity : S → Nat) : PFunctor.{0, 0} :=
  ⟨S, fun s => Fin (arity s)⟩

structure Cursor (arity : S → Nat) (X Y : Type) where
  shape : S
  processedRev : List Y
  pending : List X
  length_eq : processedRev.length + pending.length = arity shape

def start : orderedPolynomial S arity X → Cursor arity X Y
  | ⟨s, f⟩ => ⟨s, [], List.ofFn f, by simp⟩

/-- The first pending value, without consuming it. -/
def peek (c : Cursor arity X Y) : Option X := c.pending.head?

/-- Advance one position, retaining order and the shape's exact arity. -/
def next (f : X → Y) : Cursor arity X Y → Option (Cursor arity X Y)
  | ⟨_, _, [], _⟩ => none
  | ⟨s, done, x :: xs, h⟩ => some ⟨s, f x :: done, xs, by
      simp only [List.length_cons] at h ⊢
      omega⟩

/-- Complete the pending traversal, keeping contribution order. -/
def complete (f : X → Y) (c : Cursor arity X Y) : List Y :=
  c.processedRev.reverse ++ c.pending.map f

theorem next_none_iff (f : X → Y) (c : Cursor arity X Y) :
    next f c = none ↔ c.pending = [] := by
  rcases c with ⟨s, done, pending, h⟩
  cases pending <;> simp [next]

theorem complete_next (f : X → Y) (c c' : Cursor arity X Y) (h : next f c = some c') :
    complete f c' = complete f c := by
  rcases c with ⟨s, done, pending, hl⟩
  cases pending with
  | nil => simp [next] at h
  | cons x xs =>
    cases h
    simp [complete, List.reverse_cons, List.append_assoc]

theorem next_shape (f : X → Y) (c c' : Cursor arity X Y) (h : next f c = some c') :
    c'.shape = c.shape := by
  rcases c with ⟨s, done, pending, hl⟩
  cases pending with
  | nil => simp [next] at h
  | cons x xs => cases h; rfl

/-- Service at most `n` positions; exhausted cursors remain unchanged. -/
def seek (f : X → Y) : Nat → Cursor arity X Y → Cursor arity X Y
  | 0, c => c
  | n + 1, c => match next f c with
    | none => c
    | some c' => seek f n c'

theorem seek_stuck (f : X → Y) (c : Cursor arity X Y) (h : next f c = none) (n : Nat) :
    seek f n c = c := by
  cases n <;> simp [seek, h]

/-- Bounded resumptions compose by addition of their service budgets. -/
theorem seek_add (f : X → Y) (n m : Nat) (c : Cursor arity X Y) :
    seek f (n + m) c = seek f m (seek f n c) := by
  induction n generalizing c with
  | zero => simp [seek]
  | succ n ih =>
    cases hn : next f c with
    | none => simp [seek_stuck f c hn]
    | some c' => simpa [seek, hn, Nat.succ_add] using ih c'

theorem complete_seek (f : X → Y) (n : Nat) (c : Cursor arity X Y) :
    complete f (seek f n c) = complete f c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases hn : next f c with
    | none => simp [seek, hn]
    | some c' => simpa [seek, hn, ih] using complete_next f c c' hn

theorem seek_shape (f : X → Y) (n : Nat) (c : Cursor arity X Y) :
    (seek f n c).shape = c.shape := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases hn : next f c with
    | none => simp [seek, hn]
    | some c' => simpa [seek, hn, ih] using next_shape f c c' hn

theorem complete_start (f : X → Y) (s : S) (values : Fin (arity s) → X) :
    complete f (start (arity := arity) ⟨s, values⟩) = List.ofFn (fun i => f (values i)) := by
  simp [complete, start, List.map_ofFn, Function.comp_def]

theorem pending_length_seek (f : X → Y) (n : Nat) (c : Cursor arity X Y) :
    (seek f n c).pending.length = c.pending.length - n := by
  induction n generalizing c with
  | zero => simp [seek]
  | succ n ih =>
    rcases c with ⟨s, done, pending, h⟩
    cases pending <;> simp [seek, next, ih]

theorem exhausted_iff (f : X → Y) (n : Nat) (c : Cursor arity X Y) :
    (seek f n c).pending = [] ↔ c.pending.length ≤ n := by
  have hl := pending_length_seek f n c
  constructor
  · intro h; rw [h] at hl; simp only [List.length_nil] at hl; omega
  · intro h
    cases hp : (seek f n c).pending with
    | nil => rfl
    | cons x xs => rw [hp] at hl; simp only [List.length_cons] at hl; omega

/-- Change the processed-value type without disturbing pending positions. -/
def mapProcessed (g : Y → Z) (c : Cursor arity X Y) : Cursor arity X Z :=
  ⟨c.shape, c.processedRev.map g, c.pending, by simpa using c.length_eq⟩

theorem mapProcessed_next (f : X → Y) (g : Y → Z) (c : Cursor arity X Y) :
    (next f c).map (mapProcessed g) = next (g ∘ f) (mapProcessed g c) := by
  rcases c with ⟨s, done, pending, h⟩
  cases pending <;> simp [next, mapProcessed]

theorem mapProcessed_complete (f : X → Y) (g : Y → Z) (c : Cursor arity X Y) :
    (complete f c).map g = complete (g ∘ f) (mapProcessed g c) := by
  simp [complete, mapProcessed, List.map_reverse, List.map_append, List.map_map]

theorem mapProcessed_seek (f : X → Y) (g : Y → Z) (n : Nat) (c : Cursor arity X Y) :
    mapProcessed g (seek f n c) = seek (g ∘ f) n (mapProcessed g c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    have ht := mapProcessed_next f g c
    cases hn : next f c with
    | none => simp [hn] at ht; simp [seek, hn, ← ht]
    | some c' => simp only [hn, Option.map_some] at ht; simp [seek, hn, ← ht, ih]

/-- A completed traversal does not insert a value into an empty shape. -/
example (f : X → Y) (n : Nat) :
    (seek f n (⟨(), [], [], rfl⟩ : Cursor (fun _ : Unit => 0) X Y)).pending = [] := by
  rw [seek_stuck f _ rfl n]

example : complete (fun n : Nat => n + 1)
    (seek (fun n => n + 1) 1 (⟨(), [], [1, 2, 3], rfl⟩ : Cursor (fun _ : Unit => 3) Nat Nat)) =
      [2, 3, 4] := by decide

/-- Reversing the stored prefix is necessary to preserve contribution order. -/
example : ([2, 1] ++ [3] : List Nat) ≠
    complete id (⟨(), [2, 1], [3], rfl⟩ : Cursor (fun _ : Unit => 3) Nat Nat) := by decide

#print axioms seek_add
#print axioms complete_seek
#print axioms mapProcessed_seek
#print axioms exhausted_iff

end Mettapedia.Machines.OrderedDissection
